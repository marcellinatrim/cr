package main

import (
	"bufio"
	"bytes"
	"compress/gzip"
	"compress/zlib"
	"container/heap"
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/PuerkitoBio/goquery"
	"golang.org/x/net/html/charset"
)

type Config struct {
	DomainsFile        string
	WorkersPerDomain   int
	MaxTotalWorkers    int
	MaxPagesPerDomain  int
	RequestTimeout     time.Duration
	DomainDeadline     time.Duration
	CheckpointInterval time.Duration
	OutputDir          string
	StateDir           string
	UserAgents         []string
	AllowInsecureTLS   bool
}

type Finding struct {
	Domain         string    `json:"domain"`
	URL            string    `json:"url"`
	Method         string    `json:"method"`
	System         string    `json:"system"`
	Confidence     float64   `json:"confidence"`
	Tier           int       `json:"tier"`
	Signals        []string  `json:"signals"`
	Timestamp      time.Time `json:"timestamp"`
	FormScore      float64   `json:"form_score"`
	StructureScore float64   `json:"structure_score"`
	URLScore       float64   `json:"url_score"`
	TierOverride   int       `json:"-"`
}

type QueueEntry struct {
	URL        string    `json:"url"`
	Score      float64   `json:"score"`
	Depth      int       `json:"depth"`
	Discovered time.Time `json:"discovered"`
}

type queueItem struct {
	entry QueueEntry
	index int
}

type priorityBuffer struct {
	data []*queueItem
}

func (p *priorityBuffer) Len() int { return len(p.data) }
func (p *priorityBuffer) Less(i, j int) bool {
	if p.data[i].entry.Score == p.data[j].entry.Score {
		return p.data[i].entry.Discovered.After(p.data[j].entry.Discovered)
	}
	return p.data[i].entry.Score > p.data[j].entry.Score
}
func (p *priorityBuffer) Swap(i, j int) {
	p.data[i], p.data[j] = p.data[j], p.data[i]
	p.data[i].index = i
	p.data[j].index = j
}
func (p *priorityBuffer) Push(x interface{}) {
	item := x.(*queueItem)
	item.index = len(p.data)
	p.data = append(p.data, item)
}
func (p *priorityBuffer) Pop() interface{} {
	old := p.data
	n := len(old)
	item := old[n-1]
	old[n-1] = nil
	item.index = -1
	p.data = old[:n-1]
	return item
}
func (p *priorityBuffer) pushEntry(entry QueueEntry) {
	heap.Push(p, &queueItem{entry: entry})
}
func (p *priorityBuffer) popEntry() (QueueEntry, bool) {
	if p.Len() == 0 {
		return QueueEntry{}, false
	}
	item := heap.Pop(p).(*queueItem)
	return item.entry, true
}

type DiskQueue struct {
	path   string
	writer *os.File
	reader *os.File
	offset int64
	mu     sync.Mutex
}

func NewDiskQueue(path string) (*DiskQueue, error) {
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return nil, err
	}
	writer, err := os.OpenFile(path, os.O_CREATE|os.O_RDWR|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}
	dq := &DiskQueue{path: path, writer: writer}
	metaPath := path + ".meta"
	if data, err := os.ReadFile(metaPath); err == nil {
		if off, err := strconv.ParseInt(strings.TrimSpace(string(data)), 10, 64); err == nil {
			dq.offset = off
		}
	}
	return dq, nil
}

func (dq *DiskQueue) push(entry QueueEntry) error {
	dq.mu.Lock()
	defer dq.mu.Unlock()
	if dq.writer == nil {
		w, err := os.OpenFile(dq.path, os.O_CREATE|os.O_RDWR|os.O_APPEND, 0644)
		if err != nil {
			return err
		}
		dq.writer = w
	}
	payload, err := json.Marshal(entry)
	if err != nil {
		return err
	}
	line := append(payload, '\n')
	if _, err = dq.writer.Write(line); err != nil {
		return err
	}
	return dq.writer.Sync()
}

func (dq *DiskQueue) readChunk(limit int) ([]QueueEntry, error) {
	dq.mu.Lock()
	defer dq.mu.Unlock()
	if dq.reader == nil {
		r, err := os.OpenFile(dq.path, os.O_CREATE|os.O_RDWR, 0644)
		if err != nil {
			return nil, err
		}
		dq.reader = r
	}
	if _, err := dq.reader.Seek(dq.offset, io.SeekStart); err != nil {
		return nil, err
	}
	scanner := bufio.NewScanner(dq.reader)
	buffer := make([]byte, 0, 64*1024)
	scanner.Buffer(buffer, 16*1024*1024)
	entries := make([]QueueEntry, 0, limit)
	for len(entries) < limit && scanner.Scan() {
		line := scanner.Bytes()
		dq.offset += int64(len(line) + 1)
		var entry QueueEntry
		if err := json.Unmarshal(line, &entry); err != nil {
			continue
		}
		entries = append(entries, entry)
	}
	if err := scanner.Err(); err != nil {
		return entries, err
	}
	return entries, nil
}

func (dq *DiskQueue) persistOffset() error {
	dq.mu.Lock()
	defer dq.mu.Unlock()
	metaPath := dq.path + ".meta"
	tmpPath := metaPath + ".tmp"
	payload := []byte(fmt.Sprintf("%d\n", dq.offset))
	if err := os.WriteFile(tmpPath, payload, 0644); err != nil {
		return err
	}
	return os.Rename(tmpPath, metaPath)
}

func (dq *DiskQueue) close() error {
	dq.mu.Lock()
	defer dq.mu.Unlock()
	var err error
	if dq.writer != nil {
		if syncErr := dq.writer.Sync(); err == nil {
			err = syncErr
		}
		if closeErr := dq.writer.Close(); err == nil {
			err = closeErr
		}
		dq.writer = nil
	}
	if dq.reader != nil {
		if cerr := dq.reader.Close(); err == nil {
			err = cerr
		}
		dq.reader = nil
	}
	return err
}

func (dq *DiskQueue) Offset() int64 {
	dq.mu.Lock()
	defer dq.mu.Unlock()
	return dq.offset
}

func (dq *DiskQueue) SetOffset(offset int64) {
	dq.mu.Lock()
	dq.offset = offset
	dq.mu.Unlock()
}

type DomainStats struct {
	Pages           int64
	Findings        int64
	PrimaryFindings int64
	Tier4Findings   int64
	Errors          int64
	Queued          int64
	LastCheck       atomic.Value
}

type GlobalStats struct {
	DomainsTotal    int64
	DomainsActive   int64
	DomainsFinished int64
	TotalPages      int64
	TotalFindings   int64
	TotalPrimary    int64
	TotalTier4      int64
	TotalErrors     int64
}

type Aggregator struct {
	stats   *GlobalStats
	domains sync.Map
	ticker  *time.Ticker
	ctx     context.Context
	cancel  context.CancelFunc
	wg      sync.WaitGroup
}

func NewAggregator(ctx context.Context, interval time.Duration, stats *GlobalStats) *Aggregator {
	cctx, cancel := context.WithCancel(ctx)
	ag := &Aggregator{stats: stats, ticker: time.NewTicker(interval), ctx: cctx, cancel: cancel}
	ag.wg.Add(1)
	go ag.loop()
	return ag
}

func (ag *Aggregator) Register(domain string, stats *DomainStats) {
	ag.domains.Store(domain, stats)
}

func (ag *Aggregator) Unregister(domain string) {
	ag.domains.Delete(domain)
}

func (ag *Aggregator) Stop() {
	ag.cancel()
	if ag.ticker != nil {
		ag.ticker.Stop()
	}
	ag.wg.Wait()
}

func (ag *Aggregator) loop() {
	defer ag.wg.Done()
	for {
		select {
		case <-ag.ctx.Done():
			return
		case <-ag.ticker.C:
			ag.report()
		}
	}
}

func (ag *Aggregator) report() {
	totalDomains := atomic.LoadInt64(&ag.stats.DomainsTotal)
	active := atomic.LoadInt64(&ag.stats.DomainsActive)
	finished := atomic.LoadInt64(&ag.stats.DomainsFinished)
	pages := atomic.LoadInt64(&ag.stats.TotalPages)
	findings := atomic.LoadInt64(&ag.stats.TotalFindings)
	primary := atomic.LoadInt64(&ag.stats.TotalPrimary)
	tier4 := atomic.LoadInt64(&ag.stats.TotalTier4)
	errs := atomic.LoadInt64(&ag.stats.TotalErrors)
	domainSnapshots := make([]string, 0)
	ag.domains.Range(func(key, value interface{}) bool {
		domain := key.(string)
		st := value.(*DomainStats)
		last := time.Time{}
		if v := st.LastCheck.Load(); v != nil {
			if t, ok := v.(time.Time); ok {
				last = t
			}
		}
		total := atomic.LoadInt64(&st.Findings)
		pr := atomic.LoadInt64(&st.PrimaryFindings)
		reserve := atomic.LoadInt64(&st.Tier4Findings)
		domainSnapshots = append(domainSnapshots, fmt.Sprintf("%s страницы=%d находки=%d осн=%d резерв=%d ошибки=%d очередь=%d последнее=%s", domain, atomic.LoadInt64(&st.Pages), total, pr, reserve, atomic.LoadInt64(&st.Errors), atomic.LoadInt64(&st.Queued), last.Format(time.RFC3339)))
		return true
	})
	sort.Strings(domainSnapshots)
	if len(domainSnapshots) > 8 {
		domainSnapshots = domainSnapshots[:8]
	}
	line := fmt.Sprintf("сводка домены=%d активные=%d завершенные=%d страницы=%d находки=%d осн=%d резерв=%d ошибки=%d", totalDomains, active, finished, pages, findings, primary, tier4, errs)
	if len(domainSnapshots) > 0 {
		line += " домены:" + strings.Join(domainSnapshots, ";")
	}
	fmt.Println(line)
}

type MainCrawler struct {
	config     Config
	domains    []string
	results    chan *Finding
	ctx        context.Context
	cancel     context.CancelFunc
	stats      *GlobalStats
	aggregator *Aggregator
	tierFiles  map[int]*os.File
	tierEnc    map[int]*json.Encoder
	tierSync   map[int]time.Time
	outputMu   sync.Mutex
	resultsWG  sync.WaitGroup
	domainPool int
	domainsWG  sync.WaitGroup
	done       chan struct{}
	closeOnce  sync.Once
}

func NewMainCrawler(ctx context.Context, cfg Config, domains []string) (*MainCrawler, error) {
	if err := os.MkdirAll(cfg.OutputDir, 0755); err != nil {
		return nil, err
	}
	if err := os.MkdirAll(cfg.StateDir, 0755); err != nil {
		return nil, err
	}
	mc := &MainCrawler{config: cfg, domains: domains, results: make(chan *Finding, 2048)}
	mc.ctx, mc.cancel = context.WithCancel(ctx)
	mc.stats = &GlobalStats{}
	slots := cfg.MaxTotalWorkers / cfg.WorkersPerDomain
	if slots < 1 {
		slots = 1
	}
	mc.domainPool = slots
	mc.aggregator = NewAggregator(mc.ctx, 30*time.Second, mc.stats)
	mc.tierFiles = make(map[int]*os.File)
	mc.tierEnc = make(map[int]*json.Encoder)
	mc.tierSync = make(map[int]time.Time)
	for tier := 1; tier <= 4; tier++ {
		path := filepath.Join(cfg.OutputDir, fmt.Sprintf("tier%d.jsonl", tier))
		file, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
		if err != nil {
			return nil, err
		}
		mc.tierFiles[tier] = file
		encoder := json.NewEncoder(file)
		encoder.SetEscapeHTML(false)
		mc.tierEnc[tier] = encoder
		mc.tierSync[tier] = time.Time{}
	}
	return mc, nil
}

func (mc *MainCrawler) Close() {
	mc.cancel()
	mc.Wait()
}

func (mc *MainCrawler) Wait() {
	if mc.done != nil {
		<-mc.done
	}
	mc.closeOnce.Do(func() {
		for tier, f := range mc.tierFiles {
			if f == nil {
				continue
			}
			if err := f.Sync(); err != nil {
				mc.reportOutputError(fmt.Sprintf("tier-%d-sync-final", tier), err)
			}
			if err := f.Close(); err != nil {
				mc.reportOutputError(fmt.Sprintf("tier-%d-close", tier), err)
			}
		}
		mc.aggregator.Stop()
	})
}

func (mc *MainCrawler) Run() {
	mc.done = make(chan struct{})
	mc.resultsWG.Add(1)
	go mc.handleResults()
	domainsCh := make(chan string)
	go func() {
		defer close(domainsCh)
		for _, domain := range mc.domains {
			select {
			case <-mc.ctx.Done():
				return
			case domainsCh <- domain:
			}
		}
	}()
	workerCount := mc.domainPool
	if workerCount < 1 {
		workerCount = 1
	}
	mc.domainsWG.Add(workerCount)
	for i := 0; i < workerCount; i++ {
		go func() {
			defer mc.domainsWG.Done()
			for domain := range domainsCh {
				if mc.ctx.Err() != nil {
					return
				}
				mc.processDomain(domain)
			}
		}()
	}
	go func() {
		mc.domainsWG.Wait()
		close(mc.results)
		mc.resultsWG.Wait()
		close(mc.done)
	}()
}

func (mc *MainCrawler) handleResults() {
	defer mc.resultsWG.Done()
	for finding := range mc.results {
		mc.persistFinding(finding)
	}
}

func (mc *MainCrawler) reportOutputError(stage string, err error) {
	if err == nil {
		return
	}
	atomic.AddInt64(&mc.stats.TotalErrors, 1)
	fmt.Fprintf(os.Stderr, "вывод этап=%s ошибка=%v\n", stage, err)
}

func (mc *MainCrawler) persistFinding(f *Finding) {
	mc.outputMu.Lock()
	defer mc.outputMu.Unlock()
	tier := f.Tier
	if tier < 1 || tier > 4 {
		tier = 4
	}
	if enc := mc.tierEnc[tier]; enc != nil {
		if err := enc.Encode(f); err != nil {
			mc.reportOutputError(fmt.Sprintf("tier-%d-write", tier), err)
		} else if file := mc.tierFiles[tier]; file != nil {
			last := mc.tierSync[tier]
			if time.Since(last) > 5*time.Second {
				if err := file.Sync(); err != nil {
					mc.reportOutputError(fmt.Sprintf("tier-%d-sync", tier), err)
				} else {
					mc.tierSync[tier] = time.Now()
				}
			}
		}
	}
}

func (mc *MainCrawler) processDomain(domain string) {
	atomic.AddInt64(&mc.stats.DomainsTotal, 1)
	atomic.AddInt64(&mc.stats.DomainsActive, 1)
	defer atomic.AddInt64(&mc.stats.DomainsActive, -1)
	defer atomic.AddInt64(&mc.stats.DomainsFinished, 1)
	ctx, cancel := mc.domainContext()
	defer cancel()
	stats := &DomainStats{}
	stats.LastCheck.Store(time.Now())
	mc.aggregator.Register(domain, stats)
	defer mc.aggregator.Unregister(domain)
	crawler, err := NewDomainCrawler(ctx, cancel, domain, &mc.config, mc.results, stats, mc.stats)
	if err != nil {
		atomic.AddInt64(&mc.stats.TotalErrors, 1)
		return
	}
	crawler.Run()
}

func (mc *MainCrawler) domainContext() (context.Context, context.CancelFunc) {
	if mc.config.DomainDeadline > 0 {
		return context.WithTimeout(mc.ctx, mc.config.DomainDeadline)
	}
	return context.WithCancel(mc.ctx)
}

type DomainCrawler struct {
	domain      string
	config      *Config
	ctx         context.Context
	cancel      context.CancelFunc
	results     chan<- *Finding
	httpClient  *http.Client
	queue       *DiskQueue
	buffer      *priorityBuffer
	bufferMu    sync.Mutex
	pending     chan QueueEntry
	stats       *DomainStats
	global      *GlobalStats
	visited     map[uint64]struct{}
	visitedMu   sync.RWMutex
	visitedFile *os.File
	statePath   string
	lastPersist time.Time
	rng         *rand.Rand
	limiter     chan struct{}
	wg          sync.WaitGroup
	exhausted   int32
	resumed     bool
}

func (dc *DomainCrawler) reportDomainError(stage string, err error) {
	if err == nil {
		return
	}
	atomic.AddInt64(&dc.stats.Errors, 1)
	atomic.AddInt64(&dc.global.TotalErrors, 1)
	fmt.Fprintf(os.Stderr, "домен=%s этап=%s ошибка=%v\n", dc.domain, stage, err)
}

type domainCheckpoint struct {
	Pages    int64     `json:"pages"`
	Findings int64     `json:"findings"`
	Primary  int64     `json:"primary_findings"`
	Tier4    int64     `json:"tier4_findings"`
	Offset   int64     `json:"offset"`
	Updated  time.Time `json:"updated"`
}

func NewDomainCrawler(ctx context.Context, cancel context.CancelFunc, domain string, cfg *Config, results chan<- *Finding, stats *DomainStats, global *GlobalStats) (*DomainCrawler, error) {
	client := buildHTTPClient(cfg.RequestTimeout, cfg.AllowInsecureTLS)
	queuePath := filepath.Join(cfg.StateDir, domain+"_queue.jsonl")
	queue, err := NewDiskQueue(queuePath)
	if err != nil {
		return nil, err
	}
	visitedPath := filepath.Join(cfg.StateDir, domain+"_visited.jsonl")
	visitedFile, err := os.OpenFile(visitedPath, os.O_CREATE|os.O_RDWR|os.O_APPEND, 0644)
	if err != nil {
		return nil, err
	}
	visited := make(map[uint64]struct{})
	if err := loadVisited(visitedPath, visited); err != nil {
		return nil, err
	}
	statePath := filepath.Join(cfg.StateDir, domain+"_state.json")
	dc := &DomainCrawler{
		domain:      domain,
		config:      cfg,
		ctx:         ctx,
		cancel:      cancel,
		results:     results,
		httpClient:  client,
		queue:       queue,
		buffer:      &priorityBuffer{},
		pending:     make(chan QueueEntry, cfg.WorkersPerDomain*4),
		stats:       stats,
		global:      global,
		visited:     visited,
		visitedFile: visitedFile,
		statePath:   statePath,
		rng:         rand.New(rand.NewSource(time.Now().UnixNano())),
		limiter:     make(chan struct{}, cfg.WorkersPerDomain),
	}
	heap.Init(dc.buffer)
	if len(visited) > 0 {
		dc.resumed = true
	}
	dc.restoreState()
	return dc, nil
}

func (dc *DomainCrawler) Run() {
	defer dc.cleanup()
	dc.seed()
	for i := 0; i < dc.config.WorkersPerDomain; i++ {
		dc.wg.Add(1)
		go dc.worker()
	}
	dc.wg.Add(1)
	go dc.dispatcher()
	dc.wg.Wait()
}

func (dc *DomainCrawler) cleanup() {
	dc.flushAll()
	if err := dc.queue.persistOffset(); err != nil {
		dc.reportDomainError("persist-offset-final", err)
	}
	if err := dc.queue.close(); err != nil {
		dc.reportDomainError("queue-close", err)
	}
	if dc.visitedFile != nil {
		dc.visitedMu.Lock()
		if err := dc.visitedFile.Sync(); err != nil {
			dc.reportDomainError("visited-sync", err)
		}
		if err := dc.visitedFile.Close(); err != nil {
			dc.reportDomainError("visited-close", err)
		}
		dc.visitedMu.Unlock()
	}
}

func (dc *DomainCrawler) flushAll() {
	dc.bufferMu.Lock()
	defer dc.bufferMu.Unlock()
	for dc.buffer.Len() > 0 {
		entry := heap.Pop(dc.buffer).(*queueItem).entry
		if err := dc.queue.push(entry); err != nil {
			dc.reportDomainError("queue-flush", err)
		}
	}
	atomic.StoreInt64(&dc.stats.Queued, 0)
}

func (dc *DomainCrawler) seed() {
	if dc.resumed {
		dc.loadFromDisk()
		return
	}
	primary := "https://" + dc.domain
	if err := dc.enqueueSeed(primary); err != nil {
		fallback := "http://" + dc.domain
		dc.enqueueSeed(fallback)
	}
	dc.flushBuffer()
}

func (dc *DomainCrawler) enqueueSeed(start string) error {
	entry := QueueEntry{URL: start, Score: 1.0, Depth: 0, Discovered: time.Now()}
	return dc.enqueue(entry)
}

func (dc *DomainCrawler) dispatcher() {
	defer dc.wg.Done()
	ticker := time.NewTicker(2 * time.Second)
	defer ticker.Stop()
	for {
		select {
		case <-dc.ctx.Done():
			close(dc.pending)
			return
		default:
		}
		if len(dc.pending) >= cap(dc.pending)-1 {
			time.Sleep(25 * time.Millisecond)
			continue
		}
		entry, ok := dc.popBuffer()
		if !ok {
			if !dc.loadFromDisk() {
				if atomic.LoadInt32(&dc.exhausted) == 1 {
					close(dc.pending)
					return
				}
				select {
				case <-ticker.C:
					dc.flushBuffer()
				default:
				}
				time.Sleep(150 * time.Millisecond)
				continue
			}
			continue
		}
		select {
		case dc.pending <- entry:
		case <-dc.ctx.Done():
			close(dc.pending)
			return
		}
	}
}

func (dc *DomainCrawler) worker() {
	defer dc.wg.Done()
	for entry := range dc.pending {
		if entry.URL == "" {
			continue
		}
		if atomic.LoadInt64(&dc.stats.Pages) >= int64(dc.config.MaxPagesPerDomain) {
			atomic.StoreInt32(&dc.exhausted, 1)
			continue
		}
		if atomic.LoadInt64(&dc.stats.PrimaryFindings) >= 50 {
			atomic.StoreInt32(&dc.exhausted, 1)
			continue
		}
		dc.processEntry(entry)
	}
}

func (dc *DomainCrawler) processEntry(entry QueueEntry) {
	select {
	case dc.limiter <- struct{}{}:
	case <-dc.ctx.Done():
		return
	}
	defer func() { <-dc.limiter }()
	if !dc.markVisited(entry.URL) {
		return
	}
	start := time.Now()
	doc, finalURL, lastModified, _, err := dc.fetch(entry.URL)
	if err != nil {
		dc.reportDomainError("fetch", err)
		dc.touch()
		return
	}
	atomic.AddInt64(&dc.stats.Pages, 1)
	atomic.AddInt64(&dc.global.TotalPages, 1)
	dc.touch()
	structureScore := analyzePageStructure(doc)
	findings := dc.inspectForms(doc, finalURL)
	for _, finding := range findings {
		finding.Domain = dc.domain
		finding.URL = finalURL
		finding.StructureScore = structureScore
		finding.URLScore = scoreURL(finalURL, lastModified, entry.Score)
		finding.Confidence = clamp(finding.FormScore*0.6+structureScore*0.25+finding.URLScore*0.15, 0, 1)
		tier := pickTier(finding.Confidence)
		if finding.TierOverride > 0 {
			tier = finding.TierOverride
		}
		finding.Tier = tier
		finding.Timestamp = time.Now()
		atomic.AddInt64(&dc.stats.Findings, 1)
		atomic.AddInt64(&dc.global.TotalFindings, 1)
		if tier <= 3 {
			atomic.AddInt64(&dc.stats.PrimaryFindings, 1)
			atomic.AddInt64(&dc.global.TotalPrimary, 1)
		} else {
			atomic.AddInt64(&dc.stats.Tier4Findings, 1)
			atomic.AddInt64(&dc.global.TotalTier4, 1)
		}
		select {
		case dc.results <- finding:
		case <-dc.ctx.Done():
			return
		}
	}
	if atomic.LoadInt64(&dc.stats.PrimaryFindings) >= 50 {
		atomic.StoreInt32(&dc.exhausted, 1)
		return
	}
	if atomic.LoadInt64(&dc.stats.Pages) >= int64(dc.config.MaxPagesPerDomain) {
		atomic.StoreInt32(&dc.exhausted, 1)
		return
	}
	discovered := dc.extractLinks(doc, finalURL)
	freshness := scoreFreshness(lastModified, start)
	for _, link := range discovered {
		entryScore := clamp(entry.Score*0.65+freshness*0.35+scoreURL(link, time.Time{}, 0), 0, 1)
		child := QueueEntry{URL: link, Score: entryScore, Depth: entry.Depth + 1, Discovered: time.Now()}
		dc.enqueue(child)
	}
	if time.Since(dc.lastPersist) > dc.config.CheckpointInterval {
		dc.persistState()
	}
}

func (dc *DomainCrawler) fetch(raw string) (*goquery.Document, string, time.Time, int, error) {
	parsed, err := url.Parse(raw)
	if err != nil {
		return nil, raw, time.Time{}, 0, err
	}
	current := parsed
	attempts := 0
	for {
		req, err := http.NewRequestWithContext(dc.ctx, http.MethodGet, current.String(), nil)
		if err != nil {
			return nil, current.String(), time.Time{}, 0, err
		}
		req.Header.Set("User-Agent", dc.pickAgent())
		req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
		req.Header.Set("Accept-Language", "en-US,en;q=0.8,ru;q=0.7")
		res, err := dc.httpClient.Do(req)
		if err != nil {
			if attempts == 0 && current.Scheme == "https" && shouldDowngradeTLS(err) {
				attempts++
				current.Scheme = "http"
				raw = current.String()
				continue
			}
			return nil, current.String(), time.Time{}, 0, err
		}
		defer res.Body.Close()
		if res.StatusCode >= 400 {
			return nil, res.Request.URL.String(), time.Time{}, res.StatusCode, fmt.Errorf("status %d", res.StatusCode)
		}
		body, err := decodeBody(res)
		if err != nil {
			return nil, res.Request.URL.String(), time.Time{}, res.StatusCode, err
		}
		doc, err := goquery.NewDocumentFromReader(body)
		if err != nil {
			return nil, res.Request.URL.String(), time.Time{}, res.StatusCode, err
		}
		finalURL := res.Request.URL.String()
		var lastModified time.Time
		if last := res.Header.Get("Last-Modified"); last != "" {
			if parsed, err := http.ParseTime(last); err == nil {
				lastModified = parsed
			}
		}
		return doc, finalURL, lastModified, res.StatusCode, nil
	}
}

func shouldDowngradeTLS(err error) bool {
	var urlErr *url.Error
	if !errors.As(err, &urlErr) {
		return false
	}
	var hostnameErr x509.HostnameError
	if errors.As(urlErr.Err, &hostnameErr) {
		return true
	}
	var certErr *x509.CertificateInvalidError
	if errors.As(urlErr.Err, &certErr) {
		if certErr.Reason == x509.HostnameError {
			return true
		}
	}
	return false
}

func decodeBody(res *http.Response) (io.Reader, error) {
	reader := res.Body
	encoding := strings.ToLower(res.Header.Get("Content-Encoding"))
	switch encoding {
	case "gzip":
		gr, err := gzip.NewReader(reader)
		if err != nil {
			return nil, err
		}
		defer gr.Close()
		buf := new(bytes.Buffer)
		if _, err := io.Copy(buf, gr); err != nil {
			return nil, err
		}
		return convertEncoding(res.Header.Get("Content-Type"), buf.Bytes())
	case "deflate":
		zr, err := zlib.NewReader(reader)
		if err != nil {
			return nil, err
		}
		defer zr.Close()
		buf := new(bytes.Buffer)
		if _, err := io.Copy(buf, zr); err != nil {
			return nil, err
		}
		return convertEncoding(res.Header.Get("Content-Type"), buf.Bytes())
	default:
		buf := new(bytes.Buffer)
		if _, err := io.Copy(buf, reader); err != nil {
			return nil, err
		}
		return convertEncoding(res.Header.Get("Content-Type"), buf.Bytes())
	}
}

func convertEncoding(contentType string, data []byte) (io.Reader, error) {
	lower := strings.ToLower(contentType)
	if strings.Contains(lower, "charset=") {
		parts := strings.Split(lower, "charset=")
		charsetName := strings.TrimSpace(parts[len(parts)-1])
		decoder, err := charset.NewReaderLabel(charsetName, bytes.NewReader(data))
		if err == nil {
			converted := new(bytes.Buffer)
			if _, err := io.Copy(converted, decoder); err == nil {
				return converted, nil
			}
		}
	}
	enc, _, _ := charset.DetermineEncoding(data, contentType)
	if enc != nil {
		decoder := enc.NewDecoder()
		converted := new(bytes.Buffer)
		if _, err := io.Copy(converted, decoder.Reader(bytes.NewReader(data))); err == nil {
			return converted, nil
		}
	}
	return bytes.NewReader(data), nil
}

func buildHTTPClient(timeout time.Duration, allowInsecure bool) *http.Client {
	tlsConfig := &tls.Config{MinVersion: tls.VersionTLS12}
	if allowInsecure {
		tlsConfig.InsecureSkipVerify = true
	}
	transport := &http.Transport{
		Proxy:               http.ProxyFromEnvironment,
		DialContext:         (&net.Dialer{Timeout: 20 * time.Second, KeepAlive: 30 * time.Second}).DialContext,
		ForceAttemptHTTP2:   true,
		MaxIdleConns:        256,
		MaxIdleConnsPerHost: 16,
		IdleConnTimeout:     90 * time.Second,
		TLSClientConfig:     tlsConfig,
	}
	return &http.Client{Timeout: timeout, Transport: transport}
}

func (dc *DomainCrawler) pickAgent() string {
	if len(dc.config.UserAgents) == 0 {
		return "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
	}
	return dc.config.UserAgents[dc.rng.Intn(len(dc.config.UserAgents))]
}

func (dc *DomainCrawler) extractLinks(doc *goquery.Document, base string) []string {
	baseURL, err := url.Parse(base)
	if err != nil {
		return nil
	}
	seen := make(map[string]struct{})
	var links []string
	doc.Find("a[href]").Each(func(i int, sel *goquery.Selection) {
		href := strings.TrimSpace(sel.AttrOr("href", ""))
		if href == "" {
			return
		}
		ref, err := baseURL.Parse(href)
		if err != nil {
			return
		}
		if ref.Hostname() != baseURL.Hostname() {
			return
		}
		ref.Fragment = ""
		normalized := ref.String()
		if _, ok := seen[normalized]; ok {
			return
		}
		if isSystemPath(normalized) {
			return
		}
		seen[normalized] = struct{}{}
		links = append(links, normalized)
	})
	return links
}

func isSystemPath(u string) bool {
	lower := strings.ToLower(u)
	blocked := []string{"/wp-json", "/feed", "/xmlrpc.php", "/cdn-cgi", "/wp-login", "/wp-admin", "/signin", "/signup", "/cart", "/checkout", "/privacy", "/terms", "/login", "/register", "/admin"}
	for _, b := range blocked {
		if strings.Contains(lower, b) {
			return true
		}
	}
	return false
}

func (dc *DomainCrawler) inspectForms(doc *goquery.Document, url string) []*Finding {
	var findings []*Finding
	doc.Find("form").Each(func(i int, form *goquery.Selection) {
		score, method, system, signals := analyzeForm(form, doc)
		if score <= 0 {
			return
		}
		findings = append(findings, &Finding{URL: url, Method: method, System: system, FormScore: score, Signals: signals})
	})
	anomalies := detectTierFourAnomalies(doc, url)
	if len(anomalies) > 0 {
		findings = append(findings, anomalies...)
	}
	return findings
}

func detectTierFourAnomalies(doc *goquery.Document, url string) []*Finding {
	var findings []*Finding
	seen := make(map[string]struct{})
	register := func(key, method, system string, base float64, signalParts ...string) {
		if _, exists := seen[key]; exists {
			return
		}
		seen[key] = struct{}{}
		signals := make([]string, 0, len(signalParts)+2)
		signals = append(signals, "tier4:anomaly")
		signals = append(signals, signalParts...)
		findings = append(findings, &Finding{
			URL:          url,
			Method:       method,
			System:       system,
			FormScore:    clamp(base, 0, 0.45),
			Signals:      signals,
			TierOverride: 4,
		})
	}
	scriptPatterns := []struct {
		key    string
		tokens []string
		system string
		base   float64
		label  string
	}{
		{key: "utterances", tokens: []string{"utteranc.es"}, system: "utterances", base: 0.3, label: "script:utterances"},
		{key: "giscus", tokens: []string{"giscus.app"}, system: "giscus", base: 0.3, label: "script:giscus"},
		{key: "hyvor", tokens: []string{"talk.hyvor.com", "embed"}, system: "hyvor", base: 0.28, label: "script:hyvor"},
		{key: "cackle", tokens: []string{"cackle.me"}, system: "cackle", base: 0.27, label: "script:cackle"},
		{key: "commento", tokens: []string{"commento"}, system: "commento", base: 0.26, label: "script:commento"},
		{key: "isso", tokens: []string{"isso.js"}, system: "isso", base: 0.25, label: "script:isso"},
		{key: "remark42", tokens: []string{"remark42"}, system: "remark42", base: 0.27, label: "script:remark42"},
	}
	doc.Find("script[src]").Each(func(i int, sel *goquery.Selection) {
		src := strings.ToLower(strings.TrimSpace(sel.AttrOr("src", "")))
		if src == "" {
			return
		}
		for _, pattern := range scriptPatterns {
			matched := true
			for _, token := range pattern.tokens {
				if !strings.Contains(src, token) {
					matched = false
					break
				}
			}
			if matched {
				register("script:"+pattern.key, "widget", pattern.system, pattern.base, pattern.label)
				break
			}
		}
	})
	iframePatterns := []struct {
		key    string
		token  string
		system string
		base   float64
		label  string
	}{
		{key: "vk", token: "vk.com/widget_comments", system: "vk-widget", base: 0.3, label: "iframe:vk"},
		{key: "fb", token: "facebook.com/plugins/comments", system: "facebook", base: 0.3, label: "iframe:facebook"},
		{key: "disqus", token: "disqus.com/embed", system: "disqus-iframe", base: 0.32, label: "iframe:disqus"},
		{key: "telegram", token: "telegram.org/js/", system: "telegram-comments", base: 0.25, label: "iframe:telegram"},
		{key: "cackle-frame", token: "cackle.me", system: "cackle", base: 0.27, label: "iframe:cackle"},
	}
	doc.Find("iframe[src]").Each(func(i int, sel *goquery.Selection) {
		src := strings.ToLower(strings.TrimSpace(sel.AttrOr("src", "")))
		if src == "" {
			return
		}
		for _, pattern := range iframePatterns {
			if strings.Contains(src, pattern.token) {
				register("iframe:"+pattern.key, "embed", pattern.system, pattern.base, pattern.label)
				break
			}
		}
	})
	doc.Find("*[data-widget],[data-module],[data-component],[data-role],[data-controller]").Each(func(i int, sel *goquery.Selection) {
		raw := strings.ToLower(strings.Join([]string{
			sel.AttrOr("data-widget", ""),
			sel.AttrOr("data-module", ""),
			sel.AttrOr("data-component", ""),
			sel.AttrOr("data-role", ""),
			sel.AttrOr("data-controller", ""),
		}, " "))
		tokens := []struct {
			key    string
			marker string
			system string
		}{
			{key: "guestbook", marker: "guestbook", system: "guestbook"},
			{key: "wall", marker: "wall", system: "wall"},
			{key: "shoutbox", marker: "shout", system: "shoutbox"},
			{key: "testimonials", marker: "testimonial", system: "testimonials"},
			{key: "留言", marker: "留言", system: "留言板"},
		}
		for _, token := range tokens {
			if strings.Contains(raw, token.marker) {
				register("data:"+token.key, "widget", token.system, 0.24, "data:"+token.key)
				break
			}
		}
	})
	classSelectors := []struct {
		key    string
		substr string
		label  string
	}{
		{key: "guestbook-class", substr: "guestbook", label: "class:guestbook"},
		{key: "wall", substr: "wall-of-love", label: "class:wall"},
		{key: "testimonial", substr: "testimonials", label: "class:testimonials"},
		{key: "shoutbox", substr: "shoutbox", label: "class:shoutbox"},
		{key: "gbook", substr: "gbook", label: "class:gbook"},
	}
	doc.Find("div,section,aside").Each(func(i int, sel *goquery.Selection) {
		classAttr := strings.ToLower(sel.AttrOr("class", ""))
		idAttr := strings.ToLower(sel.AttrOr("id", ""))
		combined := classAttr + " " + idAttr
		for _, cs := range classSelectors {
			if strings.Contains(combined, cs.substr) {
				register("structure:"+cs.key, "section", cs.substr, 0.23, cs.label)
				break
			}
		}
	})
	doc.Find("h1,h2,h3,h4").Each(func(i int, sel *goquery.Selection) {
		text := strings.ToLower(strings.TrimSpace(sel.Text()))
		if text == "" {
			return
		}
		keywords := []struct {
			key    string
			phrase string
		}{
			{key: "guestbook-heading", phrase: "guestbook"},
			{key: "livredor", phrase: "livre d'or"},
			{key: "留言板", phrase: "留言"},
			{key: "wall-heading", phrase: "wall"},
			{key: "обратная", phrase: "книга гостей"},
			{key: "访客", phrase: "访客留言"},
		}
		for _, kw := range keywords {
			if strings.Contains(text, kw.phrase) {
				register("heading:"+kw.key, "section", "heading", 0.22, "heading:"+kw.key)
				break
			}
		}
	})
	if len(findings) > 8 {
		findings = findings[:8]
	}
	return findings
}

func analyzeForm(form *goquery.Selection, doc *goquery.Document) (float64, string, string, []string) {
	score := 0.0
	signals := make([]string, 0, 8)
	textareas := form.Find("textarea")
	taCount := textareas.Length()
	if taCount > 0 {
		score += 0.35
		signals = append(signals, fmt.Sprintf("textarea:%d", taCount))
	}
	fieldScore, fieldSignals := inspectFields(form)
	score += fieldScore
	signals = append(signals, fieldSignals...)
	contextScore, contextSignals := inspectContext(form, doc)
	score += contextScore
	signals = append(signals, contextSignals...)
	submitScore, submitSignals := inspectSubmit(form)
	score += submitScore
	signals = append(signals, submitSignals...)
	layoutScore, layoutSignals := inspectLayout(form, doc)
	score += layoutScore
	signals = append(signals, layoutSignals...)
	score = clamp(score, 0, 1.2)
	method := strings.ToLower(form.AttrOr("method", "post"))
	system := detectSystem(form)
	return clamp(score, 0, 1), method, system, signals
}

func inspectFields(form *goquery.Selection) (float64, []string) {
	score := 0.0
	signals := []string{}
	inputs := form.Find("input")
	hasName := false
	hasEmail := false
	hasWebsite := false
	hasPhone := false
	hasSubject := false
	inputs.Each(func(i int, sel *goquery.Selection) {
		t := strings.ToLower(sel.AttrOr("type", "text"))
		name := strings.ToLower(sel.AttrOr("name", ""))
		placeholder := strings.ToLower(sel.AttrOr("placeholder", ""))
		composite := name + " " + placeholder + " " + t
		if strings.Contains(composite, "email") || t == "email" {
			hasEmail = true
		}
		if strings.Contains(composite, "name") && !strings.Contains(composite, "username") {
			hasName = true
		}
		if strings.Contains(composite, "website") || strings.Contains(composite, "url") || t == "url" {
			hasWebsite = true
		}
		if strings.Contains(composite, "phone") || strings.Contains(composite, "tel") || t == "tel" {
			hasPhone = true
		}
		if strings.Contains(composite, "subject") || strings.Contains(composite, "topic") {
			hasSubject = true
		}
	})
	if hasName && hasEmail {
		score += 0.25
		signals = append(signals, "field:name+email")
	}
	if hasWebsite {
		score += 0.1
		signals = append(signals, "field:website")
	}
	if hasPhone {
		score -= 0.3
		signals = append(signals, "field:phone")
	}
	if hasSubject {
		score -= 0.25
		signals = append(signals, "field:subject")
	}
	return score, signals
}

func inspectContext(form *goquery.Selection, doc *goquery.Document) (float64, []string) {
	score := 0.0
	signals := []string{}
	surrounding := form.PrevAllFiltered("h1,h2,h3,h4,p,strong,div")
	limit := surrounding.Length()
	if limit > 4 {
		limit = 4
	}
	text := ""
	if limit > 0 {
		text = strings.ToLower(surrounding.Slice(0, limit).Text())
	}
	positives := []string{"leave a comment", "add comment", "post comment", "your thoughts", "ответить", "комментар", "обсуждени", "share feedback"}
	negatives := []string{"contact", "support", "sales", "запрос", "обратная", "поддержк", "заказ"}
	for _, kw := range positives {
		if strings.Contains(text, kw) {
			score += 0.3
			signals = append(signals, "context:"+kw)
			break
		}
	}
	for _, kw := range negatives {
		if strings.Contains(text, kw) {
			score -= 0.35
			signals = append(signals, "context-neg:"+kw)
			break
		}
	}
	return score, signals
}

func inspectSubmit(form *goquery.Selection) (float64, []string) {
	submit := form.Find("button[type='submit'],input[type='submit'],button:not([type])")
	text := strings.ToLower(submit.Text() + " " + submit.AttrOr("value", ""))
	score := 0.0
	signals := []string{}
	positives := []string{"post", "comment", "reply", "отправить", "ответить", "share"}
	negatives := []string{"send", "submit", "contact", "запрос", "order"}
	for _, kw := range positives {
		if strings.Contains(text, kw) {
			score += 0.2
			signals = append(signals, "submit:"+kw)
			break
		}
	}
	for _, kw := range negatives {
		if strings.Contains(text, kw) {
			score -= 0.2
			signals = append(signals, "submit-neg:"+kw)
			break
		}
	}
	return score, signals
}

func inspectLayout(form *goquery.Selection, doc *goquery.Document) (float64, []string) {
	score := 0.0
	signals := []string{}
	container := form.ParentsFiltered("article,.article,.entry,.post,.content,main").First()
	if container.Length() > 0 {
		score += 0.2
		signals = append(signals, "layout:article")
	}
	replies := doc.Find(".comment,.reply,.responses,.discussion,.comment-item")
	if replies.Length() > 3 {
		score += 0.25
		signals = append(signals, fmt.Sprintf("layout:threads=%d", replies.Length()))
	}
	return score, signals
}

func analyzePageStructure(doc *goquery.Document) float64 {
	score := 0.0
	repeating := countRepeating(doc)
	if repeating > 5 {
		score += 0.25
	} else if repeating > 3 {
		score += 0.15
	}
	timestamps := 0
	doc.Find("time,.date,.timestamp,[datetime],[data-time]").Each(func(i int, sel *goquery.Selection) {
		if strings.TrimSpace(sel.Text()) != "" {
			timestamps++
		}
	})
	if timestamps > 3 {
		score += 0.3
	} else if timestamps > 1 {
		score += 0.15
	}
	nested := doc.Find(".reply,.children,.nested,.thread,[style*='margin-left'],.depth-2,.depth-3")
	if nested.Length() > 2 {
		score += 0.35
	} else if nested.Length() > 0 {
		score += 0.2
	}
	avatars := doc.Find(".avatar,.user,.author,.commenter,img[alt*='avatar'],img[src*='avatar']")
	if avatars.Length() > 3 {
		score += 0.2
	}
	replyButtons := doc.Find("button,a").FilterFunction(func(i int, sel *goquery.Selection) bool {
		text := strings.ToLower(sel.Text())
		return strings.Contains(text, "reply") || strings.Contains(text, "ответ") || strings.Contains(text, "comment")
	})
	if replyButtons.Length() > 2 {
		score += 0.2
	}
	return clamp(score, 0, 1)
}

func countRepeating(doc *goquery.Document) int {
	counter := map[string]int{}
	doc.Find("div[class],article[class],section[class],li[class]").Each(func(i int, sel *goquery.Selection) {
		classes := strings.Fields(sel.AttrOr("class", ""))
		for _, className := range classes {
			if len(className) < 4 {
				continue
			}
			if strings.Contains(className, "container") || strings.Contains(className, "wrapper") || strings.Contains(className, "grid") {
				continue
			}
			counter[className]++
		}
	})
	best := 0
	for _, v := range counter {
		if v > best {
			best = v
		}
	}
	return best
}

func detectSystem(form *goquery.Selection) string {
	classes := strings.ToLower(form.AttrOr("class", ""))
	id := strings.ToLower(form.AttrOr("id", ""))
	switch {
	case strings.Contains(classes, "comment-form") || strings.Contains(id, "commentform"):
		return "wordpress"
	case strings.Contains(classes, "jetpack"):
		return "jetpack"
	case strings.Contains(classes, "disqus"):
		return "disqus"
	case strings.Contains(classes, "vk-comments"):
		return "vk"
	default:
		return "generic"
	}
}

func pickTier(confidence float64) int {
	switch {
	case confidence >= 0.85:
		return 1
	case confidence >= 0.7:
		return 2
	case confidence >= 0.5:
		return 3
	default:
		return 4
	}
}

func clamp(value, minVal, maxVal float64) float64 {
	if value < minVal {
		return minVal
	}
	if value > maxVal {
		return maxVal
	}
	return value
}

func scoreURL(u string, lastModified time.Time, base float64) float64 {
	weight := base
	lower := strings.ToLower(u)
	positives := []struct {
		pattern string
		value   float64
	}{
		{"/blog/", 0.35},
		{"/post/", 0.35},
		{"/news/", 0.3},
		{"/article/", 0.3},
		{"/review", 0.25},
		{"/discussion", 0.3},
		{"/comment", 0.4},
		{"/stories/", 0.25},
	}
	negatives := []struct {
		pattern string
		value   float64
	}{
		{"/contact", -0.4},
		{"/support", -0.4},
		{"/privacy", -0.5},
		{"/terms", -0.5},
		{"/login", -0.5},
		{"/register", -0.4},
		{"/cart", -0.5},
		{"/checkout", -0.6},
		{"/admin", -0.6},
	}
	for _, p := range positives {
		if strings.Contains(lower, p.pattern) {
			weight += p.value
		}
	}
	for _, n := range negatives {
		if strings.Contains(lower, n.pattern) {
			weight += n.value
		}
	}
	year := time.Now().Year()
	for i := 0; i < 5; i++ {
		token := fmt.Sprintf("/%d/", year-i)
		if strings.Contains(lower, token) {
			weight += 0.25 - float64(i)*0.03
			break
		}
	}
	if lastModified.After(time.Now().AddDate(0, 0, -30)) {
		weight += 0.2
	} else if lastModified.After(time.Now().AddDate(0, -3, 0)) {
		weight += 0.1
	}
	return clamp(weight, 0, 1)
}

func scoreFreshness(lastModified time.Time, start time.Time) float64 {
	if !lastModified.IsZero() {
		age := time.Since(lastModified)
		if age < 15*24*time.Hour {
			return 0.35
		}
		if age < 60*24*time.Hour {
			return 0.2
		}
		if age < 180*24*time.Hour {
			return 0.1
		}
		return 0.05
	}
	if time.Since(start) < 5*time.Minute {
		return 0.2
	}
	return 0.05
}

func (dc *DomainCrawler) enqueue(entry QueueEntry) error {
	if entry.URL == "" {
		return nil
	}
	dc.bufferMu.Lock()
	heap.Push(dc.buffer, &queueItem{entry: entry})
	queued := int64(dc.buffer.Len())
	dc.bufferMu.Unlock()
	atomic.StoreInt64(&dc.stats.Queued, queued)
	if queued > 512 {
		dc.flushBuffer()
	}
	return nil
}

func (dc *DomainCrawler) flushBuffer() {
	dc.bufferMu.Lock()
	defer dc.bufferMu.Unlock()
	if dc.buffer.Len() <= 512 {
		atomic.StoreInt64(&dc.stats.Queued, int64(dc.buffer.Len()))
		return
	}
	temp := make([]QueueEntry, 0, dc.buffer.Len())
	for dc.buffer.Len() > 0 {
		temp = append(temp, heap.Pop(dc.buffer).(*queueItem).entry)
	}
	sort.Slice(temp, func(i, j int) bool { return temp[i].Score > temp[j].Score })
	keep := 512
	if keep > len(temp) {
		keep = len(temp)
	}
	for i := 0; i < keep; i++ {
		heap.Push(dc.buffer, &queueItem{entry: temp[i]})
	}
	for i := keep; i < len(temp); i++ {
		if err := dc.queue.push(temp[i]); err != nil {
			dc.reportDomainError("queue-spill", err)
		}
	}
	atomic.StoreInt64(&dc.stats.Queued, int64(dc.buffer.Len()))
}

func (dc *DomainCrawler) loadFromDisk() bool {
	entries, err := dc.queue.readChunk(128)
	if err != nil {
		dc.reportDomainError("queue-read", err)
		return false
	}
	if len(entries) == 0 {
		atomic.StoreInt32(&dc.exhausted, 1)
		return false
	}
	dc.bufferMu.Lock()
	for _, entry := range entries {
		heap.Push(dc.buffer, &queueItem{entry: entry})
	}
	dc.bufferMu.Unlock()
	atomic.StoreInt64(&dc.stats.Queued, int64(dc.buffer.Len()))
	return true
}

func (dc *DomainCrawler) popBuffer() (QueueEntry, bool) {
	dc.bufferMu.Lock()
	defer dc.bufferMu.Unlock()
	if dc.buffer.Len() == 0 {
		return QueueEntry{}, false
	}
	entry := heap.Pop(dc.buffer).(*queueItem).entry
	atomic.StoreInt64(&dc.stats.Queued, int64(dc.buffer.Len()))
	return entry, true
}

func (dc *DomainCrawler) markVisited(raw string) bool {
	hash := hashString(raw)
	dc.visitedMu.Lock()
	defer dc.visitedMu.Unlock()
	if _, ok := dc.visited[hash]; ok {
		return false
	}
	dc.visited[hash] = struct{}{}
	if dc.visitedFile != nil {
		if _, err := fmt.Fprintf(dc.visitedFile, "%s\n", raw); err != nil {
			dc.reportDomainError("visited-write", err)
		}
	}
	return true
}

func hashString(value string) uint64 {
	const prime64 = 1099511628211
	var hash uint64 = 1469598103934665603
	for i := 0; i < len(value); i++ {
		hash ^= uint64(value[i])
		hash *= prime64
	}
	return hash
}

func loadVisited(path string, store map[uint64]struct{}) error {
	file, err := os.Open(path)
	if err != nil {
		return err
	}
	defer file.Close()
	scanner := bufio.NewScanner(file)
	buffer := make([]byte, 0, 64*1024)
	scanner.Buffer(buffer, 16*1024*1024)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		store[hashString(line)] = struct{}{}
	}
	return scanner.Err()
}

func (dc *DomainCrawler) touch() {
	dc.stats.LastCheck.Store(time.Now())
}

func (dc *DomainCrawler) persistState() {
	if err := dc.queue.persistOffset(); err != nil {
		dc.reportDomainError("persist-offset", err)
	}
	if dc.visitedFile != nil {
		dc.visitedMu.Lock()
		if err := dc.visitedFile.Sync(); err != nil {
			dc.reportDomainError("visited-sync", err)
		}
		dc.visitedMu.Unlock()
	}
	checkpoint := domainCheckpoint{
		Pages:    atomic.LoadInt64(&dc.stats.Pages),
		Findings: atomic.LoadInt64(&dc.stats.Findings),
		Primary:  atomic.LoadInt64(&dc.stats.PrimaryFindings),
		Tier4:    atomic.LoadInt64(&dc.stats.Tier4Findings),
		Offset:   dc.queue.Offset(),
		Updated:  time.Now(),
	}
	data, err := json.Marshal(checkpoint)
	if err != nil {
		dc.reportDomainError("checkpoint-encode", err)
		return
	}
	tempPath := dc.statePath + ".tmp"
	if err := os.WriteFile(tempPath, data, 0644); err != nil {
		dc.reportDomainError("checkpoint-write", err)
		return
	}
	if err := os.Rename(tempPath, dc.statePath); err != nil {
		dc.reportDomainError("checkpoint-commit", err)
		return
	}
	dc.lastPersist = time.Now()
}

func (dc *DomainCrawler) restoreState() {
	data, err := os.ReadFile(dc.statePath)
	if err != nil {
		return
	}
	var checkpoint domainCheckpoint
	if err := json.Unmarshal(data, &checkpoint); err != nil {
		return
	}
	atomic.StoreInt64(&dc.stats.Pages, checkpoint.Pages)
	atomic.StoreInt64(&dc.stats.Findings, checkpoint.Findings)
	atomic.StoreInt64(&dc.stats.PrimaryFindings, checkpoint.Primary)
	atomic.StoreInt64(&dc.stats.Tier4Findings, checkpoint.Tier4)
	dc.queue.SetOffset(checkpoint.Offset)
}

type domainList struct {
	Domains []string `json:"domains"`
}

func readDomains(path string) ([]string, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()
	var domains []string
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		domains = append(domains, line)
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	return domains, nil
}

func defaultConfig() Config {
	return Config{
		WorkersPerDomain:   5,
		MaxTotalWorkers:    100,
		MaxPagesPerDomain:  5000,
		RequestTimeout:     60 * time.Second,
		DomainDeadline:     45 * time.Minute,
		CheckpointInterval: 30 * time.Second,
		OutputDir:          "output",
		StateDir:           "state",
		UserAgents: []string{
			"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
			"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15",
			"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
		},
		AllowInsecureTLS: false,
	}
}

func parseFlags() Config {
	cfg := defaultConfig()
	domainsPath := flag.String("domains", "domains.txt", "path to domains list")
	workers := flag.Int("workers", cfg.WorkersPerDomain, "workers per domain")
	maxWorkers := flag.Int("max-workers", cfg.MaxTotalWorkers, "maximum workers total")
	maxPages := flag.Int("max-pages", cfg.MaxPagesPerDomain, "maximum pages per domain")
	outputDir := flag.String("output", cfg.OutputDir, "output directory")
	stateDir := flag.String("state", cfg.StateDir, "state directory")
	timeout := flag.Int("timeout", int(cfg.RequestTimeout.Seconds()), "request timeout seconds")
	insecureTLS := flag.Bool("insecure-tls", cfg.AllowInsecureTLS, "allow skipping TLS certificate validation")
	flag.Parse()
	cfg.DomainsFile = *domainsPath
	cfg.WorkersPerDomain = *workers
	cfg.MaxTotalWorkers = *maxWorkers
	cfg.MaxPagesPerDomain = *maxPages
	cfg.OutputDir = *outputDir
	cfg.StateDir = *stateDir
	cfg.RequestTimeout = time.Duration(*timeout) * time.Second
	cfg.AllowInsecureTLS = *insecureTLS
	return cfg
}

func main() {
	runtime.GOMAXPROCS(runtime.NumCPU())
	cfg := parseFlags()
	domains, err := readDomains(cfg.DomainsFile)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to read domains: %v\n", err)
		os.Exit(1)
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	sigs := make(chan os.Signal, 1)
	signal.Notify(sigs, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		select {
		case <-sigs:
			cancel()
		case <-ctx.Done():
		}
	}()
	crawler, err := NewMainCrawler(ctx, cfg, domains)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to initialize crawler: %v\n", err)
		os.Exit(1)
	}
	crawler.Run()
	crawler.Wait()
}
