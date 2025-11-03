package main

import (
	"bufio"
	"bytes"
	"compress/flate"
	"compress/gzip"
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"hash/crc32"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"golang.org/x/net/html"
	"golang.org/x/net/html/charset"
	"golang.org/x/text/encoding"
	"golang.org/x/text/encoding/htmlindex"
)

// ============================================================================
// КОНФИГУРАЦИЯ
// ============================================================================

type Config struct {
	// Параллелизм
	WorkersPerDomain     int
	MaxTotalWorkers      int
	MaxPagesPerDomain    int
	MinFindingsPerDomain int

	// Таймауты
	HTTPTimeout         time.Duration
	ConnectTimeout      time.Duration
	TLSHandshakeTimeout time.Duration
	DomainDeadline      time.Duration // 0 = без ограничения

	// HTTP
	UserAgent          string
	AcceptLanguage     string
	MaxRedirects       int
	MaxBodySize        int64
	InsecureSkipVerify bool

	// Директории
	DiskQueueDir  string
	CheckpointDir string
	OutputDir     string

	// Синхронизация
	TierSyncInterval   time.Duration
	JSONLSyncInterval  time.Duration
	CheckpointInterval time.Duration

	// Очереди
	MaxRAMQueue   int
	DiskBatchSize int

	// Логирование
	LogLevel string
	LogJSON  bool

	// Платформа
	WindowsMode bool
}

func DefaultConfig() *Config {
	return &Config{
		WorkersPerDomain:     5,
		MaxTotalWorkers:      100,
		MaxPagesPerDomain:    5000,
		MinFindingsPerDomain: 50,

		HTTPTimeout:         30 * time.Second,
		ConnectTimeout:      10 * time.Second,
		TLSHandshakeTimeout: 10 * time.Second,
		DomainDeadline:      0,

		UserAgent:          "Mozilla/5.0 (compatible; PavukBot/1.0; +http://example.com/bot)",
		AcceptLanguage:     "en-US,en;q=0.9",
		MaxRedirects:       10,
		MaxBodySize:        20 * 1024 * 1024, // 20 MB
		InsecureSkipVerify: false,

		DiskQueueDir:  "./data/queue",
		CheckpointDir: "./data/checkpoint",
		OutputDir:     "./data/output",

		TierSyncInterval:   5 * time.Second,
		JSONLSyncInterval:  5 * time.Second,
		CheckpointInterval: 10 * time.Second,

		MaxRAMQueue:   512,
		DiskBatchSize: 100,

		LogLevel: "INFO",
		LogJSON:  false,

		WindowsMode: runtime.GOOS == "windows",
	}
}

func (c *Config) Validate() error {
	if c.WorkersPerDomain < 1 {
		return fmt.Errorf("WorkersPerDomain must be >= 1, got %d", c.WorkersPerDomain)
	}
	if c.MaxTotalWorkers < c.WorkersPerDomain {
		c.MaxTotalWorkers = c.WorkersPerDomain
	}
	if c.MaxPagesPerDomain < 50 {
		return fmt.Errorf("MaxPagesPerDomain must be >= 50, got %d", c.MaxPagesPerDomain)
	}
	if c.MinFindingsPerDomain < 1 {
		return fmt.Errorf("MinFindingsPerDomain must be >= 1, got %d", c.MinFindingsPerDomain)
	}
	if c.MaxRAMQueue < 10 {
		c.MaxRAMQueue = 10
	}
	if c.DiskBatchSize < 1 {
		c.DiskBatchSize = 1
	}

	// Создание директорий
	for _, dir := range []string{c.DiskQueueDir, c.CheckpointDir, c.OutputDir} {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("failed to create directory %s: %w", dir, err)
		}
	}

	return nil
}

func (c *Config) MaxConcurrentDomains() int {
	max := c.MaxTotalWorkers / c.WorkersPerDomain
	if max < 1 {
		return 1
	}
	return max
}

// ============================================================================
// ЛОГИРОВАНИЕ
// ============================================================================

type LogLevel int

const (
	TRACE LogLevel = iota
	INFO
	WARN
	ERROR
)

func (l LogLevel) String() string {
	switch l {
	case TRACE:
		return "TRACE"
	case INFO:
		return "INFO"
	case WARN:
		return "WARN"
	case ERROR:
		return "ERROR"
	default:
		return "UNKNOWN"
	}
}

type Logger struct {
	level   LogLevel
	useJSON bool
	mu      sync.Mutex
}

func NewLogger(levelStr string, useJSON bool) *Logger {
	var level LogLevel
	switch strings.ToUpper(levelStr) {
	case "TRACE":
		level = TRACE
	case "INFO":
		level = INFO
	case "WARN":
		level = WARN
	case "ERROR":
		level = ERROR
	default:
		level = INFO
	}
	return &Logger{level: level, useJSON: useJSON}
}

func (l *Logger) log(level LogLevel, msg string, fields map[string]interface{}) {
	if level < l.level {
		return
	}

	l.mu.Lock()
	defer l.mu.Unlock()

	if l.useJSON {
		entry := map[string]interface{}{
			"timestamp": time.Now().Format(time.RFC3339),
			"level":     level.String(),
			"message":   msg,
		}
		for k, v := range fields {
			entry[k] = v
		}
		data, _ := json.Marshal(entry)
		fmt.Println(string(data))
	} else {
		var sb strings.Builder
		sb.WriteString(time.Now().Format("2006-01-02 15:04:05"))
		sb.WriteString(" [")
		sb.WriteString(level.String())
		sb.WriteString("] ")
		sb.WriteString(msg)
		if len(fields) > 0 {
			sb.WriteString(" {")
			first := true
			for k, v := range fields {
				if !first {
					sb.WriteString(", ")
				}
				sb.WriteString(k)
				sb.WriteString("=")
				sb.WriteString(fmt.Sprintf("%v", v))
				first = false
			}
			sb.WriteString("}")
		}
		fmt.Println(sb.String())
	}
}

func (l *Logger) Trace(msg string, fields map[string]interface{}) {
	l.log(TRACE, msg, fields)
}

func (l *Logger) Info(msg string, fields map[string]interface{}) {
	l.log(INFO, msg, fields)
}

func (l *Logger) Warn(msg string, fields map[string]interface{}) {
	l.log(WARN, msg, fields)
}

func (l *Logger) Error(msg string, fields map[string]interface{}) {
	l.log(ERROR, msg, fields)
}

// ============================================================================
// МОДЕЛИ ДАННЫХ
// ============================================================================

type Finding struct {
	URL        string    `json:"url"`
	Title      string    `json:"title"`
	Tier       int       `json:"tier"`
	TierLabel  string    `json:"tier_label"`
	Confidence float64   `json:"confidence"`
	DetectedAt time.Time `json:"detected_at"`
	Domain     string    `json:"domain"`
	Signals    []string  `json:"signals"`
}

type URLItem struct {
	URL      string
	Priority float64
	Depth    int
}

type PageMetadata struct {
	URL           string
	StatusCode    int
	ContentType   string
	ContentLength int64
	LastModified  string
	Charset       string
	RedirectChain []string
}

type DomainState struct {
	Domain       string    `json:"domain"`
	Pages        int64     `json:"pages"`
	Found        int64     `json:"found"`
	Errors       int64     `json:"errors"`
	QueueOffset  int64     `json:"queue_offset"`
	LastActivity time.Time `json:"last_activity"`
	Version      int       `json:"version"`
}

// ============================================================================
// VISITED STORE (потокобезопасный набор посещённых URL)
// ============================================================================

type VisitedStore struct {
	mu      sync.RWMutex
	visited map[string]struct{}
}

func NewVisitedStore() *VisitedStore {
	return &VisitedStore{
		visited: make(map[string]struct{}),
	}
}

func (v *VisitedStore) LoadOrStore(url string) bool {
	v.mu.Lock()
	defer v.mu.Unlock()

	if _, exists := v.visited[url]; exists {
		return true
	}
	v.visited[url] = struct{}{}
	return false
}

func (v *VisitedStore) Contains(url string) bool {
	v.mu.RLock()
	defer v.mu.RUnlock()
	_, exists := v.visited[url]
	return exists
}

func (v *VisitedStore) Size() int {
	v.mu.RLock()
	defer v.mu.RUnlock()
	return len(v.visited)
}

func (v *VisitedStore) Save(path string) error {
	v.mu.RLock()
	defer v.mu.RUnlock()

	tmpPath := path + ".tmp"
	f, err := os.Create(tmpPath)
	if err != nil {
		return fmt.Errorf("create visited tmp file: %w", err)
	}
	defer f.Close()

	w := bufio.NewWriter(f)
	for url := range v.visited {
		if _, err := w.WriteString(url + "\n"); err != nil {
			return fmt.Errorf("write visited url: %w", err)
		}
	}

	if err := w.Flush(); err != nil {
		return fmt.Errorf("flush visited: %w", err)
	}
	if err := f.Sync(); err != nil {
		return fmt.Errorf("sync visited: %w", err)
	}
	if err := f.Close(); err != nil {
		return fmt.Errorf("close visited: %w", err)
	}

	if err := os.Rename(tmpPath, path); err != nil {
		return fmt.Errorf("rename visited: %w", err)
	}

	return nil
}

func (v *VisitedStore) Load(path string) error {
	f, err := os.Open(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil
		}
		return fmt.Errorf("open visited: %w", err)
	}
	defer f.Close()

	v.mu.Lock()
	defer v.mu.Unlock()

	scanner := bufio.NewScanner(f)

	// Увеличение буфера до 16 МБ для обработки длинных URL
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 16*1024*1024)

	for scanner.Scan() {
		url := strings.TrimSpace(scanner.Text())
		if url != "" {
			v.visited[url] = struct{}{}
		}
	}

	return scanner.Err()
}

// ============================================================================
// DISK QUEUE (журнал ссылок на диске)
// ============================================================================

type DiskQueue struct {
	path      string
	file      *os.File
	mu        sync.Mutex
	offset    int64
	batchSize int
	logger    *Logger
}

func NewDiskQueue(path string, batchSize int, logger *Logger) (*DiskQueue, error) {
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return nil, fmt.Errorf("create queue dir: %w", err)
	}

	f, err := os.OpenFile(path, os.O_CREATE|os.O_RDWR|os.O_APPEND, 0644)
	if err != nil {
		return nil, fmt.Errorf("open queue file: %w", err)
	}

	dq := &DiskQueue{
		path:      path,
		file:      f,
		batchSize: batchSize,
		logger:    logger,
	}

	// Загрузить offset из метафайла
	offsetPath := path + ".offset"
	if data, err := os.ReadFile(offsetPath); err == nil {
		if offset, err := strconv.ParseInt(strings.TrimSpace(string(data)), 10, 64); err == nil {
			dq.offset = offset
		}
	}

	return dq, nil
}

func (dq *DiskQueue) Push(batch []URLItem) error {
	if len(batch) == 0 {
		return nil
	}

	dq.mu.Lock()
	defer dq.mu.Unlock()

	var buf bytes.Buffer
	for _, item := range batch {
		data, err := json.Marshal(item)
		if err != nil {
			dq.logger.Warn("failed to marshal url item", map[string]interface{}{"error": err.Error()})
			continue
		}

		// Формат: [CRC32][LENGTH][DATA]\n
		crc := crc32.ChecksumIEEE(data)
		line := fmt.Sprintf("%08x%08x%s\n", crc, len(data), data)
		buf.WriteString(line)
	}

	if _, err := dq.file.Write(buf.Bytes()); err != nil {
		return fmt.Errorf("write queue batch: %w", err)
	}

	if err := dq.file.Sync(); err != nil {
		return fmt.Errorf("sync queue: %w", err)
	}

	return nil
}

func (dq *DiskQueue) Pop(n int) ([]URLItem, error) {
	dq.mu.Lock()
	defer dq.mu.Unlock()

	if _, err := dq.file.Seek(dq.offset, io.SeekStart); err != nil {
		return nil, fmt.Errorf("seek queue: %w", err)
	}

	var items []URLItem
	scanner := bufio.NewScanner(dq.file)

	// Увеличение буфера до 16 МБ для обработки длинных строк
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 16*1024*1024)

	scanned := 0

	for scanner.Scan() && scanned < n {
		line := scanner.Text()
		if len(line) < 16 {
			dq.logger.Warn("malformed queue line", map[string]interface{}{"line_len": len(line)})
			continue
		}

		crcHex := line[0:8]
		lenHex := line[8:16]
		dataStr := line[16:]

		expectedCRC, err := strconv.ParseUint(crcHex, 16, 32)
		if err != nil {
			dq.logger.Warn("invalid crc in queue", map[string]interface{}{"error": err.Error()})
			continue
		}

		dataLen, err := strconv.ParseUint(lenHex, 16, 32)
		if err != nil {
			dq.logger.Warn("invalid length in queue", map[string]interface{}{"error": err.Error()})
			continue
		}

		if len(dataStr) != int(dataLen) {
			dq.logger.Warn("length mismatch in queue", map[string]interface{}{
				"expected": dataLen,
				"actual":   len(dataStr),
			})
			continue
		}

		actualCRC := crc32.ChecksumIEEE([]byte(dataStr))
		if actualCRC != uint32(expectedCRC) {
			dq.logger.Warn("crc mismatch in queue", map[string]interface{}{
				"expected": expectedCRC,
				"actual":   actualCRC,
			})
			continue
		}

		var item URLItem
		if err := json.Unmarshal([]byte(dataStr), &item); err != nil {
			dq.logger.Warn("failed to unmarshal queue item", map[string]interface{}{"error": err.Error()})
			continue
		}

		items = append(items, item)
		scanned++
		dq.offset += int64(len(line)) + 1 // +1 for \n
	}

	if err := scanner.Err(); err != nil {
		return items, fmt.Errorf("scan queue: %w", err)
	}

	// Сохранить offset
	if err := dq.saveOffset(); err != nil {
		dq.logger.Warn("failed to save queue offset", map[string]interface{}{"error": err.Error()})
	}

	return items, nil
}

func (dq *DiskQueue) saveOffset() error {
	offsetPath := dq.path + ".offset"
	tmpPath := offsetPath + ".tmp"

	if err := os.WriteFile(tmpPath, []byte(strconv.FormatInt(dq.offset, 10)), 0644); err != nil {
		return err
	}

	return os.Rename(tmpPath, offsetPath)
}

func (dq *DiskQueue) Close() error {
	dq.mu.Lock()
	defer dq.mu.Unlock()

	if err := dq.saveOffset(); err != nil {
		dq.logger.Warn("failed to save offset on close", map[string]interface{}{"error": err.Error()})
	}

	return dq.file.Close()
}

// ============================================================================
// PRIORITY QUEUE (RAM-heap для топовых ссылок)
// ============================================================================

type PriorityQueue struct {
	items []URLItem
	mu    sync.Mutex
}

func NewPriorityQueue() *PriorityQueue {
	return &PriorityQueue{
		items: make([]URLItem, 0),
	}
}

func (pq *PriorityQueue) Push(item URLItem) {
	pq.mu.Lock()
	defer pq.mu.Unlock()

	pq.items = append(pq.items, item)
	pq.heapifyUp(len(pq.items) - 1)
}

func (pq *PriorityQueue) Pop() (URLItem, bool) {
	pq.mu.Lock()
	defer pq.mu.Unlock()

	if len(pq.items) == 0 {
		return URLItem{}, false
	}

	item := pq.items[0]
	lastIdx := len(pq.items) - 1
	pq.items[0] = pq.items[lastIdx]
	pq.items = pq.items[:lastIdx]

	if len(pq.items) > 0 {
		pq.heapifyDown(0)
	}

	return item, true
}

func (pq *PriorityQueue) Len() int {
	pq.mu.Lock()
	defer pq.mu.Unlock()
	return len(pq.items)
}

func (pq *PriorityQueue) heapifyUp(idx int) {
	for idx > 0 {
		parent := (idx - 1) / 2
		if pq.items[idx].Priority <= pq.items[parent].Priority {
			break
		}
		pq.items[idx], pq.items[parent] = pq.items[parent], pq.items[idx]
		idx = parent
	}
}

func (pq *PriorityQueue) heapifyDown(idx int) {
	n := len(pq.items)
	for {
		largest := idx
		left := 2*idx + 1
		right := 2*idx + 2

		if left < n && pq.items[left].Priority > pq.items[largest].Priority {
			largest = left
		}
		if right < n && pq.items[right].Priority > pq.items[largest].Priority {
			largest = right
		}

		if largest == idx {
			break
		}

		pq.items[idx], pq.items[largest] = pq.items[largest], pq.items[idx]
		idx = largest
	}
}

// ============================================================================
// RESULT WRITER (запись результатов)
// ============================================================================

type ResultWriter struct {
	outputDir     string
	jsonlFile     *os.File
	tierFiles     map[int]*os.File
	uniqueURLs    map[string]struct{}
	mu            sync.Mutex
	jsonlSync     time.Duration
	tierSync      time.Duration
	lastJSONLSync time.Time
	lastTierSync  time.Time
	logger        *Logger
	reopenCount   int32
	dedupLimit    int
	dedupCounter  int64
}

func NewResultWriter(outputDir string, jsonlSync, tierSync time.Duration, logger *Logger) (*ResultWriter, error) {
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return nil, fmt.Errorf("create output dir: %w", err)
	}

	jsonlPath := filepath.Join(outputDir, "findings.jsonl")
	jsonlFile, err := os.OpenFile(jsonlPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, fmt.Errorf("open jsonl file: %w", err)
	}

	tierFiles := make(map[int]*os.File)
	for tier := 1; tier <= 4; tier++ {
		path := filepath.Join(outputDir, fmt.Sprintf("tier%d.txt", tier))
		f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
		if err != nil {
			jsonlFile.Close()
			for _, tf := range tierFiles {
				tf.Close()
			}
			return nil, fmt.Errorf("open tier%d file: %w", tier, err)
		}
		tierFiles[tier] = f
	}

	rw := &ResultWriter{
		outputDir:     outputDir,
		jsonlFile:     jsonlFile,
		tierFiles:     tierFiles,
		uniqueURLs:    make(map[string]struct{}),
		jsonlSync:     jsonlSync,
		tierSync:      tierSync,
		lastJSONLSync: time.Now(),
		lastTierSync:  time.Now(),
		logger:        logger,
		dedupLimit:    100000, // Лимит на размер dedup-карты
	}

	return rw, nil
}

func (rw *ResultWriter) WriteFinding(f Finding) error {
	rw.mu.Lock()
	defer rw.mu.Unlock()

	// Глобальный дедуп с ротацией при переполнении
	if _, exists := rw.uniqueURLs[f.URL]; exists {
		return nil
	}

	// Проверка лимита dedup-карты
	if len(rw.uniqueURLs) >= rw.dedupLimit {
		rw.logger.Warn("dedup map limit reached, clearing", map[string]interface{}{
			"size":    len(rw.uniqueURLs),
			"counter": atomic.LoadInt64(&rw.dedupCounter),
		})
		rw.uniqueURLs = make(map[string]struct{})
		atomic.AddInt64(&rw.dedupCounter, 1)
	}

	rw.uniqueURLs[f.URL] = struct{}{}

	// Запись в JSONL
	data, err := json.Marshal(f)
	if err != nil {
		return fmt.Errorf("marshal finding: %w", err)
	}

	if _, err := rw.jsonlFile.Write(append(data, '\n')); err != nil {
		// Попытка reopen
		if err := rw.reopenJSONL(); err != nil {
			rw.logger.Error("failed to reopen jsonl", map[string]interface{}{"error": err.Error()})
			return fmt.Errorf("write jsonl: %w", err)
		}
		if _, err := rw.jsonlFile.Write(append(data, '\n')); err != nil {
			return fmt.Errorf("write jsonl after reopen: %w", err)
		}
	}

	// Запись в tier файл
	if tierFile, ok := rw.tierFiles[f.Tier]; ok {
		line := f.URL + "\n"
		if _, err := tierFile.WriteString(line); err != nil {
			// Попытка reopen
			if err := rw.reopenTier(f.Tier); err != nil {
				rw.logger.Error("failed to reopen tier file", map[string]interface{}{
					"tier":  f.Tier,
					"error": err.Error(),
				})
				return fmt.Errorf("write tier%d: %w", f.Tier, err)
			}
			if _, err := tierFile.WriteString(line); err != nil {
				return fmt.Errorf("write tier%d after reopen: %w", f.Tier, err)
			}
		}
	}

	// Периодическая синхронизация
	now := time.Now()
	if now.Sub(rw.lastJSONLSync) >= rw.jsonlSync {
		if err := rw.jsonlFile.Sync(); err != nil {
			rw.logger.Warn("failed to sync jsonl", map[string]interface{}{"error": err.Error()})
		}
		rw.lastJSONLSync = now
	}

	if now.Sub(rw.lastTierSync) >= rw.tierSync {
		for tier, f := range rw.tierFiles {
			if err := f.Sync(); err != nil {
				rw.logger.Warn("failed to sync tier file", map[string]interface{}{
					"tier":  tier,
					"error": err.Error(),
				})
			}
		}
		rw.lastTierSync = now
	}

	return nil
}

func (rw *ResultWriter) reopenJSONL() error {
	count := atomic.AddInt32(&rw.reopenCount, 1)
	newPath := filepath.Join(rw.outputDir, fmt.Sprintf("findings_reopened_%d.jsonl", count))

	newFile, err := os.OpenFile(newPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return err
	}

	oldFile := rw.jsonlFile
	rw.jsonlFile = newFile
	oldFile.Close()

	rw.logger.Info("reopened jsonl file", map[string]interface{}{"new_path": newPath})
	return nil
}

func (rw *ResultWriter) reopenTier(tier int) error {
	count := atomic.AddInt32(&rw.reopenCount, 1)
	newPath := filepath.Join(rw.outputDir, fmt.Sprintf("tier%d_reopened_%d.txt", tier, count))

	newFile, err := os.OpenFile(newPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return err
	}

	oldFile := rw.tierFiles[tier]
	rw.tierFiles[tier] = newFile
	oldFile.Close()

	rw.logger.Info("reopened tier file", map[string]interface{}{
		"tier":     tier,
		"new_path": newPath,
	})
	return nil
}

func (rw *ResultWriter) Sync() error {
	rw.mu.Lock()
	defer rw.mu.Unlock()

	if err := rw.jsonlFile.Sync(); err != nil {
		rw.logger.Warn("failed final sync jsonl", map[string]interface{}{"error": err.Error()})
	}

	for tier, f := range rw.tierFiles {
		if err := f.Sync(); err != nil {
			rw.logger.Warn("failed final sync tier", map[string]interface{}{
				"tier":  tier,
				"error": err.Error(),
			})
		}
	}

	return nil
}

func (rw *ResultWriter) Close() error {
	rw.mu.Lock()
	defer rw.mu.Unlock()

	if err := rw.jsonlFile.Close(); err != nil {
		rw.logger.Warn("failed to close jsonl", map[string]interface{}{"error": err.Error()})
	}

	for tier, f := range rw.tierFiles {
		if err := f.Close(); err != nil {
			rw.logger.Warn("failed to close tier file", map[string]interface{}{
				"tier":  tier,
				"error": err.Error(),
			})
		}
	}

	return nil
}

// ============================================================================
// URL NORMALIZATION & EXTRACTION
// ============================================================================

var staticExtensions = map[string]bool{
	".jpg": true, ".jpeg": true, ".png": true, ".gif": true, ".svg": true,
	".pdf": true, ".zip": true, ".rar": true, ".tar": true, ".gz": true,
	".mp4": true, ".avi": true, ".mov": true, ".wmv": true,
	".mp3": true, ".wav": true, ".flac": true,
	".exe": true, ".dmg": true, ".iso": true,
	".css": true, ".js": true, ".woff": true, ".woff2": true, ".ttf": true, ".eot": true,
}

func normalizeURL(rawURL string, baseURL *url.URL) (string, error) {
	if rawURL == "" {
		return "", errors.New("empty url")
	}

	u, err := url.Parse(rawURL)
	if err != nil {
		return "", fmt.Errorf("parse url: %w", err)
	}

	if baseURL != nil {
		u = baseURL.ResolveReference(u)
	}

	// Только HTTP/HTTPS
	if u.Scheme != "http" && u.Scheme != "https" {
		return "", errors.New("not http/https")
	}

	// Удаление фрагмента
	u.Fragment = ""

	// Нормализация пути
	if u.Path == "" {
		u.Path = "/"
	}

	// Сортировка query параметров (allow-list подход)
	if u.RawQuery != "" {
		q := u.Query()
		allowedParams := map[string]bool{
			"p": true, "page": true, "id": true, "post": true,
			"article": true, "cat": true, "category": true,
			"tag": true, "search": true, "q": true,
		}

		newQuery := url.Values{}
		for k, v := range q {
			if allowedParams[k] {
				newQuery[k] = v
			}
		}

		u.RawQuery = newQuery.Encode()
	}

	// Удаление trailing slash (кроме корня)
	if len(u.Path) > 1 && strings.HasSuffix(u.Path, "/") {
		u.Path = strings.TrimSuffix(u.Path, "/")
	}

	// Проверка статических файлов
	ext := strings.ToLower(filepath.Ext(u.Path))
	if staticExtensions[ext] {
		return "", errors.New("static file")
	}

	return u.String(), nil
}

func isSameDomain(urlStr string, domain string) bool {
	u, err := url.Parse(urlStr)
	if err != nil {
		return false
	}

	host := strings.ToLower(u.Hostname())
	domain = strings.ToLower(domain)

	// Точное совпадение или поддомен
	return host == domain || strings.HasSuffix(host, "."+domain)
}

func extractLinks(htmlContent []byte, baseURL *url.URL, domain string) ([]string, error) {
	doc, err := html.Parse(bytes.NewReader(htmlContent))
	if err != nil {
		return nil, fmt.Errorf("parse html: %w", err)
	}

	seen := make(map[string]bool)
	var links []string

	var walk func(*html.Node)
	walk = func(n *html.Node) {
		if n.Type == html.ElementNode && n.Data == "a" {
			for _, attr := range n.Attr {
				if attr.Key == "href" {
					normalized, err := normalizeURL(attr.Val, baseURL)
					if err != nil {
						continue
					}

					if !isSameDomain(normalized, domain) {
						continue
					}

					if !seen[normalized] {
						seen[normalized] = true
						links = append(links, normalized)
					}
					break
				}
			}
		}

		for c := n.FirstChild; c != nil; c = c.NextSibling {
			walk(c)
		}
	}

	walk(doc)
	return links, nil
}

// ============================================================================
// ENCODING DETECTION & CONVERSION
// ============================================================================

func detectCharset(contentType string, body []byte) string {
	// Из Content-Type
	if contentType != "" {
		parts := strings.Split(contentType, ";")
		for _, part := range parts {
			part = strings.TrimSpace(part)
			if strings.HasPrefix(strings.ToLower(part), "charset=") {
				charset := strings.TrimPrefix(strings.ToLower(part), "charset=")
				charset = strings.Trim(charset, "\"'")
				return charset
			}
		}
	}

	// Из meta тегов
	doc, err := html.Parse(bytes.NewReader(body))
	if err == nil {
		var findCharset func(*html.Node) string
		findCharset = func(n *html.Node) string {
			if n.Type == html.ElementNode && n.Data == "meta" {
				var httpEquiv, content, charsetAttr string
				for _, attr := range n.Attr {
					switch strings.ToLower(attr.Key) {
					case "http-equiv":
						httpEquiv = strings.ToLower(attr.Val)
					case "content":
						content = attr.Val
					case "charset":
						charsetAttr = attr.Val
					}
				}

				if charsetAttr != "" {
					return charsetAttr
				}

				if httpEquiv == "content-type" && content != "" {
					parts := strings.Split(content, ";")
					for _, part := range parts {
						part = strings.TrimSpace(part)
						if strings.HasPrefix(strings.ToLower(part), "charset=") {
							return strings.TrimPrefix(strings.ToLower(part), "charset=")
						}
					}
				}
			}

			for c := n.FirstChild; c != nil; c = c.NextSibling {
				if cs := findCharset(c); cs != "" {
					return cs
				}
			}
			return ""
		}

		if cs := findCharset(doc); cs != "" {
			return cs
		}
	}

	return "utf-8"
}

func convertToUTF8(body []byte, charsetName string) ([]byte, error) {
	charsetName = strings.ToLower(strings.TrimSpace(charsetName))

	if charsetName == "" || charsetName == "utf-8" || charsetName == "utf8" {
		return body, nil
	}

	var dec *encoding.Decoder

	enc, err := htmlindex.Get(charsetName)
	if err != nil {
		// Fallback: вернуть как есть
		return body, nil
	}

	dec = enc.NewDecoder()
	decoded, err := dec.Bytes(body)
	if err != nil {
		return body, nil
	}

	return decoded, nil
}

// ============================================================================
// HTTP CLIENT & FETCHING
// ============================================================================

type HTTPClient struct {
	client *http.Client
	config *Config
	logger *Logger
}

func NewHTTPClient(config *Config, logger *Logger) *HTTPClient {
	transport := &http.Transport{
		DialContext: (&net.Dialer{
			Timeout:   config.ConnectTimeout,
			KeepAlive: 30 * time.Second,
		}).DialContext,
		TLSHandshakeTimeout:   config.TLSHandshakeTimeout,
		ResponseHeaderTimeout: config.HTTPTimeout,
		ExpectContinueTimeout: 1 * time.Second,
		MaxIdleConns:          100,
		MaxIdleConnsPerHost:   10,
		IdleConnTimeout:       90 * time.Second,
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: config.InsecureSkipVerify,
		},
	}

	client := &http.Client{
		Transport: transport,
		Timeout:   config.HTTPTimeout,
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			if len(via) >= config.MaxRedirects {
				return fmt.Errorf("too many redirects")
			}
			return nil
		},
	}

	return &HTTPClient{
		client: client,
		config: config,
		logger: logger,
	}
}

func (hc *HTTPClient) Fetch(ctx context.Context, urlStr string) ([]byte, *PageMetadata, error) {
	req, err := http.NewRequestWithContext(ctx, "GET", urlStr, nil)
	if err != nil {
		return nil, nil, fmt.Errorf("create request: %w", err)
	}

	req.Header.Set("User-Agent", hc.config.UserAgent)
	req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
	req.Header.Set("Accept-Language", hc.config.AcceptLanguage)
	req.Header.Set("Accept-Encoding", "gzip, deflate")

	resp, err := hc.client.Do(req)
	if err != nil {
		if errors.Is(err, context.DeadlineExceeded) || errors.Is(err, context.Canceled) {
			return nil, nil, fmt.Errorf("timeout or canceled: %w", err)
		}
		return nil, nil, fmt.Errorf("do request: %w", err)
	}
	defer resp.Body.Close()

	metadata := &PageMetadata{
		URL:           urlStr,
		StatusCode:    resp.StatusCode,
		ContentType:   resp.Header.Get("Content-Type"),
		ContentLength: resp.ContentLength,
		LastModified:  resp.Header.Get("Last-Modified"),
	}

	if resp.StatusCode < 200 || resp.StatusCode >= 400 {
		return nil, metadata, fmt.Errorf("bad status code: %d", resp.StatusCode)
	}

	// Ограничение размера
	limitedReader := io.LimitReader(resp.Body, hc.config.MaxBodySize)

	// Декомпрессия
	var reader io.Reader = limitedReader
	var closer io.Closer
	encoding := resp.Header.Get("Content-Encoding")

	switch encoding {
	case "gzip":
		gzr, err := gzip.NewReader(limitedReader)
		if err != nil {
			return nil, metadata, fmt.Errorf("create gzip reader: %w", err)
		}
		reader = gzr
		closer = gzr
	case "deflate":
		flateReader := flate.NewReader(limitedReader)
		reader = flateReader
		closer = flateReader.(io.Closer)
	}

	// Обязательное закрытие декомпрессора
	if closer != nil {
		defer closer.Close()
	}

	body, err := io.ReadAll(reader)
	if err != nil {
		if len(body) > 0 {
			hc.logger.Warn("partial read", map[string]interface{}{
				"url":   urlStr,
				"error": err.Error(),
				"bytes": len(body),
			})
		} else {
			return nil, metadata, fmt.Errorf("read body: %w", err)
		}
	}

	if int64(len(body)) >= hc.config.MaxBodySize {
		return nil, metadata, fmt.Errorf("body too large: %d bytes", len(body))
	}

	// Определение кодировки и конвертация
	charset := detectCharset(metadata.ContentType, body)
	metadata.Charset = charset

	utf8Body, err := convertToUTF8(body, charset)
	if err != nil {
		hc.logger.Warn("encoding conversion failed", map[string]interface{}{
			"url":     urlStr,
			"charset": charset,
			"error":   err.Error(),
		})
		utf8Body = body
	}

	return utf8Body, metadata, nil
}

// ============================================================================
// LINK PRIORITIZATION
// ============================================================================

type LinkPrioritizer struct {
	mu            sync.RWMutex
	patternCounts map[string]int64
}

func NewLinkPrioritizer() *LinkPrioritizer {
	return &LinkPrioritizer{
		patternCounts: make(map[string]int64),
	}
}

func (lp *LinkPrioritizer) PrioritizeLink(urlStr string, depth int) float64 {
	u, err := url.Parse(urlStr)
	if err != nil {
		return 0.0
	}

	score := 0.5 // Базовый скор
	path := strings.ToLower(u.Path)

	// Семантика пути (высокий приоритет)
	highPriorityPatterns := []string{
		"/blog/", "/post/", "/article/", "/news/",
		"/discussion/", "/forum/", "/thread/", "/topic/",
		"/comment/", "/comments/",
	}

	for _, pattern := range highPriorityPatterns {
		if strings.Contains(path, pattern) {
			score += 0.3
			break
		}
	}

	// Индикаторы систем комментирования
	commentSystems := []string{
		"disqus", "giscus", "discourse", "commento",
		"hyvor", "cusdis", "gitalk", "gitment",
	}

	for _, sys := range commentSystems {
		if strings.Contains(path, sys) || strings.Contains(u.RawQuery, sys) {
			score += 0.2
			break
		}
	}

	// Свежесть (год в URL)
	currentYear := time.Now().Year()
	for year := currentYear; year >= currentYear-2; year-- {
		if strings.Contains(path, fmt.Sprintf("/%d/", year)) {
			score += 0.15
			break
		}
	}

	// Наличие ID/номера (скорее всего конкретная страница)
	if strings.Contains(path, "/id/") ||
		strings.Contains(u.RawQuery, "id=") ||
		strings.Contains(u.RawQuery, "p=") ||
		strings.Contains(u.RawQuery, "post=") {
		score += 0.1
	}

	// Низкий приоритет (архивы, индексы)
	lowPriorityPatterns := []string{
		"/archive/", "/category/", "/tag/", "/author/",
		"/page/", "/index", "/sitemap",
	}

	for _, pattern := range lowPriorityPatterns {
		if strings.Contains(path, pattern) {
			score -= 0.2
			break
		}
	}

	// Штраф за глубину
	if depth > 3 {
		score -= float64(depth-3) * 0.05
	}

	// Нормализация в [0, 1]
	if score < 0 {
		score = 0
	}
	if score > 1 {
		score = 1
	}

	return score
}

func (lp *LinkPrioritizer) RecordSuccess(urlStr string) {
	u, err := url.Parse(urlStr)
	if err != nil {
		return
	}

	pathParts := strings.Split(strings.Trim(u.Path, "/"), "/")
	for i := 1; i <= len(pathParts) && i <= 3; i++ {
		pattern := "/" + strings.Join(pathParts[:i], "/") + "/"
		lp.mu.Lock()
		lp.patternCounts[pattern]++
		lp.mu.Unlock()
	}
}

// ============================================================================
// COMMENT DETECTION & CLASSIFICATION
// ============================================================================

type Signal struct {
	Type        string
	Description string
	Weight      float64
}

var commentSystems = []string{
	"disqus", "discourse", "hyvor", "cusdis", "giscus", "gitalk",
	"gitment", "commento", "commenta", "intensedebate", "cackle",
	"livefyre", "graphcomment", "isso", "coral", "remark42",
	"staticman", "commentbox", "fastcomments", "replybox",
	"wp-comments", "wordpress-comments",
}

func detectComments(htmlContent []byte, metadata *PageMetadata) (*Finding, bool) {
	doc, err := html.Parse(bytes.NewReader(htmlContent))
	if err != nil {
		return nil, false
	}

	var signals []Signal
	confidence := 0.0

	// Проверка систем комментирования
	htmlLower := strings.ToLower(string(htmlContent))
	for _, sys := range commentSystems {
		if strings.Contains(htmlLower, sys) {
			signals = append(signals, Signal{
				Type:        "comment_system",
				Description: fmt.Sprintf("detected_%s", sys),
				Weight:      0.4,
			})
			confidence += 0.4
		}
	}

	// Проверка форм комментирования
	hasForm, formSignals := detectCommentForm(doc)
	if hasForm {
		signals = append(signals, formSignals...)
		confidence += 0.3
	}

	// Проверка DOM структур комментариев
	hasCommentStructure, structSignals := detectCommentStructure(doc)
	if hasCommentStructure {
		signals = append(signals, structSignals...)
		confidence += 0.25
	}

	// Проверка JSON-LD / OG / микроформатов
	hasSchema, schemaSignals := detectSchemaMarkup(doc)
	if hasSchema {
		signals = append(signals, schemaSignals...)
		confidence += 0.2
	}

	// Отрицательные паттерны
	negativePatterns := []string{
		"comments closed", "comments are closed", "no comments",
		"comments disabled", "login required", "sign in to comment",
	}

	for _, pattern := range negativePatterns {
		if strings.Contains(htmlLower, pattern) {
			signals = append(signals, Signal{
				Type:        "negative",
				Description: pattern,
				Weight:      -0.3,
			})
			confidence -= 0.3
			break
		}
	}

	// Нормализация confidence
	if confidence < 0 {
		confidence = 0
	}
	if confidence > 1 {
		confidence = 1
	}

	// Минимальный порог
	if confidence < 0.3 {
		return nil, false
	}

	// Извлечение title
	title := extractTitle(doc)

	finding := &Finding{
		URL:        metadata.URL,
		Title:      title,
		Confidence: confidence,
		DetectedAt: time.Now(),
		Signals:    make([]string, 0, len(signals)),
	}

	for _, sig := range signals {
		finding.Signals = append(finding.Signals, fmt.Sprintf("%s:%s", sig.Type, sig.Description))
	}

	return finding, true
}

func detectCommentForm(n *html.Node) (bool, []Signal) {
	var signals []Signal
	hasTextarea := false
	hasCommentField := false
	hasSubmit := false

	var walk func(*html.Node)
	walk = func(node *html.Node) {
		if node.Type == html.ElementNode {
			switch node.Data {
			case "form":
				// Проверка action/id формы
				for _, attr := range node.Attr {
					val := strings.ToLower(attr.Val)
					if (attr.Key == "action" || attr.Key == "id") &&
						(strings.Contains(val, "comment") || strings.Contains(val, "reply")) {
						signals = append(signals, Signal{
							Type:        "form",
							Description: "comment_form_detected",
							Weight:      0.2,
						})
					}
				}

			case "textarea":
				hasTextarea = true
				for _, attr := range node.Attr {
					val := strings.ToLower(attr.Val)
					if attr.Key == "name" || attr.Key == "id" || attr.Key == "placeholder" {
						if strings.Contains(val, "comment") ||
							strings.Contains(val, "reply") ||
							strings.Contains(val, "message") {
							hasCommentField = true
						}
					}
				}

			case "input":
				var inputType string
				for _, attr := range node.Attr {
					if attr.Key == "type" {
						inputType = strings.ToLower(attr.Val)
					}
				}
				if inputType == "submit" || inputType == "button" {
					hasSubmit = true
				}

			case "button":
				hasSubmit = true
			}
		}

		for c := node.FirstChild; c != nil; c = c.NextSibling {
			walk(c)
		}
	}

	walk(n)

	if hasTextarea && hasCommentField {
		signals = append(signals, Signal{
			Type:        "form",
			Description: "textarea_with_comment_field",
			Weight:      0.25,
		})
	}

	if hasTextarea && hasSubmit {
		signals = append(signals, Signal{
			Type:        "form",
			Description: "textarea_with_submit",
			Weight:      0.15,
		})
	}

	return len(signals) > 0, signals
}

func detectCommentStructure(n *html.Node) (bool, []Signal) {
	var signals []Signal
	commentNodes := 0
	authorNodes := 0
	dateNodes := 0

	var walk func(*html.Node)
	walk = func(node *html.Node) {
		if node.Type == html.ElementNode {
			for _, attr := range node.Attr {
				val := strings.ToLower(attr.Val)

				// class/id содержат "comment"
				if attr.Key == "class" || attr.Key == "id" {
					if strings.Contains(val, "comment") && !strings.Contains(val, "no-comment") {
						commentNodes++
					}
					if strings.Contains(val, "author") || strings.Contains(val, "user") {
						authorNodes++
					}
					if strings.Contains(val, "date") || strings.Contains(val, "time") {
						dateNodes++
					}
				}

				// itemtype для микроданных
				if attr.Key == "itemtype" {
					if strings.Contains(val, "comment") || strings.Contains(val, "usercomments") {
						signals = append(signals, Signal{
							Type:        "microdata",
							Description: "comment_itemtype",
							Weight:      0.2,
						})
					}
				}
			}
		}

		for c := node.FirstChild; c != nil; c = c.NextSibling {
			walk(c)
		}
	}

	walk(n)

	if commentNodes >= 3 {
		signals = append(signals, Signal{
			Type:        "structure",
			Description: fmt.Sprintf("multiple_comment_nodes_%d", commentNodes),
			Weight:      0.2,
		})
	}

	if authorNodes >= 2 && dateNodes >= 2 {
		signals = append(signals, Signal{
			Type:        "structure",
			Description: "author_date_pattern",
			Weight:      0.15,
		})
	}

	return len(signals) > 0, signals
}

func detectSchemaMarkup(n *html.Node) (bool, []Signal) {
	var signals []Signal
	htmlStr := renderNode(n)
	htmlLower := strings.ToLower(htmlStr)

	// JSON-LD
	if strings.Contains(htmlLower, "application/ld+json") {
		if strings.Contains(htmlLower, "\"@type\":\"article\"") ||
			strings.Contains(htmlLower, "\"@type\":\"blogposting\"") ||
			strings.Contains(htmlLower, "\"@type\":\"newsarticle\"") {
			signals = append(signals, Signal{
				Type:        "jsonld",
				Description: "article_type",
				Weight:      0.15,
			})
		}

		if strings.Contains(htmlLower, "\"@type\":\"comment\"") ||
			strings.Contains(htmlLower, "commentcount") {
			signals = append(signals, Signal{
				Type:        "jsonld",
				Description: "comment_schema",
				Weight:      0.25,
			})
		}
	}

	// Open Graph
	if strings.Contains(htmlLower, "og:type") {
		if strings.Contains(htmlLower, "article") {
			signals = append(signals, Signal{
				Type:        "opengraph",
				Description: "og_article",
				Weight:      0.1,
			})
		}
	}

	return len(signals) > 0, signals
}

func extractTitle(n *html.Node) string {
	var title string

	var walk func(*html.Node)
	walk = func(node *html.Node) {
		if node.Type == html.ElementNode && node.Data == "title" {
			if node.FirstChild != nil && node.FirstChild.Type == html.TextNode {
				title = strings.TrimSpace(node.FirstChild.Data)
				return
			}
		}

		for c := node.FirstChild; c != nil; c = c.NextSibling {
			walk(c)
			if title != "" {
				return
			}
		}
	}

	walk(n)
	return title
}

func renderNode(n *html.Node) string {
	var buf bytes.Buffer
	html.Render(&buf, n)
	return buf.String()
}

// ============================================================================
// TIER CLASSIFICATION
// ============================================================================

func classifyFindingTier(confidence float64, signals []string) (int, string) {
	const (
		tier1Threshold = 0.85
		tier2Threshold = 0.70
		tier3Threshold = 0.50
		hysteresis     = 0.02
	)

	// Проверка на явные системы комментирования
	hasExplicitSystem := false
	for _, sig := range signals {
		if strings.HasPrefix(sig, "comment_system:") {
			hasExplicitSystem = true
			break
		}
	}

	if confidence >= tier1Threshold || (confidence >= tier1Threshold-hysteresis && hasExplicitSystem) {
		return 1, "абсолютная"
	}

	if confidence >= tier2Threshold {
		return 2, "вроде как можно разместить"
	}

	if confidence >= tier3Threshold {
		return 3, "сомнительно, стоит проверить"
	}

	return 4, "нетипичный формат, может подойти"
}

// ============================================================================
// CHECKPOINT MANAGEMENT
// ============================================================================

type CheckpointManager struct {
	checkpointDir string
	mu            sync.Mutex
	logger        *Logger
}

func NewCheckpointManager(dir string, logger *Logger) (*CheckpointManager, error) {
	if err := os.MkdirAll(dir, 0755); err != nil {
		return nil, fmt.Errorf("create checkpoint dir: %w", err)
	}

	return &CheckpointManager{
		checkpointDir: dir,
		logger:        logger,
	}, nil
}

func (cm *CheckpointManager) SaveDomainState(domain string, state *DomainState) error {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	state.Version = 1

	filename := fmt.Sprintf("%s.json", sanitizeDomainName(domain))
	path := filepath.Join(cm.checkpointDir, filename)
	tmpPath := path + ".tmp"

	data, err := json.MarshalIndent(state, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal state: %w", err)
	}

	if err := os.WriteFile(tmpPath, data, 0644); err != nil {
		return fmt.Errorf("write tmp checkpoint: %w", err)
	}

	// fsync
	f, err := os.OpenFile(tmpPath, os.O_RDWR, 0644)
	if err == nil {
		f.Sync()
		f.Close()
	}

	if err := os.Rename(tmpPath, path); err != nil {
		return fmt.Errorf("rename checkpoint: %w", err)
	}

	return nil
}

func (cm *CheckpointManager) LoadDomainState(domain string) (*DomainState, error) {
	cm.mu.Lock()
	defer cm.mu.Unlock()

	filename := fmt.Sprintf("%s.json", sanitizeDomainName(domain))
	path := filepath.Join(cm.checkpointDir, filename)

	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return &DomainState{
				Domain:       domain,
				LastActivity: time.Now(),
			}, nil
		}
		return nil, fmt.Errorf("read checkpoint: %w", err)
	}

	var state DomainState
	if err := json.Unmarshal(data, &state); err != nil {
		cm.logger.Warn("corrupted checkpoint, starting fresh", map[string]interface{}{
			"domain": domain,
			"error":  err.Error(),
		})
		return &DomainState{
			Domain:       domain,
			LastActivity: time.Now(),
		}, nil
	}

	// Миграция версий (если нужно в будущем)
	if state.Version == 0 {
		state.Version = 1
	}

	return &state, nil
}

func sanitizeDomainName(domain string) string {
	domain = strings.ReplaceAll(domain, ":", "_")
	domain = strings.ReplaceAll(domain, "/", "_")
	domain = strings.ReplaceAll(domain, "\\", "_")
	return domain
}

// ============================================================================
// DOMAIN CRAWLER (обход одного домена)
// ============================================================================

type DomainCrawler struct {
	domain       string
	config       *Config
	httpClient   *HTTPClient
	resultWriter *ResultWriter
	visited      *VisitedStore
	ramQueue     *PriorityQueue
	diskQueue    *DiskQueue
	prioritizer  *LinkPrioritizer
	checkpoint   *CheckpointManager
	logger       *Logger

	ctx    context.Context
	cancel context.CancelFunc
	wg     sync.WaitGroup

	pages        int64
	found        int64
	errors       int64
	lastActivity time.Time
	activityMu   sync.Mutex

	stopping int32
}

func NewDomainCrawler(
	domain string,
	config *Config,
	httpClient *HTTPClient,
	resultWriter *ResultWriter,
	checkpoint *CheckpointManager,
	logger *Logger,
) (*DomainCrawler, error) {

	ctx, cancel := context.WithCancel(context.Background())
	if config.DomainDeadline > 0 {
		ctx, cancel = context.WithTimeout(context.Background(), config.DomainDeadline)
	}

	queuePath := filepath.Join(config.DiskQueueDir, sanitizeDomainName(domain)+".queue")
	diskQueue, err := NewDiskQueue(queuePath, config.DiskBatchSize, logger)
	if err != nil {
		cancel()
		return nil, fmt.Errorf("create disk queue: %w", err)
	}

	dc := &DomainCrawler{
		domain:       domain,
		config:       config,
		httpClient:   httpClient,
		resultWriter: resultWriter,
		visited:      NewVisitedStore(),
		ramQueue:     NewPriorityQueue(),
		diskQueue:    diskQueue,
		prioritizer:  NewLinkPrioritizer(),
		checkpoint:   checkpoint,
		logger:       logger,
		ctx:          ctx,
		cancel:       cancel,
		lastActivity: time.Now(),
	}

	// Загрузка состояния
	if err := dc.loadState(); err != nil {
		dc.logger.Warn("failed to load domain state", map[string]interface{}{
			"domain": domain,
			"error":  err.Error(),
		})
	}

	return dc, nil
}

func (dc *DomainCrawler) loadState() error {
	state, err := dc.checkpoint.LoadDomainState(dc.domain)
	if err != nil {
		return err
	}

	atomic.StoreInt64(&dc.pages, state.Pages)
	atomic.StoreInt64(&dc.found, state.Found)
	atomic.StoreInt64(&dc.errors, state.Errors)
	dc.lastActivity = state.LastActivity

	// Загрузка visited
	visitedPath := filepath.Join(dc.config.CheckpointDir, sanitizeDomainName(dc.domain)+"_visited.jsonl")
	if err := dc.visited.Load(visitedPath); err != nil {
		dc.logger.Warn("failed to load visited", map[string]interface{}{
			"domain": dc.domain,
			"error":  err.Error(),
		})
	}

	dc.logger.Info("loaded domain state", map[string]interface{}{
		"domain":  dc.domain,
		"pages":   state.Pages,
		"found":   state.Found,
		"visited": dc.visited.Size(),
	})

	return nil
}

func (dc *DomainCrawler) saveState() error {
	state := &DomainState{
		Domain:       dc.domain,
		Pages:        atomic.LoadInt64(&dc.pages),
		Found:        atomic.LoadInt64(&dc.found),
		Errors:       atomic.LoadInt64(&dc.errors),
		QueueOffset:  0,
		LastActivity: dc.getLastActivity(),
	}

	if err := dc.checkpoint.SaveDomainState(dc.domain, state); err != nil {
		return err
	}

	// Сохранение visited
	visitedPath := filepath.Join(dc.config.CheckpointDir, sanitizeDomainName(dc.domain)+"_visited.jsonl")
	if err := dc.visited.Save(visitedPath); err != nil {
		return err
	}

	return nil
}

func (dc *DomainCrawler) Start(ctx context.Context) error {
	dc.logger.Info("starting domain crawler", map[string]interface{}{"domain": dc.domain})

	// Посев начальных URL
	if err := dc.seedInitialURLs(); err != nil {
		dc.logger.Error("failed to seed urls", map[string]interface{}{
			"domain": dc.domain,
			"error":  err.Error(),
		})
		return err
	}

	// Запуск воркеров
	for i := 0; i < dc.config.WorkersPerDomain; i++ {
		dc.wg.Add(1)
		go dc.worker(i)
	}

	// Запуск монитора
	dc.wg.Add(1)
	go dc.monitor()

	// Запуск периодического чекпоинта
	dc.wg.Add(1)
	go dc.checkpointLoop()

	// Ожидание завершения
	dc.wg.Wait()

	// Финальное сохранение
	if err := dc.saveState(); err != nil {
		dc.logger.Warn("failed to save final state", map[string]interface{}{
			"domain": dc.domain,
			"error":  err.Error(),
		})
	}

	dc.logger.Info("domain crawler finished", map[string]interface{}{
		"domain": dc.domain,
		"pages":  atomic.LoadInt64(&dc.pages),
		"found":  atomic.LoadInt64(&dc.found),
		"errors": atomic.LoadInt64(&dc.errors),
	})

	return nil
}

func (dc *DomainCrawler) seedInitialURLs() error {
	baseURL := fmt.Sprintf("https://%s/", dc.domain)

	// Домашняя страница
	if !dc.visited.Contains(baseURL) {
		dc.enqueueURL(baseURL, 0.8, 0)
	}

	// Попытка загрузить sitemap
	sitemapURL := fmt.Sprintf("https://%s/sitemap.xml", dc.domain)
	dc.enqueueURL(sitemapURL, 0.5, 0)

	// Типичные страницы
	commonPaths := []string{
		"/blog/", "/posts/", "/articles/", "/news/",
		"/forum/", "/community/", "/discussion/",
	}

	for _, path := range commonPaths {
		url := fmt.Sprintf("https://%s%s", dc.domain, path)
		if !dc.visited.Contains(url) {
			dc.enqueueURL(url, 0.6, 0)
		}
	}

	return nil
}

func (dc *DomainCrawler) enqueueURL(urlStr string, priority float64, depth int) {
	item := URLItem{
		URL:      urlStr,
		Priority: priority,
		Depth:    depth,
	}

	// Сначала в RAM очередь
	if dc.ramQueue.Len() < dc.config.MaxRAMQueue {
		dc.ramQueue.Push(item)
	} else {
		// Пролив в disk очередь
		if err := dc.diskQueue.Push([]URLItem{item}); err != nil {
			dc.logger.Warn("failed to push to disk queue", map[string]interface{}{
				"url":   urlStr,
				"error": err.Error(),
			})
		}
	}

	dc.updateActivity()
}

func (dc *DomainCrawler) worker(id int) {
	defer dc.wg.Done()
	defer func() {
		if r := recover(); r != nil {
			dc.logger.Error("worker panic recovered", map[string]interface{}{
				"worker_id": id,
				"domain":    dc.domain,
				"panic":     r,
			})
		}
	}()

	dc.logger.Trace("worker started", map[string]interface{}{
		"worker_id": id,
		"domain":    dc.domain,
	})

	for {
		select {
		case <-dc.ctx.Done():
			dc.logger.Trace("worker stopping", map[string]interface{}{
				"worker_id": id,
				"domain":    dc.domain,
			})
			return
		default:
		}

		// Проверка стоп-условий
		if dc.shouldStop() {
			dc.logger.Trace("worker detected stop condition", map[string]interface{}{
				"worker_id": id,
				"domain":    dc.domain,
			})
			dc.cancel()
			return
		}

		// Получение URL из очереди
		item, ok := dc.dequeueURL()
		if !ok {
			time.Sleep(100 * time.Millisecond)
			continue
		}

		dc.processURL(item)
	}
}

func (dc *DomainCrawler) dequeueURL() (URLItem, bool) {
	// Сначала из RAM
	if item, ok := dc.ramQueue.Pop(); ok {
		return item, true
	}

	// Затем из disk
	items, err := dc.diskQueue.Pop(10)
	if err != nil {
		dc.logger.Warn("failed to pop from disk queue", map[string]interface{}{
			"domain": dc.domain,
			"error":  err.Error(),
		})
		return URLItem{}, false
	}

	if len(items) == 0 {
		return URLItem{}, false
	}

	// Первый элемент возвращаем, остальные в RAM
	for i := 1; i < len(items); i++ {
		if dc.ramQueue.Len() < dc.config.MaxRAMQueue {
			dc.ramQueue.Push(items[i])
		} else {
			break
		}
	}

	return items[0], true
}

func (dc *DomainCrawler) processURL(item URLItem) {
	// Дедуп через visited
	if dc.visited.LoadOrStore(item.URL) {
		return
	}

	dc.logger.Trace("processing url", map[string]interface{}{
		"domain":   dc.domain,
		"url":      item.URL,
		"priority": item.Priority,
		"depth":    item.Depth,
	})

	// Контекст с таймаутом для запроса
	ctx, cancel := context.WithTimeout(dc.ctx, dc.config.HTTPTimeout)
	defer cancel()

	// Загрузка страницы
	body, metadata, err := dc.httpClient.Fetch(ctx, item.URL)
	if err != nil {
		atomic.AddInt64(&dc.errors, 1)
		dc.logger.Trace("fetch failed", map[string]interface{}{
			"domain": dc.domain,
			"url":    item.URL,
			"error":  err.Error(),
		})
		return
	}

	atomic.AddInt64(&dc.pages, 1)
	dc.updateActivity()

	// Извлечение ссылок
	baseURL, _ := url.Parse(item.URL)
	links, err := extractLinks(body, baseURL, dc.domain)
	if err != nil {
		dc.logger.Trace("extract links failed", map[string]interface{}{
			"domain": dc.domain,
			"url":    item.URL,
			"error":  err.Error(),
		})
	} else {
		dc.enqueueLinks(links, item.Depth+1)
	}

	// Детекция комментариев
	finding, detected := detectComments(body, metadata)
	if detected {
		finding.Domain = dc.domain
		tier, label := classifyFindingTier(finding.Confidence, finding.Signals)
		finding.Tier = tier
		finding.TierLabel = label

		// Запись результата
		if err := dc.resultWriter.WriteFinding(*finding); err != nil {
			dc.logger.Warn("failed to write finding", map[string]interface{}{
				"domain": dc.domain,
				"url":    item.URL,
				"error":  err.Error(),
			})
		} else {
			atomic.AddInt64(&dc.found, 1)
			dc.prioritizer.RecordSuccess(item.URL)

			dc.logger.Info("found comments", map[string]interface{}{
				"domain":     dc.domain,
				"url":        item.URL,
				"tier":       tier,
				"tier_label": label,
				"confidence": finding.Confidence,
			})
		}
	}
}

func (dc *DomainCrawler) enqueueLinks(links []string, depth int) {
	// Батчевая обработка
	batch := make([]URLItem, 0, len(links))

	for _, link := range links {
		if dc.visited.Contains(link) {
			continue
		}

		priority := dc.prioritizer.PrioritizeLink(link, depth)
		item := URLItem{
			URL:      link,
			Priority: priority,
			Depth:    depth,
		}

		if dc.ramQueue.Len() < dc.config.MaxRAMQueue {
			dc.ramQueue.Push(item)
		} else {
			batch = append(batch, item)
		}
	}

	// Пролив избытка на диск
	if len(batch) > 0 {
		if err := dc.diskQueue.Push(batch); err != nil {
			dc.logger.Warn("failed to push batch to disk", map[string]interface{}{
				"domain": dc.domain,
				"count":  len(batch),
				"error":  err.Error(),
			})
		}
	}
}

func (dc *DomainCrawler) shouldStop() bool {
	if atomic.LoadInt32(&dc.stopping) == 1 {
		return true
	}

	found := atomic.LoadInt64(&dc.found)
	pages := atomic.LoadInt64(&dc.pages)

	// Достигнут минимум находок
	if found >= int64(dc.config.MinFindingsPerDomain) {
		atomic.StoreInt32(&dc.stopping, 1)
		return true
	}

	// Достигнут лимит страниц
	if pages >= int64(dc.config.MaxPagesPerDomain) {
		atomic.StoreInt32(&dc.stopping, 1)
		return true
	}

	return false
}

func (dc *DomainCrawler) monitor() {
	defer dc.wg.Done()

	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()

	inactivityCount := 0
	const maxInactivity = 6 // 30 секунд

	for {
		select {
		case <-dc.ctx.Done():
			return
		case <-ticker.C:
			pages := atomic.LoadInt64(&dc.pages)
			found := atomic.LoadInt64(&dc.found)
			errors := atomic.LoadInt64(&dc.errors)
			ramQLen := dc.ramQueue.Len()
			visitedSize := dc.visited.Size()

			lastActivity := dc.getLastActivity()
			timeSinceActivity := time.Since(lastActivity)

			dc.logger.Info("domain progress", map[string]interface{}{
				"domain":        dc.domain,
				"pages":         pages,
				"found":         found,
				"errors":        errors,
				"ram_queue":     ramQLen,
				"visited":       visitedSize,
				"last_activity": timeSinceActivity.Seconds(),
			})

			// Проверка инактивности
			if ramQLen == 0 && timeSinceActivity > 5*time.Second {
				inactivityCount++
				if inactivityCount >= maxInactivity {
					dc.logger.Info("domain inactive, stopping", map[string]interface{}{
						"domain": dc.domain,
					})
					dc.cancel()
					return
				}
			} else {
				inactivityCount = 0
			}
		}
	}
}

func (dc *DomainCrawler) checkpointLoop() {
	defer dc.wg.Done()

	ticker := time.NewTicker(dc.config.CheckpointInterval)
	defer ticker.Stop()

	for {
		select {
		case <-dc.ctx.Done():
			return
		case <-ticker.C:
			if err := dc.saveState(); err != nil {
				dc.logger.Warn("checkpoint failed", map[string]interface{}{
					"domain": dc.domain,
					"error":  err.Error(),
				})
			} else {
				dc.logger.Trace("checkpoint saved", map[string]interface{}{
					"domain": dc.domain,
				})
			}
		}
	}
}

func (dc *DomainCrawler) updateActivity() {
	dc.activityMu.Lock()
	dc.lastActivity = time.Now()
	dc.activityMu.Unlock()
}

func (dc *DomainCrawler) getLastActivity() time.Time {
	dc.activityMu.Lock()
	defer dc.activityMu.Unlock()
	return dc.lastActivity
}

func (dc *DomainCrawler) Close() error {
	dc.cancel()
	dc.wg.Wait()

	if err := dc.diskQueue.Close(); err != nil {
		dc.logger.Warn("failed to close disk queue", map[string]interface{}{
			"domain": dc.domain,
			"error":  err.Error(),
		})
	}

	return nil
}

// ============================================================================
// MAIN CRAWLER (управление доменами)
// ============================================================================

type MainCrawler struct {
	config       *Config
	domains      []string
	httpClient   *HTTPClient
	resultWriter *ResultWriter
	checkpoint   *CheckpointManager
	logger       *Logger

	semaphore chan struct{}
	wg        sync.WaitGroup
	ctx       context.Context
	cancel    context.CancelFunc

	shuttingDown     int32
	completedDomains map[string]bool
	completedMu      sync.Mutex
}

func NewMainCrawler(config *Config, domains []string, logger *Logger) (*MainCrawler, error) {
	if err := config.Validate(); err != nil {
		return nil, fmt.Errorf("invalid config: %w", err)
	}

	httpClient := NewHTTPClient(config, logger)

	resultWriter, err := NewResultWriter(
		config.OutputDir,
		config.JSONLSyncInterval,
		config.TierSyncInterval,
		logger,
	)
	if err != nil {
		return nil, fmt.Errorf("create result writer: %w", err)
	}

	checkpoint, err := NewCheckpointManager(config.CheckpointDir, logger)
	if err != nil {
		return nil, fmt.Errorf("create checkpoint manager: %w", err)
	}

	ctx, cancel := context.WithCancel(context.Background())

	maxDomains := config.MaxConcurrentDomains()

	mc := &MainCrawler{
		config:           config,
		domains:          domains,
		httpClient:       httpClient,
		resultWriter:     resultWriter,
		checkpoint:       checkpoint,
		logger:           logger,
		semaphore:        make(chan struct{}, maxDomains),
		ctx:              ctx,
		cancel:           cancel,
		completedDomains: make(map[string]bool),
	}

	return mc, nil
}

func (mc *MainCrawler) Run(ctx context.Context) error {
	mc.logger.Info("starting main crawler", map[string]interface{}{
		"domains":            len(mc.domains),
		"max_concurrent":     cap(mc.semaphore),
		"workers_per_domain": mc.config.WorkersPerDomain,
	})

	for _, domain := range mc.domains {
		if atomic.LoadInt32(&mc.shuttingDown) == 1 {
			mc.logger.Info("shutdown in progress, skipping remaining domains", nil)
			break
		}

		// Проверка, не завершён ли уже домен
		if mc.isCompleted(domain) {
			mc.logger.Info("domain already completed, skipping", map[string]interface{}{
				"domain": domain,
			})
			continue
		}

		// Захват семафора
		select {
		case mc.semaphore <- struct{}{}:
		case <-mc.ctx.Done():
			mc.logger.Info("context canceled while waiting for semaphore", nil)
			break
		}

		mc.wg.Add(1)
		go mc.processDomain(domain)
	}

	// Ожидание завершения всех доменов
	mc.wg.Wait()

	// Финальная синхронизация
	if err := mc.resultWriter.Sync(); err != nil {
		mc.logger.Warn("final sync failed", map[string]interface{}{"error": err.Error()})
	}

	mc.logger.Info("main crawler finished", map[string]interface{}{
		"completed_domains": len(mc.completedDomains),
	})

	return nil
}

func (mc *MainCrawler) processDomain(domain string) {
	defer mc.wg.Done()
	defer func() { <-mc.semaphore }()
	defer func() {
		if r := recover(); r != nil {
			mc.logger.Error("domain processing panic recovered", map[string]interface{}{
				"domain": domain,
				"panic":  r,
			})
		}
	}()

	mc.logger.Info("processing domain", map[string]interface{}{"domain": domain})

	crawler, err := NewDomainCrawler(
		domain,
		mc.config,
		mc.httpClient,
		mc.resultWriter,
		mc.checkpoint,
		mc.logger,
	)
	if err != nil {
		mc.logger.Error("failed to create domain crawler", map[string]interface{}{
			"domain": domain,
			"error":  err.Error(),
		})
		return
	}
	defer crawler.Close()

	if err := crawler.Start(mc.ctx); err != nil {
		mc.logger.Error("domain crawler failed", map[string]interface{}{
			"domain": domain,
			"error":  err.Error(),
		})
		return
	}

	mc.markCompleted(domain)
	mc.logger.Info("domain completed", map[string]interface{}{"domain": domain})
}

func (mc *MainCrawler) isCompleted(domain string) bool {
	mc.completedMu.Lock()
	defer mc.completedMu.Unlock()
	return mc.completedDomains[domain]
}

func (mc *MainCrawler) markCompleted(domain string) {
	mc.completedMu.Lock()
	defer mc.completedMu.Unlock()
	mc.completedDomains[domain] = true
}

func (mc *MainCrawler) Shutdown(ctx context.Context) error {
	mc.logger.Info("initiating graceful shutdown", nil)

	atomic.StoreInt32(&mc.shuttingDown, 1)
	mc.cancel()

	// Ожидание завершения с таймаутом
	done := make(chan struct{})
	go func() {
		mc.wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		mc.logger.Info("graceful shutdown completed", nil)
	case <-ctx.Done():
		mc.logger.Warn("graceful shutdown timeout", nil)
		return fmt.Errorf("graceful shutdown timeout")
	}

	// Закрытие writer
	if err := mc.resultWriter.Sync(); err != nil {
		mc.logger.Warn("failed to sync result writer", map[string]interface{}{"error": err.Error()})
	}
	if err := mc.resultWriter.Close(); err != nil {
		mc.logger.Warn("failed to close result writer", map[string]interface{}{"error": err.Error()})
	}

	return nil
}

// ============================================================================
// CLI & MAIN
// ============================================================================

type CLIFlags struct {
	DomainsFile      string
	WorkersPerDomain int
	MaxWorkers       int
	MaxPages         int
	MinFindings      int
	OutputDir        string
	CheckpointDir    string
	QueueDir         string
	Timeout          time.Duration
	LogLevel         string
	LogJSON          bool
	WindowsMode      bool
}

func parseFlags() (*CLIFlags, error) {
	flags := &CLIFlags{}

	flag.StringVar(&flags.DomainsFile, "domains", "", "path to domains file (one per line)")
	flag.IntVar(&flags.WorkersPerDomain, "workers", 5, "workers per domain")
	flag.IntVar(&flags.MaxWorkers, "max-workers", 100, "max total workers")
	flag.IntVar(&flags.MaxPages, "max-pages", 5000, "max pages per domain")
	flag.IntVar(&flags.MinFindings, "min-findings", 50, "minimum findings per domain")
	flag.StringVar(&flags.OutputDir, "output", "./data/output", "output directory")
	flag.StringVar(&flags.CheckpointDir, "checkpoint", "./data/checkpoint", "checkpoint directory")
	flag.StringVar(&flags.QueueDir, "queue", "./data/queue", "queue directory")
	flag.DurationVar(&flags.Timeout, "timeout", 0, "domain timeout (0=no limit)")
	flag.StringVar(&flags.LogLevel, "log-level", "INFO", "log level (TRACE/INFO/WARN/ERROR)")
	flag.BoolVar(&flags.LogJSON, "log-json", false, "output logs as JSON")
	flag.BoolVar(&flags.WindowsMode, "windows-mode", runtime.GOOS == "windows", "Windows compatibility mode")

	flag.Parse()

	if flags.DomainsFile == "" {
		return nil, fmt.Errorf("domains file is required")
	}

	return flags, nil
}

func loadDomains(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("open domains file: %w", err)
	}
	defer f.Close()

	var domains []string
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		domain := strings.TrimSpace(scanner.Text())
		if domain != "" && !strings.HasPrefix(domain, "#") {
			domains = append(domains, domain)
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("scan domains: %w", err)
	}

	return domains, nil
}

func main() {
	flags, err := parseFlags()
	if err != nil {
		log.Fatalf("Invalid flags: %v", err)
	}

	logger := NewLogger(flags.LogLevel, flags.LogJSON)

	domains, err := loadDomains(flags.DomainsFile)
	if err != nil {
		logger.Error("failed to load domains", map[string]interface{}{"error": err.Error()})
		os.Exit(1)
	}

	logger.Info("loaded domains", map[string]interface{}{"count": len(domains)})

	config := DefaultConfig()
	config.WorkersPerDomain = flags.WorkersPerDomain
	config.MaxTotalWorkers = flags.MaxWorkers
	config.MaxPagesPerDomain = flags.MaxPages
	config.MinFindingsPerDomain = flags.MinFindings
	config.OutputDir = flags.OutputDir
	config.CheckpointDir = flags.CheckpointDir
	config.DiskQueueDir = flags.QueueDir
	config.DomainDeadline = flags.Timeout
	config.LogLevel = flags.LogLevel
	config.LogJSON = flags.LogJSON
	config.WindowsMode = flags.WindowsMode

	crawler, err := NewMainCrawler(config, domains, logger)
	if err != nil {
		logger.Error("failed to create crawler", map[string]interface{}{"error": err.Error()})
		os.Exit(1)
	}

	// Обработка сигналов
	sigChan := make(chan os.Signal, 1)
	if config.WindowsMode {
		// Windows: только os.Interrupt (Ctrl+C)
		signal.Notify(sigChan, os.Interrupt)
	} else {
		// Unix-like: SIGINT и SIGTERM
		signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)
	}

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Горутина для обработки сигналов
	go func() {
		sig := <-sigChan
		logger.Info("received signal", map[string]interface{}{"signal": sig.String()})

		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer shutdownCancel()

		if err := crawler.Shutdown(shutdownCtx); err != nil {
			logger.Error("shutdown error", map[string]interface{}{"error": err.Error()})
			os.Exit(1)
		}

		cancel()
	}()

	// Запуск краулера
	if err := crawler.Run(ctx); err != nil {
		logger.Error("crawler error", map[string]interface{}{"error": err.Error()})
		os.Exit(1)
	}

	logger.Info("crawler completed successfully", nil)
}
