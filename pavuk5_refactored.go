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
	"hash/fnv"
	"io"
	"log"
	"math"
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
)

var (
	randMu     sync.Mutex
	globalRand = rand.New(rand.NewSource(time.Now().UnixNano()))
)

func randomFloat64() float64 {
	randMu.Lock()
	defer randMu.Unlock()
	return globalRand.Float64()
}

// ============================================================================
// HTML PARSER (SELF-CONTAINED)
// ============================================================================

var htmlEscapeReplacer = strings.NewReplacer(
	"&", "&amp;",
	"<", "&lt;",
	">", "&gt;",
	"\"", "&quot;",
)

// HTMLNodeType describes the type of an HTML node in the simplified parser.
type HTMLNodeType int

const (
	// HTMLDocumentNode represents the root document node.
	HTMLDocumentNode HTMLNodeType = iota
	// HTMLElementNode represents an element node, e.g. <div>.
	HTMLElementNode
	// HTMLTextNode represents a text node.
	HTMLTextNode
	// HTMLCommentNode represents an HTML comment.
	HTMLCommentNode
)

// HTMLAttribute stores a single HTML attribute key/value pair.
type HTMLAttribute struct {
	Key string
	Val string
}

// HTMLNode provides a minimal DOM-like structure compatible with the crawler's needs.
type HTMLNode struct {
	Type        HTMLNodeType
	Data        string
	Attr        []HTMLAttribute
	Parent      *HTMLNode
	FirstChild  *HTMLNode
	LastChild   *HTMLNode
	PrevSibling *HTMLNode
	NextSibling *HTMLNode
}

func newHTMLNode(nodeType HTMLNodeType, data string) *HTMLNode {
	return &HTMLNode{Type: nodeType, Data: strings.ToLower(data)}
}

func (n *HTMLNode) appendChild(child *HTMLNode) {
	if child == nil {
		return
	}
	child.Parent = n
	if n.FirstChild == nil {
		n.FirstChild = child
		n.LastChild = child
		return
	}
	child.PrevSibling = n.LastChild
	n.LastChild.NextSibling = child
	n.LastChild = child
}

// parseHTML builds a lightweight DOM tree from the provided reader.
func parseHTML(r io.Reader) (*HTMLNode, error) {
	data, err := io.ReadAll(r)
	if err != nil {
		return nil, err
	}

	parser := &htmlParser{data: data, length: len(data)}
	return parser.parse()
}

type htmlParser struct {
	data   []byte
	length int
	pos    int
}

func (p *htmlParser) parse() (*HTMLNode, error) {
	root := &HTMLNode{Type: HTMLDocumentNode}
	current := root

	for p.pos < p.length {
		if p.peek() == '<' {
			switch {
			case p.match("<!--"):
				comment := p.readUntil("-->")
				node := &HTMLNode{Type: HTMLCommentNode, Data: comment}
				current.appendChild(node)
			case p.match("</"):
				name := p.readTagName()
				p.skipUntil('>')
				p.consume('>')
				name = strings.ToLower(name)
				for current != root && current.Data != name {
					current = current.Parent
				}
				if current.Parent != nil {
					current = current.Parent
				}
			case p.match("<?"):
				p.readUntil("?>")
			case p.match("<!"):
				p.skipUntil('>')
				p.consume('>')
			default:
				name, attrs, selfClosing := p.parseStartTag()
				node := newHTMLNode(HTMLElementNode, name)
				node.Attr = attrs
				current.appendChild(node)
				if selfClosing || isVoidElement(node.Data) {
					// nothing
				} else {
					current = node
				}
			}
		} else {
			text := p.readText()
			if text != "" {
				node := &HTMLNode{Type: HTMLTextNode, Data: text}
				current.appendChild(node)
			}
		}
	}

	return root, nil
}

func (p *htmlParser) peek() byte {
	if p.pos >= p.length {
		return 0
	}
	return p.data[p.pos]
}

func (p *htmlParser) match(prefix string) bool {
	if p.pos+len(prefix) > p.length {
		return false
	}
	if string(p.data[p.pos:p.pos+len(prefix)]) == prefix {
		p.pos += len(prefix)
		return true
	}
	return false
}

func (p *htmlParser) readUntil(delim string) string {
	idx := bytes.Index(p.data[p.pos:], []byte(delim))
	if idx == -1 {
		idx = p.length - p.pos
	}
	result := string(p.data[p.pos : p.pos+idx])
	p.pos += idx + len(delim)
	return result
}

func (p *htmlParser) consume(ch byte) {
	if p.pos < p.length && p.data[p.pos] == ch {
		p.pos++
	}
}

func (p *htmlParser) readTagName() string {
	start := p.pos
	for p.pos < p.length {
		ch := p.data[p.pos]
		if isSpace(ch) || ch == '>' || ch == '/' {
			break
		}
		p.pos++
	}
	return string(p.data[start:p.pos])
}

func (p *htmlParser) readText() string {
	start := p.pos
	for p.pos < p.length && p.data[p.pos] != '<' {
		p.pos++
	}
	return string(p.data[start:p.pos])
}

func (p *htmlParser) parseStartTag() (string, []HTMLAttribute, bool) {
	name := p.readTagName()
	attrs := make([]HTMLAttribute, 0, 4)
	selfClosing := false

	for p.pos < p.length {
		p.skipSpaces()
		if p.pos >= p.length {
			break
		}
		ch := p.data[p.pos]
		if ch == '>' {
			p.pos++
			break
		}
		if ch == '/' {
			p.pos++
			p.skipSpaces()
			p.consume('>')
			selfClosing = true
			break
		}

		attrName := p.readTagName()
		if attrName == "" {
			p.skipUntil('>')
			p.consume('>')
			break
		}

		attrVal := ""
		p.skipSpaces()
		if p.pos < p.length && p.data[p.pos] == '=' {
			p.pos++
			p.skipSpaces()
			attrVal = p.readAttrValue()
		}

		attrs = append(attrs, HTMLAttribute{Key: strings.ToLower(attrName), Val: attrVal})
	}

	return strings.ToLower(name), attrs, selfClosing
}

func (p *htmlParser) readAttrValue() string {
	if p.pos >= p.length {
		return ""
	}

	quote := p.data[p.pos]
	if quote == '"' || quote == '\'' {
		p.pos++
		start := p.pos
		for p.pos < p.length && p.data[p.pos] != quote {
			p.pos++
		}
		val := string(p.data[start:p.pos])
		p.consume(quote)
		return val
	}

	start := p.pos
	for p.pos < p.length {
		ch := p.data[p.pos]
		if isSpace(ch) || ch == '>' {
			break
		}
		if ch == '/' {
			break
		}
		p.pos++
	}
	return string(p.data[start:p.pos])
}

func (p *htmlParser) skipSpaces() {
	for p.pos < p.length && isSpace(p.data[p.pos]) {
		p.pos++
	}
}

func (p *htmlParser) skipUntil(ch byte) {
	for p.pos < p.length && p.data[p.pos] != ch {
		p.pos++
	}
}

func isSpace(ch byte) bool {
	return ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t' || ch == '\f'
}

var voidElements = map[string]struct{}{
	"area": {}, "base": {}, "br": {}, "col": {}, "embed": {}, "hr": {}, "img": {}, "input": {},
	"link": {}, "meta": {}, "param": {}, "source": {}, "track": {}, "wbr": {},
}

func isVoidElement(name string) bool {
	_, ok := voidElements[name]
	return ok
}

// renderHTML produces a textual representation of the HTML tree.
func renderHTML(n *HTMLNode) string {
	var sb strings.Builder
	renderHTMLInto(&sb, n)
	return sb.String()
}

func renderHTMLInto(sb *strings.Builder, n *HTMLNode) {
	if n == nil {
		return
	}

	switch n.Type {
	case HTMLDocumentNode:
		for child := n.FirstChild; child != nil; child = child.NextSibling {
			renderHTMLInto(sb, child)
		}
	case HTMLElementNode:
		sb.WriteByte('<')
		sb.WriteString(n.Data)
		for _, attr := range n.Attr {
			sb.WriteByte(' ')
			sb.WriteString(attr.Key)
			sb.WriteString("=\"")
			sb.WriteString(htmlEscape(attr.Val))
			sb.WriteByte('"')
		}
		if isVoidElement(n.Data) {
			sb.WriteByte('>')
			return
		}
		sb.WriteByte('>')
		for child := n.FirstChild; child != nil; child = child.NextSibling {
			renderHTMLInto(sb, child)
		}
		sb.WriteString("</")
		sb.WriteString(n.Data)
		sb.WriteByte('>')
	case HTMLTextNode:
		sb.WriteString(htmlEscape(n.Data))
	case HTMLCommentNode:
		sb.WriteString("<!--")
		sb.WriteString(n.Data)
		sb.WriteString("-->")
	}
}

func htmlEscape(s string) string {
	if s == "" {
		return s
	}
	return htmlEscapeReplacer.Replace(s)
}

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
	EnableRetry        bool
	MaxRetries         int
	RetryBaseBackoff   time.Duration
	EnableRedirectLoop bool

	// Директории
	DiskQueueDir  string
	CheckpointDir string
	OutputDir     string

	// Синхронизация
	TierSyncInterval    time.Duration
	JSONLSyncInterval   time.Duration
	CheckpointInterval  time.Duration
	GlobalStatsInterval time.Duration

	// Очереди
	MaxRAMQueue              int
	DiskBatchSize            int
	EnableVisitedSnapshot    bool
	VisitedSnapshotThreshold int

	// Логирование
	LogLevel string
	LogJSON  bool

	// Платформа
	WindowsMode bool

	// Приоритезация и классификация
	EnableTierHysteresis    bool
	TierHysteresisWindow    float64
	TierHysteresisTTL       time.Duration
	TierHysteresisCache     int
	EnableLastModifiedBonus bool
	EnableCanonicalDedup    bool

	// Rate limit
	EnableRateLimit bool
	RateLimitRPS    float64

	// Robots policy ("log" или "respect")
	RobotsPolicy string

	// Глобальная статистика
	GlobalStatsPath string
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
		EnableRetry:        true,
		MaxRetries:         3,
		RetryBaseBackoff:   500 * time.Millisecond,
		EnableRedirectLoop: true,

		DiskQueueDir:  "./data/queue",
		CheckpointDir: "./data/checkpoint",
		OutputDir:     "./data/output",

		TierSyncInterval:    5 * time.Second,
		JSONLSyncInterval:   5 * time.Second,
		CheckpointInterval:  10 * time.Second,
		GlobalStatsInterval: 15 * time.Second,

		MaxRAMQueue:              512,
		DiskBatchSize:            100,
		EnableVisitedSnapshot:    true,
		VisitedSnapshotThreshold: 5_000_000,

		LogLevel: "INFO",
		LogJSON:  false,

		WindowsMode: runtime.GOOS == "windows",

		EnableTierHysteresis:    true,
		TierHysteresisWindow:    0.02,
		TierHysteresisTTL:       10 * time.Minute,
		TierHysteresisCache:     10000,
		EnableLastModifiedBonus: true,
		EnableCanonicalDedup:    true,

		EnableRateLimit: false,
		RateLimitRPS:    3.0,

		RobotsPolicy: "log",
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
	if c.MaxRetries < 1 {
		c.MaxRetries = 1
	}
	if c.RetryBaseBackoff <= 0 {
		c.RetryBaseBackoff = 500 * time.Millisecond
	}
	if c.GlobalStatsInterval <= 0 {
		c.GlobalStatsInterval = 15 * time.Second
	}
	if c.EnableRateLimit && c.RateLimitRPS <= 0 {
		c.RateLimitRPS = 1.0
	}
	if !c.EnableRateLimit && c.RateLimitRPS < 0 {
		c.RateLimitRPS = 0
	}
	if c.TierHysteresisCache <= 0 {
		c.TierHysteresisCache = 10000
	}
	if c.TierHysteresisWindow < 0 {
		c.TierHysteresisWindow = 0
	}
	if c.TierHysteresisTTL <= 0 {
		c.TierHysteresisTTL = 10 * time.Minute
	}
	if c.EnableVisitedSnapshot && c.VisitedSnapshotThreshold <= 0 {
		c.VisitedSnapshotThreshold = 5_000_000
	}
	if c.RobotsPolicy == "" {
		c.RobotsPolicy = "log"
	}

	// Создание директорий
	for _, dir := range []string{c.DiskQueueDir, c.CheckpointDir, c.OutputDir} {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("failed to create directory %s: %w", dir, err)
		}
	}

	if c.GlobalStatsPath == "" {
		c.GlobalStatsPath = filepath.Join(c.OutputDir, "global_stats.json")
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
// RATE LIMITER
// ============================================================================

type RateLimiter struct {
	mu         sync.Mutex
	tokens     float64
	capacity   float64
	refillRate float64
	last       time.Time
}

func NewRateLimiter(rps float64) *RateLimiter {
	if rps <= 0 {
		rps = 1
	}
	return &RateLimiter{
		tokens:     rps,
		capacity:   rps,
		refillRate: rps,
		last:       time.Now(),
	}
}

func (rl *RateLimiter) Wait(ctx context.Context) error {
	if rl == nil {
		return nil
	}

	rl.mu.Lock()
	defer rl.mu.Unlock()

	for {
		now := time.Now()
		elapsed := now.Sub(rl.last).Seconds()
		if elapsed > 0 {
			rl.tokens = math.Min(rl.capacity, rl.tokens+elapsed*rl.refillRate)
			rl.last = now
		}

		if rl.tokens >= 1 {
			rl.tokens -= 1
			return nil
		}

		deficit := 1 - rl.tokens
		waitDuration := time.Duration(deficit / rl.refillRate * float64(time.Second))
		if waitDuration < 10*time.Millisecond {
			waitDuration = 10 * time.Millisecond
		}

		rl.mu.Unlock()
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(waitDuration):
		}
		rl.mu.Lock()
	}
}

// ============================================================================
// ROBOTS.TXT CHECKER
// ============================================================================

type RobotsAgent struct {
	mu        sync.Mutex
	domain    string
	policy    string
	fetched   bool
	disallow  []string
	allow     []string
	client    *HTTPClient
	logger    *Logger
	lastFetch time.Time
}

func NewRobotsAgent(domain, policy string, client *HTTPClient, logger *Logger) *RobotsAgent {
	return &RobotsAgent{domain: domain, policy: strings.ToLower(policy), client: client, logger: logger}
}

func (ra *RobotsAgent) Check(ctx context.Context, rawURL string) (bool, string) {
	if ra == nil {
		return true, ""
	}

	ra.mu.Lock()
	if !ra.fetched {
		ra.fetch(ctx)
	}
	ra.mu.Unlock()

	u, err := url.Parse(rawURL)
	if err != nil {
		return true, ""
	}

	path := u.EscapedPath()
	if path == "" {
		path = "/"
	}

	// Allow rules override disallow
	for _, allow := range ra.allow {
		if allow == "" {
			continue
		}
		if robotsMatch(path, allow) {
			return true, ""
		}
	}

	for _, dis := range ra.disallow {
		if dis == "" {
			continue
		}
		if robotsMatch(path, dis) {
			if ra.policy == "respect" {
				return false, dis
			}
			return true, dis
		}
	}

	return true, ""
}

func (ra *RobotsAgent) fetch(ctx context.Context) {
	ra.fetched = true

	if ra.client == nil {
		return
	}

	robotsURLs := []string{
		fmt.Sprintf("https://%s/robots.txt", ra.domain),
		fmt.Sprintf("http://%s/robots.txt", ra.domain),
	}

	for _, robotsURL := range robotsURLs {
		body, metadata, err := ra.client.Fetch(ctx, robotsURL)
		if err != nil {
			ra.logger.Trace("robots fetch failed", map[string]interface{}{"domain": ra.domain, "url": robotsURL, "error": err.Error()})
			continue
		}

		content := string(body)
		disallow, allow := parseRobots(content)
		ra.disallow = disallow
		ra.allow = allow
		ra.lastFetch = time.Now()
		ra.logger.Trace("robots loaded", map[string]interface{}{"domain": ra.domain, "url": metadata.URL, "disallow": len(disallow)})
		return
	}
}

func parseRobots(content string) ([]string, []string) {
	var disallow []string
	var allow []string
	applies := false

	lines := strings.Split(content, "\n")
	for _, line := range lines {
		if idx := strings.Index(line, "#"); idx >= 0 {
			line = line[:idx]
		}
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		lower := strings.ToLower(line)
		switch {
		case strings.HasPrefix(lower, "user-agent:"):
			agent := strings.TrimSpace(line[len("user-agent:"):])
			agent = strings.ToLower(agent)
			applies = agent == "*" || agent == ""
		case applies && strings.HasPrefix(lower, "disallow:"):
			rule := strings.TrimSpace(line[len("disallow:"):])
			disallow = append(disallow, rule)
		case applies && strings.HasPrefix(lower, "allow:"):
			rule := strings.TrimSpace(line[len("allow:"):])
			allow = append(allow, rule)
		}
	}

	// Учитываем длину allow для последующей проверки (длинные приоритетнее)
	sort.SliceStable(allow, func(i, j int) bool { return len(allow[i]) > len(allow[j]) })

	return disallow, allow
}

func robotsMatch(path, pattern string) bool {
	if pattern == "" {
		return false
	}
	if pattern == "/" {
		return true
	}

	if strings.Contains(pattern, "*") {
		parts := strings.Split(pattern, "*")
		idx := 0
		for i, part := range parts {
			if part == "" {
				continue
			}
			pos := strings.Index(path[idx:], part)
			if pos == -1 {
				return false
			}
			idx += pos + len(part)
			if i == 0 && !strings.HasPrefix(path, part) {
				return false
			}
		}
		if !strings.HasSuffix(pattern, "*") && !strings.HasSuffix(path, parts[len(parts)-1]) {
			return false
		}
		return true
	}

	return strings.HasPrefix(path, pattern)
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
	mu                sync.RWMutex
	hot               map[string]struct{}
	cold              map[uint64]struct{}
	first             map[uint64]string
	collisions        map[uint64]map[string]struct{}
	snapshotThreshold int
	snapshotPath      string
	total             int64
}

func NewVisitedStore() *VisitedStore {
	return &VisitedStore{
		hot:        make(map[string]struct{}),
		cold:       make(map[uint64]struct{}),
		first:      make(map[uint64]string),
		collisions: make(map[uint64]map[string]struct{}),
	}
}

func (v *VisitedStore) ConfigureSnapshot(path string, threshold int) {
	v.mu.Lock()
	defer v.mu.Unlock()
	v.snapshotPath = path
	v.snapshotThreshold = threshold
}

func (v *VisitedStore) LoadOrStore(url string) bool {
	v.mu.Lock()
	defer v.mu.Unlock()

	if _, exists := v.hot[url]; exists {
		return true
	}
	if v.existsInCold(url) {
		return true
	}

	v.hot[url] = struct{}{}
	v.total++
	v.maybeSnapshotLocked()
	return false
}

func (v *VisitedStore) Contains(url string) bool {
	v.mu.RLock()
	defer v.mu.RUnlock()

	if _, exists := v.hot[url]; exists {
		return true
	}

	return v.existsInCold(url)
}

func (v *VisitedStore) Size() int {
	v.mu.RLock()
	defer v.mu.RUnlock()
	return int(v.total)
}

func (v *VisitedStore) Save(path string) error {
	v.mu.Lock()
	defer v.mu.Unlock()

	if path != "" {
		v.snapshotPath = path
	}

	urls := make([]string, 0, len(v.hot)+len(v.first))
	for _, url := range v.first {
		urls = append(urls, url)
	}
	for _, bucket := range v.collisions {
		for url := range bucket {
			if url != "" {
				urls = append(urls, url)
			}
		}
	}
	for url := range v.hot {
		urls = append(urls, url)
	}

	sort.Strings(urls)

	tmpPath := path + ".tmp"
	f, err := os.Create(tmpPath)
	if err != nil {
		return fmt.Errorf("create visited tmp file: %w", err)
	}

	w := bufio.NewWriter(f)
	for _, url := range urls {
		if url == "" {
			continue
		}
		if _, err := w.WriteString(url + "\n"); err != nil {
			f.Close()
			os.Remove(tmpPath)
			return fmt.Errorf("write visited url: %w", err)
		}
	}

	if err := w.Flush(); err != nil {
		f.Close()
		os.Remove(tmpPath)
		return fmt.Errorf("flush visited: %w", err)
	}
	if err := f.Sync(); err != nil {
		f.Close()
		os.Remove(tmpPath)
		return fmt.Errorf("sync visited: %w", err)
	}
	if err := f.Close(); err != nil {
		os.Remove(tmpPath)
		return fmt.Errorf("close visited: %w", err)
	}

	if err := os.Rename(tmpPath, path); err != nil {
		return fmt.Errorf("rename visited: %w", err)
	}

	// После успешного сохранения очищаем hot и переносим в cold
	for url := range v.hot {
		v.addCold(url)
	}
	v.hot = make(map[string]struct{})

	return nil
}

func (v *VisitedStore) Load(path string) error {
	f, err := os.Open(path)
	if err != nil {
		if os.IsNotExist(err) {
			v.ConfigureSnapshot(path, v.snapshotThreshold)
			return nil
		}
		return fmt.Errorf("open visited: %w", err)
	}
	defer f.Close()

	v.mu.Lock()
	defer v.mu.Unlock()

	v.snapshotPath = path

	scanner := bufio.NewScanner(f)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 16*1024*1024)

	for scanner.Scan() {
		url := strings.TrimSpace(scanner.Text())
		if url == "" {
			continue
		}
		if !v.existsInCold(url) {
			v.addCold(url)
			v.total++
		}
	}

	return scanner.Err()
}

func (v *VisitedStore) maybeSnapshotLocked() {
	if v.snapshotThreshold <= 0 || len(v.hot) < v.snapshotThreshold {
		return
	}
	if v.snapshotPath == "" {
		return
	}

	urls := make([]string, 0, len(v.hot))
	for url := range v.hot {
		urls = append(urls, url)
	}

	if len(urls) == 0 {
		return
	}

	file, err := os.OpenFile(v.snapshotPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return
	}

	writer := bufio.NewWriter(file)
	for _, url := range urls {
		if _, err := writer.WriteString(url + "\n"); err != nil {
			file.Close()
			return
		}
	}
	if err := writer.Flush(); err != nil {
		file.Close()
		return
	}
	if err := file.Sync(); err != nil {
		file.Close()
		return
	}
	if err := file.Close(); err != nil {
		return
	}

	for _, url := range urls {
		v.addCold(url)
		delete(v.hot, url)
	}
}

func (v *VisitedStore) existsInCold(url string) bool {
	hash := hashURL(url)
	if _, ok := v.cold[hash]; !ok {
		return false
	}

	if first, ok := v.first[hash]; ok {
		if first == url {
			return true
		}
	}

	if bucket, ok := v.collisions[hash]; ok {
		if _, exists := bucket[url]; exists {
			return true
		}
	}

	return false
}

func (v *VisitedStore) addCold(url string) {
	hash := hashURL(url)
	if _, ok := v.cold[hash]; !ok {
		v.cold[hash] = struct{}{}
		v.first[hash] = url
		return
	}

	if existing, ok := v.first[hash]; ok {
		if existing == url {
			return
		}
	}

	bucket := v.collisions[hash]
	if bucket == nil {
		bucket = make(map[string]struct{})
	}
	bucket[url] = struct{}{}
	v.collisions[hash] = bucket
}

func hashURL(url string) uint64 {
	h := fnv.New64a()
	_, _ = h.Write([]byte(url))
	return h.Sum64()
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
// GLOBAL STATS MANAGER
// ============================================================================

type GlobalStatsSnapshot struct {
	Version          int64            `json:"version"`
	UpdatedAt        time.Time        `json:"updated_at"`
	Pages            int64            `json:"pages"`
	Findings         int64            `json:"findings"`
	TierCounts       map[string]int64 `json:"tier_counts"`
	ErrorsByKind     map[string]int64 `json:"errors_by_kind"`
	DomainsCompleted []string         `json:"domains_completed"`
}

type GlobalStatsManager struct {
	mu       sync.Mutex
	snapshot GlobalStatsSnapshot
	output   string
	interval time.Duration
	logger   *Logger
	ticker   *time.Ticker
	stop     chan struct{}
	domains  map[string]struct{}
	closed   int32
}

func NewGlobalStatsManager(path string, interval time.Duration, logger *Logger) *GlobalStatsManager {
	gsm := &GlobalStatsManager{
		snapshot: GlobalStatsSnapshot{
			Version:      1,
			TierCounts:   make(map[string]int64),
			ErrorsByKind: make(map[string]int64),
		},
		output:   path,
		interval: interval,
		logger:   logger,
		stop:     make(chan struct{}),
		domains:  make(map[string]struct{}),
	}

	if interval > 0 {
		gsm.ticker = time.NewTicker(interval)
		go gsm.loop()
	}

	return gsm
}

func (gsm *GlobalStatsManager) loop() {
	for {
		select {
		case <-gsm.stop:
			return
		case <-gsm.ticker.C:
			if err := gsm.Flush(); err != nil {
				gsm.logger.Warn("failed to flush global stats", map[string]interface{}{"error": err.Error()})
			}
		}
	}
}

func (gsm *GlobalStatsManager) RecordPage(domain string) {
	gsm.mu.Lock()
	gsm.snapshot.Pages++
	gsm.mu.Unlock()
}

func (gsm *GlobalStatsManager) RecordFinding(domain string, tier int) {
	gsm.mu.Lock()
	gsm.snapshot.Findings++
	tierKey := fmt.Sprintf("tier_%d", tier)
	gsm.snapshot.TierCounts[tierKey]++
	gsm.mu.Unlock()
}

func (gsm *GlobalStatsManager) RecordError(kind string) {
	gsm.mu.Lock()
	if kind == "" {
		kind = "unknown"
	}
	gsm.snapshot.ErrorsByKind[kind]++
	gsm.mu.Unlock()
}

func (gsm *GlobalStatsManager) MarkDomainCompleted(domain string) {
	gsm.mu.Lock()
	if domain != "" {
		gsm.domains[domain] = struct{}{}
	}
	gsm.mu.Unlock()
}

func (gsm *GlobalStatsManager) Flush() error {
	gsm.mu.Lock()
	defer gsm.mu.Unlock()

	if gsm.output == "" {
		return nil
	}

	gsm.snapshot.UpdatedAt = time.Now().UTC()

	domains := make([]string, 0, len(gsm.domains))
	for domain := range gsm.domains {
		domains = append(domains, domain)
	}
	sort.Strings(domains)

	snapshot := GlobalStatsSnapshot{
		Version:          gsm.snapshot.Version,
		UpdatedAt:        gsm.snapshot.UpdatedAt,
		Pages:            gsm.snapshot.Pages,
		Findings:         gsm.snapshot.Findings,
		TierCounts:       make(map[string]int64, len(gsm.snapshot.TierCounts)),
		ErrorsByKind:     make(map[string]int64, len(gsm.snapshot.ErrorsByKind)),
		DomainsCompleted: domains,
	}

	for k, v := range gsm.snapshot.TierCounts {
		snapshot.TierCounts[k] = v
	}
	for k, v := range gsm.snapshot.ErrorsByKind {
		snapshot.ErrorsByKind[k] = v
	}

	data, err := json.MarshalIndent(snapshot, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal global stats: %w", err)
	}

	tmpPath := gsm.output + ".tmp"
	f, err := os.Create(tmpPath)
	if err != nil {
		return fmt.Errorf("create global stats tmp: %w", err)
	}

	if _, err := f.Write(data); err != nil {
		f.Close()
		os.Remove(tmpPath)
		return fmt.Errorf("write global stats tmp: %w", err)
	}
	if err := f.Sync(); err != nil {
		f.Close()
		os.Remove(tmpPath)
		return fmt.Errorf("sync global stats tmp: %w", err)
	}
	if err := f.Close(); err != nil {
		os.Remove(tmpPath)
		return fmt.Errorf("close global stats tmp: %w", err)
	}

	if err := os.Rename(tmpPath, gsm.output); err != nil {
		return fmt.Errorf("rename global stats: %w", err)
	}

	return nil
}

func (gsm *GlobalStatsManager) Close() error {
	if !atomic.CompareAndSwapInt32(&gsm.closed, 0, 1) {
		return nil
	}

	if gsm.ticker != nil {
		gsm.ticker.Stop()
	}
	close(gsm.stop)

	return gsm.Flush()
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

func extractLinks(doc *HTMLNode, baseURL *url.URL, domain string) ([]string, error) {
	if doc == nil {
		return nil, errors.New("nil document")
	}

	seen := make(map[string]bool)
	var links []string

	var walk func(*HTMLNode)
	walk = func(n *HTMLNode) {
		if n.Type == HTMLElementNode && n.Data == "a" {
			for _, attr := range n.Attr {
				if strings.ToLower(attr.Key) == "href" {
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

func extractCanonicalURL(doc *HTMLNode, baseURL *url.URL, domain string) string {
	if doc == nil {
		return ""
	}

	var canonical string
	var walk func(*HTMLNode)
	walk = func(n *HTMLNode) {
		if canonical != "" {
			return
		}
		if n.Type == HTMLElementNode && n.Data == "link" {
			var rel, href string
			for _, attr := range n.Attr {
				switch strings.ToLower(attr.Key) {
				case "rel":
					rel = strings.ToLower(attr.Val)
				case "href":
					href = attr.Val
				}
			}
			if strings.Contains(rel, "canonical") && href != "" {
				if normalized, err := normalizeURL(href, baseURL); err == nil {
					if isSameDomain(normalized, domain) {
						canonical = normalized
						return
					}
				}
			}
		}

		for c := n.FirstChild; c != nil; c = c.NextSibling {
			walk(c)
			if canonical != "" {
				return
			}
		}
	}

	walk(doc)
	return canonical
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
	doc, err := parseHTML(bytes.NewReader(body))
	if err == nil {
		var findCharset func(*HTMLNode) string
		findCharset = func(n *HTMLNode) string {
			if n.Type == HTMLElementNode && n.Data == "meta" {
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

	switch charsetName {
	case "", "utf-8", "utf8":
		return body, nil
	case "iso-8859-1", "latin1":
		return []byte(string(decodeSingleByte(body, latin1Table))), nil
	case "windows-1252", "cp1252":
		return []byte(string(decodeSingleByte(body, windows1252Table))), nil
	case "windows-1251", "cp1251":
		return []byte(string(decodeSingleByte(body, windows1251Table))), nil
	case "koi8-r":
		return []byte(string(decodeSingleByte(body, koi8rTable))), nil
	default:
		return body, nil
	}
}

func decodeSingleByte(data []byte, table [256]rune) []rune {
	if len(data) == 0 {
		return nil
	}

	result := make([]rune, len(data))
	for i, b := range data {
		r := table[int(b)]
		if r == 0xfffe || r == 0x0000 {
			r = '?'
		}
		result[i] = r
	}
	return result
}

var latin1Table = func() [256]rune {
	var table [256]rune
	for i := 0; i < len(table); i++ {
		table[i] = rune(i)
	}
	return table
}()

var windows1252Table = func() [256]rune {
	table := latin1Table
	overrides := map[int]rune{
		0x80: 0x20ac,
		0x81: 0xfffe,
		0x82: 0x201a,
		0x83: 0x0192,
		0x84: 0x201e,
		0x85: 0x2026,
		0x86: 0x2020,
		0x87: 0x2021,
		0x88: 0x02c6,
		0x89: 0x2030,
		0x8a: 0x0160,
		0x8b: 0x2039,
		0x8c: 0x0152,
		0x8d: 0xfffe,
		0x8e: 0x017d,
		0x8f: 0xfffe,
		0x90: 0xfffe,
		0x91: 0x2018,
		0x92: 0x2019,
		0x93: 0x201c,
		0x94: 0x201d,
		0x95: 0x2022,
		0x96: 0x2013,
		0x97: 0x2014,
		0x98: 0x02dc,
		0x99: 0x2122,
		0x9a: 0x0161,
		0x9b: 0x203a,
		0x9c: 0x0153,
		0x9d: 0xfffe,
		0x9e: 0x017e,
		0x9f: 0x0178,
	}
	for idx, r := range overrides {
		table[idx] = r
	}
	return table
}()

var windows1251Table = func() [256]rune {
	var table [256]rune
	for i := 0; i < 128; i++ {
		table[i] = rune(i)
	}
	mapping := [...]rune{
		0x0402, 0x0403, 0x201a, 0x0453, 0x201e, 0x2026, 0x2020, 0x2021,
		0x20ac, 0x2030, 0x0409, 0x2039, 0x040a, 0x040c, 0x040b, 0x040f,
		0x0452, 0x2018, 0x2019, 0x201c, 0x201d, 0x2022, 0x2013, 0x2014,
		0xfffe, 0x2122, 0x0459, 0x203a, 0x045a, 0x045c, 0x045b, 0x045f,
		0x00a0, 0x040e, 0x045e, 0x0408, 0x00a4, 0x0490, 0x00a6, 0x00a7,
		0x0401, 0x00a9, 0x0404, 0x00ab, 0x00ac, 0x00ad, 0x00ae, 0x0407,
		0x00b0, 0x00b1, 0x0406, 0x0456, 0x0491, 0x00b5, 0x00b6, 0x00b7,
		0x0451, 0x2116, 0x0454, 0x00bb, 0x0458, 0x0405, 0x0455, 0x0457,
		0x0410, 0x0411, 0x0412, 0x0413, 0x0414, 0x0415, 0x0416, 0x0417,
		0x0418, 0x0419, 0x041a, 0x041b, 0x041c, 0x041d, 0x041e, 0x041f,
		0x0420, 0x0421, 0x0422, 0x0423, 0x0424, 0x0425, 0x0426, 0x0427,
		0x0428, 0x0429, 0x042a, 0x042b, 0x042c, 0x042d, 0x042e, 0x042f,
		0x0430, 0x0431, 0x0432, 0x0433, 0x0434, 0x0435, 0x0436, 0x0437,
		0x0438, 0x0439, 0x043a, 0x043b, 0x043c, 0x043d, 0x043e, 0x043f,
		0x0440, 0x0441, 0x0442, 0x0443, 0x0444, 0x0445, 0x0446, 0x0447,
		0x0448, 0x0449, 0x044a, 0x044b, 0x044c, 0x044d, 0x044e, 0x044f,
	}
	for i, r := range mapping {
		table[0x80+i] = r
	}
	return table
}()

var koi8rTable = func() [256]rune {
	var table [256]rune
	for i := 0; i < 128; i++ {
		table[i] = rune(i)
	}
	mapping := [...]rune{
		0x2500, 0x2502, 0x250c, 0x2510, 0x2514, 0x2518, 0x251c, 0x2524,
		0x252c, 0x2534, 0x253c, 0x2580, 0x2584, 0x2588, 0x258c, 0x2590,
		0x2591, 0x2592, 0x2593, 0x2320, 0x25a0, 0x2219, 0x221a, 0x2248,
		0x2264, 0x2265, 0x00a0, 0x2321, 0x00b0, 0x00b2, 0x00b7, 0x00f7,
		0x2550, 0x2551, 0x2552, 0x0451, 0x2553, 0x2554, 0x2555, 0x2556,
		0x2557, 0x2558, 0x2559, 0x255a, 0x255b, 0x255c, 0x255d, 0x255e,
		0x255f, 0x2560, 0x2561, 0x0401, 0x2562, 0x2563, 0x2564, 0x2565,
		0x2566, 0x2567, 0x2568, 0x2569, 0x256a, 0x256b, 0x256c, 0x00a9,
		0x044e, 0x0430, 0x0431, 0x0446, 0x0434, 0x0435, 0x0444, 0x0433,
		0x0445, 0x0438, 0x0439, 0x043a, 0x043b, 0x043c, 0x043d, 0x043e,
		0x043f, 0x044f, 0x0440, 0x0441, 0x0442, 0x0443, 0x0436, 0x0432,
		0x044c, 0x044b, 0x0437, 0x0448, 0x044d, 0x0449, 0x0447, 0x044a,
		0x042e, 0x0410, 0x0411, 0x0426, 0x0414, 0x0415, 0x0424, 0x0413,
		0x0425, 0x0418, 0x0419, 0x041a, 0x041b, 0x041c, 0x041d, 0x041e,
		0x041f, 0x042f, 0x0420, 0x0421, 0x0422, 0x0423, 0x0416, 0x0412,
		0x042c, 0x042b, 0x0417, 0x0428, 0x042d, 0x0429, 0x0427, 0x042a,
	}
	for i, r := range mapping {
		table[0x80+i] = r
	}
	return table
}()

// ============================================================================
// HTTP CLIENT & FETCHING
// ============================================================================

var ErrRedirectLoop = errors.New("redirect loop detected")

type HTTPStatusError struct {
	StatusCode int
	URL        string
}

func (e *HTTPStatusError) Error() string {
	return fmt.Sprintf("http status %d", e.StatusCode)
}

type redirectContextKey struct{}

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

	checkRedirect := func(req *http.Request, via []*http.Request) error {
		if len(via) >= config.MaxRedirects {
			return fmt.Errorf("too many redirects")
		}
		if config.EnableRedirectLoop {
			if chainPtr, ok := req.Context().Value(redirectContextKey{}).(*[]string); ok && chainPtr != nil {
				current := req.URL.String()
				for _, prev := range *chainPtr {
					if prev == current {
						return ErrRedirectLoop
					}
				}
				*chainPtr = append(*chainPtr, current)
			}
		}
		return nil
	}

	client := &http.Client{
		Transport:     transport,
		Timeout:       config.HTTPTimeout,
		CheckRedirect: checkRedirect,
	}

	return &HTTPClient{
		client: client,
		config: config,
		logger: logger,
	}
}

func (hc *HTTPClient) Fetch(ctx context.Context, urlStr string) ([]byte, *PageMetadata, error) {
	if ctx == nil {
		ctx = context.Background()
	}

	attempts := 1
	if hc.config.EnableRetry && hc.config.MaxRetries > attempts {
		attempts = hc.config.MaxRetries
	}

	var lastErr error
	var lastMeta *PageMetadata

	for attempt := 1; attempt <= attempts; attempt++ {
		chain := []string{urlStr}
		attemptCtx := context.WithValue(ctx, redirectContextKey{}, &chain)

		start := time.Now()
		body, metadata, err := hc.fetchOnce(attemptCtx, urlStr, &chain)
		elapsed := time.Since(start)

		fields := map[string]interface{}{
			"url":        urlStr,
			"attempt":    fmt.Sprintf("%d/%d", attempt, attempts),
			"elapsed_ms": elapsed.Milliseconds(),
		}
		if metadata != nil {
			if metadata.StatusCode != 0 {
				fields["status"] = metadata.StatusCode
			}
			if len(metadata.RedirectChain) > 0 {
				fields["redirects"] = len(metadata.RedirectChain)
			}
		}

		if err != nil {
			fields["error"] = err.Error()
			hc.logger.Trace("http_fetch", fields)
			lastErr = err
			lastMeta = metadata
			if !hc.shouldRetry(err, metadata) || attempt == attempts {
				return nil, metadata, err
			}

			backoff := hc.backoffDuration(attempt)
			select {
			case <-ctx.Done():
				return nil, metadata, ctx.Err()
			case <-time.After(backoff):
			}
			continue
		}

		hc.logger.Trace("http_fetch", fields)
		return body, metadata, nil
	}

	return nil, lastMeta, lastErr
}

func (hc *HTTPClient) fetchOnce(ctx context.Context, urlStr string, chain *[]string) ([]byte, *PageMetadata, error) {
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
		return nil, nil, err
	}
	defer resp.Body.Close()

	metadata := &PageMetadata{
		URL:           resp.Request.URL.String(),
		StatusCode:    resp.StatusCode,
		ContentType:   resp.Header.Get("Content-Type"),
		ContentLength: resp.ContentLength,
		LastModified:  resp.Header.Get("Last-Modified"),
	}

	if chain != nil {
		metadata.RedirectChain = append([]string(nil), *chain...)
	}

	if resp.StatusCode < 200 || resp.StatusCode >= 400 {
		return nil, metadata, &HTTPStatusError{StatusCode: resp.StatusCode, URL: metadata.URL}
	}

	limitedReader := io.LimitReader(resp.Body, hc.config.MaxBodySize)

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

	if closer != nil {
		defer closer.Close()
	}

	body, err := io.ReadAll(reader)
	if err != nil {
		if len(body) > 0 {
			hc.logger.Warn("partial read", map[string]interface{}{
				"url":   metadata.URL,
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

	charset := detectCharset(metadata.ContentType, body)
	metadata.Charset = charset

	utf8Body, err := convertToUTF8(body, charset)
	if err != nil {
		hc.logger.Warn("encoding conversion failed", map[string]interface{}{
			"url":     metadata.URL,
			"charset": charset,
			"error":   err.Error(),
		})
		utf8Body = body
	}

	return utf8Body, metadata, nil
}

func (hc *HTTPClient) shouldRetry(err error, metadata *PageMetadata) bool {
	if !hc.config.EnableRetry {
		return false
	}

	if err == nil {
		return false
	}

	if errors.Is(err, ErrRedirectLoop) {
		return false
	}

	if errors.Is(err, context.Canceled) {
		return false
	}

	if errors.Is(err, context.DeadlineExceeded) {
		return true
	}

	var statusErr *HTTPStatusError
	if errors.As(err, &statusErr) {
		if statusErr.StatusCode == 429 || (statusErr.StatusCode >= 500 && statusErr.StatusCode < 600) {
			return true
		}
	}

	var urlErr *url.Error
	if errors.As(err, &urlErr) {
		if urlErr.Timeout() {
			return true
		}
	}

	var netErr net.Error
	if errors.As(err, &netErr) {
		if netErr.Timeout() || netErr.Temporary() {
			return true
		}
	}

	var dnsErr *net.DNSError
	if errors.As(err, &dnsErr) {
		return true
	}

	if metadata != nil {
		if metadata.StatusCode == 429 || (metadata.StatusCode >= 500 && metadata.StatusCode < 600) {
			return true
		}
	}

	return false
}

func (hc *HTTPClient) backoffDuration(attempt int) time.Duration {
	if attempt < 1 {
		attempt = 1
	}
	base := hc.config.RetryBaseBackoff
	if base <= 0 {
		base = 500 * time.Millisecond
	}
	multiplier := time.Duration(1 << uint(attempt-1))
	jitter := time.Duration(randomFloat64() * float64(base))
	return multiplier*base + jitter
}

func classifyErrorKind(err error) string {
	if err == nil {
		return ""
	}

	if errors.Is(err, context.Canceled) {
		return "canceled"
	}

	if errors.Is(err, context.DeadlineExceeded) {
		return "timeout"
	}

	var statusErr *HTTPStatusError
	if errors.As(err, &statusErr) {
		switch {
		case statusErr.StatusCode == 429:
			return "http_429"
		case statusErr.StatusCode >= 500 && statusErr.StatusCode < 600:
			return "http_5xx"
		case statusErr.StatusCode >= 400 && statusErr.StatusCode < 500:
			return "http_4xx"
		}
	}

	var dnsErr *net.DNSError
	if errors.As(err, &dnsErr) {
		return "dns_error"
	}

	var urlErr *url.Error
	if errors.As(err, &urlErr) {
		if urlErr.Timeout() {
			return "timeout"
		}
	}

	var netErr net.Error
	if errors.As(err, &netErr) {
		if netErr.Timeout() {
			return "timeout"
		}
	}

	if errors.Is(err, ErrRedirectLoop) {
		return "redirect_loop"
	}

	return "network_error"
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

type tierCacheEntry struct {
	Confidence float64
	Tier       int
	Expiry     time.Time
}

type TierClassifier struct {
	mu                 sync.Mutex
	window             float64
	ttl                time.Duration
	capacity           int
	enableHysteresis   bool
	enableLastModified bool
	entries            map[string]tierCacheEntry
	order              []string
}

func NewTierClassifier(config *Config) *TierClassifier {
	tc := &TierClassifier{
		window:             config.TierHysteresisWindow,
		ttl:                config.TierHysteresisTTL,
		capacity:           config.TierHysteresisCache,
		enableHysteresis:   config.EnableTierHysteresis,
		enableLastModified: config.EnableLastModifiedBonus,
		entries:            make(map[string]tierCacheEntry),
	}
	return tc
}

func (tc *TierClassifier) Classify(url string, baseConfidence float64, metadata *PageMetadata) (int, float64) {
	confidence := baseConfidence
	if confidence < 0 {
		confidence = 0
	}
	if confidence > 1 {
		confidence = 1
	}

	if tc.enableLastModified && metadata != nil {
		if lm, err := http.ParseTime(metadata.LastModified); err == nil {
			age := time.Since(lm)
			if age >= 0 && age <= 90*24*time.Hour {
				freshness := 1 - age.Hours()/(90*24)
				if freshness < 0 {
					freshness = 0
				}
				bonus := 0.05 + 0.05*freshness
				if bonus > 0.1 {
					bonus = 0.1
				}
				confidence = math.Min(1, confidence+bonus)
			}
		}
	}

	tier := tierFromConfidence(confidence)

	if !tc.enableHysteresis || url == "" {
		tc.store(url, tier, confidence)
		return tier, confidence
	}

	tc.mu.Lock()
	defer tc.mu.Unlock()

	now := time.Now()
	if entry, ok := tc.entries[url]; ok && now.Before(entry.Expiry) {
		if entry.Tier != tier {
			if math.Abs(confidence-entry.Confidence) <= tc.window {
				tier = entry.Tier
				confidence = entry.Confidence
			}
		}
	}

	tc.entries[url] = tierCacheEntry{Confidence: confidence, Tier: tier, Expiry: now.Add(tc.ttl)}
	tc.order = append(tc.order, url)
	if len(tc.order) > tc.capacity {
		oldest := tc.order[0]
		tc.order = tc.order[1:]
		delete(tc.entries, oldest)
	}

	return tier, confidence
}

func (tc *TierClassifier) store(url string, tier int, confidence float64) {
	if url == "" || !tc.enableHysteresis {
		return
	}
	tc.mu.Lock()
	defer tc.mu.Unlock()
	now := time.Now()
	tc.entries[url] = tierCacheEntry{Confidence: confidence, Tier: tier, Expiry: now.Add(tc.ttl)}
	tc.order = append(tc.order, url)
	if len(tc.order) > tc.capacity {
		oldest := tc.order[0]
		tc.order = tc.order[1:]
		delete(tc.entries, oldest)
	}
}

func detectComments(doc *HTMLNode, htmlLower string, metadata *PageMetadata) (*Finding, bool) {
	if doc == nil {
		return nil, false
	}

	var signals []Signal
	confidence := 0.0

	// Проверка систем комментирования
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

func detectCommentForm(n *HTMLNode) (bool, []Signal) {
	var signals []Signal
	hasTextarea := false
	hasCommentField := false
	hasSubmit := false

	var walk func(*HTMLNode)
	walk = func(node *HTMLNode) {
		if node.Type == HTMLElementNode {
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

func detectCommentStructure(n *HTMLNode) (bool, []Signal) {
	var signals []Signal
	commentNodes := 0
	authorNodes := 0
	dateNodes := 0

	var walk func(*HTMLNode)
	walk = func(node *HTMLNode) {
		if node.Type == HTMLElementNode {
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

func detectSchemaMarkup(n *HTMLNode) (bool, []Signal) {
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

func extractTitle(n *HTMLNode) string {
	var title string

	var walk func(*HTMLNode)
	walk = func(node *HTMLNode) {
		if node.Type == HTMLElementNode && node.Data == "title" {
			if node.FirstChild != nil && node.FirstChild.Type == HTMLTextNode {
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

func renderNode(n *HTMLNode) string {
	return renderHTML(n)
}

// ============================================================================
// TIER CLASSIFICATION
// ============================================================================

func tierFromConfidence(confidence float64) int {
	switch {
	case confidence >= 0.85:
		return 1
	case confidence >= 0.70:
		return 2
	case confidence >= 0.50:
		return 3
	default:
		return 4
	}
}

func tierLabel(tier int) string {
	switch tier {
	case 1:
		return "абсолютная"
	case 2:
		return "вроде как можно разместить"
	case 3:
		return "сомнительно, стоит проверить"
	default:
		return "нетипичный формат, может подойти"
	}
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
	domain         string
	config         *Config
	httpClient     *HTTPClient
	resultWriter   *ResultWriter
	visited        *VisitedStore
	ramQueue       *PriorityQueue
	diskQueue      *DiskQueue
	prioritizer    *LinkPrioritizer
	checkpoint     *CheckpointManager
	logger         *Logger
	stats          *GlobalStatsManager
	tierClassifier *TierClassifier
	rateLimiter    *RateLimiter
	robots         *RobotsAgent

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
	stats *GlobalStatsManager,
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

	var rateLimiter *RateLimiter
	if config.EnableRateLimit {
		rateLimiter = NewRateLimiter(config.RateLimitRPS)
	}

	var robots *RobotsAgent
	if strings.ToLower(config.RobotsPolicy) != "off" {
		robots = NewRobotsAgent(domain, config.RobotsPolicy, httpClient, logger)
	}

	dc := &DomainCrawler{
		domain:         domain,
		config:         config,
		httpClient:     httpClient,
		resultWriter:   resultWriter,
		visited:        NewVisitedStore(),
		ramQueue:       NewPriorityQueue(),
		diskQueue:      diskQueue,
		prioritizer:    NewLinkPrioritizer(),
		checkpoint:     checkpoint,
		logger:         logger,
		stats:          stats,
		tierClassifier: NewTierClassifier(config),
		rateLimiter:    rateLimiter,
		robots:         robots,
		ctx:            ctx,
		cancel:         cancel,
		lastActivity:   time.Now(),
	}

	visitedPath := filepath.Join(config.CheckpointDir, sanitizeDomainName(domain)+"_visited.jsonl")
	threshold := 0
	if config.EnableVisitedSnapshot {
		threshold = config.VisitedSnapshotThreshold
	}
	dc.visited.ConfigureSnapshot(visitedPath, threshold)

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
		if dc.stats != nil {
			dc.stats.RecordError("checkpoint_save")
		}
		return err
	}

	// Сохранение visited
	visitedPath := filepath.Join(dc.config.CheckpointDir, sanitizeDomainName(dc.domain)+"_visited.jsonl")
	if err := dc.visited.Save(visitedPath); err != nil {
		if dc.stats != nil {
			dc.stats.RecordError("visited_save")
		}
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
			if dc.stats != nil {
				dc.stats.RecordError("disk_queue_push")
			}
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
		if dc.stats != nil {
			dc.stats.RecordError("disk_queue_pop")
		}
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

	if dc.robots != nil {
		allowed, rule := dc.robots.Check(dc.ctx, item.URL)
		if !allowed {
			dc.logger.Info("blocked by robots", map[string]interface{}{
				"domain": dc.domain,
				"url":    item.URL,
				"rule":   rule,
			})
			if dc.stats != nil {
				dc.stats.RecordError("robots_blocked")
			}
			return
		}
		if rule != "" {
			dc.logger.Trace("robots restriction", map[string]interface{}{
				"domain": dc.domain,
				"url":    item.URL,
				"rule":   rule,
			})
		}
	}

	if dc.rateLimiter != nil {
		if err := dc.rateLimiter.Wait(dc.ctx); err != nil {
			dc.logger.Trace("rate limiter wait failed", map[string]interface{}{
				"domain": dc.domain,
				"url":    item.URL,
				"error":  err.Error(),
			})
			return
		}
	}

	// Контекст с таймаутом для запроса
	ctx, cancel := context.WithTimeout(dc.ctx, dc.config.HTTPTimeout)
	defer cancel()

	// Загрузка страницы
	body, metadata, err := dc.httpClient.Fetch(ctx, item.URL)
	if err != nil {
		atomic.AddInt64(&dc.errors, 1)
		if dc.stats != nil {
			dc.stats.RecordError(classifyErrorKind(err))
		}
		dc.logger.Trace("fetch failed", map[string]interface{}{
			"domain": dc.domain,
			"url":    item.URL,
			"error":  err.Error(),
		})
		return
	}

	atomic.AddInt64(&dc.pages, 1)
	if dc.stats != nil {
		dc.stats.RecordPage(dc.domain)
	}
	dc.updateActivity()

	baseURL, _ := url.Parse(metadata.URL)
	doc, parseErr := parseHTML(bytes.NewReader(body))
	if parseErr != nil {
		atomic.AddInt64(&dc.errors, 1)
		if dc.stats != nil {
			dc.stats.RecordError("parse_html")
		}
		dc.logger.Warn("parse html failed", map[string]interface{}{
			"domain": dc.domain,
			"url":    metadata.URL,
			"error":  parseErr.Error(),
		})
		return
	}

	if dc.config.EnableCanonicalDedup {
		if canonical := extractCanonicalURL(doc, baseURL, dc.domain); canonical != "" && canonical != metadata.URL {
			dc.logger.Trace("canonical detected", map[string]interface{}{
				"domain":    dc.domain,
				"url":       metadata.URL,
				"canonical": canonical,
			})
			dc.visited.LoadOrStore(canonical)
			metadata.URL = canonical
			baseURL, _ = url.Parse(canonical)
		}
	}

	htmlLower := strings.ToLower(string(body))

	links, err := extractLinks(doc, baseURL, dc.domain)
	if err != nil {
		dc.logger.Trace("extract links failed", map[string]interface{}{
			"domain": dc.domain,
			"url":    metadata.URL,
			"error":  err.Error(),
		})
		if dc.stats != nil {
			dc.stats.RecordError("extract_links")
		}
	} else {
		dc.enqueueLinks(links, item.Depth+1)
	}

	// Детекция комментариев
	finding, detected := detectComments(doc, htmlLower, metadata)
	if detected {
		finding.Domain = dc.domain
		if dc.tierClassifier != nil {
			tier, confidence := dc.tierClassifier.Classify(finding.URL, finding.Confidence, metadata)
			finding.Confidence = confidence
			finding.Tier = tier
			finding.TierLabel = tierLabel(tier)
		} else {
			tier := tierFromConfidence(finding.Confidence)
			finding.Tier = tier
			finding.TierLabel = tierLabel(tier)
		}

		// Запись результата
		if err := dc.resultWriter.WriteFinding(*finding); err != nil {
			dc.logger.Warn("failed to write finding", map[string]interface{}{
				"domain": dc.domain,
				"url":    item.URL,
				"error":  err.Error(),
			})
			if dc.stats != nil {
				dc.stats.RecordError("result_writer")
			}
		} else {
			atomic.AddInt64(&dc.found, 1)
			dc.prioritizer.RecordSuccess(finding.URL)
			if dc.stats != nil {
				dc.stats.RecordFinding(dc.domain, finding.Tier)
			}

			dc.logger.Info("found comments", map[string]interface{}{
				"domain":     dc.domain,
				"url":        finding.URL,
				"tier":       finding.Tier,
				"tier_label": finding.TierLabel,
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
				if dc.stats != nil {
					dc.stats.RecordError("checkpoint_save")
				}
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
	stats        *GlobalStatsManager

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

	stats := NewGlobalStatsManager(config.GlobalStatsPath, config.GlobalStatsInterval, logger)

	ctx, cancel := context.WithCancel(context.Background())

	maxDomains := config.MaxConcurrentDomains()

	mc := &MainCrawler{
		config:           config,
		domains:          domains,
		httpClient:       httpClient,
		resultWriter:     resultWriter,
		checkpoint:       checkpoint,
		logger:           logger,
		stats:            stats,
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
	if err := mc.stats.Flush(); err != nil {
		mc.logger.Warn("final stats flush failed", map[string]interface{}{"error": err.Error()})
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
		mc.stats,
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
	mc.stats.MarkDomainCompleted(domain)
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

	if err := mc.stats.Close(); err != nil {
		mc.logger.Warn("failed to close stats", map[string]interface{}{"error": err.Error()})
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
	RateLimit        bool
	RateLimitRPS     float64
	RespectRobots    bool
	StatsInterval    time.Duration
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
	flag.BoolVar(&flags.RateLimit, "rate-limit", false, "enable per-domain rate limiting")
	flag.Float64Var(&flags.RateLimitRPS, "rate-limit-rps", 3.0, "requests per second when rate limit is enabled")
	flag.BoolVar(&flags.RespectRobots, "respect-robots", false, "respect robots.txt disallow rules")
	flag.DurationVar(&flags.StatsInterval, "stats-interval", 15*time.Second, "global stats flush interval")

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
	config.EnableRateLimit = flags.RateLimit
	config.RateLimitRPS = flags.RateLimitRPS
	config.GlobalStatsInterval = flags.StatsInterval
	if flags.RespectRobots {
		config.RobotsPolicy = "respect"
	} else {
		config.RobotsPolicy = "log"
	}

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
