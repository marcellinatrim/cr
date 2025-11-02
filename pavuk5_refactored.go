package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"regexp"
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
	"golang.org/x/time/rate"
)

// ============================================================================
// CONFIGURATION
// ============================================================================

type Config struct {
	WorkersPerDomain   int           `json:"workers_per_domain"`
	MaxTotalWorkers    int           `json:"max_total_workers"`
	MaxPagesPerDomain  int           `json:"max_pages_per_domain"`
	RequestTimeout     time.Duration `json:"request_timeout"`
	DomainTimeout      time.Duration `json:"domain_timeout"`
	RatePerDomain      float64       `json:"rate_per_domain"`
	OutputFile         string        `json:"output_file"`
	CheckpointFile     string        `json:"checkpoint_file"`
	CheckpointInterval time.Duration `json:"checkpoint_interval"`
	RetryAttempts      int           `json:"retry_attempts"`
	UserAgents         []string      `json:"user_agents"`
}

func DefaultConfig() *Config {
	return &Config{
		WorkersPerDomain:   3,
		MaxTotalWorkers:    300,
		MaxPagesPerDomain:  1000,
		RequestTimeout:     90 * time.Second,
		DomainTimeout:      30 * time.Minute,
		RatePerDomain:      3.0,
		OutputFile:         "comments_found.jsonl",
		CheckpointFile:     "checkpoint.json",
		CheckpointInterval: 60 * time.Second,
		RetryAttempts:      3,
		UserAgents: []string{
			"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
			"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
			"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
		},
	}
}

// ============================================================================
// CORE TYPES
// ============================================================================

type Finding struct {
	Domain         string    `json:"domain"`
	URL            string    `json:"url"`
	Method         string    `json:"method"`
	System         string    `json:"system"`
	Confidence     float64   `json:"confidence"`
	Tier           int       `json:"tier"`
	HasTextarea    bool      `json:"has_textarea"`
	TextareaCount  int       `json:"textarea_count"`
	Signals        []string  `json:"signals"`
	Timestamp      time.Time `json:"timestamp"`
	PageContext    float64   `json:"page_context"`    // NEW: контекст страницы
	URLWeight      float64   `json:"url_weight"`       // NEW: вес URL
	FormSemantics  float64   `json:"form_semantics"`   // NEW: семантика формы
}

type DomainCrawler struct {
	domain      string
	config      *Config
	client      *http.Client
	rateLimiter *rate.Limiter
	visited     sync.Map
	queue       chan string
	results     chan *Finding
	errors      int64
	pages       int64
	found       int64
	
	timeoutErrors   int64
	networkErrors   int64
	parseErrors     int64
	notFoundErrors  int64
	
	// Pattern tracking для адаптивного поиска
	successPatterns sync.Map  // URL паттерны где нашли комментарии
	patternCounts   sync.Map  // Счетчики успешных паттернов
	
	ctx         context.Context
	cancel      context.CancelFunc
	wg          sync.WaitGroup
}

type MainCrawler struct {
	config         *Config
	domains        []string
	domainCrawlers sync.Map
	results        chan *Finding
	checkpoint     *Checkpoint
	checkpointMu   sync.RWMutex
	outputFile     *os.File
	outputMu       sync.Mutex
	
	tier1File      *os.File
	tier2File      *os.File
	tier3File      *os.File
	tier4File      *os.File
	
	tierCounts     [5]int64
	
	startTime      time.Time
	domainsTotal   int64
	domainsActive  int64
	domainsDone    int64
	domainsWithComments int64
	pagesTotal     int64
	findingsTotal  int64
	errorsTotal    int64
	
	errorTypes     sync.Map
	
	ctx    context.Context
	cancel context.CancelFunc
	wg     sync.WaitGroup
}

type Checkpoint struct {
	ProcessedDomains map[string]bool   `json:"processed_domains"`
	Statistics       map[string]int64  `json:"statistics"`
	Timestamp        time.Time         `json:"timestamp"`
}

// ============================================================================
// NEW: ENHANCED CONTEXT ANALYSIS
// ============================================================================

// analyzeURLContext - анализирует URL для определения вероятности наличия комментариев
func analyzeURLContext(urlStr string) (contextType string, weight float64) {
	urlLower := strings.ToLower(urlStr)
	
	// Паттерны с весами
	patterns := []struct {
		pattern string
		weight  float64
		isRegex bool
	}{
		// Высокая вероятность комментариев
		{"/blog/", 0.4, false},
		{"/post/", 0.4, false},
		{"/article/", 0.35, false},
		{"/news/", 0.3, false},
		{`/\d{4}/\d{2}/`, 0.35, true}, // даты в URL
		{"/entry/", 0.3, false},
		{"/story/", 0.3, false},
		
		// Средняя вероятность
		{"/review", 0.2, false},
		{"/product/", 0.15, false},
		{"/topic/", 0.2, false},
		{"/discussion/", 0.3, false},
		
		// Низкая вероятность (но не исключаем)
		{"/contact", -0.3, false},
		{"/about", -0.2, false},
		{"/search", -0.4, false},
		{"/category/", -0.15, false},
		{"/tag/", -0.15, false},
		{"/archive/", -0.1, false},
		
		// Системные страницы
		{"/login", -0.5, false},
		{"/register", -0.5, false},
		{"/admin", -0.6, false},
		{"/privacy", -0.4, false},
		{"/terms", -0.4, false},
		{"/subscribe", -0.35, false},
		{"/unsubscribe", -0.5, false},
		{"/checkout", -0.6, false},
		{"/cart", -0.6, false},
		{"/support", -0.3, false},
		{"/help", -0.3, false},
		{"/faq", -0.3, false},
	}
	
	totalWeight := 0.0
	matchCount := 0
	
	for _, p := range patterns {
		matched := false
		if p.isRegex {
			if match, _ := regexp.MatchString(p.pattern, urlLower); match {
				matched = true
			}
		} else {
			if strings.Contains(urlLower, p.pattern) {
				matched = true
			}
		}
		
		if matched {
			totalWeight += p.weight
			matchCount++
		}
	}
	
	// Веса накапливаются без нормализации для сохранения силы множественных сигналов
	
	// Определяем тип контекста
	if totalWeight > 0.2 {
		contextType = "content"
	} else if totalWeight < -0.2 {
		contextType = "system"
	} else {
		contextType = "neutral"
	}
	
	return contextType, totalWeight
}

// analyzePageStructure - анализирует структуру страницы для поиска паттернов комментариев
func analyzePageStructure(doc *goquery.Document) float64 {
	score := 0.0
	
	// Паттерн 1: Последовательность однотипных блоков (возможно комментарии)
	repeatingBlocks := findRepeatingStructures(doc)
	if repeatingBlocks > 5 {
		score += 0.25
	} else if repeatingBlocks > 3 {
		score += 0.15
	}
	
	// Паттерн 2: Временные метки рядом с текстовыми блоками
	timestampCount := 0
	doc.Find("time, .date, .timestamp, [datetime], .posted, .published").Each(func(i int, s *goquery.Selection) {
		// Проверяем наличие текстового контента рядом
		parent := s.Parent()
		if parent.Find("p, .text, .content, .message, .body").Length() > 0 {
			timestampCount++
		}
	})
	
	if timestampCount > 3 {
		score += 0.3
	} else if timestampCount > 1 {
		score += 0.15
	}
	
	// Паттерн 3: Вложенность структур (threading)
	nestedStructures := doc.Find(".reply, .children, .nested, .thread, .indent, [style*='margin-left'], .level-2, .depth-2")
	if nestedStructures.Length() > 2 {
		score += 0.35 // Сильный сигнал
	} else if nestedStructures.Length() > 0 {
		score += 0.2
	}
	
	// Паттерн 4: Наличие аватаров/имён пользователей
	userIndicators := doc.Find(".avatar, .user, .author, .commenter, .username, .profile-pic, img[alt*='avatar']")
	if userIndicators.Length() > 3 {
		score += 0.2
	}
	
	// Паттерн 5: Счётчики комментариев
	counterPatterns := []string{
		"comments", "комментари", "отзыв", "обсужден",
		"responses", "replies", "discussion",
	}
	
	doc.Find("span, div, a").Each(func(i int, s *goquery.Selection) {
		text := strings.ToLower(s.Text())
		for _, pattern := range counterPatterns {
			if strings.Contains(text, pattern) && regexp.MustCompile(`\d+`).MatchString(text) {
				score += 0.15
				return
			}
		}
	})
	
	// Паттерн 6: Кнопки ответа/цитирования
	replyButtons := doc.Find("button, a").FilterFunction(func(i int, s *goquery.Selection) bool {
		text := strings.ToLower(s.Text())
		return strings.Contains(text, "reply") || 
		       strings.Contains(text, "ответить") ||
		       strings.Contains(text, "quote") ||
		       strings.Contains(text, "цитировать")
	})
	
	if replyButtons.Length() > 2 {
		score += 0.25
	}
	
	return math.Min(score, 1.0) // Ограничиваем максимум
}

// findRepeatingStructures - находит повторяющиеся структуры на странице
func findRepeatingStructures(doc *goquery.Document) int {
	classCount := make(map[string]int)
	
	// Ищем div, article, section с классами
	doc.Find("div[class], article[class], section[class], li[class]").Each(func(i int, s *goquery.Selection) {
		class, exists := s.Attr("class")
		if !exists || class == "" {
			return
		}
		
		// Игнорируем обёртки и контейнеры
		classLower := strings.ToLower(class)
		if strings.Contains(classLower, "wrapper") || 
		   strings.Contains(classLower, "container") ||
		   strings.Contains(classLower, "row") ||
		   strings.Contains(classLower, "col-") {
			return
		}
		
		// Считаем только значимые классы
		classes := strings.Fields(class)
		for _, c := range classes {
			if len(c) > 3 { // Игнорируем короткие классы
				classCount[c]++
			}
		}
	})
	
	// Находим максимальное количество повторений
	maxRepeat := 0
	for _, count := range classCount {
		if count > maxRepeat {
			maxRepeat = count
		}
	}
	
	return maxRepeat
}

// analyzeFormSemantics - семантический анализ формы в контексте страницы
func analyzeFormSemantics(form *goquery.Selection, pageDoc *goquery.Document) float64 {
	score := 0.0
	
	// 1. Анализ заголовка/текста ПЕРЕД формой
	prevAll := form.PrevAll()
	prevText := ""
	prevAll.Each(func(i int, s *goquery.Selection) {
		if i < 3 { // Смотрим только 3 предыдущих элемента
			prevText += " " + strings.ToLower(s.Text())
		}
	})
	
	// Позитивные индикаторы для комментариев
	commentKeywords := []string{
		"leave a comment", "add comment", "post comment",
		"share your thoughts", "join the discussion",
		"what do you think", "your opinion",
		"оставить комментарий", "добавить комментарий",
		"ваше мнение", "поделитесь мыслями",
		"write a review", "leave feedback",
	}
	
	// Негативные индикаторы (контактные формы)
	contactKeywords := []string{
		"contact us", "get in touch", "reach out",
		"send us a message", "inquiry", "support request",
		"свяжитесь с нами", "написать нам", "обратная связь",
		"задать вопрос", "техподдержка",
	}
	
	for _, kw := range commentKeywords {
		if strings.Contains(prevText, kw) {
			score += 0.35
			break
		}
	}
	
	for _, kw := range contactKeywords {
		if strings.Contains(prevText, kw) {
			score -= 0.4
			break
		}
	}
	
	// 2. Анализ полей формы
	textareas := form.Find("textarea")
	inputs := form.Find("input[type!='hidden']")
	selects := form.Find("select")
	
	// Проверяем имена и placeholder у textarea
	hasGoodTextarea := false
	textareas.Each(func(i int, ta *goquery.Selection) {
		name := strings.ToLower(ta.AttrOr("name", ""))
		placeholder := strings.ToLower(ta.AttrOr("placeholder", ""))
		id := strings.ToLower(ta.AttrOr("id", ""))
		
		if strings.Contains(name, "comment") || 
		   strings.Contains(placeholder, "comment") ||
		   strings.Contains(id, "comment") {
			hasGoodTextarea = true
			score += 0.3
		} else if strings.Contains(name, "message") || 
		          strings.Contains(name, "text") ||
		          strings.Contains(name, "content") {
			score += 0.15
		} else if strings.Contains(name, "body") ||
		          strings.Contains(name, "reply") {
			score += 0.2
		}
	})
	
	// Используем hasGoodTextarea для дополнительной проверки
	if hasGoodTextarea {
		score += 0.1 // Бонус за правильное имя textarea
	}
	
	// Анализ input полей
	hasEmail := false
	hasName := false
	hasPhone := false
	hasSubject := false
	hasWebsite := false
	hasCompany := false
	
	inputs.Each(func(i int, inp *goquery.Selection) {
		inputType := strings.ToLower(inp.AttrOr("type", "text"))
		name := strings.ToLower(inp.AttrOr("name", ""))
		placeholder := strings.ToLower(inp.AttrOr("placeholder", ""))
		
		combined := name + " " + placeholder + " " + inputType
		
		if strings.Contains(combined, "email") || inputType == "email" {
			hasEmail = true
		}
		if strings.Contains(combined, "name") && !strings.Contains(combined, "username") {
			hasName = true
		}
		if strings.Contains(combined, "phone") || strings.Contains(combined, "tel") || inputType == "tel" {
			hasPhone = true
		}
		if strings.Contains(combined, "subject") || strings.Contains(combined, "title") {
			hasSubject = true
		}
		if strings.Contains(combined, "website") || strings.Contains(combined, "url") || inputType == "url" {
			hasWebsite = true
		}
		if strings.Contains(combined, "company") || strings.Contains(combined, "organization") {
			hasCompany = true
		}
	})
	
	// Паттерн комментарной формы: name + email + website (опционально) + textarea
	if hasName && hasEmail && !hasPhone && !hasSubject && !hasCompany {
		score += 0.3
		if hasWebsite {
			score += 0.1 // URL поле часто в комментариях
		}
	}
	
	// Паттерн контактной формы: phone или subject или company
	if hasPhone {
		score -= 0.4
	}
	if hasSubject {
		score -= 0.3
	}
	if hasCompany {
		score -= 0.3
	}
	
	// Наличие селектов часто указывает на контактную форму
	if selects.Length() > 0 {
		score -= 0.2
	}
	
	// 3. Проверка кнопки отправки
	submitBtn := form.Find("button[type='submit'], input[type='submit'], button:not([type='button'])")
	submitText := strings.ToLower(submitBtn.Text() + " " + submitBtn.AttrOr("value", ""))
	
	if strings.Contains(submitText, "post comment") ||
	   strings.Contains(submitText, "add comment") ||
	   strings.Contains(submitText, "submit comment") ||
	   strings.Contains(submitText, "отправить комментарий") {
		score += 0.25
	} else if strings.Contains(submitText, "send") ||
	          strings.Contains(submitText, "submit") ||
	          strings.Contains(submitText, "отправить") {
		// Нейтральная кнопка
		score += 0.05
	}
	
	// 4. Позиция формы на странице
	formParent := form.Parent()
	
	// Проверяем, находится ли форма внутри статьи
	if formParent.Closest("article, .article, .post, .entry, .content, main").Length() > 0 {
		score += WEIGHT_MEDIUM
	}
	
	// Проверяем наличие заголовка комментариев перед формой
	// Ищем в пределах того же родителя
	headings := formParent.Find("h2, h3, h4, .section-title")
	headings.Each(func(i int, h *goquery.Selection) {
		text := strings.ToLower(h.Text())
		if strings.Contains(text, "comment") || 
		   strings.Contains(text, "discussion") ||
		   strings.Contains(text, "leave") ||
		   strings.Contains(text, "reply") {
			score += WEIGHT_MEDIUM
			return // прерываем цикл
		}
	})
	
	// Проверяем есть ли комментарии рядом с формой
	if formParent.Find(".comment, .comments-list, .discussion").Length() > 0 {
		score += WEIGHT_STRONG
	}
	
	return math.Min(math.Max(score, -1.0), 1.0) // Ограничиваем диапазон [-1, 1]
}

// categorizeSignals - категоризирует сигналы на сильные, слабые и негативные
func categorizeSignals(signals []string) (strong, weak, negative int) {
	for _, sig := range signals {
		sigLower := strings.ToLower(sig)
		
		// Сильные позитивные сигналы
		if strings.Contains(sigLower, "existing_comments") ||
		   strings.Contains(sigLower, "button_post_comment") ||
		   strings.Contains(sigLower, "textarea_comment") ||
		   strings.Contains(sigLower, "comment_section") ||
		   strings.Contains(sigLower, "reply_button") ||
		   strings.Contains(sigLower, "thread_structure") ||
		   strings.Contains(sigLower, "modern_system") ||
		   strings.Contains(sigLower, "schema_org") ||
		   strings.Contains(sigLower, "wordpress_comments") {
			strong++
		} else if strings.Contains(sigLower, "in_article") ||
		          strings.Contains(sigLower, "simple_form") ||
		          strings.Contains(sigLower, "has_author") ||
		          strings.Contains(sigLower, "timestamp") ||
		          strings.Contains(sigLower, "content_url") {
			weak++
		} else if strings.Contains(sigLower, "has_phone") ||
		          strings.Contains(sigLower, "has_subject") ||
		          strings.Contains(sigLower, "contact") ||
		          strings.Contains(sigLower, "complex_form") ||
		          strings.Contains(sigLower, "has_company") {
			negative++
		}
	}
	
	return strong, weak, negative
}

// Константы для категорий весов
const (
	WEIGHT_STRONG = 0.3
	WEIGHT_MEDIUM = 0.15
	WEIGHT_WEAK   = 0.05
	WEIGHT_NEGATIVE = -0.3
)

// ============================================================================
// ENHANCED TIER CLASSIFICATION
// ============================================================================

func classifyFindingTierV2(finding *Finding, doc *goquery.Document) int {
	// Анализируем URL контекст (уже должен быть заполнен)
	urlScore := finding.URLWeight
	
	// Анализируем структуру страницы (уже должен быть заполнен)
	pageScore := finding.PageContext
	
	// Анализируем семантику формы (уже должен быть заполнен)
	formScore := finding.FormSemantics
	
	// Доверие к методу детектирования
	methodTrust := 0.0
	switch finding.Method {
	case "modern_system":
		methodTrust = 0.9
	case "native_form":
		methodTrust = 0.5
	case "dynamic_system":
		methodTrust = 0.7
	case "placeholder":
		methodTrust = 0.3
	}
	
	// Анализ сигналов
	strongCount, weakCount, negCount := categorizeSignals(finding.Signals)
	signalScore := float64(strongCount)*0.4 + float64(weakCount)*0.15 - float64(negCount)*0.5
	
	// Взвешенная сумма факторов
	weights := map[string]float64{
		"url":     0.15,
		"page":    0.25,
		"form":    0.20,
		"method":  0.25,
		"signals": 0.15,
	}
	
	totalScore := urlScore*weights["url"] +
	              pageScore*weights["page"] +
	              formScore*weights["form"] +
	              methodTrust*weights["method"] +
	              signalScore*weights["signals"]
	
	// Дополнительная проверка confidence
	totalScore = (totalScore + finding.Confidence) / 2
	
	// Классификация по общему баллу
	if totalScore >= 0.75 {
		return 1 // Определённо комментарии
	} else if totalScore >= 0.50 {
		return 2 // Вероятно комментарии
	} else if totalScore >= 0.25 {
		return 3 // Возможно комментарии
	}
	
	return 4 // Сомнительно
}

// ============================================================================
// DOMAIN CRAWLER - Enhanced version
// ============================================================================

func NewDomainCrawler(domain string, config *Config, results chan *Finding) *DomainCrawler {
	ctx, cancel := context.WithTimeout(context.Background(), config.DomainTimeout)
	
	transport := &http.Transport{
		MaxIdleConns:        10,
		MaxIdleConnsPerHost: config.WorkersPerDomain,
		IdleConnTimeout:     90 * time.Second,
		DisableCompression:  false,
		TLSClientConfig:     &tls.Config{InsecureSkipVerify: true},
		DialContext: (&net.Dialer{
			Timeout:   30 * time.Second,
			KeepAlive: 60 * time.Second,
		}).DialContext,
	}
	
	client := &http.Client{
		Transport: transport,
		Timeout:   config.RequestTimeout,
		CheckRedirect: func(req *http.Request, via []*http.Request) error {
			if len(via) >= 5 {
				return fmt.Errorf("too many redirects")
			}
			return nil
		},
	}
	
	return &DomainCrawler{
		domain:      domain,
		config:      config,
		client:      client,
		rateLimiter: rate.NewLimiter(rate.Limit(config.RatePerDomain), int(config.RatePerDomain)),
		queue:       make(chan string, 10000),
		results:     results,
		ctx:         ctx,
		cancel:      cancel,
	}
}

func (dc *DomainCrawler) Start() {
	for i := 0; i < dc.config.WorkersPerDomain; i++ {
		dc.wg.Add(1)
		go dc.worker(i)
	}
	
	dc.seedInitialURLs()
	
	dc.wg.Add(1)
	go dc.monitor()
}

func (dc *DomainCrawler) seedInitialURLs() {
	mainURL := "https://" + dc.domain
	
	doc, finalURL, err := dc.fetchAndParse(mainURL)
	if err != nil {
		mainURL = "http://" + dc.domain
		doc, finalURL, err = dc.fetchAndParse(mainURL)
		if err != nil {
			log.Printf("[%s] Main page failed, trying sitemap", dc.domain)
			dc.processSitemap()
			
			if len(dc.queue) == 0 {
				log.Printf("[%s] No accessible pages found", dc.domain)
				dc.cancel()
				return
			}
			return
		}
	}
	
	dc.visited.Store(finalURL, true)
	atomic.AddInt64(&dc.pages, 1)
	
	dc.detectComments(doc, finalURL)
	
	links := dc.extractLinks(doc, finalURL)
	prioritized := dc.prioritizeLinks(links)
	for _, link := range prioritized {
		select {
		case dc.queue <- link:
		default:
		}
	}
	
	dc.processSitemap()
}

func (dc *DomainCrawler) worker(id int) {
	defer dc.wg.Done()
	
	defer func() {
		if r := recover(); r != nil {
			log.Printf("[%s] Worker %d recovered from panic: %v", dc.domain, id, r)
			dc.wg.Add(1)
			go dc.worker(id)
		}
	}()
	
	for {
		select {
		case <-dc.ctx.Done():
			return
			
		case url := <-dc.queue:
			if url == "" {
				continue
			}
			
			if _, visited := dc.visited.LoadOrStore(url, true); visited {
				continue
			}
			
			if atomic.LoadInt64(&dc.pages) >= int64(dc.config.MaxPagesPerDomain) {
				continue
			}
			
			dc.rateLimiter.Wait(dc.ctx)
			dc.processURL(url)
			
			pages := atomic.LoadInt64(&dc.pages)
			found := atomic.LoadInt64(&dc.found)
			
			if found >= 50 {
				log.Printf("[%s] Found enough comments (%d pages), stopping", dc.domain, found)
				dc.cancel()
				return
			}
			
			if pages >= int64(dc.config.MaxPagesPerDomain) {
				log.Printf("[%s] Reached page limit (%d), found %d comments", dc.domain, pages, found)
				dc.cancel()
				return
			}
		}
	}
}

func (dc *DomainCrawler) processURL(url string) {
	atomic.AddInt64(&dc.pages, 1)
	
	doc, finalURL, err := dc.fetchAndParse(url)
	if err != nil {
		atomic.AddInt64(&dc.errors, 1)
		errStr := err.Error()
		
		// Детальное логирование ошибок
		if strings.Contains(errStr, "timeout") {
			atomic.AddInt64(&dc.timeoutErrors, 1)
			log.Printf("[%s] Timeout error on %s: %v", dc.domain, url, err)
		} else if strings.Contains(errStr, "status 404") {
			atomic.AddInt64(&dc.notFoundErrors, 1)
			// 404 не логируем, это нормально
		} else if strings.Contains(errStr, "connection refused") {
			atomic.AddInt64(&dc.networkErrors, 1)
			log.Printf("[%s] Network error: %v", dc.domain, err)
		} else if strings.Contains(errStr, "status 403") || strings.Contains(errStr, "status 401") {
			log.Printf("[%s] Access denied on %s: %v", dc.domain, url, err)
		} else {
			atomic.AddInt64(&dc.parseErrors, 1)
			log.Printf("[%s] Parse error on %s: %v", dc.domain, url, err)
		}
		return
	}
	
	// Получаем лучшую находку
	finding := dc.detectComments(doc, finalURL)
	
	if finding != nil {
		// Классифицируем с новой системой
		tier := classifyFindingTierV2(finding, doc)
		finding.Tier = tier
		
		// Фильтруем только совсем мусорные
		if finding.Confidence < 0.1 {
			log.Printf("[%s] Skipping very low confidence (%.2f) on %s", dc.domain, finding.Confidence, url)
			return
		}
		
		// Для tier 4 с очень низкой confidence - логируем и пропускаем
		if tier == 4 && finding.Confidence < 0.3 {
			log.Printf("[%s] Skipping tier 4 with low confidence (%.2f) on %s", dc.domain, finding.Confidence, url)
			return
		}
		
		dc.results <- finding
		atomic.AddInt64(&dc.found, 1)
		
		// НОВОЕ: Обучаемся на успешной находке
		if tier <= 2 && finding.Confidence >= 0.7 {
			dc.learnFromSuccess(finalURL)
		}
		
		// Логируем находки по уровням
		switch tier {
		case 1:
			log.Printf("[%s] TIER 1 found: %s (system: %s, confidence: %.2f)", 
				dc.domain, finalURL, finding.System, finding.Confidence)
		case 2:
			log.Printf("[%s] Tier 2 found: %s (confidence: %.2f)", 
				dc.domain, finalURL, finding.Confidence)
		}
	}
	
	// Продолжаем обход для стратегии "умри, но найди"
	if atomic.LoadInt64(&dc.pages) < int64(dc.config.MaxPagesPerDomain) {
		links := dc.extractLinks(doc, finalURL)
		
		// Используем улучшенную приоритизацию с извлечением дат из HTML
		prioritized := dc.prioritizeLinksByFreshnessEnhanced(links, doc)
		
		for _, link := range prioritized {
			if _, visited := dc.visited.Load(link); !visited {
				select {
				case dc.queue <- link:
				default:
				}
			}
		}
	}
}

func (dc *DomainCrawler) fetchAndParse(url string) (*goquery.Document, string, error) {
	var lastErr error
	
	for attempt := 1; attempt <= dc.config.RetryAttempts; attempt++ {
		req, err := http.NewRequestWithContext(dc.ctx, "GET", url, nil)
		if err != nil {
			return nil, "", err
		}
		
		ua := dc.config.UserAgents[rand.Intn(len(dc.config.UserAgents))]
		req.Header.Set("User-Agent", ua)
		req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
		req.Header.Set("Accept-Language", "en-US,en;q=0.9,ru;q=0.8")
		
		resp, err := dc.client.Do(req)
		if err != nil {
			lastErr = err
			if strings.Contains(err.Error(), "timeout") && attempt < dc.config.RetryAttempts {
				time.Sleep(time.Second * time.Duration(attempt*2))
				continue
			}
			return nil, "", err
		}
		defer resp.Body.Close()
		
		if resp.StatusCode >= 400 {
			return nil, "", fmt.Errorf("status %d", resp.StatusCode)
		}
		
		reader, err := charset.NewReader(resp.Body, resp.Header.Get("Content-Type"))
		if err != nil {
			reader = resp.Body
		}
		
		body, err := io.ReadAll(io.LimitReader(reader, 10*1024*1024))
		if err != nil {
			lastErr = err
			if attempt < dc.config.RetryAttempts {
				time.Sleep(time.Second * time.Duration(attempt))
				continue
			}
			return nil, "", err
		}
		
		doc, err := goquery.NewDocumentFromReader(bytes.NewReader(body))
		if err != nil {
			return nil, "", err
		}
		
		return doc, resp.Request.URL.String(), nil
	}
	
	return nil, "", lastErr
}

// detectStructuredData - обнаруживает комментарии через Schema.org и JSON-LD
func (dc *DomainCrawler) detectStructuredData(doc *goquery.Document, url string) *Finding {
	score := 0.0
	signals := []string{}
	
	// 1. Проверяем Schema.org микроразметку
	schemaComments := doc.Find("[itemtype*='schema.org/Comment'], [itemtype*='schema.org/UserComments']")
	if schemaComments.Length() > 0 {
		score += 0.9
		signals = append(signals, "schema_org_comment")
	}
	
	// 2. Проверяем JSON-LD структуры
	doc.Find("script[type='application/ld+json']").Each(func(i int, s *goquery.Selection) {
		jsonText := s.Text()
		if strings.Contains(jsonText, "\"@type\":\"Comment\"") ||
		   strings.Contains(jsonText, "\"@type\":\"UserComments\"") ||
		   strings.Contains(jsonText, "\"@type\":\"DiscussionForumPosting\"") ||
		   strings.Contains(jsonText, "\"comment\":") ||
		   strings.Contains(jsonText, "\"commentCount\":") {
			score += 0.85
			signals = append(signals, "json_ld_comment")
		}
		
		// Проверяем тип статьи
		if strings.Contains(jsonText, "\"@type\":\"Article\"") ||
		   strings.Contains(jsonText, "\"@type\":\"BlogPosting\"") ||
		   strings.Contains(jsonText, "\"@type\":\"NewsArticle\"") {
			score += 0.3
			signals = append(signals, "article_context")
		}
	})
	
	// 3. Open Graph метатеги
	doc.Find("meta[property^='og:']").Each(func(i int, s *goquery.Selection) {
		prop, _ := s.Attr("property")
		content, _ := s.Attr("content")
		
		if prop == "og:type" {
			if strings.Contains(content, "article") || 
			   strings.Contains(content, "blog") ||
			   strings.Contains(content, "website") {
				score += 0.2
				signals = append(signals, "og_type_article")
			}
		}
	})
	
	// 4. Микроформаты
	if doc.Find(".h-entry, .h-card, .e-content, .p-comment").Length() > 0 {
		score += 0.3
		signals = append(signals, "microformats")
	}
	
	// 5. WordPress/CMS классы
	wpIndicators := []string{
		".wp-comment", ".wp-comment-author", 
		"#wp-comment-cookies-consent",
		".comment-metadata", ".comment-awaiting-moderation",
		".comment-edit-link", ".comment-reply-link",
		".comments-area", ".comment-list",
		".commentlist", ".comment-navigation",
	}
	
	wpScore := 0.0
	for _, indicator := range wpIndicators {
		if doc.Find(indicator).Length() > 0 {
			wpScore += 0.15
			if wpScore == 0.15 { // Добавляем сигнал только один раз
				signals = append(signals, "wordpress_comments")
			}
		}
	}
	score += math.Min(wpScore, 0.6) // Максимум 0.6 от WordPress
	
	// 6. Drupal индикаторы
	drupalIndicators := []string{
		".comment-wrapper", ".comment-permalink",
		".comment-submitted", ".comment-user-",
		"#comments", ".indented",
	}
	
	drupalScore := 0.0
	for _, indicator := range drupalIndicators {
		if doc.Find(indicator).Length() > 0 {
			drupalScore += 0.1
			if drupalScore == 0.1 {
				signals = append(signals, "drupal_comments")
			}
		}
	}
	score += math.Min(drupalScore, 0.4)
	
	// 7. Проверяем data-атрибуты
	doc.Find("[data-comment], [data-comments], [data-comment-id], [data-comment-count]").Each(func(i int, s *goquery.Selection) {
		score += 0.1
		if i == 0 {
			signals = append(signals, "data_attributes")
		}
	})
	
	if score > 0.5 {
		return &Finding{
			Domain:     dc.domain,
			URL:        url,
			Method:     "structured_data",
			System:     "schema_org",
			Confidence: math.Min(score, 1.0),
			Signals:    signals,
			Timestamp:  time.Now(),
		}
	}
	
	return nil
}

// ENHANCED detectComments with structured data
func (dc *DomainCrawler) detectComments(doc *goquery.Document, url string) *Finding {
	var bestFinding *Finding
	maxConfidence := 0.0
	
	// Предварительный анализ контекста страницы
	pageContext := analyzePageStructure(doc)
	_, urlWeight := analyzeURLContext(url)
	
	// 1. Check modern comment systems (highest priority)
	if finding := dc.detectModernSystems(doc, url); finding != nil {
		finding.PageContext = pageContext
		finding.URLWeight = urlWeight
		if finding.Confidence > maxConfidence {
			bestFinding = finding
			maxConfidence = finding.Confidence
		}
	}
	
	// 2. Check structured data - только если не нашли modern system с высокой confidence
	if maxConfidence < 0.9 {
		if finding := dc.detectStructuredData(doc, url); finding != nil {
			finding.PageContext = pageContext
			finding.URLWeight = urlWeight
			if finding.Confidence > maxConfidence {
				bestFinding = finding
				maxConfidence = finding.Confidence
			}
		}
	}
	
	// 3. Check native forms - только если не нашли надежную систему
	if maxConfidence < 0.8 {
		if finding := dc.detectNativeFormsEnhanced(doc, url, pageContext, urlWeight); finding != nil {
			if finding.Confidence > maxConfidence {
				bestFinding = finding
				maxConfidence = finding.Confidence
			}
		}
	}
	
	// 4. Check AJAX/dynamic systems
	if maxConfidence < 0.7 {
		if finding := dc.detectDynamicSystems(doc, url); finding != nil {
			finding.PageContext = pageContext
			finding.URLWeight = urlWeight
			if finding.Confidence > maxConfidence {
				bestFinding = finding
				maxConfidence = finding.Confidence
			}
		}
	}
	
	// 5. Check placeholders - только как последний вариант
	if maxConfidence < 0.5 && (pageContext > 0.2 || urlWeight > 0.1) {
		if finding := dc.detectPlaceholdersEnhanced(doc, url, pageContext); finding != nil {
			finding.URLWeight = urlWeight
			if finding.Confidence > maxConfidence {
				bestFinding = finding
				maxConfidence = finding.Confidence
			}
		}
	}
	
	return bestFinding
}

func (dc *DomainCrawler) detectModernSystems(doc *goquery.Document, url string) *Finding {
	systems := map[string][]string{
		// Популярные системы
		"disqus": {
			"#disqus_thread", ".disqus", "disqus.com/embed",
			"disqus_config", "dsq-", "disqus-comment",
		},
		"facebook": {
			".fb-comments", "#fb-root", "facebook.com/plugins/comments",
			"fb:comments", "class=\"fb-comments\"",
		},
		"vk": {
			"#vk_comments", ".vk_comments", "VK.Widgets.Comments",
			"vk.com/widget_comments", "vk_comments",
		},
		"wordpress": {
			"#commentform", "#respond", ".comment-respond",
			"comment-reply-link", "wp-comment", "wp-comment-",
			"wordpress-comment", "#comments-title",
		},
		
		// Новые и self-hosted системы
		"commento": {
			"#commento", ".commento", "commento.io",
			"commento-root", "data-commento",
		},
		"utterances": {
			".utterances", "utterances-frame", "utteranc.es",
		},
		"giscus": {
			".giscus", "giscus-frame", "giscus.app",
		},
		"remark42": {
			"#remark42", ".remark42", "remark42__root",
		},
		"hyvor": {
			"hyvor-talk", "talk.hyvor.com", "hyvor-talk-comments",
		},
		"cusdis": {
			"#cusdis_thread", ".cusdis", "cusdis.com",
			"data-host=\"cusdis", "cusdis-root",
		},
		"waline": {
			"#waline", ".waline", "waline-comment",
			"waline.js", "@waline/client",
		},
		"twikoo": {
			"#twikoo", ".twikoo", "twikoo-container",
			"twikoo.js", "twikoo-comment",
		},
		"artalk": {
			"#artalk", ".artalk", "artalk-comment",
			"artalk.js", "artalk-container",
		},
		"isso": {
			"#isso-thread", ".isso-comment", "data-isso",
			"isso-postbox", "embed.min.js",
		},
		"schnack": {
			".schnack-comments", "#schnack-comments",
			"schnack.js", "data-schnack",
		},
		
		// Региональные системы
		"livere": {
			"#lv-container", ".livere", "livere.com",
			"livere-comment", "city.livere.com",
		},
		"hypercomments": {
			"#hypercomments_widget", "hypercomments.com",
			".hc-comment", "hypercomments_mix",
		},
		"yandex": {
			"ya-comments", "yandex.ru/comments",
			"yandex-comments-widget",
		},
		
		// CMS-специфичные
		"drupal": {
			"#comments", ".comment-wrapper", "drupal-comment",
			".comment-form", "#comment-form",
		},
		"joomla": {
			"#jcomments", ".jcomments", "com_jcomments",
		},
		"ghost": {
			"#ghost-comments", ".ghost-comments", "data-ghost-comment",
		},
		
		// React/Vue компоненты (по паттернам)
		"react_comments": {
			"data-reactroot", "__react-comment", "react-comment-",
			"CommentSection", "CommentBox", "CommentList",
		},
		"vue_comments": {
			"v-comment", "vue-comment", "comment-component",
			"data-v-", "_comment_", "__vue__",
		},
		
		// Другие
		"telegram": {
			".telegram-comments", "comments.app", "tg-comments",
		},
		"coral": {
			"coral-embed-stream", "coral-comment", "coralproject",
		},
		"cackle": {
			"#mc-container", ".cackle_widget", "cackle.me",
			"cackle-comment", "mc-comment",
		},
		"muut": {
			".muut", "#muut", "muut.com", "muut-widget",
		},
		"spot.im": {
			"spot-im", "spotim", "spot-im-frame",
			"data-spot-im", "spotim_launcher",
		},
	}
	
	html, _ := doc.Html()
	htmlLower := strings.ToLower(html)
	
	for system, patterns := range systems {
		for _, pattern := range patterns {
			if strings.Contains(htmlLower, pattern) ||
			   doc.Find(pattern).Length() > 0 {
				return &Finding{
					Domain:     dc.domain,
					URL:        url,
					Method:     "modern_system",
					System:     system,
					Confidence: 0.95,
					Signals:    []string{system + "_detected", "modern_system"},
					Timestamp:  time.Now(),
				}
			}
		}
	}
	
	return nil
}

// ENHANCED native form detection
func (dc *DomainCrawler) detectNativeFormsEnhanced(doc *goquery.Document, url string, pageContext, urlWeight float64) *Finding {
	var bestFinding *Finding
	maxScore := 0.0
	
	// Фиксированный базовый порог с бонусом за хороший контекст
	minThreshold := 0.3
	if pageContext > 0.3 || urlWeight > 0.2 {
		// Хороший контекст СНИЖАЕТ требования, а не повышает
		minThreshold = 0.25  
	}
	
	doc.Find("form").Each(func(i int, form *goquery.Selection) {
		textareas := form.Find("textarea")
		if textareas.Length() == 0 {
			return
		}
		
		// Пропускаем явные поисковые формы
		if form.Find("input[type='search']").Length() > 0 ||
		   form.Find("input[name='q']").Length() > 0 ||
		   form.Find("input[name='s']").Length() > 0 {
			return
		}
		
		// Семантический анализ формы
		formSemantics := analyzeFormSemantics(form, doc)
		
		// Комбинированная оценка
		score := 0.0
		signals := []string{}
		
		// Базовая оценка от контекста
		score += pageContext * 0.3
		score += urlWeight * 0.2
		score += formSemantics * 0.5
		
		// УЛУЧШЕННАЯ ЭВРИСТИКА для нестандартных имён полей
		
		// Анализ textarea - расширенный список паттернов
		textareaPatterns := []struct{
			patterns []string
			weight float64
			signal string
		}{
			{[]string{"comment", "reply", "response"}, 0.35, "textarea_comment"},
			{[]string{"message", "msg", "text", "content", "body"}, 0.25, "textarea_message"},
			{[]string{"review", "feedback", "opinion"}, 0.2, "textarea_review"},
			{[]string{"post", "entry", "note"}, 0.15, "textarea_post"},
			{[]string{"description", "desc", "details"}, 0.1, "textarea_description"},
		}
		
		textareaAnalyzed := false
		textareas.Each(func(j int, ta *goquery.Selection) {
			if textareaAnalyzed {
				return
			}
			
			// Собираем все атрибуты для анализа
			name := strings.ToLower(ta.AttrOr("name", ""))
			id := strings.ToLower(ta.AttrOr("id", ""))
			placeholder := strings.ToLower(ta.AttrOr("placeholder", ""))
			className := strings.ToLower(ta.AttrOr("class", ""))
			ariaLabel := strings.ToLower(ta.AttrOr("aria-label", ""))
			
			combined := name + " " + id + " " + placeholder + " " + className + " " + ariaLabel
			
			// Проверяем паттерны
			for _, pattern := range textareaPatterns {
				for _, p := range pattern.patterns {
					if strings.Contains(combined, p) {
						score += pattern.weight
						signals = append(signals, pattern.signal)
						textareaAnalyzed = true
						break
					}
				}
				if textareaAnalyzed {
					break
				}
			}
		})
		
		// Анализ других полей формы - улучшенная эвристика
		fields := form.Find("input[type!='hidden'], select")
		fieldSignatures := make(map[string]bool)
		fieldTypes := make(map[string]int)
		
		fields.Each(func(j int, field *goquery.Selection) {
			fieldType := strings.ToLower(field.AttrOr("type", "text"))
			name := strings.ToLower(field.AttrOr("name", ""))
			placeholder := strings.ToLower(field.AttrOr("placeholder", ""))
			
			// Создаём сигнатуру поля
			combined := name + " " + placeholder
			
			// Классифицируем поля
			if fieldType == "email" || strings.Contains(combined, "email") || strings.Contains(combined, "mail") {
				fieldSignatures["email"] = true
				fieldTypes["email"]++
			}
			if strings.Contains(combined, "name") || strings.Contains(combined, "author") || 
			   strings.Contains(combined, "nick") || strings.Contains(combined, "user") {
				fieldSignatures["name"] = true
				fieldTypes["name"]++
			}
			if fieldType == "url" || strings.Contains(combined, "website") || 
			   strings.Contains(combined, "site") || strings.Contains(combined, "url") {
				fieldSignatures["website"] = true
				fieldTypes["website"]++
			}
			if fieldType == "tel" || strings.Contains(combined, "phone") || 
			   strings.Contains(combined, "tel") || strings.Contains(combined, "mobile") {
				fieldSignatures["phone"] = true
				fieldTypes["phone"]++
			}
			if strings.Contains(combined, "subject") || strings.Contains(combined, "title") ||
			   strings.Contains(combined, "topic") {
				fieldSignatures["subject"] = true
				fieldTypes["subject"]++
			}
			if strings.Contains(combined, "company") || strings.Contains(combined, "organization") ||
			   strings.Contains(combined, "business") {
				fieldSignatures["company"] = true
				fieldTypes["company"]++
			}
		})
		
		// УЛУЧШЕННАЯ ЛОГИКА: Паттерны комбинаций полей
		
		// Паттерн 1: Классический комментарий (name + email + [website])
		if fieldSignatures["name"] && fieldSignatures["email"] && !fieldSignatures["phone"] && !fieldSignatures["subject"] {
			score += 0.35
			signals = append(signals, "classic_comment_fields")
			if fieldSignatures["website"] {
				score += 0.1
				signals = append(signals, "has_website")
			}
		}
		
		// Паттерн 2: Минималистичный комментарий (только email или name)
		if (fieldSignatures["email"] || fieldSignatures["name"]) && 
		   !fieldSignatures["phone"] && !fieldSignatures["subject"] && !fieldSignatures["company"] {
			score += 0.2
			signals = append(signals, "minimal_comment_fields")
		}
		
		// Паттерн 3: Анонимный комментарий (только textarea)
		if len(fieldSignatures) == 0 && textareas.Length() == 1 {
			score += 0.15
			signals = append(signals, "anonymous_comment")
		}
		
		// Негативные паттерны (контактная форма)
		if fieldSignatures["phone"] {
			score -= 0.4
			signals = append(signals, "has_phone")
		}
		if fieldSignatures["subject"] {
			score -= 0.25
			signals = append(signals, "has_subject")
		}
		if fieldSignatures["company"] {
			score -= 0.3
			signals = append(signals, "has_company")
		}
		
		// Проверка кнопки submit - расширенный список
		submitButtons := form.Find("button[type='submit'], input[type='submit'], button:not([type='button'])")
		submitText := ""
		submitButtons.Each(func(j int, btn *goquery.Selection) {
			submitText += " " + strings.ToLower(btn.Text() + " " + btn.AttrOr("value", ""))
		})
		
		submitPatterns := []struct{
			patterns []string
			weight float64
			signal string
		}{
			{[]string{"post comment", "add comment", "submit comment", "leave comment"}, 0.3, "button_comment"},
			{[]string{"reply", "respond", "answer"}, 0.25, "button_reply"},
			{[]string{"send", "submit", "post", "publish"}, 0.1, "button_generic"},
			{[]string{"contact", "inquiry", "get in touch"}, -0.3, "button_contact"},
		}
		
		for _, pattern := range submitPatterns {
			for _, p := range pattern.patterns {
				if strings.Contains(submitText, p) {
					score += pattern.weight
					signals = append(signals, pattern.signal)
					break
				}
			}
		}
		
		// Проверка контекста формы
		if form.Closest("article, .article, .post, .entry, .content-area, #content, main").Length() > 0 {
			score += 0.15
			signals = append(signals, "in_article")
		}
		
		// Проверка на существующие комментарии поблизости
		parent := form.Parent()
		for i := 0; i < 3; i++ { // Проверяем 3 уровня вверх
			if parent.Find(".comment, #comments, .discussion, .responses").Length() > 0 {
				score += 0.2
				signals = append(signals, "existing_comments_nearby")
				break
			}
			parent = parent.Parent()
		}
		
		// Проверка сложности формы
		totalFields := fields.Length() + textareas.Length()
		if totalFields <= 4 {
			score += 0.1
			signals = append(signals, "simple_form")
		} else if totalFields > 7 {
			score -= 0.15
			signals = append(signals, "complex_form")
		}
		
		if pageContext > 0.3 {
			signals = append(signals, "good_page_context")
		}
		if urlWeight > 0.2 {
			signals = append(signals, "content_url")
		}
		if formSemantics > 0.3 {
			signals = append(signals, "comment_form_semantics")
		}
		
		// Финальная проверка
		if score > minThreshold && score > maxScore {
			maxScore = score
			bestFinding = &Finding{
				Domain:        dc.domain,
				URL:           url,
				Method:        "native_form",
				System:        "native",
				Confidence:    math.Min(score, 1.0),
				HasTextarea:   true,
				TextareaCount: textareas.Length(),
				Signals:       signals,
				Timestamp:     time.Now(),
				PageContext:   pageContext,
				URLWeight:     urlWeight,
				FormSemantics: formSemantics,
			}
		}
	})
	
	return bestFinding
}

func (dc *DomainCrawler) detectDynamicSystems(doc *goquery.Document, url string) *Finding {
	html, _ := doc.Html()
	
	ajaxPatterns := []string{
		"loadComments", "fetchComments", "getComments",
		"ajax.*comment", "comment.*ajax",
		"comments-container", "comments-wrapper",
		"data-comments", "data-discussion-url",
		"discussionUrl", "commentsEndpoint",
	}
	
	for _, pattern := range ajaxPatterns {
		re := regexp.MustCompile(`(?i)` + pattern)
		if re.MatchString(html) {
			return &Finding{
				Domain:     dc.domain,
				URL:        url,
				Method:     "dynamic_system",
				System:     "ajax",
				Confidence: 0.7,
				Signals:    []string{pattern, "ajax_loader"},
				Timestamp:  time.Now(),
			}
		}
	}
	
	return nil
}

// ENHANCED placeholder detection
func (dc *DomainCrawler) detectPlaceholdersEnhanced(doc *goquery.Document, url string, pageContext float64) *Finding {
	// Требуем минимальный контекст страницы
	if pageContext < 0.1 {
		return nil
	}
	
	text := strings.ToLower(doc.Text())
	
	// Проверяем наличие формы или места для комментариев
	hasCommentArea := doc.Find("form textarea, #comments, .comments, .discussion").Length() > 0
	if !hasCommentArea {
		return nil
	}
	
	placeholders := map[string]float64{
		"no comments yet":          0.5,
		"be the first to comment":  0.5,
		"0 comments":               0.4,
		"leave a comment":          0.4,
		"нет комментариев":         0.5,
		"комментариев пока нет":    0.5,
		"будьте первым":           0.4,
		"оставить комментарий":     0.4,
		"start the discussion":     0.5,
		"join the conversation":    0.4,
	}
	
	for placeholder, baseConfidence := range placeholders {
		if strings.Contains(text, placeholder) {
			// Корректируем confidence на основе контекста
			adjustedConfidence := baseConfidence + pageContext*0.2
			
			return &Finding{
				Domain:      dc.domain,
				URL:         url,
				Method:      "placeholder",
				System:      "placeholder",
				Confidence:  math.Min(adjustedConfidence, 0.8),
				Signals:     []string{placeholder, "has_comment_area"},
				Timestamp:   time.Now(),
				PageContext: pageContext,
			}
		}
	}
	
	return nil
}

func (dc *DomainCrawler) extractLinks(doc *goquery.Document, baseURL string) []string {
	base, _ := url.Parse(baseURL)
	links := make(map[string]bool)
	
	doc.Find("a[href]").Each(func(i int, s *goquery.Selection) {
		href, exists := s.Attr("href")
		if !exists || href == "" {
			return
		}
		
		u, err := url.Parse(href)
		if err != nil {
			return
		}
		
		absolute := base.ResolveReference(u)
		
		if absolute.Host != dc.domain && absolute.Host != "www."+dc.domain {
			return
		}
		
		absolute.Fragment = ""
		absolute.RawQuery = cleanQuery(absolute.Query())
		
		path := strings.ToLower(absolute.Path)
		skipExts := []string{
			".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".ico",
			".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
			".zip", ".rar", ".7z", ".tar", ".gz",
			".mp3", ".mp4", ".avi", ".mov", ".wmv", ".flv",
			".js", ".css", ".xml", ".json", ".txt",
			".woff", ".woff2", ".ttf", ".eot",
		}
		for _, ext := range skipExts {
			if strings.HasSuffix(path, ext) {
				return
			}
		}
		
		skipPaths := []string{
			"/wp-admin", "/admin", "/cgi-bin", "/scripts",
			"/wp-includes", "/wp-content/uploads", "/assets",
			"/.well-known", "/api/", "/feed", "/rss",
		}
		for _, skip := range skipPaths {
			if strings.Contains(path, skip) {
				return
			}
		}
		
		links[absolute.String()] = true
	})
	
	result := make([]string, 0, len(links))
	for link := range links {
		result = append(result, link)
	}
	
	return result
}

func (dc *DomainCrawler) prioritizeLinks(links []string) []string {
	type scoredLink struct {
		url   string
		score int
	}
	
	scored := make([]scoredLink, 0, len(links))
	
	for _, link := range links {
		score := 50
		lower := strings.ToLower(link)
		
		// High priority
		if strings.Contains(lower, "comment") ||
		   strings.Contains(lower, "discuss") ||
		   strings.Contains(lower, "review") ||
		   strings.Contains(lower, "forum") {
			score += 40
		}
		
		if strings.Contains(lower, "blog") ||
		   strings.Contains(lower, "article") ||
		   strings.Contains(lower, "post") ||
		   strings.Contains(lower, "news") {
			score += 30
		}
		
		if regexp.MustCompile(`/202[34]/`).MatchString(lower) {
			score += 20
		}
		
		// Low priority
		if strings.Contains(lower, "contact") ||
		   strings.Contains(lower, "about") ||
		   strings.Contains(lower, "privacy") ||
		   strings.Contains(lower, "terms") ||
		   strings.Contains(lower, "login") {
			score -= 20
		}
		
		scored = append(scored, scoredLink{url: link, score: score})
	}
	
	sort.Slice(scored, func(i, j int) bool {
		return scored[i].score > scored[j].score
	})
	
	result := make([]string, len(scored))
	for i, sl := range scored {
		result[i] = sl.url
	}
	
	return result
}

// extractDateFromPage - извлекает дату публикации со страницы
func extractDateFromPage(doc *goquery.Document) (year int, month int, confidence float64) {
	currentYear := time.Now().Year()
	year, month = 0, 0
	confidence = 0.0
	
	// 1. Проверяем meta теги (самый надежный источник)
	doc.Find("meta").Each(func(i int, s *goquery.Selection) {
		property, _ := s.Attr("property")
		name, _ := s.Attr("name")
		content, _ := s.Attr("content")
		
		// Open Graph и Schema.org даты
		if property == "article:published_time" || 
		   property == "article:modified_time" ||
		   name == "publish_date" ||
		   name == "date" {
			if t, err := time.Parse(time.RFC3339, content); err == nil {
				year = t.Year()
				month = int(t.Month())
				confidence = 0.9
				return
			}
			// Пробуем другие форматы
			if t, err := time.Parse("2006-01-02", content); err == nil {
				year = t.Year()
				month = int(t.Month())
				confidence = 0.9
				return
			}
		}
	})
	
	if confidence > 0 {
		return
	}
	
	// 2. Проверяем time элементы
	doc.Find("time[datetime]").Each(func(i int, s *goquery.Selection) {
		datetime, exists := s.Attr("datetime")
		if !exists {
			return
		}
		
		if t, err := time.Parse(time.RFC3339, datetime); err == nil {
			year = t.Year()
			month = int(t.Month())
			confidence = 0.8
			return
		}
		if t, err := time.Parse("2006-01-02", datetime); err == nil {
			year = t.Year()
			month = int(t.Month())
			confidence = 0.8
			return
		}
	})
	
	if confidence > 0 {
		return
	}
	
	// 3. Ищем даты в тексте (менее надежно)
	datePatterns := []struct {
		regex *regexp.Regexp
		conf  float64
	}{
		{regexp.MustCompile(`(\d{4})-(\d{1,2})-\d{1,2}`), 0.6},
		{regexp.MustCompile(`(\d{1,2})/(\d{1,2})/(\d{4})`), 0.5},
		{regexp.MustCompile(`(January|February|March|April|May|June|July|August|September|October|November|December)\s+\d{1,2},?\s+(\d{4})`), 0.5},
	}
	
	doc.Find(".date, .post-date, .entry-date, .published, .timestamp").Each(func(i int, s *goquery.Selection) {
		text := s.Text()
		for _, p := range datePatterns {
			if matches := p.regex.FindStringSubmatch(text); len(matches) > 0 {
				// Простая логика извлечения года
				for _, match := range matches {
					if y, err := strconv.Atoi(match); err == nil && y > 2000 && y <= currentYear {
						year = y
						confidence = p.conf
						return
					}
				}
			}
		}
	})
	
	return
}

// extractURLPattern - извлекает паттерн из URL для обучения
func extractURLPattern(urlStr string) string {
	u, err := url.Parse(urlStr)
	if err != nil {
		return ""
	}
	
	path := u.Path
	// Заменяем числа на плейсхолдеры для обобщения паттерна
	// /2024/12/article-name -> /{year}/{month}/article-name
	path = regexp.MustCompile(`/\d{4}/`).ReplaceAllString(path, "/{year}/")
	path = regexp.MustCompile(`/\d{1,2}/`).ReplaceAllString(path, "/{num}/")
	path = regexp.MustCompile(`-\d+`).ReplaceAllString(path, "-{id}")
	path = regexp.MustCompile(`/\d+$`).ReplaceAllString(path, "/{id}")
	
	return path
}

// learnFromSuccess - запоминает успешный паттерн
func (dc *DomainCrawler) learnFromSuccess(url string) {
	pattern := extractURLPattern(url)
	if pattern == "" {
		return
	}
	
	// Увеличиваем счетчик для этого паттерна
	if count, ok := dc.patternCounts.Load(pattern); ok {
		dc.patternCounts.Store(pattern, count.(int)+1)
	} else {
		dc.patternCounts.Store(pattern, 1)
	}
	
	// Запоминаем URL как успешный
	dc.successPatterns.Store(url, true)
	
	log.Printf("[%s] Learned pattern: %s (count: %d)", dc.domain, pattern, dc.getPatternCount(pattern))
}

// getPatternCount - получает счетчик для паттерна
func (dc *DomainCrawler) getPatternCount(pattern string) int {
	if count, ok := dc.patternCounts.Load(pattern); ok {
		return count.(int)
	}
	return 0
}

// scoreByPattern - оценивает URL на основе изученных паттернов
func (dc *DomainCrawler) scoreByPattern(url string) int {
	pattern := extractURLPattern(url)
	if pattern == "" {
		return 0
	}
	
	count := dc.getPatternCount(pattern)
	
	// Чем чаще находили комментарии по этому паттерну, тем выше приоритет
	switch {
	case count >= 10:
		return 100 // Очень успешный паттерн
	case count >= 5:
		return 70
	case count >= 2:
		return 40
	case count == 1:
		return 20
	default:
		return 0
	}
}

// prioritizeLinksByFreshnessEnhanced - улучшенная приоритизация с извлечением дат из контента
func (dc *DomainCrawler) prioritizeLinksByFreshnessEnhanced(links []string, currentDoc *goquery.Document) []string {
	type scoredLink struct {
		url           string
		score         int
		year          int
		month         int
		confidence    float64
		patternScore  int  // NEW: оценка на основе успешных паттернов
	}
	
	scored := make([]scoredLink, 0, len(links))
	currentYear := time.Now().Year()
	currentMonth := int(time.Now().Month())
	
	// Регулярные выражения для дат в URL
	yearMonthRegex := regexp.MustCompile(`/(\d{4})/(\d{1,2})/`)
	yearOnlyRegex := regexp.MustCompile(`/(\d{4})/`)
	
	// Если можем, извлекаем дату текущей страницы для контекста
	pageYear, _, _ := extractDateFromPage(currentDoc)
	
	// Считаем сколько успешных находок уже было
	foundCount := atomic.LoadInt64(&dc.found)
	
	for _, link := range links {
		sl := scoredLink{url: link, score: 50}
		lower := strings.ToLower(link)
		
		// НОВОЕ: Оцениваем на основе изученных паттернов
		sl.patternScore = dc.scoreByPattern(link)
		sl.score += sl.patternScore
		
		// Извлекаем дату из URL
		if matches := yearMonthRegex.FindStringSubmatch(link); len(matches) > 2 {
			sl.year, _ = strconv.Atoi(matches[1])
			sl.month, _ = strconv.Atoi(matches[2])
			sl.confidence = 0.7
		} else if matches := yearOnlyRegex.FindStringSubmatch(link); len(matches) > 1 {
			sl.year, _ = strconv.Atoi(matches[1])
			sl.confidence = 0.5
		}
		
		// Оцениваем свежесть (не исключаем старые!)
		if sl.year > 0 {
			yearDiff := currentYear - sl.year
			
			switch {
			case yearDiff == 0: // Текущий год
				sl.score += 100
				if sl.month >= currentMonth-2 {
					sl.score += 50 // Последние 2 месяца
				}
			case yearDiff == 1: // Прошлый год
				sl.score += 70
			case yearDiff <= 2: // 2 года
				sl.score += 50
			case yearDiff <= 5: // До 5 лет
				sl.score += 20
			case yearDiff <= 10: // До 10 лет
				sl.score += 5
			default: // Старше 10 лет
				sl.score += 0 // НЕ штрафуем старый контент
			}
		} else if pageYear > 0 {
			// Если не знаем дату ссылки, используем дату страницы как подсказку
			yearDiff := currentYear - pageYear
			if yearDiff <= 1 {
				sl.score += 30
			}
		}
		
		// Дополнительные индикаторы
		if strings.Contains(lower, "comment") || strings.Contains(lower, "discuss") {
			sl.score += 30
		}
		if strings.Contains(lower, "blog") || strings.Contains(lower, "article") || 
		   strings.Contains(lower, "post") || strings.Contains(lower, "news") {
			sl.score += 20
		}
		
		// После первых 20 находок снижаем штраф для агрегаторов
		// (может там тоже есть комментарии)
		penaltyReduction := 0
		if foundCount > 20 {
			penaltyReduction = 10
		}
		
		if strings.Contains(lower, "/page/") || strings.Contains(lower, "/tag/") ||
		   strings.Contains(lower, "/category/") || strings.Contains(lower, "/archive/") {
			sl.score -= (30 - penaltyReduction) // Адаптивный штраф
		}
		
		scored = append(scored, sl)
	}
	
	// Сортируем по score, потом по паттерну, потом по дате
	sort.Slice(scored, func(i, j int) bool {
		if scored[i].score != scored[j].score {
			return scored[i].score > scored[j].score
		}
		if scored[i].patternScore != scored[j].patternScore {
			return scored[i].patternScore > scored[j].patternScore
		}
		if scored[i].year != scored[j].year {
			return scored[i].year > scored[j].year
		}
		return scored[i].month > scored[j].month
	})
	
	// Логируем топ-5 для отладки (только если нашли что-то интересное)
	if len(scored) > 0 && scored[0].patternScore > 0 {
		log.Printf("[%s] Top prioritized URLs (pattern learning active):", dc.domain)
		for i := 0; i < 5 && i < len(scored); i++ {
			log.Printf("  [%d] Score:%d Pattern:%d Year:%d URL:%s", 
				i+1, scored[i].score, scored[i].patternScore, scored[i].year, scored[i].url)
		}
	}
	
	result := make([]string, len(scored))
	for i, sl := range scored {
		result[i] = sl.url
	}
	
	return result
}

func (dc *DomainCrawler) processSitemap() {
	// Пробуем несколько вариантов sitemap
	sitemapURLs := []string{
		"https://" + dc.domain + "/sitemap.xml",
		"https://" + dc.domain + "/sitemap_index.xml", 
		"https://" + dc.domain + "/sitemap1.xml",
		"https://" + dc.domain + "/post-sitemap.xml",
		"https://" + dc.domain + "/page-sitemap.xml",
		"http://" + dc.domain + "/sitemap.xml",
	}
	
	allLinks := make([]string, 0, 1000)
	
	for _, sitemapURL := range sitemapURLs {
		req, err := http.NewRequestWithContext(dc.ctx, "GET", sitemapURL, nil)
		if err != nil {
			continue
		}
		
		ua := dc.config.UserAgents[rand.Intn(len(dc.config.UserAgents))]
		req.Header.Set("User-Agent", ua)
		
		resp, err := dc.client.Do(req)
		if err != nil {
			continue
		}
		defer resp.Body.Close()
		
		if resp.StatusCode != 200 {
			continue
		}
		
		body, err := io.ReadAll(io.LimitReader(resp.Body, 5*1024*1024)) // Увеличил до 5MB
		if err != nil {
			continue
		}
		
		// Парсим sitemap
		if strings.Contains(string(body), "<sitemapindex") {
			// Это индексный файл - извлекаем вложенные sitemap
			re := regexp.MustCompile(`<loc>([^<]+)</loc>`)
			matches := re.FindAllSubmatch(body, -1)
			
			for _, match := range matches {
				if len(match) > 1 {
					nestedURL := string(match[1])
					// Рекурсивно обрабатываем вложенные sitemap
					dc.processSitemapURL(nestedURL, &allLinks)
				}
			}
		} else {
			// Обычный sitemap
			dc.extractLinksFromSitemap(body, &allLinks)
		}
		
		if len(allLinks) > 100 {
			break // Достаточно ссылок
		}
	}
	
	// Также проверяем robots.txt для поиска sitemap
	dc.processRobotsTxt(&allLinks)
	
	// Приоритизируем и добавляем в очередь
	if len(allLinks) > 0 {
		prioritized := dc.prioritizeLinks(allLinks)
		maxToAdd := 200 // Увеличил лимит
		if len(prioritized) < maxToAdd {
			maxToAdd = len(prioritized)
		}
		
		for i := 0; i < maxToAdd; i++ {
			select {
			case dc.queue <- prioritized[i]:
			default:
			}
		}
	}
}

func (dc *DomainCrawler) processSitemapURL(sitemapURL string, allLinks *[]string) {
	req, err := http.NewRequestWithContext(dc.ctx, "GET", sitemapURL, nil)
	if err != nil {
		return
	}
	
	ua := dc.config.UserAgents[rand.Intn(len(dc.config.UserAgents))]
	req.Header.Set("User-Agent", ua)
	
	resp, err := dc.client.Do(req)
	if err != nil {
		return
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != 200 {
		return
	}
	
	body, err := io.ReadAll(io.LimitReader(resp.Body, 2*1024*1024))
	if err != nil {
		return
	}
	
	dc.extractLinksFromSitemap(body, allLinks)
}

func (dc *DomainCrawler) extractLinksFromSitemap(body []byte, allLinks *[]string) {
	// Извлекаем URL с приоритетами и датами
	re := regexp.MustCompile(`<url>.*?<loc>([^<]+)</loc>.*?(?:<lastmod>([^<]+)</lastmod>)?.*?(?:<priority>([^<]+)</priority>)?.*?</url>`)
	matches := re.FindAllSubmatch(body, -1)
	
	type urlInfo struct {
		url      string
		lastmod  string
		priority float64
	}
	
	urls := make([]urlInfo, 0, len(matches))
	
	for _, match := range matches {
		if len(match) > 1 {
			info := urlInfo{
				url:      string(match[1]),
				lastmod:  "",
				priority: 0.5,
			}
			
			if len(match) > 2 && match[2] != nil {
				info.lastmod = string(match[2])
			}
			
			if len(match) > 3 && match[3] != nil {
				if p, err := strconv.ParseFloat(string(match[3]), 64); err == nil {
					info.priority = p
				}
			}
			
			urls = append(urls, info)
		}
	}
	
	// Сортируем по приоритету и дате
	sort.Slice(urls, func(i, j int) bool {
		// Сначала по приоритету
		if urls[i].priority != urls[j].priority {
			return urls[i].priority > urls[j].priority
		}
		// Потом по дате (новые первыми)
		return urls[i].lastmod > urls[j].lastmod
	})
	
	// Добавляем в список
	for _, info := range urls {
		*allLinks = append(*allLinks, info.url)
	}
}

func (dc *DomainCrawler) processRobotsTxt(allLinks *[]string) {
	robotsURL := "https://" + dc.domain + "/robots.txt"
	
	req, err := http.NewRequestWithContext(dc.ctx, "GET", robotsURL, nil)
	if err != nil {
		return
	}
	
	ua := dc.config.UserAgents[rand.Intn(len(dc.config.UserAgents))]
	req.Header.Set("User-Agent", ua)
	
	resp, err := dc.client.Do(req)
	if err != nil {
		return
	}
	defer resp.Body.Close()
	
	if resp.StatusCode != 200 {
		return
	}
	
	body, err := io.ReadAll(io.LimitReader(resp.Body, 100*1024))
	if err != nil {
		return
	}
	
	// Ищем sitemap в robots.txt
	lines := strings.Split(string(body), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(strings.ToLower(line), "sitemap:") {
			sitemapURL := strings.TrimSpace(line[8:])
			dc.processSitemapURL(sitemapURL, allLinks)
		}
	}
	
	// Также анализируем разрешённые пути
	userAgentBlock := false
	for _, line := range lines {
		line = strings.TrimSpace(strings.ToLower(line))
		
		if strings.HasPrefix(line, "user-agent:") {
			ua := strings.TrimSpace(line[11:])
			userAgentBlock = (ua == "*" || strings.Contains(ua, "bot"))
		}
		
		if userAgentBlock && strings.HasPrefix(line, "allow:") {
			path := strings.TrimSpace(line[6:])
			if path != "/" && path != "" {
				// Добавляем разрешённые пути для исследования
				fullURL := "https://" + dc.domain + path
				*allLinks = append(*allLinks, fullURL)
			}
		}
	}
}

func (dc *DomainCrawler) monitor() {
	defer dc.wg.Done()
	
	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()
	
	emptyQueueCount := 0
	
	for {
		select {
		case <-dc.ctx.Done():
			return
			
		case <-ticker.C:
			pages := atomic.LoadInt64(&dc.pages)
			found := atomic.LoadInt64(&dc.found)
			queueLen := len(dc.queue)
			
			if queueLen == 0 {
				emptyQueueCount++
				
				if emptyQueueCount >= 3 {
					if pages >= 50 || found > 0 {
						log.Printf("[%s] Completed: %d pages, %d with comments", dc.domain, pages, found)
						dc.cancel()
						return
					} else if pages > 0 {
						log.Printf("[%s] Insufficient pages (%d), stopping", dc.domain, pages)
						dc.cancel()
						return
					}
				}
			} else {
				emptyQueueCount = 0
			}
			
			if pages >= int64(dc.config.MaxPagesPerDomain) {
				log.Printf("[%s] Reached max pages limit (%d)", dc.domain, pages)
				dc.cancel()
				return
			}
		}
	}
}

func (dc *DomainCrawler) Wait() {
	dc.wg.Wait()
}

func (dc *DomainCrawler) Stats() (pages, found, errors int64) {
	return atomic.LoadInt64(&dc.pages),
	       atomic.LoadInt64(&dc.found),
	       atomic.LoadInt64(&dc.errors)
}

// ============================================================================
// MAIN CRAWLER
// ============================================================================

func NewMainCrawler(config *Config) (*MainCrawler, error) {
	ctx, cancel := context.WithCancel(context.Background())
	
	outputFile, err := os.OpenFile(config.OutputFile, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
	if err != nil {
		cancel()
		return nil, err
	}
	
	tier1File, _ := os.Create("tier1_definite_comments.txt")
	tier2File, _ := os.Create("tier2_probable_comments.txt")
	tier3File, _ := os.Create("tier3_possible_comments.txt")
	tier4File, _ := os.Create("tier4_ambiguous.txt")
	
	crawler := &MainCrawler{
		config:     config,
		results:    make(chan *Finding, 1000),
		outputFile: outputFile,
		tier1File:  tier1File,
		tier2File:  tier2File,
		tier3File:  tier3File,
		tier4File:  tier4File,
		ctx:        ctx,
		cancel:     cancel,
		startTime:  time.Now(),
	}
	
	crawler.loadCheckpoint()
	
	return crawler, nil
}

func (mc *MainCrawler) loadCheckpoint() {
	data, err := os.ReadFile(mc.config.CheckpointFile)
	if err != nil {
		mc.checkpoint = &Checkpoint{
			ProcessedDomains: make(map[string]bool),
			Statistics:       make(map[string]int64),
		}
		return
	}
	
	var cp Checkpoint
	if err := json.Unmarshal(data, &cp); err != nil {
		mc.checkpoint = &Checkpoint{
			ProcessedDomains: make(map[string]bool),
			Statistics:       make(map[string]int64),
		}
		return
	}
	
	mc.checkpoint = &cp
}

func (mc *MainCrawler) saveCheckpoint() {
	mc.checkpointMu.Lock()
	defer mc.checkpointMu.Unlock()
	
	mc.checkpoint.Timestamp = time.Now()
	mc.checkpoint.Statistics["domains_done"] = atomic.LoadInt64(&mc.domainsDone)
	mc.checkpoint.Statistics["domains_with_comments"] = atomic.LoadInt64(&mc.domainsWithComments)
	mc.checkpoint.Statistics["pages_total"] = atomic.LoadInt64(&mc.pagesTotal)
	mc.checkpoint.Statistics["pages_with_comments"] = atomic.LoadInt64(&mc.findingsTotal)
	
	data, _ := json.MarshalIndent(mc.checkpoint, "", "  ")
	os.WriteFile(mc.config.CheckpointFile, data, 0644)
}

func (mc *MainCrawler) Run(domainFile string) error {
	domains, err := mc.loadDomains(domainFile)
	if err != nil {
		return err
	}
	
	mc.domains = domains
	atomic.StoreInt64(&mc.domainsTotal, int64(len(domains)))
	
	log.Printf("Starting: %d domains | Workers: %d per domain | Timeout: %s", 
		len(domains), mc.config.WorkersPerDomain, mc.config.RequestTimeout)
	
	mc.wg.Add(1)
	go mc.processResults()
	
	mc.wg.Add(1)
	go mc.checkpointRoutine()
	
	mc.wg.Add(1)
	go mc.progressReporter()
	
	semaphore := make(chan struct{}, mc.config.MaxTotalWorkers/mc.config.WorkersPerDomain)
	
	for _, domain := range domains {
		mc.checkpointMu.RLock()
		processed := mc.checkpoint.ProcessedDomains[domain]
		mc.checkpointMu.RUnlock()
		
		if processed {
			atomic.AddInt64(&mc.domainsDone, 1)
			continue
		}
		
		semaphore <- struct{}{}
		mc.wg.Add(1)
		
		go func(d string) {
			defer mc.wg.Done()
			defer func() { <-semaphore }()
			
			mc.processDomain(d)
		}(domain)
	}
	
	mc.wg.Wait()
	
	mc.saveCheckpoint()
	mc.printFinalStats()
	
	return nil
}

func (mc *MainCrawler) processDomain(domain string) {
	atomic.AddInt64(&mc.domainsActive, 1)
	defer atomic.AddInt64(&mc.domainsActive, -1)
	defer atomic.AddInt64(&mc.domainsDone, 1)
	
	dc := NewDomainCrawler(domain, mc.config, mc.results)
	mc.domainCrawlers.Store(domain, dc)
	defer mc.domainCrawlers.Delete(domain)
	
	dc.Start()
	dc.Wait()
	
	pages, found, errors := dc.Stats()
	atomic.AddInt64(&mc.pagesTotal, pages)
	atomic.AddInt64(&mc.errorsTotal, errors)
	
	if found > 0 {
		atomic.AddInt64(&mc.findingsTotal, found)
		atomic.AddInt64(&mc.domainsWithComments, 1)
		log.Printf("[%s] Completed: %d pages, %d pages with comments", domain, pages, found)
	}
	
	mc.checkpointMu.Lock()
	mc.checkpoint.ProcessedDomains[domain] = true
	mc.checkpointMu.Unlock()
}

func (mc *MainCrawler) processResults() {
	defer mc.wg.Done()
	defer mc.tier1File.Close()
	defer mc.tier2File.Close()
	defer mc.tier3File.Close()
	defer mc.tier4File.Close()
	
	encoder := json.NewEncoder(mc.outputFile)
	uniqueURLs := make(map[string]bool)
	
	txtFile, err := os.Create("urls_with_comments.txt")
	if err == nil {
		defer txtFile.Close()
	}
	
	for {
		select {
		case finding := <-mc.results:
			if finding == nil {
				continue
			}
			
			if uniqueURLs[finding.URL] {
				continue
			}
			uniqueURLs[finding.URL] = true
			
			// Tier уже установлен в processURL
			tier := finding.Tier
			if tier < 1 || tier > 4 {
				tier = 4
			}
			
			atomic.AddInt64(&mc.tierCounts[tier], 1)
			
			line := finding.URL + "\n"
			
			switch tier {
			case 1:
				mc.tier1File.WriteString(line)
			case 2:
				mc.tier2File.WriteString(line)
			case 3:
				mc.tier3File.WriteString(line)
			case 4:
				mc.tier4File.WriteString(line)
			}
			
			if txtFile != nil && tier <= 3 {
				txtFile.WriteString(line)
			}
			
			mc.outputMu.Lock()
			encoder.Encode(finding)
			mc.outputMu.Unlock()
			
		case <-mc.ctx.Done():
			for len(mc.results) > 0 {
				finding := <-mc.results
				if finding != nil && !uniqueURLs[finding.URL] {
					uniqueURLs[finding.URL] = true
					tier := finding.Tier
					
					if tier < 1 || tier > 4 {
						tier = 4
					}
					
					atomic.AddInt64(&mc.tierCounts[tier], 1)
					
					line := finding.URL + "\n"
					switch tier {
					case 1:
						mc.tier1File.WriteString(line)
					case 2:
						mc.tier2File.WriteString(line)
					case 3:
						mc.tier3File.WriteString(line)
					case 4:
						mc.tier4File.WriteString(line)
					}
					
					if txtFile != nil && tier <= 3 {
						txtFile.WriteString(line)
					}
					
					encoder.Encode(finding)
				}
			}
			
			log.Println("\n" + strings.Repeat("=", 60))
			log.Println("TIER DISTRIBUTION:")
			log.Printf("  Tier 1 (definite):  %d URLs", atomic.LoadInt64(&mc.tierCounts[1]))
			log.Printf("  Tier 2 (probable):  %d URLs", atomic.LoadInt64(&mc.tierCounts[2]))
			log.Printf("  Tier 3 (possible):  %d URLs", atomic.LoadInt64(&mc.tierCounts[3]))
			log.Printf("  Tier 4 (ambiguous): %d URLs", atomic.LoadInt64(&mc.tierCounts[4]))
			total := atomic.LoadInt64(&mc.tierCounts[1]) + atomic.LoadInt64(&mc.tierCounts[2]) +
			        atomic.LoadInt64(&mc.tierCounts[3]) + atomic.LoadInt64(&mc.tierCounts[4])
			log.Printf("  Total classified:   %d URLs", total)
			log.Println(strings.Repeat("=", 60))
			
			return
		}
	}
}

func (mc *MainCrawler) checkpointRoutine() {
	defer mc.wg.Done()
	
	ticker := time.NewTicker(mc.config.CheckpointInterval)
	defer ticker.Stop()
	
	for {
		select {
		case <-ticker.C:
			mc.saveCheckpoint()
		case <-mc.ctx.Done():
			return
		}
	}
}

func (mc *MainCrawler) progressReporter() {
	defer mc.wg.Done()
	
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()
	
	for {
		select {
		case <-ticker.C:
			mc.printStats()
		case <-mc.ctx.Done():
			return
		}
	}
}

func (mc *MainCrawler) printStats() {
	elapsed := time.Since(mc.startTime)
	domainsTotal := atomic.LoadInt64(&mc.domainsTotal)
	domainsDone := atomic.LoadInt64(&mc.domainsDone)
	domainsActive := atomic.LoadInt64(&mc.domainsActive)
	pagesTotal := atomic.LoadInt64(&mc.pagesTotal)
	findingsTotal := atomic.LoadInt64(&mc.findingsTotal)
	errorsTotal := atomic.LoadInt64(&mc.errorsTotal)
	
	pagesPerSec := float64(pagesTotal) / elapsed.Seconds()
	domainsProgress := float64(domainsDone) * 100 / float64(domainsTotal)
	
	tier1 := atomic.LoadInt64(&mc.tierCounts[1])
	tier2 := atomic.LoadInt64(&mc.tierCounts[2])
	tierStr := ""
	if tier1 > 0 || tier2 > 0 {
		tierStr = fmt.Sprintf(" | T1:%d T2:%d", tier1, tier2)
	}
	
	log.Printf("[%.1f%%] Active: %d | Done: %d/%d | Pages: %d (%.1f/s) | Pages with comments: %d%s | Errors: %d",
		domainsProgress,
		domainsActive,
		domainsDone, domainsTotal,
		pagesTotal, pagesPerSec,
		findingsTotal,
		tierStr,
		errorsTotal,
	)
}

func (mc *MainCrawler) printFinalStats() {
	elapsed := time.Since(mc.startTime)
	domainsTotal := atomic.LoadInt64(&mc.domainsTotal)
	domainsDone := atomic.LoadInt64(&mc.domainsDone)
	pagesTotal := atomic.LoadInt64(&mc.pagesTotal)
	domainsWithComments := atomic.LoadInt64(&mc.domainsWithComments)
	pagesWithComments := atomic.LoadInt64(&mc.findingsTotal)
	errorsTotal := atomic.LoadInt64(&mc.errorsTotal)
	
	successRate := float64(domainsWithComments) * 100 / maxFloat(1, float64(domainsDone))
	
	fmt.Println("\n" + strings.Repeat("=", 60))
	fmt.Printf("FINAL RESULTS\n")
	fmt.Println(strings.Repeat("=", 60))
	fmt.Printf("Runtime: %s\n", elapsed.Truncate(time.Second))
	fmt.Printf("Domains processed: %d/%d\n", domainsDone, domainsTotal)
	fmt.Printf("Total pages crawled: %d\n", pagesTotal)
	fmt.Printf("Domains with comments: %d (%.1f%%)\n", domainsWithComments, successRate)
	fmt.Printf("Pages with comments: %d\n", pagesWithComments)
	fmt.Printf("Total errors: %d\n", errorsTotal)
	fmt.Printf("Output files:\n")
	fmt.Printf("  - %s (JSON with all data)\n", mc.config.OutputFile)
	fmt.Printf("  - tier1_definite_comments.txt\n")
	fmt.Printf("  - tier2_probable_comments.txt\n")
	fmt.Printf("  - tier3_possible_comments.txt\n")
	fmt.Printf("  - tier4_ambiguous.txt\n")
	fmt.Println(strings.Repeat("=", 60))
}

func (mc *MainCrawler) loadDomains(path string) ([]string, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()
	
	var domains []string
	scanner := bufio.NewScanner(file)
	
	for scanner.Scan() {
		domain := strings.TrimSpace(scanner.Text())
		if domain == "" || strings.HasPrefix(domain, "#") {
			continue
		}
		
		domain = strings.TrimPrefix(domain, "http://")
		domain = strings.TrimPrefix(domain, "https://")
		domain = strings.TrimPrefix(domain, "www.")
		domain = strings.TrimSuffix(domain, "/")
		
		domains = append(domains, strings.ToLower(domain))
	}
	
	return domains, scanner.Err()
}

func (mc *MainCrawler) Shutdown() {
	log.Println("Shutting down...")
	mc.cancel()
	
	mc.domainCrawlers.Range(func(key, value interface{}) bool {
		if dc, ok := value.(*DomainCrawler); ok {
			dc.cancel()
		}
		return true
	})
	
	mc.wg.Wait()
	mc.outputFile.Close()
	mc.saveCheckpoint()
	mc.printFinalStats()
}

// ============================================================================
// UTILITIES
// ============================================================================

func cleanQuery(values url.Values) string {
	tracking := []string{
		"utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
		"gclid", "fbclid", "yclid", "_ga",
	}
	
	for _, param := range tracking {
		values.Del(param)
	}
	
	return values.Encode()
}

func maxFloat(a, b float64) float64 {
	if a > b {
		return a
	}
	return b
}

// ============================================================================
// MAIN
// ============================================================================

func main() {
	runtime.GOMAXPROCS(runtime.NumCPU())
	
	var (
		domainFile = flag.String("domains", "", "Domain list file (required)")
		workers    = flag.Int("workers", 3, "Workers per domain")
		maxWorkers = flag.Int("max-workers", 300, "Maximum total workers")
		maxPages   = flag.Int("max-pages", 1000, "Max pages per domain")
		output     = flag.String("output", "comments_found.jsonl", "Output file")
		checkpoint = flag.String("checkpoint", "checkpoint.json", "Checkpoint file")
	)
	
	flag.Parse()
	
	if *domainFile == "" {
		log.Fatal("Domain file is required (-domains flag)")
	}
	
	config := DefaultConfig()
	config.WorkersPerDomain = *workers
	config.MaxTotalWorkers = *maxWorkers
	config.MaxPagesPerDomain = *maxPages
	config.OutputFile = *output
	config.CheckpointFile = *checkpoint
	
	crawler, err := NewMainCrawler(config)
	if err != nil {
		log.Fatalf("Failed to create crawler: %v", err)
	}
	
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)
	
	go func() {
		<-sigChan
		crawler.Shutdown()
		os.Exit(0)
	}()
	
	if err := crawler.Run(*domainFile); err != nil {
		log.Fatalf("Crawler failed: %v", err)
	}
}