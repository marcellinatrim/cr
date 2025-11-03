package main

import (
	"io"
	"strings"
)

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
				current.appendChild(&HTMLNode{Type: HTMLTextNode, Data: text})
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
	if len(prefix) == 0 {
		return false
	}
	if p.pos+len(prefix) > p.length {
		return false
	}
	if string(p.data[p.pos:p.pos+len(prefix)]) == prefix {
		p.pos += len(prefix)
		return true
	}
	return false
}

func (p *htmlParser) consume(expected byte) {
	if p.pos < p.length && p.data[p.pos] == expected {
		p.pos++
	}
}

func (p *htmlParser) readUntil(delim string) string {
	idx := strings.Index(string(p.data[p.pos:]), delim)
	if idx == -1 {
		result := string(p.data[p.pos:])
		p.pos = p.length
		return result
	}
	result := string(p.data[p.pos : p.pos+idx])
	p.pos += idx + len(delim)
	return result
}

func (p *htmlParser) readText() string {
	start := p.pos
	for p.pos < p.length && p.data[p.pos] != '<' {
		p.pos++
	}
	if start == p.pos {
		return ""
	}
	text := string(p.data[start:p.pos])
	if strings.TrimSpace(text) == "" {
		return ""
	}
	return text
}

func (p *htmlParser) readTagName() string {
	start := p.pos
	for p.pos < p.length {
		ch := p.data[p.pos]
		if isSpace(ch) || ch == '/' || ch == '>' {
			break
		}
		p.pos++
	}
	return string(p.data[start:p.pos])
}

func (p *htmlParser) parseStartTag() (string, []HTMLAttribute, bool) {
	if p.peek() == '<' {
		p.pos++
	}
	p.skipSpaces()
	name := p.readTagName()
	attrs := make([]HTMLAttribute, 0)
	selfClosing := false

	for {
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
			selfClosing = true
			p.pos++
			p.skipSpaces()
			p.consume('>')
			break
		}

		attrName := p.readTagName()
		if attrName == "" {
			p.pos++
			continue
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
