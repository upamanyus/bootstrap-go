// Package spec implements the surface language for pre- and postconditions:
// separation-logic assertions written in Iris notation (with ASCII
// alternatives), plus their lowering to checker assertions.
package spec

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

type tokKind int

const (
	tEOF tokKind = iota
	tIdent
	tNum
	tSym
)

type token struct {
	kind tokKind
	text string // canonical text for tSym, source text for tIdent, digits for tNum
	num  uint64 // tNum
	pos  int    // rune offset in the source
}

func (t token) String() string {
	switch t.kind {
	case tEOF:
		return "end of input"
	case tNum:
		return t.text
	default:
		return strconv.Quote(t.text)
	}
}

// canon maps every accepted spelling of a symbol to its canonical spelling.
// The canonical spelling is what the parser matches on.
var canon = map[string]string{
	"∨":   "∨",
	`\/`:  "∨",
	"∗":   "∗",
	"*":   "∗",
	"⌜":   "⌜",
	"[":   "⌜",
	"⌝":   "⌝",
	"]":   "⌝",
	"∃":   "∃",
	"↦":   "↦",
	"|->": "↦",
	"(":   "(",
	")":   ")",
	",":   ",",
	":":   ":",
	"||":  "||",
	"&&":  "&&",
	"==":  "==",
	"!=":  "!=",
	"≠":   "!=",
	"<=u": "<=u",
	"<=s": "<=s",
	">=u": ">=u",
	">=s": ">=s",
	"<u":  "<u",
	"<s":  "<s",
	">u":  ">u",
	">s":  ">s",
	"<=":  "<=",
	"≤":   "<=",
	"≤u":  "<=u",
	"≤s":  "<=s",
	">=":  ">=",
	"≥":   ">=",
	"≥u":  ">=u",
	"≥s":  ">=s",
	"<":   "<",
	">":   ">",
	"+":   "+",
	"-":   "-",
	"!":   "!",
	"¬":   "!",
}

// symbols holds the keys of canon sorted so that longer spellings are tried
// first (so that "<=u" wins over "<=" and "<").
var symbols []string

func init() {
	for s := range canon {
		symbols = append(symbols, s)
	}
	sort.Slice(symbols, func(i, j int) bool {
		if len(symbols[i]) != len(symbols[j]) {
			return len(symbols[i]) > len(symbols[j])
		}
		return symbols[i] < symbols[j]
	})
}

func identRune(r rune, first bool) bool {
	if r == '_' || r == '$' || unicode.IsLetter(r) {
		return true
	}
	return !first && unicode.IsDigit(r)
}

// lex tokenizes src.
func lex(src string) ([]token, error) {
	var toks []token
	i := 0    // byte offset
	rpos := 0 // rune offset
	for i < len(src) {
		r, w := utf8.DecodeRuneInString(src[i:])
		if unicode.IsSpace(r) {
			i += w
			rpos++
			continue
		}
		if unicode.IsDigit(r) {
			j := i
			for j < len(src) {
				r2, w2 := utf8.DecodeRuneInString(src[j:])
				if !unicode.IsDigit(r2) {
					break
				}
				j += w2
			}
			text := src[i:j]
			n, err := strconv.ParseUint(text, 10, 64)
			if err != nil {
				return nil, fmt.Errorf("at offset %d: %s does not fit in 64 bits", rpos, text)
			}
			toks = append(toks, token{kind: tNum, text: text, num: n, pos: rpos})
			rpos += utf8.RuneCountInString(text)
			i = j
			continue
		}
		if identRune(r, true) {
			j := i
			for j < len(src) {
				r2, w2 := utf8.DecodeRuneInString(src[j:])
				if !identRune(r2, false) {
					break
				}
				j += w2
			}
			text := src[i:j]
			n := utf8.RuneCountInString(text)
			if text == "exists" {
				toks = append(toks, token{kind: tSym, text: "∃", pos: rpos})
			} else {
				toks = append(toks, token{kind: tIdent, text: text, pos: rpos})
			}
			rpos += n
			i = j
			continue
		}
		matched := false
		for _, s := range symbols {
			if strings.HasPrefix(src[i:], s) {
				toks = append(toks, token{kind: tSym, text: canon[s], pos: rpos})
				rpos += utf8.RuneCountInString(s)
				i += len(s)
				matched = true
				break
			}
		}
		if !matched {
			return nil, fmt.Errorf("at offset %d: unexpected character %q", rpos, r)
		}
	}
	toks = append(toks, token{kind: tEOF, pos: rpos})
	return toks, nil
}
