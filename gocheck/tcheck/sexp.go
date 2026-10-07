package main

import (
	"fmt"
	"strings"
)

// The table file is a sequence of S-expressions. Atoms are runs of
// characters other than whitespace and parentheses; a Lean term is written
// between backquotes (and may contain anything but a backquote); a string
// is written between double quotes. A semicolon starts a comment that runs
// to the end of the line.

type nodeKind int

const (
	nAtom nodeKind = iota
	nList
	nLean
	nString
)

type node struct {
	kind nodeKind
	text string // atom, Lean text, or string contents
	list []*node
	line int
}

func (n *node) String() string {
	switch n.kind {
	case nAtom:
		return n.text
	case nLean:
		return "`" + n.text + "`"
	case nString:
		return fmt.Sprintf("%q", n.text)
	}
	var parts []string
	for _, c := range n.list {
		parts = append(parts, c.String())
	}
	return "(" + strings.Join(parts, " ") + ")"
}

func (n *node) isAtom(s string) bool { return n.kind == nAtom && n.text == s }

// head returns the first atom of a list, or "".
func (n *node) head() string {
	if n.kind == nList && len(n.list) > 0 && n.list[0].kind == nAtom {
		return n.list[0].text
	}
	return ""
}

func parseSexps(src string) ([]*node, error) {
	line := 1
	i := 0
	var stack [][]*node
	var top []*node
	var lines []int
	for i < len(src) {
		c := src[i]
		switch {
		case c == '\n':
			line++
			i++
		case c == ' ' || c == '\t' || c == '\r':
			i++
		case c == ';':
			for i < len(src) && src[i] != '\n' {
				i++
			}
		case c == '(':
			stack = append(stack, top)
			lines = append(lines, line)
			top = nil
			i++
		case c == ')':
			if len(stack) == 0 {
				return nil, fmt.Errorf("line %d: unbalanced )", line)
			}
			n := &node{kind: nList, list: top, line: lines[len(lines)-1]}
			top = append(stack[len(stack)-1], n)
			stack = stack[:len(stack)-1]
			lines = lines[:len(lines)-1]
			i++
		case c == '`':
			j := strings.IndexByte(src[i+1:], '`')
			if j < 0 {
				return nil, fmt.Errorf("line %d: unterminated Lean term", line)
			}
			text := src[i+1 : i+1+j]
			top = append(top, &node{kind: nLean, text: text, line: line})
			line += strings.Count(text, "\n")
			i += j + 2
		case c == '"':
			j := strings.IndexByte(src[i+1:], '"')
			if j < 0 {
				return nil, fmt.Errorf("line %d: unterminated string", line)
			}
			top = append(top, &node{kind: nString, text: src[i+1 : i+1+j], line: line})
			i += j + 2
		default:
			j := i
			for j < len(src) && !strings.ContainsRune(" \t\r\n()`\";", rune(src[j])) {
				j++
			}
			top = append(top, &node{kind: nAtom, text: src[i:j], line: line})
			i = j
		}
	}
	if len(stack) != 0 {
		return nil, fmt.Errorf("unbalanced ( opened at line %d", lines[len(lines)-1])
	}
	return top, nil
}
