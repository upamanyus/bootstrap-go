// Command rocqgoal prints a goal exported by new/proof/rocqgoal/export.v the
// way the Iris proof mode shows it: the Rocq context, then, if the goal is a
// proof mode goal, its persistent and spatial contexts, with typed points-to
// facts and a WP recognized.
//
// Usage: rocqgoal [-width N] [-time] [FILE]   (standard input without FILE)
package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"strings"
	"time"

	"github.com/mit-pdos/perennial/gocheck/rocqgoal"
)

func main() {
	width := flag.Int("width", 100, "cut terms off after this many bytes (0: never)")
	timing := flag.Bool("time", false, "print how long parsing and recognizing took")
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: rocqgoal [-width N] [-time] [FILE]\n")
		flag.PrintDefaults()
	}
	flag.Parse()
	var src []byte
	var err error
	switch flag.NArg() {
	case 0:
		src, err = io.ReadAll(os.Stdin)
	case 1:
		src, err = os.ReadFile(flag.Arg(0))
	default:
		flag.Usage()
		os.Exit(2)
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "rocqgoal: %v\n", err)
		os.Exit(2)
	}

	t0 := time.Now()
	g, err := rocqgoal.Parse(strings.TrimSpace(string(src)))
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		os.Exit(1)
	}
	t1 := time.Now()
	ipm, ipmErr := g.IPM()
	t2 := time.Now()

	short := func(t *rocqgoal.Term) string { return rocqgoal.Short(t, *width) }
	for _, h := range g.Hyps {
		if h.Body != nil {
			fmt.Printf("%s := %s : %s\n", h.Name, short(h.Body), short(h.Type))
		} else {
			fmt.Printf("%s : %s\n", h.Name, short(h.Type))
		}
	}
	if ipmErr != nil {
		fmt.Printf("==================================\n%s\n", short(g.Concl))
	} else {
		fmt.Printf("----------------------------------□\n")
		for _, h := range ipm.Persistent {
			fmt.Printf("%s : %s\n", h.Label(), prop(h.Prop, short))
		}
		fmt.Printf("----------------------------------∗\n")
		for _, h := range ipm.Spatial {
			fmt.Printf("%s : %s\n", h.Label(), prop(h.Prop, short))
		}
		fmt.Printf("----------------------------------\n%s\n", prop(ipm.Goal, short))
	}
	if *timing {
		fmt.Fprintf(os.Stderr, "parse %v, recognize %v, %d bytes\n", t1.Sub(t0), t2.Sub(t1), len(src))
	}
}

// prop prints an Iris proposition, with the forms this package recognizes
// in their usual notation.
func prop(t *rocqgoal.Term, short func(*rocqgoal.Term) string) string {
	if p, ok := rocqgoal.AsPointsTo(t); ok {
		return fmt.Sprintf("%s ↦{%s} %s   (typed_pointsto at %s)", short(p.Loc), short(p.Dfrac), short(p.Val), short(p.Type))
	}
	if w, ok := rocqgoal.AsWP(t); ok {
		return fmt.Sprintf("WP %s {{ %s }}", short(w.Expr), short(w.Post))
	}
	return short(t)
}
