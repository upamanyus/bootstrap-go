// Package examples contains small Go functions that are targets for the
// symbolic-execution proof checker.
package examples

// Double is the motivating example: heap access, arithmetic, control flow.
func Double(x int, z *int) {
	y := x
	if x == 0 {
		y = 37
	}
	*z = y + y
}

// Max returns the larger of two unsigned integers.
func Max(a uint64, b uint64) uint64 {
	if a < b {
		return b
	}
	return a
}

// Swap exchanges the contents of two pointers.
func Swap(p *uint64, q *uint64) {
	tmp := *p
	*p = *q
	*q = tmp
}

// Abs returns the absolute value of x (wrapping for MinInt64).
func Abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// CondStore stores into p only if the flag is set, and reports whether it did.
func CondStore(flag bool, p *uint64, v uint64) bool {
	if !flag {
		return false
	}
	*p = v
	return true
}
