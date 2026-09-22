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

// Median3 returns the median of three unsigned integers, the long way: it
// copies them into locals, sorts the locals with a three-comparator sorting
// network (each comparator swaps its pair into order), and returns the middle
// one.
func Median3(a uint64, b uint64, c uint64) uint64 {
	x := a
	y := b
	z := c

	// Comparator (x, y): afterwards x <= y.
	if y < x {
		t := x
		x = y
		y = t
	}

	// Comparator (y, z): afterwards z is the maximum.
	if z < y {
		t := y
		y = z
		z = t
	}

	// Comparator (x, y): afterwards x <= y <= z.
	if y < x {
		t := x
		x = y
		y = t
	}

	return y
}
