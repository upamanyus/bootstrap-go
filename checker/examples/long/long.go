// Package long contains longer targets for the symbolic-execution checker:
// functions that take many steps and branches to compute something simple.
package long

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
