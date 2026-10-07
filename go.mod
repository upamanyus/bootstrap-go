module github.com/upamanyus/bootstrap-go

go 1.26

require github.com/mit-pdos/perennial v0.0.0

require (
	github.com/fatih/color v1.19.0 // indirect
	github.com/mattn/go-colorable v0.1.14 // indirect
	github.com/mattn/go-isatty v0.0.20 // indirect
	github.com/pelletier/go-toml/v2 v2.4.3 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	golang.org/x/mod v0.39.0 // indirect
	golang.org/x/sync v0.22.0 // indirect
	golang.org/x/sys v0.47.0 // indirect
	golang.org/x/tools v0.49.0 // indirect
)

// goose (translator and Go library) comes from the Lean Perennial dependency,
// at the revision lake-manifest.json pins.
replace github.com/mit-pdos/perennial => ./.lake/packages/perennial
