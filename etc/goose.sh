#!/usr/bin/env bash
# Regenerate the Goose output for this repository's Go packages, with the goose
# of the pinned Perennial dependency (.lake/packages/perennial).
#
# Goose's Lean backend writes modules under `Perennial.Code` and
# `Perennial.GeneratedProof`; a module under `Perennial.` is resolved to the
# Perennial package, so the output is moved under the module root
# `Generated.` (the Lean namespaces inside are unchanged).
set -euo pipefail
cd "$(dirname "$0")/.."

if [ ! -d .lake/packages/perennial ]; then
	echo "missing .lake/packages/perennial (go.mod's replacement for perennial):" >&2
	echo "run 'lake build' first, which fetches the Lake dependencies" >&2
	exit 2
fi
pkgs=(./checker ./checker/examples ./tcheck)
bin=$(mktemp -d); out=$(mktemp -d); trap 'rm -rf "$bin" "$out"' EXIT
(cd .lake/packages/perennial && GOBIN="$bin" go install ./goose/cmd/goose ./goose/cmd/proofgen)
"$bin/goose" -lean -out "$out/Code" -configdir "$out/Code" -dir . "${pkgs[@]}"
"$bin/proofgen" -lean -out "$out/GeneratedProof" -configdir "$out/Code" -dir . "${pkgs[@]}"
rm -rf Generated && mkdir -p Generated
mv "$out/Code" "$out/GeneratedProof" Generated/
find Generated -name '*.lean' -exec sed -i \
  -e 's/^import Perennial\.\(Code\|GeneratedProof\)\.github_com\.upamanyus\./import Generated.\1.github_com.upamanyus./' {} +
