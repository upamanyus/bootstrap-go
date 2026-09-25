#!/usr/bin/env bash
# Regenerates the test inputs in this directory: the exports, in full, of the
# goals in new/proof/rocqgoal/examples/. Each example reports its goals with
# [report_goal "name"], which prints only a size; this script compiles a copy
# of it with [dump_goal "name"] instead, which prints the export, and writes
# the export of goal "name" to name.sexp here.
#
# Needs rocq in PATH and new/proof/rocqgoal/export.vo and the imports of the
# examples built (for median3.v, checker/examples/examples_init.vo).
#
# Run from the repository root: bash gocheck/rocqgoal/testdata/regen.sh
set -euo pipefail

OUT=gocheck/rocqgoal/testdata
EX=new/proof/rocqgoal/examples

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# The global arguments Rocq needs, extracted from _RocqProject the same way
# the Makefile does.
args=$(sed -E -e '/^#/d' -e 's/-arg ([^ ]*)/\1/g' _RocqProject)

for f in small median3; do
	sed 's/report_goal/dump_goal/' "$EX/$f.v" >"$tmp/$f.v"
	# The copy gets the logical name of the original, so the export names
	# its definitions as the build does.
	# shellcheck disable=SC2086
	rocq compile $args -Q "$tmp" New.proof.rocqgoal.examples "$tmp/$f.v" >"$tmp/$f.log"
	awk -v out="$OUT" '
		/^== / { name = $2; next }
		name != "" && /^\(Goal/ { f = out "/" name ".sexp"; print > f; close(f); print "wrote " f; name = "" }
	' "$tmp/$f.log"
done
