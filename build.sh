#!/bin/bash
# Build and check all Lean files in dependency order.
# Needs a Lake project with Mathlib (Lean v4.34); point MATHLIB_PROJECT at it.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
proj="${MATHLIB_PROJECT:?set MATHLIB_PROJECT to a Lake project directory that has Mathlib}"
mkdir -p "$here/.build"
cd "$proj"
for m in RejOrder Fourier Bathwater AltR0 AltR0Final; do
  echo "== $m"
  lake env bash -c "LEAN_PATH=\$LEAN_PATH:$here/.build lean -R '$here' -o '$here/.build/$m.olean' '$here/$m.lean'" \
    2>&1 | grep -E "error|sorry" && { echo "FAILED: $m"; exit 1; } || true
done
echo "all files OK"
