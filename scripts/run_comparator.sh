#!/usr/bin/env bash
set -euo pipefail

readonly PALOMAR_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly PALOMAR_REPO_ROOT="$(cd "$PALOMAR_SCRIPT_DIR/.." && pwd)"

: "${COMPARATOR:?Set COMPARATOR to the Comparator executable.}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to the Lean 4.33-compatible exporter.}"

export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT"
if [[ -n "${FAKE_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$FAKE_LANDRUN"
fi

cd "$PALOMAR_REPO_ROOT"
lake env "$COMPARATOR" comparator-black-scholes.json
