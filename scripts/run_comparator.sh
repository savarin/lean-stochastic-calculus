#!/usr/bin/env bash
set -euo pipefail

readonly PALOMAR_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly PALOMAR_REPO_ROOT="$(cd "$PALOMAR_SCRIPT_DIR/.." && pwd)"

cd "$PALOMAR_REPO_ROOT"

# Linux uses Lake's bubblewrap sandbox. macOS users must explicitly select a
# local check; this does not reproduce Palomar's protected verification.
PALOMAR_COMMAND=(lake comparator)
if [[ "${1:-}" == "--local" ]]; then
  PALOMAR_COMMAND+=(--inadvisably-no-sandbox)
  shift
  echo "Local check without the Linux sandbox; not a Palomar verification."
fi
if [[ $# -ne 0 ]]; then
  echo "Usage: bash scripts/run_comparator.sh [--local]" >&2
  exit 2
fi

# Keep the submission config within Palomar's allowed schema. Select the
# bundled independent checkers in a temporary local copy, as Palomar does.
mkdir -p .lake
PALOMAR_CHECK_DIR=$(mktemp -d "$PALOMAR_REPO_ROOT/.lake/comparator-XXXXXX")
trap 'rm -rf "$PALOMAR_CHECK_DIR"' EXIT
python3 - "$PALOMAR_CHECK_DIR/config.json" "$(lean --print-prefix)" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path("comparator-black-scholes.json").read_text())
config.pop("enable_nanoda", None)
binary_dir = pathlib.Path(sys.argv[2]) / "bin"
config["external_kernels"] = {
    "nanoda": [str(binary_dir / "nanoda_bin")],
    "con-ron": [str(binary_dir / "con-ron")],
}
pathlib.Path(sys.argv[1]).write_text(json.dumps(config) + "\n")
PY
"${PALOMAR_COMMAND[@]}" --config "$PALOMAR_CHECK_DIR/config.json"
