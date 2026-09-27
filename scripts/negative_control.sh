#!/bin/bash
# Negative control: confirm the comparator rejects a mutated theorem statement.
#
# Mutates the Challenge by weakening the conjunction: drops the absolute
# continuity clause "Q ≪ P ∧ P ≪ Q", making the boundary inconsistent.
# The Solution still proves the original (unmutated) statement, so the
# mutated Challenge and the Solution should no longer match.
# Requires a passing baseline first.
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# -gt 1 || ( $# -eq 1 && "$1" != "--local" ) ]]; then
  echo "Usage: bash scripts/negative_control.sh [--local]" >&2
  exit 2
fi

CHALLENGE="BlackScholesChallenge.lean"
THEOREM="PalomarBlackScholes.black_scholes"

echo "=== Negative control ==="

# Step 1: Verify baseline passes
echo "[1/3] Verifying baseline ..."
if ! BASELINE=$(bash scripts/run_comparator.sh "$@" 2>&1); then
  echo "$BASELINE"
  echo "FAIL: baseline Comparator run failed"
  exit 1
fi
if ! echo "$BASELINE" | grep -q "Your solution is okay"; then
  echo "FAIL: baseline comparator run does not pass — negative control is unreliable"
  echo "$BASELINE" | tail -5
  exit 1
fi
echo "  Baseline passes"

# Step 2: Build a mutated Challenge
echo "[2/3] Building mutated Challenge ..."
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/bs-neg-ctrl-XXXXXX")

cp "$CHALLENGE" "$WORKDIR/Challenge.lean.orig"
restore() {
  local result=$?
  trap - EXIT
  echo "  Restoring original Challenge source and rebuilding ..."
  if ! cp "$WORKDIR/Challenge.lean.orig" "$CHALLENGE"; then
    echo "FAIL: restore the Challenge from $WORKDIR/Challenge.lean.orig" >&2
    exit 1
  fi
  if ! lake build BlackScholesChallenge; then
    echo "FAIL: original source restored, but rebuilding failed" >&2
    result=1
  fi
  rm -rf "$WORKDIR"
  exit "$result"
}
trap restore EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

python3 - "$CHALLENGE" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_text()
clause = "IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧"
if source.count(clause) != 1:
    raise SystemExit("FAIL: expected exactly one clause to mutate")
path.write_text(source.replace(clause, "IsProbabilityMeasure Q ∧"))
PY

echo "  Mutated: dropped absolute-continuity clauses"
if ! lake build BlackScholesChallenge 2>&1 | tail -3; then
  echo "  (mutated build failed — trap restores $CHALLENGE)"
  exit 1
fi

# Step 3: Run comparator on mutated Challenge
echo "[3/3] Running comparator on mutated Challenge ..."
RESULT=0
OUTPUT=$(bash scripts/run_comparator.sh "$@" 2>&1) || RESULT=$?
echo "$OUTPUT" | tail -5

if [[ "$RESULT" -eq 1 ]] && echo "$OUTPUT" | grep -qF \
  "error: Challenge and solution theorem statement do not match: '$THEOREM'"; then
  echo "PASS: comparator correctly rejected the mutated Challenge (statement mismatch)"
  exit 0
else
  echo "FAIL: comparator did not reject $THEOREM as expected"
  exit 1
fi
