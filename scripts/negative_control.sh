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

: "${COMPARATOR:?Set COMPARATOR to the comparator binary path}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to a v4.33.0-compatible lean4export binary}"

if [[ -n "${FAKE_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$FAKE_LANDRUN"
fi

CONFIG="comparator-black-scholes.json"
CHALLENGE="BlackScholesChallenge.lean"
THEOREM="PalomarBlackScholes.black_scholes"

echo "=== Negative control ==="

# Step 1: Verify baseline passes
echo "[1/3] Verifying baseline ..."
BASELINE=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
if ! echo "$BASELINE" | grep -qi "Your solution is okay"; then
  echo "FAIL: baseline comparator run does not pass — negative control is unreliable"
  echo "$BASELINE" | tail -5
  exit 1
fi
echo "  Baseline passes"

# Step 2: Build a mutated Challenge
echo "[2/3] Building mutated Challenge ..."
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/bs-neg-ctrl-XXXXXX")

cp "$CHALLENGE" "$WORKDIR/Challenge.lean.orig"
trap 'cp "$WORKDIR/Challenge.lean.orig" "$CHALLENGE"; rm -rf "$WORKDIR"' EXIT

sed 's/IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧/IsProbabilityMeasure Q ∧/' "$CHALLENGE" > "$WORKDIR/Challenge.lean"
cp "$WORKDIR/Challenge.lean" "$CHALLENGE"

echo "  Mutated: dropped absolute-continuity clauses"
if ! lake build BlackScholesChallenge 2>&1 | tail -3; then
  echo "  (mutated build failed — trap restores $CHALLENGE)"
  exit 1
fi

# Step 3: Run comparator on mutated Challenge
echo "[3/3] Running comparator on mutated Challenge ..."
OUTPUT=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
echo "$OUTPUT" | tail -5

echo "  Restoring original and rebuilding ..."

if echo "$OUTPUT" | grep -q "^FAIL $THEOREM"; then
  echo "PASS: comparator correctly rejected the mutated Challenge (statement mismatch)"
  exit 0
else
  echo "FAIL: comparator did not reject $THEOREM as expected"
  exit 1
fi
