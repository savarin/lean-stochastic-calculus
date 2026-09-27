# lean-stochastic-calculus

Black-Scholes option pricing from first principles, formalized in Lean 4
against Mathlib. The library builds the Itô integral and proves the general
predictable (dynamic) Girsanov theorem. The Black-Scholes proof applies that
theorem at a constant drift to price European call options under the
risk-neutral measure. Prepared for submission to
[Palomar](https://palomar-registry.org).

## Main result

- `PalomarBlackScholes.black_scholes`
  (Challenge declaration): for any strong solution of the geometric
  Brownian motion SDE, the Girsanov risk-neutral measure prices the
  European call at the Black-Scholes closed form.

## Scope

The formalization covers a single asset driven by scalar Brownian motion
on a finite time horizon. The initial asset price, strike, volatility and
maturity are strictly positive. The drift and interest rate are constant real
numbers; either may be negative. The formula is the price at time zero,
expressed as a discounted expectation under the constructed measure.

The Brownian driver has almost-surely continuous paths, and its value at each
time is assumed strongly measurable. A solution is adapted to the driver's
natural filtration, has almost-surely continuous paths and the given initial
value, has an integrable drift along almost every path, and satisfies the SDE
through convergence in probability of explicit left sums. The sample space is
an arbitrary measurable space. Under these assumptions, the theorem proves:

- Existence and mutual absolute continuity of the risk-neutral measure
- Brownianity of the shifted driver under the new measure
- The martingale property of the discounted stopped asset
- Integrability of the call payoff
- Equality of the discounted expectation with the Black-Scholes formula

The submitted theorem covers this expectation formula and the supporting
change of measure. It does not include a trading-strategy replication theorem
or a conditional option-price process at later times. Zero strike, zero
volatility and zero maturity are outside its stated scope.

The library contains 65 Lean source files (~46k lines) organized in six
stages. See [LIBRARY.md](LIBRARY.md) for per-file descriptions.

## Proof architecture

```
Itô integral construction
         │
  Quadratic variation ⟨B⟩ = t
         │
     Itô formula
         │
  Doléans-Dade exponential ── Novikov condition
         │
  General predictable Girsanov theorem
         │
  Constant-drift instance θ = (μ − r) / σ
         │
  Black-Scholes pricing
```

Here “dynamic” describes the general theorem: it allows a drift that varies
with time and the random path, subject to its stated conditions. Black-Scholes
needs the constant drift above, for which the proof supplies those conditions
directly. The constructor that would supply them for arbitrary integrands
remains deferred. [BLUEPRINT.md](BLUEPRINT.md) explains each step and names
the Lean lemmas used.

## Trust boundary

The 114-line Mathlib-only
[BlackScholesChallenge.lean](BlackScholesChallenge.lean) exposes the
Palomar boundary: one theorem, zero definition holes.
[BlackScholesSolution.lean](BlackScholesSolution.lean) restates every
Challenge definition with the same body and discharges the theorem by the
sorry-free proof library under `StochasticCalculus/`. The proof route and
its code mapping are in [BLUEPRINT.md](BLUEPRINT.md).

- Challenge imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Build and verify

Lean and Mathlib **v4.35.0-rc3** are pinned. This is a release candidate.

```bash
lake exe cache get
lake build StochasticCalculus BlackScholesSolution --iofail
lake build BlackScholesChallenge
python3 scripts/check_boundary.py
lake env lean scripts/check_girsanov_route.lean
```

The library and the Solution build with `--iofail`, which rejects warnings
and informational output from Lean. The Challenge is built separately because
its one deliberate `sorry` is reported as a warning.

Lean 4.35 bundles Comparator, the matching exporter, and independent proof
checkers. The scripts use those tools directly; no separate Comparator or
lean4export installation is needed. On Linux with `bubblewrap` available:

```bash
python3 scripts/check_boundary.py --comparator
bash scripts/negative_control.sh
```

On macOS, append `--local` to each command. This explicitly runs without
the Linux sandbox. The scripts enable the bundled NanoDa and con-ron
checkers in a temporary configuration, alongside Lean's own kernel. The
negative control requires a passing baseline, changes the statement,
checks that Comparator rejects it, then restores and rebuilds the original.

To validate metadata and packaging with Palomar's pinned validator
(Python 3.11 or later):

```bash
python3 -m venv .lake/checks-venv
.lake/checks-venv/bin/python -m pip install -r scripts/requirements-checks.txt
git clone https://github.com/PalomarRegistry/PalomarSubmission.git .lake/palomar-submission
git -C .lake/palomar-submission checkout --detach a59f25bd8a66bf6faf3a4f4260d412989c0185ea
.lake/checks-venv/bin/python scripts/check_metadata.py
```

Palomar independently reruns its protected checks on the submitted commit.
The local checks do not constitute Palomar acceptance. The validator pin
records the rules checked here; reassess it if submission is delayed.

## Verification

The Lean 4.35 verification results, exact versions, commands, and limits
are recorded in [VERIFICATION.md](VERIFICATION.md). Earlier results from
Lean 4.33 do not establish that the upgraded project passes.

GitHub CI checks the strict build, publication boundary, dynamic Girsanov
dependency, metadata, and packaging. The full local Comparator and
negative-control results are recorded separately; Palomar performs the
protected verification after submission.

## Production and review

The proof library was written by agents and is checked by the Lean
kernel: Codex built the library and the boundary on 2026-09-07 in the
`lean-pipeline/black-scholes-sde` workspace, and Claude Fable 5.1 rerouted
the measure change through the predictable Girsanov theorem, pruned unused
parts of the library, and split the largest files
on 2026-09-21. Codex upgraded the project to Lean and Mathlib 4.35 and
updated the submission checks on 2026-09-27. The author directed the work,
read the Challenge and the metadata, and approved the earlier changes;
the upgrade was prepared for author review before committing. The library
has not been examined in depth by human experts. Details, including model
names and cost notes, are in `formalization.yaml`.

The mathematics follows a standard route to the established Black-Scholes
formula. The metadata identifies the original paper as the source of the
result and explains the different proof route; no mathematical novelty is
claimed.

## Submission settings

Submission requires public access to
`https://github.com/savarin/lean-stochastic-calculus` and the full 40-character
identifier of the final pushed commit. Require the GitHub Build workflow to
pass on that same commit, including any review fixes.
The project and `formalization.yaml` are at the repository root; the Comparator
configuration path is **`comparator-black-scholes.json`** and must be supplied
explicitly because it differs from the default filename.

The responsible author or maintainer submits under that relationship.
These are the inputs for [Palomar submission](https://palomar-registry.org/how-to-submit);
this repository does not submit or register the result automatically.

## License

Apache-2.0.
