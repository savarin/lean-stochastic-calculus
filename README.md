# lean-stochastic-calculus

Black-Scholes option pricing from first principles, formalized in Lean 4
against Mathlib. The proof builds the Itô integral, derives the Girsanov
change-of-measure theorem, and uses it to price European call options
under the risk-neutral measure. Prepared for submission to
[Palomar](https://palomar-registry.org).

## Main result

- `PalomarBlackScholes.black_scholes`
  (Challenge declaration): for any strong solution of the geometric
  Brownian motion SDE, the Girsanov risk-neutral measure prices the
  European call at the Black-Scholes closed form.

## Scope

The formalization covers a single asset driven by scalar Brownian motion
on a finite time horizon. Starting from the Itô integral construction,
it proves:

- Existence and mutual absolute continuity of the risk-neutral measure
- Brownianity of the shifted driver under the new measure
- The martingale property of the discounted stopped asset
- Integrability of the call payoff
- Equality of the discounted expectation with the Black-Scholes formula

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
  Girsanov change of measure
         │
  Black-Scholes pricing
```

## Trust boundary

The 114-line Mathlib-only
[BlackScholesChallenge.lean](BlackScholesChallenge.lean) exposes the
Palomar boundary: one theorem, zero definition holes.
[BlackScholesSolution.lean](BlackScholesSolution.lean) restates every
Challenge definition with the same body and discharges the theorem by the
sorry-free proof library under `StochasticCalculus/`. The proof route and
its code mapping are in [BLUEPRINT.md](BLUEPRINT.md).

- Imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Build and verify

Lean and Mathlib v4.33.0 are pinned.

```bash
lake exe cache get
lake build StochasticCalculus BlackScholesSolution --iofail
lake build BlackScholesChallenge
python3 scripts/check_boundary.py
```

The library and the Solution build with `--iofail`, which rejects any
stray informational output. The Challenge is built separately because its
one deliberate `sorry` is reported as a warning.

Comparator smoke test and negative control (require the pinned Comparator
and lean4export binaries; on macOS point `FAKE_LANDRUN` at the
Comparator's `scripts/fake-landrun.sh`):

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh
```

Palomar runs its own pinned Comparator, Landrun sandbox, and NanoDa
kernel independently; `enable_nanoda` is set to `false` in the local
config because the NanoDa binary is not distributed.

## Verification

On 2026-09-21 the pinned Comparator (leanprover/comparator at
`8d84e67`, 2026-08-25, with lean4export built for Lean v4.33.0) accepted
the Challenge/Solution pair: "Lean default kernel accepts the solution".
The negative control, run the same day with the same binaries, requires
the unmodified baseline to pass, then mutates the Challenge (dropping the
absolute-continuity clauses), confirms the mutated boundary still
elaborates, and verifies that the Comparator rejects specifically the
named theorem. `check_boundary.py` validates the closed Comparator
schema, verifies Mathlib-only imports, checks the deliberate sorry count,
confirms each selected declaration is present in the Challenge, and
audits that all declarations use only the permitted axioms.

## Production and review

The proof library was written by agents and is checked by the Lean
kernel: Codex built the library and the boundary on 2026-09-07 in the
`lean-pipeline/black-scholes-sde` workspace, and Claude Fable 5.1 rerouted
the measure change through the predictable Girsanov theorem, pruned the
library to the declarations the theorems use, and split the largest files
on 2026-09-21. The author directed the work, read the Challenge and the
metadata, and approved each change; the library has not been examined in
depth by human experts. Details, including model names and cost notes, are
in `formalization.yaml`.

## License

Apache-2.0.
