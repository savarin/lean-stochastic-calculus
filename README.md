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

The library contains 45 Lean source files (~65k lines) organized in six
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
[BlackScholesSolution.lean](BlackScholesSolution.lean) delegates to the
sorry-free proof library under `StochasticCalculus/`.

- Imports: Mathlib only
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`

## Build and verify

Lean and Mathlib v4.33.0 are pinned.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py
```

Negative control (requires pinned Comparator and lean4export binaries):

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/negative_control.sh
```

Optional Comparator smoke test:

```bash
COMPARATOR=<path> LEAN4EXPORT=<path> bash scripts/run_comparator.sh
```

Palomar runs its own pinned Comparator, Landrun sandbox, and NanoDa
kernel independently; `enable_nanoda` is set to `false` in the local
config because the NanoDa binary is not distributed.

## Verification

The Comparator accepts the Challenge/Solution pair. The negative control
requires the unmodified baseline to pass, then mutates the Challenge
(dropping the absolute-continuity clauses), confirms the mutated boundary
still elaborates, and verifies that Comparator rejects specifically the
named theorem. `check_boundary.py` validates the closed Comparator
schema, verifies Mathlib-only imports, checks the deliberate sorry count,
confirms each selected declaration is present in the Challenge, and
audits that all declarations use only the permitted axioms.

## License

Apache-2.0.
