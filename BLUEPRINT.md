# Black–Scholes pricing via the predictable Girsanov theorem

## Target

`PalomarBlackScholes.black_scholes` (`BlackScholesChallenge.lean`): for a
real Brownian motion `B` with almost-surely continuous paths, every strong
solution `X` of the linear SDE `dX = μX dt + σX dB` with `X_0 = spot`, and
every maturity `T > 0`, the exact terminal density measure

```
Q = P.withDensity (exp (−θ B_T − θ² T / 2)),   θ = (μ − r) / σ
```

is a probability measure equivalent to `P`; the shifted driver
`B_t + θ (t ∧ T)` is a Brownian motion under `Q`; the discounted asset
stopped at `T` is a `Q`-martingale in the natural filtration of `B`; the
call payoff is `Q`-integrable; and its discounted `Q`-expectation is the
Black–Scholes formula `S Φ(d₁) − K e^{−rT} Φ(d₂)`.

The strong solution is pinned by concrete left-sum convergence in
probability (`IsStrongLinearSolution`), not by an abstract stochastic
integral, so the Challenge imports only Mathlib.

## Proof route

1. **Uniqueness of the strong solution.** Every strong solution agrees
   almost surely with geometric Brownian motion
   `spot · exp((μ − σ²/2) t + σ B_t)`
   (`geometricBrownianMotion_unique_strong_solution`, `GBMLocalization.lean`),
   by a Gronwall-type localization along bounded path exits.

2. **A continuous version of the driver.** `IsBrownianReal` gives continuous
   paths and a zero start only almost surely, while the Girsanov density
   contract asks for both at every sample point. `continuousBrownianVersion`
   zeroes one measurable null set (`toMeasurable` of the bad set); every
   path is then continuous and starts at zero, each time slice stays
   strongly measurable, and the result is again a Brownian motion agreeing
   with `B` almost surely at every fixed time (`BrownianContinuousVersion.lean`).

3. **The Girsanov density contract at constant drift.** For the version
   `B'`, the process `M = −θ B'_{t ∧ T}` is a continuous martingale in the
   natural filtration of `B'` with deterministic bracket `θ² (t ∧ T)`;
   Novikov's condition is automatic for a deterministic bracket. These
   assemble into `GirsanovDensityData`
   (`girsanovDensityData_neg_mul_stopped`, `GirsanovConstantDrift.lean`),
   with the quadratic variation of the stopped scaled driver supplied by
   `hasQuadraticVariationBeforeStop_preBrownianReal`
   (`LocalMartingaleContract.lean`) and the cross variation with `B'` by
   `tendstoInMeasure_stopped_brownian_brownian_covariation`
   (`QuadraticVariation.lean`).

4. **The predictable Girsanov theorem.** Under the density contract and the
   cross-variation identity, the shifted driver is pre-Brownian for the exact
   terminal density measure
   (`GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_predictable`,
   `GirsanovTheorem.lean`). The proof closes the complex Doléans–Dade
   martingale of `M + i c B'` by Novikov uniform integrability and identifies
   the law through characteristic functions of increments. Its development
   is the chain `CrossVariationProcess` → `GirsanovMeasure` → … →
   `Girsanov` → `GirsanovCrossVariation` → … → `GirsanovTheorem`.

5. **Transport back to `B`.** The density and the shifted driver of `B'`
   agree with those of `B` almost surely at each fixed time, so
   `withDensity_congr_ae` identifies the two measures and
   `IsPreBrownianReal.congr` transfers Brownianity
   (`isPreBrownianReal_girsanovShiftedBrownian_const_dynamic`). Integrability
   and expectation one of the density give equivalence of measures and the
   probability property (`girsanovMeasure_const_mutuallyAbsolutelyContinuous`,
   `isProbabilityMeasure_girsanovMeasure_const`).

6. **The discounted martingale.** Under `Q` the discounted stopped asset
   equals `spot` times the Doléans–Dade exponential of `σ` times the shifted
   driver, stopped at `T` (`discounted_gbm_eq_exponential`); that exponential
   is a martingale by the Gaussian-increment argument
   (`martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements`,
   `DoleansDade.lean`), and a deterministic drift shift leaves the natural
   filtration unchanged (`natural_add_deterministic`).

7. **Evaluation of the call.** The terminal asset is a lognormal function of
   a standard Gaussian under `Q`; the discounted expectation is computed
   through the Esscher tilt of the standard Gaussian
   (`tilted_gaussianReal`, `setIntegral_exp_sub_half_sq_standardGaussian`)
   to the closed form (`brownianCallPrice_eq_blackScholes`,
   `call_expectation_eq_blackScholes`, all in `BlackScholes.lean`).

## Key lemmas

| Step | Declaration | File |
|---|---|---|
| 1 | `geometricBrownianMotion_unique_strong_solution` | `GBMLocalization.lean` |
| 2 | `continuousBrownianVersion`, `isBrownianReal_continuousBrownianVersion` | `BrownianContinuousVersion.lean` |
| 3 | `girsanovDensityData_neg_mul_stopped` | `GirsanovConstantDrift.lean` |
| 3 | `hasQuadraticVariationBeforeStop_preBrownianReal` | `LocalMartingaleContract.lean` |
| 3 | `novikovCondition_deterministic` | `Novikov.lean` |
| 4 | `GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_predictable` | `GirsanovTheorem.lean` |
| 4 | `GirsanovDensityData.martingale_stopAt_complexDoleans_predictable` | `GirsanovTheorem.lean` |
| 5 | `isPreBrownianReal_girsanovShiftedBrownian_const_dynamic` | `GirsanovConstantDrift.lean` |
| 5 | `girsanovMeasure_const_mutuallyAbsolutelyContinuous` | `GirsanovConstantDrift.lean` |
| 6 | `martingale_discountedStoppedAsset`, `natural_add_deterministic` | `BlackScholes.lean` |
| 6 | `martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements` | `DoleansDade.lean` |
| 7 | `call_expectation_eq_blackScholes`, `integrable_callPayoff` | `BlackScholes.lean` |
| all | `StochasticCalculus.BlackScholes.black_scholes` | `BlackScholes.lean` |

## Code mapping

Every Challenge definition is restated with the same body in
`BlackScholesSolution.lean`, so the Comparator sees identical constants, and
each has a library twin used by the proof:

| Challenge (`PalomarBlackScholes`) | Library twin |
|---|---|
| `uniformPartitionTime` | `StochasticCalculus.uniformPartitionTime` |
| `geometricBrownianMotion` | `StochasticCalculus.geometricBrownianMotion` |
| `linearSDESpaceApprox`, `linearSDEResidual` | `StochasticCalculus.linearSDESpaceApprox`, `StochasticCalculus.linearSDEResidual` |
| `IsStrongLinearSolution` | `StochasticCalculus.IsStrongLinearSDESolution` |
| `marketPriceOfRisk`, `riskNeutralMeasure`, `riskNeutralBrownian`, `discountedStoppedAsset`, `blackScholesCall` | the same names in `StochasticCalculus.BlackScholes` |
| `black_scholes` | `StochasticCalculus.BlackScholes.black_scholes` |

The Solution proof is one `exact` of the library theorem; the definitions
unfold to the same terms on both sides.

## Pitfalls

- **Almost-sure versus every-path.** Mathlib's `IsBrownianReal` is
  almost-surely continuous; the density contract is pointwise. Use the
  continuous version and transport, never a pointwise hypothesis on `B`.
- **Adaptedness of a totalized process.** Zeroing the bad paths inspects
  the whole path, so the totalized driver is adapted only to its own natural
  filtration. The theorem is applied in that filtration and the conclusion,
  which does not mention the filtration, is transported.
- **Lp representatives.** `predictableQuadraticVariation` integrates the
  coerced representative of an `L²` integrand, which is fixed only up to a
  null set; pointwise statements about it are not provable. The packaging
  `ItoGirsanovDensityData` therefore takes a free bracket representative
  with an almost-everywhere modification field.
- **Comparator bodies.** Palomar compares every shared non-target constant
  body for body. A Solution definition that delegates to the library is
  rejected even when definitionally equal; restate the body.
- **Reachability and `rfl` lemmas.** A lemma proved by `rfl` and used by
  `simp` leaves no trace in the proof term. When pruning by kernel
  reachability, check the source for such uses before deleting.

## Provenance

The library originates in the `lean-pipeline/black-scholes-sde` workspace
(commit `e5a7803`, proof built 2026-09-07 with Codex), consolidated into
this repository on 2026-09-17. On 2026-09-21 the measure change was
rerouted from a constant-drift Gaussian oracle to the predictable Girsanov
theorem, the library was pruned to the declarations reachable from the two
Palomar theorems, and the two largest files were split by topic
(Claude Fable 5.1 with Claude Code). The Challenge statement is unchanged
across these steps.
