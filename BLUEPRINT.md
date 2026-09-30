# Black–Scholes pricing via the predictable Girsanov theorem

The predictable Girsanov theorem is the general, dynamic theorem in this
library: its drift may depend on time and the random path, under the
conditions stated in the theorem. Black-Scholes applies its constant-drift
case. The steps below construct the required input data, apply the general
theorem, and use the resulting change of measure to evaluate the option price.

## Target

`PalomarBlackScholes.black_scholes` (`BlackScholesChallenge.lean`): fix
strictly positive initial price `spot`, strike `K`, volatility `σ` and maturity
`T`, and arbitrary constant real drift `μ` and interest rate `r`. Let `B` be
a real Brownian motion with almost-surely continuous paths and strongly
measurable values at every time. For every strong solution `X` of the linear
SDE `dX = μX dt + σX dB` with `X_0 = spot` almost surely, the exact terminal
density measure

```
Q = P.withDensity (exp (−θ B_T − θ² T / 2)),   θ = (μ − r) / σ
```

is a probability measure equivalent to `P`; the shifted driver
`B_t + θ (t ∧ T)` is a Brownian motion under `Q`; the discounted asset
stopped at `T` is a `Q`-martingale in the natural filtration of `B`; the
call payoff is `Q`-integrable; and its discounted `Q`-expectation at time zero
is the Black–Scholes formula `spot Φ(d₁) − K e^{−rT} Φ(d₂)`.

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

3. **Preparing the constant-drift inputs for the general Girsanov theorem.**
   For the version `B'`, the process `M = −θ B'_{t ∧ T}` is a continuous
   martingale in the natural filtration of `B'` with deterministic bracket
   `θ² (t ∧ T)`;
   Novikov's condition is automatic for a deterministic bracket. These
   assemble into `GirsanovDensityData`
   (`girsanovDensityData_neg_mul_stopped`, `GirsanovConstantDrift.lean`),
   with the quadratic variation of the stopped scaled driver supplied by
   `hasQuadraticVariationBeforeStop_preBrownianReal`
   (`LocalMartingaleContract.lean`). The package has no cross-variation
   field. The cross variation between the stopped driver and `B'` is a
   separate hypothesis of the general theorem: the constant-drift bridge
   proves it with `tendstoInMeasure_stopped_brownian_brownian_covariation`
   (`QuadraticVariation.lean`) and supplies it, alongside the package, when
   it applies the theorem in step 4.

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
   and strict positivity of the density give equivalence of measures
   (`girsanovMeasure_const_mutuallyAbsolutelyContinuous`). Absolute continuity
   transfers almost-sure path continuity from `P` to `Q`, so the shifted driver
   is Brownian (`isBrownianReal_riskNeutralBrownian`, `BlackScholes.lean`).
   The final proof obtains the probability property from this Brownian law
   through `hW.isGaussianProcess.isProbabilityMeasure`.

6. **The discounted martingale.** For the explicit geometric Brownian motion
   of step 1, the discounted asset stopped at `T` equals `spot` times the
   Doléans–Dade exponential of `σ` times the shifted driver, stopped at `T`.
   This is an algebraic identity on every path, with no measure involved
   (`discounted_gbm_eq_exponential`). That exponential is a `Q`-martingale by
   the Gaussian-increment argument
   (`martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements`,
   `DoleansDade.lean`), and a deterministic drift shift leaves the natural
   filtration unchanged (`natural_add_deterministic`). The theorem covers
   every allowed strong solution, not only the explicit formula:
   `martingale_discountedStoppedAsset` uses the uniqueness of step 1 to make
   the given solution agree with the formula `P`-almost surely, then `Q ≪ P`
   to keep that agreement `Q`-almost surely, and with the solution's
   adaptedness transfers the martingale property to it.

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
| 3 | `novikovCondition_deterministic` | `NovikovCondition.lean` |
| 4 | `GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_predictable` | `GirsanovTheorem.lean` |
| 4 | `GirsanovDensityData.martingale_stopAt_complexDoleans_predictable` | `GirsanovTheorem.lean` |
| 5 | `isPreBrownianReal_girsanovShiftedBrownian_const_dynamic` | `GirsanovConstantDrift.lean` |
| 5 | `girsanovMeasure_const_mutuallyAbsolutelyContinuous` | `GirsanovConstantDrift.lean` |
| 5 | `isBrownianReal_riskNeutralBrownian` | `BlackScholes.lean` |
| 6 | `martingale_discountedStoppedAsset`, `natural_add_deterministic` | `BlackScholes.lean` |
| 6 | `martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements` | `DoleansDade.lean` |
| 7 | `call_expectation_eq_blackScholes`, `integrable_callPayoff` | `BlackScholes.lean` |
| all | `StochasticCalculus.BlackScholes.black_scholes` | `BlackScholes.lean` |

## Deferred constructor and proof-dependency check

The fully general constructor would build the martingale, bracket and other
input data from a predictable integrand under the required conditions.
That work remains deferred. Step 3 supplies the data directly for the constant
drift needed here, on the arbitrary measurable sample space of the Challenge.
The existing `GirsanovItoData.lean` adapter assumes additional Gaussian
sample-space structure; it and `GirsanovFiltered.lean` are retained for future
constructor work and are not used by the Black-Scholes proof.

Run `lake env lean scripts/check_girsanov_route.lean` to follow the dependencies
of the completed proof. It requires the general predictable Girsanov theorem,
the constant-drift bridge and the continuous Brownian version to occur in that
proof, and rejects a dependency on the old Gaussian measure-change shortcut.
The results on Lean 4.35 are recorded in
[README.md § Verification](README.md#verification).
The Gaussian calculations in steps 6 and 7 remain part of the proof after the
change of measure has been established.

## Code mapping

### Submission definitions

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

The Solution proof applies the library theorem with one `exact`. The two
strong-solution structures are distinct Lean types with the same five
conditions, so the proof passes those fields explicitly into the library
structure. The remaining boundary definitions unfold to their library twins.

Under Lean's module system a proof nested in a definition becomes a helper
named after its file, so `geometricBrownianMotion`, `riskNeutralMeasure` and
`blackScholesCall` carry `@[expose]` in both files to keep those constants
identical.

### Library catalogue

The 65 files are under `StochasticCalculus/` (names omit `.lean`), and each
opens with its own description. Files marked † contribute no declaration to
the completed Black-Scholes proof, which reaches the other 53; they belong to
the wider library and are retained.

Shared foundation, by dependency layer:

- Layer 0, only Mathlib: CameronMartin †, Symmetrization †, FubiniLift †
- Layer 1: CameronMartinTheorem †, Simplex †
- Layer 2: IteratedIntegral
- Layer 3: WienerIntegral
- Layer 4: PredictableProcess †
- Layer 5: ElementaryIto, PredictableDensity †
- Layer 6: ItoConstruction †

Black-Scholes chain, by stage:

- Stage A, the natural Itô process: ItoProcess †
- Stage B, quadratic variation: TendstoInMeasureAlgebra, UniformPartitionSums,
  QuadraticVariationContract, QuadraticVariation,
  QuadraticVariationElementary †, QuadraticVariationDensity
- Stage C, Itô formula: ItoFormula, ItoMaximal, QuadraticVariationTightness,
  QuadraticVariationGrid, TightProduct, ItoFormulaPartition,
  ItoFormulaGeneral, WeightedBracketRiemann
- Stage D, exponential martingales: LocalMartingaleContract,
  ContinuousExitTime, ElementaryMartingaleIntegral, LocalizingStoppedProcess,
  PartitionStoppingTime, MartingaleLeftSum, DoleansDadeExponential,
  DoleansDadeMartingale, DoleansDade, GeometricBrownianMotion, GBMGronwall,
  NovikovCondition, Novikov
- Stage E, Girsanov core: GBMLocalization, CrossVariationProcess,
  GirsanovMeasure, GirsanovMartingaleTransform, GirsanovCommonRefinement,
  GirsanovFourierIncrement, GirsanovComplexEuler, GirsanovMeshControl,
  GirsanovStoppedControl, Girsanov, GirsanovClosure, GirsanovMoments,
  MartingaleFourthMoment, GirsanovBounded, StoppedVariation, ZeroBracket
- Stage F, Girsanov applications → Black-Scholes: GirsanovCrossVariation,
  StoppedCrossVariation, GirsanovLocalization, GirsanovExits, GirsanovTheorem,
  GirsanovFiltered †, BrownianContinuousVersion, GirsanovConstantDrift,
  GirsanovItoData †, BlackScholes

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
(proof built 2026-09-07 with Codex) and was consolidated into this
repository on 2026-09-18;
[`fe6cd1d`](https://github.com/savarin/lean-stochastic-calculus/commit/fe6cd1d053741a2de5ac6cc727ec3bb49a55cf80)
is the imported repository snapshot. On 2026-09-21 the measure change was
rerouted from a constant-drift Gaussian oracle to the predictable Girsanov
theorem and a proof-dependency audit guided the library cleanup; early on
2026-09-22 the five largest files were split by topic into 24 files (Claude
Fable 5.1 with Claude Code).
The Challenge statement is unchanged
across these steps. On 2026-09-27 Codex upgraded Lean and Mathlib together to
v4.35.0-rc3, repaired the affected proofs, and verified that the dynamic
Girsanov route remains in the completed proof. The Challenge and Solution
source files were preserved unchanged during the upgrade. On 2026-09-29 the
files were ported to Lean's module system (Claude Opus 5.5 with Claude Code);
the Challenge statement is unchanged.
