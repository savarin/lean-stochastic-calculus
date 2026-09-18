# lean-stochastic-calculus

## Library guide

### Shared foundation

**Layer 0** — no internal dependencies, only Mathlib.

| File | Description |
|---|---|
| CameronMartin | Cameron-Martin Hilbert space of a Gaussian measure and its covariance embedding |
| Symmetrization | Symmetrization operator on functions of n variables; orthogonal L² projection |
| FubiniLift | Fubini isomorphism L²(μ; L²(ν)) ≅ L²(ν × μ) |

**Layer 1** — depends on Layer 0.

| File | Description |
|---|---|
| CameronMartinTheorem | Cameron-Martin theorem: translated Gaussian density formula and mutual absolute continuity |
| Simplex | The simplex Δₙ = {t₁ < ⋯ < tₙ} and its n!-fold tiling of the cube; ∫g = n!·∫\_Δₙ g for symmetric g |

**Layer 2** — depends on Layer 1.

| File | Description |
|---|---|
| IteratedIntegral | Iterated-integral Hilbert laws: step-function Itô isometry, IteratedIntegralFamily on L²((ℝ≥0)ⁿ), Hilbert-sum assembly |

**Layer 3** — depends on Layers 1–2.

| File | Description |
|---|---|
| WienerIntegral | Wiener integral J₁: L²(ℝ≥0) → L²(P) via dense extension of B(t) = J₁(1\_{(0,t]}); Itô isometry, Gaussianity, first-chaos characterization |

**Layer 4** — depends on Layer 2.

| File | Description |
|---|---|
| PredictableProcess | Predictable processes in L²: adapted elementary step functions, predictable projection via conditional expectation, timewise L² conditional expectation |

**Layer 5** — depends on Layer 4.

| File | Description |
|---|---|
| ElementaryIto | Itô isometry on elementary step processes: orthogonality of disjoint-interval Brownian values, inner product agreement with predictable tensors, partition-level isometry |
| PredictableDensity | Density of adapted elementary processes in predictable L²: π-system generation, orthogonality propagation by π-λ, trimmed-measure equivalence |

**Layer 6** — depends on Layer 5.

| File | Description |
|---|---|
| ItoConstruction | Brownian Itô integral on all predictable L²: cross-interval reduction, dense extension via `extendOfNorm`, centering and isometry packaging |

### Black-Scholes chain

**Stage A** — BS roots, depends on shared foundation.

| File | Description |
|---|---|
| GirsanovConstantOracle | Constant-drift Girsanov: Esscher tilt of Gaussians, MGF-based measure identification, stopped-drift pre-Brownian property |
| ItoProcess | Natural Itô integral as a time-indexed L² process: predictable time restriction, representative selection, martingale property |
| ItoSDE | Itô process SDE structure: X\_t = X\_0 + ∫μ ds + ∫σ dB with the constructed stochastic integral pinned as the representative |

**Stage B** — Quadratic variation, depends on Stage A.

| File | Description |
|---|---|
| QuadraticVariation | Quadratic variation ⟨B⟩\_t = t and ⟨X⟩\_t = ∫σ² ds: uniform-partition L² and in-probability convergence, stopped brackets, elementary diffusion brackets |
| QuadraticVariationElementary | Exact bracket for finite sums of adapted Brownian blocks: clipped-interval covariation, predictable bracket ∫σ² ds for finitely supported integrands |
| QuadraticVariationDensity | Extension of exact bracket to all predictable L² integrands: uniform L¹ perturbation estimates, convergence-together, change of variables to displayed diffusion |

**Stage C** — Itô formula, depends on Stage B.

| File | Description |
|---|---|
| ItoFormula | Itô's formula for Brownian motion: f(B\_t) = f(0) + ∫f' dB + ½∫f'' ds via Taylor partition sums, convergence in measure, and the no-pointwise-identity rule |
| ItoMaximal | Doob's maximal inequality for Itô integrals: conditional Jensen for L² submartingales, grid-independent finite-time bounds |
| QuadraticVariationTightness | Tail-transfer lemma: terminal QV convergence in measure implies uniform probability control for weighted bracket arguments |
| QuadraticVariationGrid | Quadratic variation on a common rational grid: prefix sums, rescaling identity, coherent-process convergence along common refinements |
| TightProduct | Vanishing-error localization: a random error vanishing in measure stays negligible after multiplication by an eventually tight nonneg control |
| ItoFormulaGeneral | General Itô formula f(t,X\_t): exact partition reduction into dt/dX/d⟨X⟩ sums plus remainder, unconditional formula for quadratic state functions of Itô processes |
| WeightedBracketRiemann | Weighted bracket Riemann sums: continuous weights integrated against ⟨X⟩ via uniform half-open partitions, closing diffusion-weighted QV for natural Itô integrals |

**Stage D** — Exponential martingales, depends on Stage C.

| File | Description |
|---|---|
| DoleansDade | Doléans-Dade stochastic exponential: continuous local martingales, ε(M)\_t = exp(M\_t − ½⟨M⟩\_t), Itô cancellation, Brownian exponential martingale |
| GeometricBrownianMotion | Geometric Brownian motion exp((μ−σ²/2)t + σB\_t): linear SDE identity via time-dependent Itô formula, L² uniqueness of strong solutions |
| GBMGronwall | Integral Grönwall for localized moment profiles: nonneg integrable function controlled by its own time integral vanishes |
| Novikov | Novikov's condition: exponential integrability E[exp(½⟨M⟩\_T)] < ∞ upgrades local martingale to true uniformly integrable martingale on [0,T] |

**Stage E** — Girsanov core, depends on Stages B–D.

| File | Description |
|---|---|
| GBMLocalization | Localization of linear SDE: dyadic sampled exits approximate bounded path-exit coefficient under original measure |
| Girsanov | Girsanov change of measure: terminal density Z\_T from Doléans-Dade, Novikov normalization, shifted Brownian pre-Brownian property, PredictableGirsanovDensityData |
| GirsanovClosure | Common-grid closure: stochastic Taylor residual transport to rational times, martingale closure for exponential density |
| GirsanovMoments | Moment consequences of Novikov: half-bracket exponential bounds both signs of stopped martingale, all polynomial moments |
| MartingaleFourthMoment | Fourth-moment bounds for discrete martingale variation: quartic convexity inequality, second moment of quadratic sum bounded by terminal fourth moment |
| GirsanovBounded | Girsanov closure under bounded density: paired probability limit becomes L¹ limit, real integrator is true L² martingale |
| StoppedVariation | Random cutoffs of variation approximations: monotone completed-cell sandwich, evaluation at bounded random cutoff without path regularity |
| ZeroBracket | Vanishing of continuous local martingale on zero-bracket paths: exponential bounds force square moment to vanish, continuity makes it simultaneous |

**Stage F** — Girsanov applications → Black-Scholes, depends on Stages A + E.

| File | Description |
|---|---|
| GirsanovCrossVariation | Mixed-variation stopping: L⁴ martingale estimates upgrade deterministic cross sums to L¹ compensated products |
| StoppedCrossVariation | Cross-variation under continuous stopping: first process stopped, second on deterministic grids |
| GirsanovLocalization | Polynomial moment control from terminally stopped brackets, enabling bounded-density closure |
| GirsanovExits | Bounded path exits for the predictable Girsanov closure |
| GirsanovTheorem | Predictable Girsanov theorem: Novikov UI removes bounded exits, characteristic functions identify the shifted measure |
| GirsanovFiltered | Girsanov in an arbitrary Brownian filtration: adaptedness + independent increments suffice |
| GirsanovRegression | Constant-coefficient Girsanov regression: exact identities for every real coefficient and finite horizon |
| BlackScholes | Black-Scholes call pricing: Gaussian CDF calculation + SDE derivation via Girsanov measure change, merged from BlackScholes + BlackScholesSDE |


