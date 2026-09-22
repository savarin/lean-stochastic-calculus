# Library guide

Per-file descriptions organized by dependency layer.

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
| ItoProcess | Natural Itô integral as a time-indexed L² process: predictable time restriction, representative selection, martingale property |

**Stage B** — Quadratic variation, depends on Stage A.

| File | Description |
|---|---|
| TendstoInMeasureAlgebra | Convergence in measure for real sequences: sums, fixed and constant multiples, comparison, without measurability side conditions |
| UniformPartitionSums | IsBrownianMotion abbreviation, the uniform partition of [0,t], quadratic, fourth, cross and total variation sums with their identities and measurability, integrated drift |
| QuadraticVariationContract | Quadratic variation in L² and in probability at a fixed time; closure under a.e. modification, zero-variation sums, time-constant multiples, stopping |
| QuadraticVariation | Quadratic variation ⟨B⟩\_t = t in L² and in probability: stopped, time-changed and block versions, covariation of stopped and interval Brownian blocks |
| QuadraticVariationElementary | Exact bracket for finite sums of adapted Brownian blocks: clipped-interval covariation, predictable bracket ∫σ² ds for finitely supported integrands |
| QuadraticVariationDensity | Extension of exact bracket to all predictable L² integrands: uniform L¹ perturbation estimates, convergence-together, change of variables to displayed diffusion |

**Stage C** — Itô formula, depends on Stage B.

| File | Description |
|---|---|
| ItoFormula | Taylor partition sums along Brownian paths: Taylor remainder with uniform compact bounds, convergence of derivative-weighted increment sums, left Riemann sums, and quadratic-variation-controlled remainders along uniform partitions |
| ItoMaximal | Doob's maximal inequality for Itô integrals: conditional Jensen for L² submartingales, grid-independent finite-time bounds |
| QuadraticVariationTightness | Tail-transfer lemma: terminal QV convergence in measure implies uniform probability control for weighted bracket arguments |
| QuadraticVariationGrid | Quadratic variation on a common rational grid: prefix sums, rescaling identity, coherent-process convergence along common refinements |
| TightProduct | Vanishing-error localization: a random error vanishing in measure stays negligible after multiplication by an eventually tight nonneg control |
| ItoFormulaPartition | General Itô formula f(t,X\_t): exact partition reduction into dt/dX/d⟨X⟩ sums plus remainder, uniform Taylor bounds on rectangles, continuous modifications and their variation sums |
| ItoFormulaGeneral | Continuous modifications of natural Itô processes: Doob's compact-time L² bound, fast-converging modification limits, existence of a continuous modification with before-stop quadratic variation |
| WeightedBracketRiemann | Weighted bracket Riemann sums: continuous weights integrated against ⟨X⟩ via uniform half-open partitions, closing diffusion-weighted QV for natural Itô integrals |

**Stage D** — Exponential martingales, depends on Stage C.

| File | Description |
|---|---|
| LocalMartingaleContract | Local martingales via Mathlib's Locally predicate and the quadratic-variation contracts in probability: fixed-time, before-stop, stopped, with pre-Brownian instances |
| ContinuousExitTime | Continuous exit times: dyadic hitting times of a closed ball's complement, their limit as a stopping time, global exit sequences localizing a continuous process |
| ElementaryMartingaleIntegral | Elementary martingale integrals on one interval: continuity, adaptedness, martingality, orthogonal increments, martingale property through L¹ and in-measure limits |
| LocalizingStoppedProcess | Localized stopped processes behind Mathlib's local properties, the local quadratic-variation contract with a common localizer, bounds at continuous exits |
| PartitionStoppingTime | Partition-valued stopping times: first grid index after a bounded rule, martingality of bounded stopped and localized processes, convergence through uniform approximation |
| MartingaleLeftSum | Left sums against a martingale: finite elementary integrals, the uniformly adapted left-sum process, terminal L² bounds, double localization at continuous exits |
| DoleansDadeExponential | Doléans-Dade exponential ε(M)\_t = exp(M\_t − ½⟨M⟩\_t): capped version, integral candidate, left-sum processes, Stieltjes bracket integral, Taylor expansion of the logarithm |
| DoleansDadeMartingale | Martingality of the stochastic exponential: Itô expansion of exp on the compensated logarithm, left sums converge to the candidate, martingale at paired exits |
| DoleansDade | Exponential martingales of centered Gaussian increments, the Brownian specialization in its natural filtration, and the exponential of a constant multiple of Brownian motion |
| GeometricBrownianMotion | Geometric Brownian motion exp((μ−σ²/2)t + σB\_t): linear SDE identity via time-dependent Itô formula, L² uniqueness of strong solutions |
| GBMGronwall | Integral Grönwall for localized moment profiles: nonneg integrable function controlled by its own time integral vanishes |
| NovikovCondition | Novikov's condition E[exp(½⟨M⟩\_T)] < ∞, deterministic and earlier-time cases, deterministic stopping of martingales, uniform integrability on bounded intervals, nonnegative local martingales |
| Novikov | Novikov's theorem: Kazamaki's condition, uniform integrability from uniform Lᵖ bounds, scaling trick, stopped stochastic exponential is a uniformly integrable martingale with expectation one |

**Stage E** — Girsanov core, depends on Stages B–D.

| File | Description |
|---|---|
| GBMLocalization | Localization of linear SDE: dyadic sampled exits approximate bounded path-exit coefficient under original measure |
| CrossVariationProcess | Cross-variation contract in probability, fixed-time convergence of pre-Brownian evaluations, closure of convergence in measure under continuous maps and complex scalars |
| GirsanovMeasure | Terminal density Z\_T from Doléans-Dade, the measure Z\_T·P, integrated and regularised drift, shifted driver, GirsanovDensityData with its first consequences |
| GirsanovMartingaleTransform | Banach-valued elementary and uniformly adapted martingale transforms, prefix and stopped cross-variation sums along common refinements |
| GirsanovCommonRefinement | Block cross-variation sums, maximal complex step error along common refinements, martingale closure under in-measure limits with uniform integrability, fourth-moment block oscillation bounds |
| GirsanovFourierIncrement | Brownian Fourier increments and their martingale property, the complex combination M + icB with bracket, the complex Doléans-Dade exponential, freezing-density tightness |
| GirsanovComplexEuler | Capped complex Girsanov exponential and Euler processes, second-order residual bound, weighted bracket, quadratic, cross and higher-order residual sums |
| GirsanovMeshControl | Fourth-variation and maximal-increment mesh controls, stopped mesh controls of the complex combination and its bracket, total-variation approximations of the drift |
| GirsanovStoppedControl | Stopped density left maximum, stopped weight control, compensated square control, stopped variation control, higher-order vanishing and tight controls |
| Girsanov | Girsanov theorem endpoint: Euler residual identity, integrability of the stopped complex Doléans-Dade combination, Fourier-increment martingale conditions, shifted driver pre-Brownian under Z\_T·P |
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
| BrownianContinuousVersion | Version of a Brownian motion with every path continuous and starting at zero: one measurable null set replaced by the zero path, strongly measurable slices, almost-sure agreement at fixed times |
| GirsanovConstantDrift | Constant-drift Girsanov through the predictable theorem: stopped scaled driver as the continuous martingale, deterministic bracket, Novikov automatic; equivalence and probability of the exact terminal density measure |
| GirsanovItoData | Girsanov density data from a predictable L² integrand with a free bracket representative and almost-everywhere modification field; the constant integrand instantiates it on the continuous version of the driver |
| BlackScholes | Black-Scholes call pricing: Gaussian CDF calculation + SDE derivation via the dynamic Girsanov measure change at the market price of risk |
