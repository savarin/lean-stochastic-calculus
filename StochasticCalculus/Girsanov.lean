/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.Novikov
import StochasticCalculus.QuadraticVariation
import StochasticCalculus.QuadraticVariationDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian

/-!
# Girsanov change of measure

This file begins the predictable-integrand Girsanov theorem by constructing
the terminal change of measure from the Doléans--Dade exponential.  The
definition is the unnormalised density `Z_T · P`, rather than an abstract or
existentially chosen probability measure.  Novikov's theorem supplies the
missing normalization `∫ Z_T dP = 1`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- Enlarging a filtration enlarges its predictable sigma-algebra. -/
theorem Filtration.predictable_mono
    {W I : Type*} [MeasurableSpace W] [Preorder I] [OrderBot I]
    {V U : Filtration I ‹MeasurableSpace W›} (hVU : V ≤ U) :
    V.predictable ≤ U.predictable := by
  apply MeasurableSpace.generateFrom_le
  rintro A (⟨S, hS, rfl⟩ | ⟨t, S, hS, rfl⟩)
  · exact MeasurableSpace.measurableSet_generateFrom
      (Or.inl ⟨S, hVU ⊥ S hS, rfl⟩)
  · exact MeasurableSpace.measurableSet_generateFrom
      (Or.inr ⟨t, S, hVU t S hS, rfl⟩)

/-- Strong adaptation is monotone under enlargement of the filtration. -/
theorem StronglyAdapted.mono_filtration
    {W I : Type*} [MeasurableSpace W] [Preorder I]
    {E : I → Type*} [∀ t, TopologicalSpace (E t)]
    {V U : Filtration I ‹MeasurableSpace W›} {X : ∀ t, W → E t}
    (hX : StronglyAdapted V X) (hVU : V ≤ U) : StronglyAdapted U X :=
  fun t ↦ (hX t).mono (hVU t)

/-- Strong predictability is monotone under enlargement of the filtration. -/
theorem IsStronglyPredictable.mono_filtration
    {W I E : Type*} [MeasurableSpace W] [Preorder I] [OrderBot I]
    [TopologicalSpace E]
    {V U : Filtration I ‹MeasurableSpace W›} {X : I → W → E}
    (hX : IsStronglyPredictable V X) (hVU : V ≤ U) :
    IsStronglyPredictable U X :=
  hX.mono (Filtration.predictable_mono hVU)

/-- A strongly predictable real process on nonnegative time is jointly
measurable for the ambient product measurable space. -/
theorem IsStronglyPredictable.measurable_uncurry_nnreal
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {theta : ℝ≥0 → W → ℝ}
    (h : IsStronglyPredictable V theta) :
    Measurable (Function.uncurry theta) := by
  apply (h.mono ?_).measurable
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (V.le 0 A hA)
  · intro i A hA
    exact measurableSet_Ioi.prod (V.le i A hA)

/-- Convergence in probability is preserved by an integrable real density.
This is the sequential absolute-continuity fact needed to transport
pathwise quadratic-variation limits across a Girsanov measure. -/
theorem TendstoInMeasure.withDensity_of_integrable_real
    {W I E : Type*} [MeasurableSpace W] [EDist E]
    {P : Measure W} [SFinite P]
    {X : I → W → E} {l : Filter I} {x : W → E}
    {Z : W → ℝ} (hZ : Integrable Z P)
    (h : TendstoInMeasure P X l x) :
    TendstoInMeasure (P.withDensity fun omega => ENNReal.ofReal (Z omega))
      X l x := by
  intro epsilon hepsilon
  simp_rw [withDensity_apply']
  exact tendsto_setLIntegral_zero (ne_of_lt hZ.lintegral_lt_top)
    (h epsilon hepsilon)

/-- A real random variable whose moment-generating function is Gaussian has
the corresponding Gaussian law. -/
theorem hasLaw_gaussianReal_of_mgf_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {X : W → ℝ} (hX : AEMeasurable X P) (m : ℝ) (v : ℝ≥0)
    (hmgf : mgf X P = mgf id (gaussianReal m v)) :
    HasLaw X (gaussianReal m v) P := by
  have heqOn := eqOn_complexMGF_of_mgf hmgf.symm
  have hcomplex : complexMGF id (gaussianReal m v) = complexMGF X P := by
    funext z
    apply heqOn
    simp only [integrableExpSet_id_gaussianReal, interior_univ, Set.mem_univ,
      Set.ofPred_true]
  refine ⟨hX, ?_⟩
  have hmap := Measure.ext_of_complexMGF_eq aemeasurable_id hX hcomplex
  simpa only [Measure.map_id] using hmap.symm

/-- A finite measure and a scalar multiple of a Gaussian measure are equal
after mapping when they have the same moment-generating function and mass.
This non-normalized form is needed for laws restricted to past events. -/
theorem map_eq_smul_gaussianReal_of_mgf_eq
    {W : Type*} [MeasurableSpace W] {mu : Measure W} [IsFiniteMeasure mu]
    {X : W → ℝ} (hX : AEMeasurable X mu) (m : ℝ) (v : ℝ≥0)
    (a : ℝ≥0∞) (ha : a ≠ ∞) (hmass : mu Set.univ = a)
    (hmgf : mgf X mu = mgf id (a • gaussianReal m v)) :
    mu.map X = a • gaussianReal m v := by
  by_cases ha0 : a = 0
  · have hmu0 : mu = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact hmass.trans ha0
    simp [hmu0, ha0]
  have hmu0 : mu ≠ 0 := by
    intro hzero
    have : a = 0 := by simpa [hzero] using hmass.symm
    exact ha0 this
  have htarget0 : a • gaussianReal m v ≠ 0 := by
    simp only [ne_eq, Measure.ennreal_smul_eq_zero, ha0, false_or]
    exact IsProbabilityMeasure.ne_zero (gaussianReal m v)
  have hzero : mu = 0 ↔ a • gaussianReal m v = 0 :=
    ⟨fun h ↦ (hmu0 h).elim, fun h ↦ (htarget0 h).elim⟩
  have htargetSet :
      integrableExpSet id (a • gaussianReal m v) = Set.univ := by
    ext c
    simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (integrable_exp_mul_gaussianReal c).smul_measure ha
  have hsourceSet : integrableExpSet X mu = Set.univ := by
    rw [integrableExpSet_eq_of_mgf' hmgf hzero, htargetSet]
  have heqOn := eqOn_complexMGF_of_mgf' hmgf hzero
  have hcomplex : complexMGF X mu =
      complexMGF id (a • gaussianReal m v) := by
    funext z
    apply heqOn
    rw [hsourceSet]
    simp
  let : IsFiniteMeasure (a • gaussianReal m v) :=
    (gaussianReal m v).smul_finite ha
  have hmap := Measure.ext_of_complexMGF_eq hX aemeasurable_id hcomplex
  simpa only [Measure.map_id] using hmap

/-- The one-dimensional-law half of Lévy's characterization: if every
scaled stochastic exponential of `X_t` has expectation one, then `X_t` is
centered Gaussian with variance `t`. -/
theorem hasLaw_gaussianReal_of_scaledExponential_integral_eq_one
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {X : ℝ≥0 → W → ℝ}
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (t : ℝ≥0)
    (hexp : ∀ c : ℝ,
      (∫ omega, Real.exp (c * X t omega - c ^ 2 * (t : ℝ) / 2) ∂P) = 1) :
    HasLaw (X t) (gaussianReal 0 t) P := by
  apply hasLaw_gaussianReal_of_mgf_eq (hXmeas t) 0 t
  rw [mgf_id_gaussianReal]
  funext c
  have hfactor : (fun omega ↦ Real.exp (c * X t omega)) =
      fun omega ↦ Real.exp (c ^ 2 * (t : ℝ) / 2) *
        Real.exp (c * X t omega - c ^ 2 * (t : ℝ) / 2) := by
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mgf, hfactor, integral_const_mul, hexp c, mul_one]
  congr 1
  ring

/-- A centered Gaussian law gives the sharp sub-Gaussian moment bound. -/
theorem HasLaw.hasSubgaussianMGF_gaussianReal_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : W → ℝ} {v : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P) :
    HasSubgaussianMGF X v P where
  integrable_exp_mul c := by
    have hi := integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := v) c
    rw [← h.map_eq] at hi
    exact hi.comp_aemeasurable h.aemeasurable
  mgf_le c := by
    rw [mgf_gaussianReal h.map_eq c]
    norm_num

/-- The marginal-law half of Lévy's characterization obtained directly
from the robust local quadratic-variation contract and Novikov's theorem. -/
theorem HasLocalQuadraticVariationProcessInProbability.hasLaw_gaussianReal_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0)
    (t : ℝ≥0) : HasLaw (X t) (gaussianReal 0 t) P := by
  apply hasLaw_gaussianReal_of_scaledExponential_integral_eq_one
    (fun s ↦ ((hadapt s).mono (𝒱.le s)).aemeasurable) t
  intro c
  let bracketC : ℝ≥0 → W → ℝ := fun s _omega ↦ c ^ 2 * (s : ℝ)
  have hN : NovikovCondition bracketC P t :=
    novikovCondition_deterministic (fun s : ℝ≥0 ↦ c ^ 2 * (s : ℝ)) t
  have hlocalC : HasLocalQuadraticVariationProcessInProbability
      (fun s omega ↦ c * X s omega) bracketC 𝒱 P := by
    simpa only [bracketC] using hlocal.const_mul c
  have hcontC (omega : W) : Continuous (fun s ↦ c * X s omega) :=
    continuous_const.mul (hcont omega)
  have hadaptC : StronglyAdapted 𝒱 (fun s omega ↦ c * X s omega) := by
    intro s
    exact stronglyMeasurable_const.mul (hadapt s)
  have hbracketAdaptC : StronglyAdapted 𝒱 bracketC := by
    intro s
    exact stronglyMeasurable_const
  have hbracketPathC (omega : W) :
      Continuous (fun s ↦ bracketC s omega) ∧
        Monotone (fun s ↦ bracketC s omega) := by
    refine ⟨continuous_const.mul continuous_subtype_val, ?_⟩
    intro a b hab
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    exact_mod_cast hab
  have h := hN.integral_doleansDade_eq_one_of_le hlocalC hcontC
    hadaptC hbracketAdaptC hbracketPathC
    (fun omega ↦ by rw [hzero omega, mul_zero])
    (fun _omega ↦ by simp [bracketC]) (le_refl t)
  rw [show (fun omega ↦ Real.exp
      (c * X t omega - c ^ 2 * (t : ℝ) / 2)) =
      fun omega ↦ doleansDadeExponential
        (fun s omega ↦ c * X s omega) bracketC t omega by
    funext omega
    simp only [doleansDadeExponential, doleansDadeLog, bracketC]
    congr 1
    ring]
  exact h

/-- Every scaled stochastic exponential of a continuous local martingale
with deterministic clock bracket is a true finite-horizon martingale. -/
theorem HasLocalQuadraticVariationProcessInProbability.martingale_scaledExponential_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0)
    (c : ℝ) (T : ℝ≥0) :
    Martingale (fun t omega ↦ Real.exp
      (c * X (min t T) omega - c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2)) 𝒱 P := by
  let bracketC : ℝ≥0 → W → ℝ := fun s _omega ↦ c ^ 2 * (s : ℝ)
  have hN : NovikovCondition bracketC P T :=
    novikovCondition_deterministic (fun s : ℝ≥0 ↦ c ^ 2 * (s : ℝ)) T
  have hlocalC : HasLocalQuadraticVariationProcessInProbability
      (fun s omega ↦ c * X s omega) bracketC 𝒱 P := by
    simpa only [bracketC] using hlocal.const_mul c
  have hcontC (omega : W) : Continuous (fun s ↦ c * X s omega) :=
    continuous_const.mul (hcont omega)
  have hadaptC : StronglyAdapted 𝒱 (fun s omega ↦ c * X s omega) := by
    intro s
    exact stronglyMeasurable_const.mul (hadapt s)
  have hbracketAdaptC : StronglyAdapted 𝒱 bracketC := by
    intro s
    exact stronglyMeasurable_const
  have hbracketPathC (omega : W) :
      Continuous (fun s ↦ bracketC s omega) ∧
        Monotone (fun s ↦ bracketC s omega) := by
    refine ⟨continuous_const.mul continuous_subtype_val, ?_⟩
    intro a b hab
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    exact_mod_cast hab
  have hmart := hN.martingale_stopAt_doleansDade hlocalC hcontC
    hadaptC hbracketAdaptC hbracketPathC
    (fun omega ↦ by rw [hzero omega, mul_zero])
    (fun _omega ↦ by simp [bracketC])
  convert hmart using 1
  funext t omega
  simp only [doleansDadeExponential, doleansDadeLog, bracketC]
  congr 1
  ring

/-- Conditional exponential moments of an increment factor over every event
in the past filtration.  This is the conditional-law core of Lévy's
characterization. -/
theorem setIntegral_exp_increment_eq_of_scaledExponential_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {X : ℝ≥0 → W → ℝ} (hadapt : StronglyAdapted 𝒱 X)
    (hlaw : ∀ u, HasLaw (X u) (gaussianReal 0 u) P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hexp : ∀ c : ℝ, Martingale (fun u omega ↦
      Real.exp (c * X (min u t) omega - c ^ 2 * ((min u t : ℝ≥0) : ℝ) / 2)) 𝒱 P)
    {A : Set W} (hA : MeasurableSet[𝒱 s] A) (c : ℝ) :
    (∫ omega in A, Real.exp (c * (X t omega - X s omega)) ∂P) =
      P.real A * Real.exp (((t : ℝ) - (s : ℝ)) * c ^ 2 / 2) := by
  let Z : ℝ≥0 → W → ℝ := fun u omega ↦
    Real.exp (c * X (min u t) omega - c ^ 2 * ((min u t : ℝ≥0) : ℝ) / 2)
  let L : W → ℝ := fun omega ↦
    Real.exp (-c * X s omega + c ^ 2 * (t : ℝ) / 2)
  have hincSG : HasSubgaussianMGF
      (fun omega ↦ X t omega - X s omega) ((t.sqrt + s.sqrt) ^ 2) P := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      (HasLaw.hasSubgaussianMGF_gaussianReal_zero (hlaw t)).add
        (HasLaw.hasSubgaussianMGF_gaussianReal_zero (hlaw s)).neg
  have hincInt : Integrable
      (fun omega ↦ Real.exp (c * (X t omega - X s omega))) P :=
    hincSG.integrable_exp_mul c
  have hL : StronglyMeasurable[𝒱 s] L := by
    apply Real.continuous_exp.comp_stronglyMeasurable
    have hcx : StronglyMeasurable[𝒱 s] (fun omega ↦ c * X s omega) :=
      stronglyMeasurable_const.mul (hadapt s)
    have hcst : StronglyMeasurable[𝒱 s]
        (fun _omega : W ↦ c ^ 2 * (t : ℝ) / 2) := stronglyMeasurable_const
    convert hcx.neg.add hcst using 1
    funext omega
    simp only [Pi.neg_apply, Pi.add_apply]
    ring
  have hprodInt : Integrable (fun omega ↦ L omega * Z t omega) P := by
    apply hincInt.congr
    exact Filter.Eventually.of_forall fun omega ↦ by
      simp only [L, Z, min_self]
      rw [← Real.exp_add]
      congr 1
      ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hL hprodInt
    ((hexp c).integrable t)
  have hcond := (hexp c).condExp_ae_eq hst
  have hA0 : MeasurableSet A := 𝒱.le s A hA
  calc
    (∫ omega in A, Real.exp (c * (X t omega - X s omega)) ∂P) =
        ∫ omega in A, L omega * Z t omega ∂P := by
      apply setIntegral_congr_fun hA0
      intro omega _
      simp only [L, Z, min_self]
      rw [← Real.exp_add]
      congr 1
      ring
    _ = ∫ omega in A, P[fun w ↦ L w * Z t w | 𝒱 s] omega ∂P := by
      symm
      exact setIntegral_condExp (𝒱.le s) hprodInt hA
    _ = ∫ omega in A, L omega * P[Z t | 𝒱 s] omega ∂P := by
      apply setIntegral_congr_ae hA0
      filter_upwards [hpull] with omega hp _
      exact hp
    _ = ∫ _omega in A, Real.exp (((t : ℝ) - (s : ℝ)) * c ^ 2 / 2) ∂P := by
      apply setIntegral_congr_ae hA0
      filter_upwards [hcond] with omega hc _
      rw [hc]
      simp only [L, min_eq_left hst]
      rw [← Real.exp_add]
      congr 1
      ring
    _ = P.real A * Real.exp (((t : ℝ) - (s : ℝ)) * c ^ 2 / 2) := by
      rw [setIntegral_const, smul_eq_mul]

/-- The clock-bracket contract determines conditional increment moment
generating functions on all past events. -/
theorem HasLocalQuadraticVariationProcessInProbability.setIntegral_exp_increment_eq_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set W}
    (hA : MeasurableSet[𝒱 s] A) (c : ℝ) :
    (∫ omega in A, Real.exp (c * (X t omega - X s omega)) ∂P) =
      P.real A * Real.exp (((t : ℝ) - (s : ℝ)) * c ^ 2 / 2) := by
  apply setIntegral_exp_increment_eq_of_scaledExponential_martingale hadapt
    (fun u ↦ HasLocalQuadraticVariationProcessInProbability.hasLaw_gaussianReal_clock
      hlocal hcont hadapt hzero u) hst
    (fun d ↦ HasLocalQuadraticVariationProcessInProbability.martingale_scaledExponential_clock
      hlocal hcont hadapt hzero d t)
    hA c

/-- Restricted to any past event, a future increment has the corresponding
scalar multiple of its centered Gaussian law. -/
theorem HasLocalQuadraticVariationProcessInProbability.map_restrict_increment_eq_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set W}
    (hA : MeasurableSet[𝒱 s] A) :
    (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
      P A • gaussianReal 0 (t - s) := by
  have hinc : AEMeasurable (fun omega ↦ X t omega - X s omega) P :=
    (((hadapt t).mono (𝒱.le t)).aemeasurable).sub
      (((hadapt s).mono (𝒱.le s)).aemeasurable)
  have hincR : AEMeasurable (fun omega ↦ X t omega - X s omega)
      (P.restrict A) := hinc.mono_measure Measure.restrict_le_self
  apply map_eq_smul_gaussianReal_of_mgf_eq hincR 0 (t - s) (P A)
    (measure_ne_top P A)
  · rw [Measure.restrict_apply_univ]
  · funext c
    rw [mgf_smul_measure, mgf_id_gaussianReal]
    change (∫ omega in A, Real.exp (c * (X t omega - X s omega)) ∂P) = _
    rw [HasLocalQuadraticVariationProcessInProbability.setIntegral_exp_increment_eq_clock
      hlocal hcont hadapt hzero hst hA c]
    simp only [measureReal_def, zero_mul, zero_add]
    congr 2
    rw [NNReal.coe_sub hst]

/-- Every future increment is independent of the current filtration. -/
theorem HasLocalQuadraticVariationProcessInProbability.indep_increment_filtration_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (𝒱 s) (MeasurableSpace.comap
      (fun omega ↦ X t omega - X s omega) inferInstance) P := by
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc P :=
    (((hadapt t).mono (𝒱.le t)).aemeasurable).sub
      (((hadapt s).mono (𝒱.le s)).aemeasurable)
  have hmapU : P.map inc = gaussianReal 0 (t - s) := by
    have h := HasLocalQuadraticVariationProcessInProbability.map_restrict_increment_eq_clock
      hlocal hcont hadapt hzero hst (A := Set.univ) MeasurableSet.univ
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using h
  apply indep_comap_of_bcf (𝒱.le s) hinc
  intro A hA f
  have hincR : AEMeasurable inc (P.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  have hmapA :=
    HasLocalQuadraticVariationProcessInProbability.map_restrict_increment_eq_clock
      hlocal hcont hadapt hzero hst hA
  calc
    (∫ omega in A, f (inc omega) ∂P) =
        ∫ x, f x ∂((P.restrict A).map inc) := by
      rw [integral_map hincR f.continuous.measurable.aestronglyMeasurable]
    _ = ∫ x, f x ∂(P A • gaussianReal 0 (t - s)) := by rw [hmapA]
    _ = P.real A * ∫ x, f x ∂(gaussianReal 0 (t - s)) := by
      rw [integral_smul_measure, smul_eq_mul, measureReal_def]
    _ = P.real A * ∫ omega, f (inc omega) ∂P := by
      congr 1
      rw [← hmapU, integral_map hinc f.continuous.measurable.aestronglyMeasurable]

/-- Clock bracket plus the continuous local-martingale contract yields
independent increments. -/
theorem HasLocalQuadraticVariationProcessInProbability.hasIndepIncrements_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0) :
    HasIndepIncrements X P := by
  intro n times htimes
  let Y : Fin n → W → ℝ := fun i omega ↦
    X (times i.succ) omega - X (times i.castSucc) omega
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
      have ha : a ∉ S := by
        intro haS
        exact (lt_irrefl a) (hmax a haS)
      have hprev : MeasurableSet[𝒱 (times a.castSucc)]
          (⋂ i ∈ S, Y i ⁻¹' sets i) := by
        apply S.measurableSet_biInter
        intro i hi
        have hiright : i.succ ≤ a.castSucc := by
          apply Fin.mk_le_mk.mpr
          have hia := hmax i hi
          omega
        have hleft : i.castSucc ≤ i.succ := Fin.castSucc_le_succ i
        have hYi : StronglyMeasurable[𝒱 (times i.succ)] (Y i) := by
          exact (hadapt (times i.succ)).sub
            ((hadapt (times i.castSucc)).mono (𝒱.mono (htimes hleft)))
        exact (hYi.mono (𝒱.mono (htimes hiright))).measurable
          (hsets i (by simp [hi]))
      have hcurr : MeasurableSet[MeasurableSpace.comap (Y a) inferInstance]
          (Y a ⁻¹' sets a) :=
        (hsets a (by simp)).preimage (comap_measurable (Y a))
      have hindep :=
        HasLocalQuadraticVariationProcessInProbability.indep_increment_filtration_clock
          hlocal hcont hadapt hzero (htimes (Fin.castSucc_le_succ a))
      have hfactor :=
        (hindep.indepSet_of_measurableSet hprev hcurr).measure_inter_eq_mul
      rw [Finset.set_biInter_insert, Finset.prod_insert ha, Set.inter_comm,
        hfactor, ih (fun i hi ↦ hsets i (by simp [hi]))]
      exact mul_comm _ _

/-- Lévy's characterization in the robust common-localizer formulation:
a continuous adapted local martingale starting at zero whose bracket is the
deterministic clock is a pre-Brownian motion. -/
theorem HasLocalQuadraticVariationProcessInProbability.isPreBrownianReal_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hadapt : StronglyAdapted 𝒱 X)
    (hzero : ∀ omega, X 0 omega = 0) :
    IsPreBrownianReal X P := by
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · exact fun t ↦ HasLocalQuadraticVariationProcessInProbability.hasLaw_gaussianReal_clock
      hlocal hcont hadapt hzero t
  · exact HasLocalQuadraticVariationProcessInProbability.hasIndepIncrements_clock
      hlocal hcont hadapt hzero

/-- If all future increments restricted to past events have their
mass-scaled Gaussian laws, then each increment is independent of the current
filtration. -/
theorem indep_increment_filtration_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (V s) (MeasurableSpace.comap
      (fun omega ↦ X t omega - X s omega) inferInstance) P := by
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc P :=
    (((hadapt t).mono (V.le t)).aemeasurable).sub
      (((hadapt s).mono (V.le s)).aemeasurable)
  have hmapU : P.map inc = gaussianReal 0 (t - s) := by
    have h := hrestricted hst (A := Set.univ) MeasurableSet.univ
    simpa only [inc, Measure.restrict_univ, measure_univ, one_smul] using h
  apply indep_comap_of_bcf (V.le s) hinc
  intro A hA f
  have hincR : AEMeasurable inc (P.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  have hmapA := hrestricted hst hA
  calc
    (∫ omega in A, f (inc omega) ∂P) =
        ∫ x, f x ∂((P.restrict A).map inc) := by
      rw [integral_map hincR f.continuous.measurable.aestronglyMeasurable]
    _ = ∫ x, f x ∂(P A • gaussianReal 0 (t - s)) := by
      simpa only [inc] using congrArg (fun mu ↦ ∫ x, f x ∂mu) hmapA
    _ = P.real A * ∫ x, f x ∂(gaussianReal 0 (t - s)) := by
      rw [integral_smul_measure, smul_eq_mul, measureReal_def]
    _ = P.real A * ∫ omega, f (inc omega) ∂P := by
      congr 1
      rw [← hmapU, integral_map hinc f.continuous.measurable.aestronglyMeasurable]

/-- Past-event Gaussian increment laws imply independent increments. -/
theorem hasIndepIncrements_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    HasIndepIncrements X P := by
  intro n times htimes
  let Y : Fin n → W → ℝ := fun i omega ↦
    X (times i.succ) omega - X (times i.castSucc) omega
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
      have ha : a ∉ S := by
        intro haS
        exact (lt_irrefl a) (hmax a haS)
      have hprev : MeasurableSet[V (times a.castSucc)]
          (⋂ i ∈ S, Y i ⁻¹' sets i) := by
        apply S.measurableSet_biInter
        intro i hi
        have hiright : i.succ ≤ a.castSucc := by
          apply Fin.mk_le_mk.mpr
          have hia := hmax i hi
          omega
        have hleft : i.castSucc ≤ i.succ := Fin.castSucc_le_succ i
        have hYi : StronglyMeasurable[V (times i.succ)] (Y i) := by
          exact (hadapt (times i.succ)).sub
            ((hadapt (times i.castSucc)).mono (V.mono (htimes hleft)))
        exact (hYi.mono (V.mono (htimes hiright))).measurable
          (hsets i (by simp [hi]))
      have hcurr : MeasurableSet[MeasurableSpace.comap (Y a) inferInstance]
          (Y a ⁻¹' sets a) :=
        (hsets a (by simp)).preimage (comap_measurable (Y a))
      have hindep := indep_increment_filtration_of_map_restrict_increment_eq
        hadapt hrestricted (htimes (Fin.castSucc_le_succ a))
      have hfactor :=
        (hindep.indepSet_of_measurableSet hprev hcurr).measure_inter_eq_mul
      rw [Finset.set_biInter_insert, Finset.prod_insert ha, Set.inter_comm,
        hfactor, ih (fun i hi ↦ hsets i (by simp [hi]))]
      exact mul_comm _ _

/-- A process is pre-Brownian once every future increment, restricted to an
arbitrary event in the current filtration, has the corresponding
mass-scaled centered Gaussian law.  This isolates the probabilistic endpoint
of exponential-martingale proofs of Lévy and Girsanov theorems. -/
theorem isPreBrownianReal_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hzero : ∀ omega, X 0 omega = 0)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    IsPreBrownianReal X P := by
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    have hX : AEMeasurable (X t) P :=
      ((hadapt t).mono (V.le t)).aemeasurable
    refine ⟨hX, ?_⟩
    have h := hrestricted (s := 0) (t := t) (by exact bot_le)
      (A := Set.univ) MeasurableSet.univ
    simpa only [Measure.restrict_univ, hzero, sub_zero, measure_univ,
      one_smul, tsub_zero] using h
  · exact hasIndepIncrements_of_map_restrict_increment_eq hadapt hrestricted

/-- Almost-sure normalization variant of the past-event Gaussian increment
criterion.  Subtracting the time-zero random variable leaves every increment
unchanged and produces an everywhere normalized representative. -/
theorem isPreBrownianReal_of_map_restrict_increment_eq_of_ae_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    IsPreBrownianReal X P := by
  let Y : ℝ≥0 → W → ℝ := fun t omega ↦ -X 0 omega + X t omega
  have hYadapt : StronglyAdapted V Y := by
    intro t
    exact ((hadapt 0).mono (V.mono bot_le)).neg.add (hadapt t)
  have hYrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ Y t omega - Y s omega) =
          P A • gaussianReal 0 (t - s) := by
    intro s t hst A hA
    have hfun : (fun omega ↦ Y t omega - Y s omega) =
        (fun omega ↦ X t omega - X s omega) := by
      funext omega
      simp only [Y]
      ring
    rw [hfun]
    exact hrestricted hst hA
  have hY := isPreBrownianReal_of_map_restrict_increment_eq hYadapt
    (fun omega ↦ by simp only [Y]; ring) hYrestricted
  apply hY.congr
  intro t
  filter_upwards [hzero] with omega homega
  simp only [Y, homega, neg_zero, zero_add]

/-- A true continuous martingale with deterministic stopped quadratic
variation is Brownian.  This packages the final conversion from the usual
stopped-bracket form to the robust common-localizer form used by the Lévy
characterization above. -/
theorem Martingale.isPreBrownianReal_of_stoppedQuadraticVariation_clock
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hmart : Martingale X 𝒱 P)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hzero : ∀ omega, X 0 omega = 0) :
    IsPreBrownianReal X P := by
  have hbefore : HasQuadraticVariationBeforeStopProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) P :=
    hstopped.toBeforeStop
      (fun t ↦ ((hmart.stronglyAdapted t).mono
        (𝒱.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hcont)
  have hlocal : HasLocalQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) 𝒱 P := by
    have hlocX : localizingStoppedProcess X (fun _ ↦ ⊤) = X := by
      funext t omega
      simp [localizingStoppedProcess]
    have hlocClock : localizingStoppedProcess
        (fun t (_omega : W) ↦ (t : ℝ)) (fun _ ↦ ⊤) =
          (fun (t : ℝ≥0) (_omega : W) ↦ (t : ℝ)) := by
      funext t omega
      simp [localizingStoppedProcess]
    refine ⟨fun _ _ ↦ ⊤, isLocalizingSequence_const_top _ _, ?_, ?_⟩
    · intro k
      rw [hlocX]
      exact hmart
    · intro k
      rw [hlocX, hlocClock]
      exact hbefore
  exact hlocal.isPreBrownianReal_clock hcont hmart.stronglyAdapted hzero

/-- Almost-sure normalization variant of the martingale Lévy endpoint.
Subtracting the time-constant initial value produces an everywhere-normalized
version without changing any stopped quadratic-variation sum. -/
theorem Martingale.isPreBrownianReal_of_stoppedQuadraticVariation_clock_of_ae_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hmart : Martingale X 𝒱 P)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability X
      (fun t _omega ↦ (t : ℝ)) P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0) :
    IsPreBrownianReal X P := by
  let Y : ℝ≥0 → W → ℝ := fun t omega ↦ -X 0 omega + X t omega
  have hconst : Martingale (fun _ ↦ -X 0) 𝒱 P :=
    martingale_const_fun 𝒱 P (hmart.stronglyAdapted 0).neg
      (hmart.integrable 0).neg
  have hYmart : Martingale Y 𝒱 P := hconst.add hmart
  have hYstopped : HasStoppedQuadraticVariationProcessInProbability Y
      (fun t _omega ↦ (t : ℝ)) P := by
    intro T a
    apply (hstopped T a).congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      exact (quadraticVariationApprox_add_timeConstant
        (fun s omega ↦ X (min s a) omega) (fun omega ↦ -X 0 omega)
        T (n + 1) omega).symm
  have hYcont : ∀ omega, Continuous (fun t ↦ Y t omega) := fun omega ↦
    continuous_const.add (hcont omega)
  have hYzero : ∀ omega, Y 0 omega = 0 := fun omega ↦ by
    simp only [Y]
    ring
  have hYpre := Martingale.isPreBrownianReal_of_stoppedQuadraticVariation_clock
    hYmart hYstopped hYcont hYzero
  apply hYpre.congr
  intro t
  filter_upwards [hzero] with omega homega
  simp only [Y, homega, neg_zero, zero_add]

/-- Process-valued quadratic covariation along uniform partitions. -/
def HasCrossVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (X Y covariation : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ t, TendstoInMeasure P
    (fun n ↦ quadraticCovariationApprox X Y t (n + 1))
    Filter.atTop (covariation t)

/-- A quadratic-variation process is its own cross-variation process. -/
theorem HasQuadraticVariationProcessInProbability.toCrossVariationSelf
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Q : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationProcessInProbability X Q P) :
    HasCrossVariationProcessInProbability X X Q P := by
  intro t
  apply (h t).congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    unfold quadraticCovariationApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [pow_two]

/-- A robust before-stop covariation contract contains the ordinary
fixed-time covariation contract. -/
theorem HasCrossVariationBeforeStopProcessInProbability.toProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationBeforeStopProcessInProbability X Y C P) :
    HasCrossVariationProcessInProbability X Y C P := by
  intro t
  have hterminal := h t t
  simp only [min_self] at hterminal
  apply hterminal.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    unfold quadraticCovariationBeforeStopApprox quadraticCovariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]

/-- Quadratic variation of a deterministic linear combination, including
the cross term.  This is the process-level polarization rule needed to form
the bracket of `M + c B` in exponential-test proofs of Girsanov's theorem. -/
theorem HasQuadraticVariationProcessInProbability.linearCombination_of_cross
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y qX qY covariation : ℝ≥0 → W → ℝ}
    (hX : HasQuadraticVariationProcessInProbability X qX P)
    (hY : HasQuadraticVariationProcessInProbability Y qY P)
    (hXY : HasCrossVariationProcessInProbability X Y covariation P)
    (c d : ℝ) :
    HasQuadraticVariationProcessInProbability
      (fun t omega ↦ c * X t omega + d * Y t omega)
      (fun t omega ↦ c ^ 2 * qX t omega + d ^ 2 * qY t omega +
        2 * c * d * covariation t omega) P := by
  intro t
  have hqX := (hX t).const_mul_real_noMeas (c ^ 2)
  have hqY := (hY t).const_mul_real_noMeas (d ^ 2)
  have hcross := (hXY t).const_mul_real_noMeas (2 * c * d)
  have htotal := (hqX.add_real_noMeas hqY).add_real_noMeas hcross
  apply htotal.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [quadraticVariationApprox_linearCombination]
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The common-localizer contract and a pre-Brownian driver supply the
fixed-time quadratic variation of every deterministic linear combination.
This is the polarization input for Fourier forms of Girsanov's theorem. -/
theorem
    HasLocalQuadraticVariationProcessInProbability.linearCombination_preBrownian_of_cross
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B covariation : ℝ≥0 → W → ℝ}
    (hM : HasLocalQuadraticVariationProcessInProbability M bracket V P)
    (hB : IsPreBrownianReal B P)
    (hcross : HasCrossVariationProcessInProbability M B covariation P)
    (c d : ℝ) :
    HasQuadraticVariationProcessInProbability
      (fun t omega ↦ c * M t omega + d * B t omega)
      (fun t omega ↦ c ^ 2 * bracket t omega + d ^ 2 * (t : ℝ) +
        2 * c * d * covariation t omega) P := by
  have hBqv : HasQuadraticVariationProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) P :=
    fun t ↦ quadraticVariation_preBrownianReal_inProbability hB t
  exact HasQuadraticVariationProcessInProbability.linearCombination_of_cross
    hM.toProcess hBqv hcross c d

/-- Every pre-Brownian version is stochastically continuous, even though its
sample paths need not be the continuous version.  Chebyshev's inequality and
the exact Gaussian increment variance give the result directly. -/
theorem IsPreBrownianReal.tendstoInMeasure_eval
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n ↦ B (a n)) atTop (B r) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  have haReal : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ)) atTop (nhds (r : ℝ)) :=
    (NNReal.continuous_coe.tendsto r).comp ha
  have hnndist : Tendsto
      (fun n ↦ (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ))
      atTop (nhds 0) := by
    have hnn := haReal.nndist (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (r : ℝ)) atTop (nhds (r : ℝ)))
    have hnn' : Tendsto
        (fun n ↦ nndist ((a n : ℝ≥0) : ℝ) (r : ℝ))
        atTop (nhds 0) := by simpa using hnn
    have hcoe := (NNReal.continuous_coe.tendsto 0).comp hnn'
    change Tendsto
      (fun n ↦ (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ))
      atTop (nhds 0) at hcoe
    exact hcoe
  have hbound : Tendsto
      (fun n ↦ ENNReal.ofReal
        ((nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) / epsilon ^ 2))
      atTop (nhds 0) := by
    have hdiv := hnndist.div_const (epsilon ^ 2)
    have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdiv
    change Tendsto
      (fun n ↦ ENNReal.ofReal
        ((nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) / epsilon ^ 2))
      atTop (nhds (ENNReal.ofReal (0 / epsilon ^ 2))) at hofReal
    simpa using hofReal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbound (fun _ ↦ zero_le) ?_
  intro n
  have hmem : MemLp (B (a n) - B r) 2 P :=
    (hB.hasLaw_sub (a n) r).hasGaussianLaw.memLp_two
  have hmean : ∫ omega, B (a n) omega - B r omega ∂P = 0 := by
    rw [integral_sub (hB.integrable_eval (a n)) (hB.integrable_eval r),
      hB.integral_eval (a n), hB.integral_eval r, sub_zero]
  have hvar : variance (B (a n) - B r) P =
      (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) := by
    rw [(hB.hasLaw_sub (a n) r).variance_eq, variance_id_gaussianReal]
    rfl
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  simpa only [Pi.sub_apply, Real.dist_eq, hmean, sub_zero, hvar] using hcheb

/-- A continuous function of two random variables preserves joint
convergence in measure.  The proof uses the subsequence characterization:
first choose an almost-surely convergent subsequence for the first variable,
then refine it for the second variable. -/
theorem TendstoInMeasure.continuous_comp₂
    {A E F G : Type*} [MeasurableSpace A]
    [MetricSpace E] [MetricSpace F] [MetricSpace G]
    {P : Measure A} [IsFiniteMeasure P]
    {X : ℕ → A → E} {Y : ℕ → A → F}
    {x : A → E} {y : A → F}
    (hXmeas : ∀ n, AEStronglyMeasurable (X n) P)
    (hYmeas : ∀ n, AEStronglyMeasurable (Y n) P)
    (hX : TendstoInMeasure P X atTop x)
    (hY : TendstoInMeasure P Y atTop y)
    {f : E → F → G} (hf : Continuous f.uncurry) :
    TendstoInMeasure P (fun n omega ↦ f (X n omega) (Y n omega)) atTop
      (fun omega ↦ f (x omega) (y omega)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff]
  · intro ns hns
    obtain ⟨ks, hks, hXae⟩ :=
      (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    obtain ⟨ls, hls, hYae⟩ :=
      ((hY.comp hns.tendsto_atTop).comp hks.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ks ∘ ls, hks.comp hls, ?_⟩
    filter_upwards [hXae, hYae] with omega hXomega hYomega
    have hpair : Tendsto (fun i ↦
        (X (ns ((ks ∘ ls) i)) omega, Y (ns ((ks ∘ ls) i)) omega))
        atTop (nhds (x omega, y omega)) := by
      rw [nhds_prod_eq]
      simpa only [Function.comp_apply] using
        (hXomega.comp hls.tendsto_atTop).prodMk hYomega
    change Tendsto (Function.uncurry f ∘ fun i ↦
      (X (ns ((ks ∘ ls) i)) omega, Y (ns ((ks ∘ ls) i)) omega))
      atTop (nhds (Function.uncurry f (x omega, y omega)))
    exact hf.continuousAt.tendsto.comp hpair
  · intro n
    exact hf.comp_aestronglyMeasurable₂ (hXmeas n) (hYmeas n)

/-- A continuous map preserves convergence in measure on a finite measure
space. -/
theorem TendstoInMeasure.continuous_comp
    {A E F : Type*} [MeasurableSpace A] [MetricSpace E] [MetricSpace F]
    {P : Measure A} [IsFiniteMeasure P]
    {X : ℕ → A → E} {x : A → E}
    (hXmeas : ∀ n, AEStronglyMeasurable (X n) P)
    (hX : TendstoInMeasure P X atTop x)
    {f : E → F} (hf : Continuous f) :
    TendstoInMeasure P (fun n omega ↦ f (X n omega)) atTop
      (fun omega ↦ f (x omega)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff]
  · intro ns hns
    obtain ⟨ks, hks, hXae⟩ :=
      (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ks, hks, ?_⟩
    filter_upwards [hXae] with omega hXomega
    exact hf.continuousAt.tendsto.comp hXomega
  · intro n
    exact hf.comp_aestronglyMeasurable (hXmeas n)

/-- Pointwise addition preserves convergence in measure in any seminormed
additive group, without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.add_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y : ι → A → E} {x y : A → E}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega => X i omega + Y i omega) l
      (fun omega => x omega + y omega) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hXhalf := hX (epsilon / 2) hhalf
  have hYhalf := hY (epsilon / 2) hhalf
  have hsum : Tendsto (fun i =>
      P {omega | epsilon / 2 ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)})
      l (nhds 0) := by
    simpa only [add_zero] using hXhalf.add hYhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro i
  calc
    P {omega | epsilon ≤
        dist (X i omega + Y i omega) (x omega + y omega)} ≤
        P ({omega | epsilon / 2 ≤ dist (X i omega) (x omega)} ∪
          {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      change epsilon ≤
        dist (X i omega + Y i omega) (x omega + y omega) at homega
      by_contra hunion
      have hXsmall : dist (X i omega) (x omega) < epsilon / 2 :=
        lt_of_not_ge (fun hbad => hunion (Or.inl hbad))
      have hYsmall : dist (Y i omega) (y omega) < epsilon / 2 :=
        lt_of_not_ge (fun hbad => hunion (Or.inr hbad))
      have hdist :
          dist (X i omega + Y i omega) (x omega + y omega) ≤
            dist (X i omega) (x omega) +
              dist (Y i omega) (y omega) :=
        dist_add_add_le _ _ _ _
      linarith
    _ ≤ P {omega | epsilon / 2 ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)} :=
      measure_union_le _ _

/-- Pairing two families preserves convergence in measure, without
measurability assumptions on either family. -/
theorem TendstoInMeasure.prodMk_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E} {Y : ι → A → F} {x : A → E} {y : A → F}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega ↦ (X i omega, Y i omega)) l
      (fun omega ↦ (x omega, y omega)) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro epsilon hepsilon
  have hsum : Tendsto (fun i ↦
      P {omega | epsilon ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon ≤ dist (Y i omega) (y omega)}) l (nhds 0) := by
    simpa only [add_zero] using
      (hX epsilon hepsilon).add (hY epsilon hepsilon)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ ↦ zero_le) ?_
  intro i
  calc
    P {omega | epsilon ≤
        dist (X i omega, Y i omega) (x omega, y omega)} ≤
        P ({omega | epsilon ≤ dist (X i omega) (x omega)} ∪
          {omega | epsilon ≤ dist (Y i omega) (y omega)}) := by
      apply measure_mono
      intro omega homega
      simpa only [Set.mem_ofPred_eq, Set.mem_union, Prod.dist_eq,
        le_max_iff] using homega
    _ ≤ P {omega | epsilon ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon ≤ dist (Y i omega) (y omega)} :=
      measure_union_le _ _

/-- The first coordinate of a product-valued convergence-in-measure limit
converges without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.fst_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E × F} {x : A → E × F} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) :
    TendstoInMeasure P (fun i omega ↦ (X i omega).1) l
      (fun omega ↦ (x omega).1) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  have hpair := hX epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hpair (fun _ ↦ zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  change epsilon ≤ dist (X i omega).1 (x omega).1 at homega
  change epsilon ≤ dist (X i omega) (x omega)
  rw [Prod.dist_eq]
  exact homega.trans (le_max_left _ _)

/-- The second coordinate of a product-valued convergence-in-measure limit
converges without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.snd_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E × F} {x : A → E × F} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) :
    TendstoInMeasure P (fun i omega ↦ (X i omega).2) l
      (fun omega ↦ (x omega).2) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  have hpair := hX epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hpair (fun _ ↦ zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  change epsilon ≤ dist (X i omega).2 (x omega).2 at homega
  change epsilon ≤ dist (X i omega) (x omega)
  rw [Prod.dist_eq]
  exact homega.trans (le_max_right _ _)

/-- Three varying normed-valued approximation families admit one strictly
increasing fine-grid diagonal along which all three errors vanish. -/
theorem TendstoInMeasure.exists_strictMono_diagonal_sub_three_normed
    {A E₁ E₂ E₃ : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [NormedAddCommGroup E₃] {P : Measure A} [IsFiniteMeasure P]
    {F₁ : ℕ → ℕ → A → E₁} {G₁ : ℕ → A → E₁}
    {F₂ : ℕ → ℕ → A → E₂} {G₂ : ℕ → A → E₂}
    {F₃ : ℕ → ℕ → A → E₃} {G₃ : ℕ → A → E₃}
    (h₁ : ∀ k, TendstoInMeasure P (F₁ k) atTop (G₁ k))
    (h₂ : ∀ k, TendstoInMeasure P (F₂ k) atTop (G₂ k))
    (h₃ : ∀ k, TendstoInMeasure P (F₃ k) atTop (G₃ k)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega ↦ F₁ k (m k) omega - G₁ k omega)
        atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun k omega ↦ F₂ k (m k) omega - G₂ k omega)
        atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun k omega ↦ F₃ k (m k) omega - G₃ k omega)
        atTop (fun _ ↦ 0) := by
  let F : ℕ → ℕ → A → E₁ × (E₂ × E₃) := fun k n omega ↦
    (F₁ k n omega, F₂ k n omega, F₃ k n omega)
  let G : ℕ → A → E₁ × (E₂ × E₃) := fun k omega ↦
    (G₁ k omega, G₂ k omega, G₃ k omega)
  have hFG : ∀ k, TendstoInMeasure P (F k) atTop (G k) := by
    intro k
    exact TendstoInMeasure.prodMk_noMeas (h₁ k)
      (TendstoInMeasure.prodMk_noMeas (h₂ k) (h₃ k))
  obtain ⟨m, hm, hdiag⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal_sub_normed hFG
  have hdiag₁ := TendstoInMeasure.fst_noMeas hdiag
  have hdiagRest := TendstoInMeasure.snd_noMeas hdiag
  have hdiag₂ := TendstoInMeasure.fst_noMeas hdiagRest
  have hdiag₃ := TendstoInMeasure.snd_noMeas hdiagRest
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · simpa only [F, G, Prod.fst_sub, Pi.zero_apply, Prod.fst_zero] using hdiag₁
  · simpa only [F, G, Prod.snd_sub, Prod.fst_sub, Pi.zero_apply,
      Prod.snd_zero, Prod.fst_zero] using hdiag₂
  · simpa only [F, G, Prod.snd_sub, Pi.zero_apply, Prod.snd_zero] using hdiag₃

/-- Pointwise subtraction preserves convergence in measure in any
seminormed additive group, without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.sub_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y : ι → A → E} {x y : A → E}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega => X i omega - Y i omega) l
      (fun omega => x omega - y omega) := by
  have hneg : TendstoInMeasure P (fun i omega => -Y i omega) l
      (fun omega => -y omega) := by
    rw [tendstoInMeasure_iff_norm] at hY ⊢
    intro epsilon hepsilon
    simpa only [neg_sub_neg, norm_neg, norm_sub_rev] using
      hY epsilon hepsilon
  simpa only [sub_eq_add_neg] using
    TendstoInMeasure.add_normed_noMeas hX hneg

/-- If two normed-valued families converge to the same varying comparison
family after subtraction, then their mutual difference vanishes. -/
theorem TendstoInMeasure.sub_of_sub_common_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y G : ι → A → E} {l : Filter ι}
    (hX : TendstoInMeasure P (fun i omega ↦ X i omega - G i omega) l
      (fun _ ↦ 0))
    (hY : TendstoInMeasure P (fun i omega ↦ Y i omega - G i omega) l
      (fun _ ↦ 0)) :
    TendstoInMeasure P (fun i omega ↦ X i omega - Y i omega) l
      (fun _ ↦ 0) := by
  have hdiff := TendstoInMeasure.sub_normed_noMeas hX hY
  have hdiff' : TendstoInMeasure P
      (fun i omega ↦ X i omega - G i omega - (Y i omega - G i omega)) l
      (fun _ ↦ 0) := by
    simpa only [sub_zero] using hdiff
  apply hdiff'.congr_left
  intro i
  exact Filter.Eventually.of_forall fun omega ↦ by
    change X i omega - G i omega - (Y i omega - G i omega) =
      X i omega - Y i omega
    rw [sub_sub_sub_cancel_right]

/-- Two vanishing differences with a shared intermediate family concatenate
to a vanishing endpoint difference. -/
theorem TendstoInMeasure.sub_chain_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y Z : ι → A → E} {l : Filter ι}
    (hXY : TendstoInMeasure P (fun i omega ↦ X i omega - Y i omega) l
      (fun _ ↦ 0))
    (hYZ : TendstoInMeasure P (fun i omega ↦ Y i omega - Z i omega) l
      (fun _ ↦ 0)) :
    TendstoInMeasure P (fun i omega ↦ X i omega - Z i omega) l
      (fun _ ↦ 0) := by
  have hsum := TendstoInMeasure.add_normed_noMeas hXY hYZ
  have hsum' : TendstoInMeasure P (fun i omega ↦
      (X i omega - Y i omega) + (Y i omega - Z i omega)) l
      (fun _ ↦ 0) := by
    simpa only [zero_add] using hsum
  apply hsum'.congr_left
  intro i
  exact Filter.Eventually.of_forall fun omega ↦ by
    change (X i omega - Y i omega) + (Y i omega - Z i omega) =
      X i omega - Z i omega
    rw [sub_add_sub_cancel]

/-- Multiplication by a deterministic complex scalar preserves convergence
in measure without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.const_mul_complex_noMeas
    {A ι : Type*} [MeasurableSpace A] {P : Measure A}
    {X : ι → A → ℂ} {x : A → ℂ} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) (c : ℂ) :
    TendstoInMeasure P (fun i omega => c * X i omega) l
      (fun omega => c * x omega) := by
  rw [tendstoInMeasure_iff_norm] at hX ⊢
  intro epsilon hepsilon
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, sub_self, norm_zero, Set.ofPred_false,
      measure_empty, not_le.mpr hepsilon] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0))
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hscaled := hX (epsilon / ‖c‖) (div_pos hepsilon hcpos)
    have hfun :
        (fun i => P {omega | epsilon ≤ ‖c * X i omega - c * x omega‖}) =
        (fun i => P {omega | epsilon / ‖c‖ ≤ ‖X i omega - x omega‖}) := by
      funext i
      apply congrArg P
      ext omega
      simp only [Set.mem_ofPred_eq, ← mul_sub, norm_mul]
      rw [div_le_iff₀ hcpos, mul_comm]
    rw [hfun]
    exact hscaled

/-- The isometric inclusion of the reals into the complexes preserves
convergence in measure without measurability hypotheses. -/
theorem TendstoInMeasure.ofReal_noMeas
    {A ι : Type*} [MeasurableSpace A] {P : Measure A}
    {X : ι → A → ℝ} {x : A → ℝ} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) :
    TendstoInMeasure P (fun i omega => (X i omega : ℂ)) l
      (fun omega => (x omega : ℂ)) := by
  rw [tendstoInMeasure_iff_norm] at hX ⊢
  intro epsilon hepsilon
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    hX epsilon hepsilon

/-- A complex family converges in measure when its real and imaginary parts
do, without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.of_re_im_noMeas
    {A ι : Type*} [MeasurableSpace A] {P : Measure A}
    {X : ι → A → ℂ} {x : A → ℂ} {l : Filter ι}
    (hre : TendstoInMeasure P (fun i omega => (X i omega).re) l
      (fun omega => (x omega).re))
    (him : TendstoInMeasure P (fun i omega => (X i omega).im) l
      (fun omega => (x omega).im)) :
    TendstoInMeasure P X l x := by
  have hreC := TendstoInMeasure.ofReal_noMeas hre
  have himC := TendstoInMeasure.ofReal_noMeas him
  have hsum := TendstoInMeasure.add_normed_noMeas hreC
    (TendstoInMeasure.const_mul_complex_noMeas himC Complex.I)
  apply hsum.congr
  · intro i
    exact Filter.Eventually.of_forall fun omega => by
      change ((X i omega).re : ℂ) + Complex.I * ((X i omega).im : ℂ) =
        X i omega
      rw [mul_comm]
      exact Complex.re_add_im (X i omega)
  · exact Filter.Eventually.of_forall fun omega => by
      change ((x omega).re : ℂ) + Complex.I * ((x omega).im : ℂ) = x omega
      rw [mul_comm]
      exact Complex.re_add_im (x omega)

/-- Pointwise domination by a nonnegative real family transfers convergence
in measure to zero, without measurability assumptions on either family. -/
theorem TendstoInMeasure.of_norm_le_nonneg_noMeas
    {A ι E : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X : ι → A → E} {b : ι → A → ℝ}
    {l : Filter ι}
    (hb : TendstoInMeasure P b l (fun _ => 0))
    (hb_nonneg : ∀ i omega, 0 ≤ b i omega)
    (hXb : ∀ i omega, ‖X i omega‖ ≤ b i omega) :
    TendstoInMeasure P X l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hb ⊢
  intro epsilon hepsilon
  have hlimit := hb epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hlimit (fun _ => zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (hb_nonneg i omega)] at homega ⊢
  exact homega.trans (hXb i omega)

/-- A real-valued convergence-in-measure limit is almost everywhere
nonpositive if every approximant is pointwise nonpositive. -/
theorem TendstoInMeasure.ae_le_zero_of_forall_le_zero
    {A : Type*} [MeasurableSpace A] {P : Measure A}
    {f : ℕ → A → ℝ} {g : A → ℝ}
    (hfg : TendstoInMeasure P f atTop g)
    (hf : ∀ n omega, f n omega ≤ 0) : g ≤ᵐ[P] fun _ => 0 := by
  obtain ⟨ns, _hns, hae⟩ := hfg.exists_seq_tendsto_ae
  filter_upwards [hae] with omega homega
  exact le_of_tendsto homega
    (Filter.Eventually.of_forall fun n => hf (ns n) omega)

set_option maxHeartbeats 4000000 in
-- Combining three convergence-in-measure limits is elaboration-intensive.
/-- Fixed-time Kunita--Watanabe inequality obtained directly from uniform
partition convergence in measure. -/
theorem HasCrossVariationProcessInProbability.sq_le_mul_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C QX QY : ℝ≥0 → W → ℝ}
    (hcross : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQY : HasQuadraticVariationProcessInProbability Y QY P)
    (t : ℝ≥0) :
    (fun omega => C t omega ^ 2) ≤ᵐ[P]
      fun omega => QX t omega * QY t omega := by
  let cov : ℕ → W → ℝ := fun n =>
    quadraticCovariationApprox X Y t (n + 1)
  let qX : ℕ → W → ℝ := fun n => quadraticVariationApprox X t (n + 1)
  let qY : ℕ → W → ℝ := fun n => quadraticVariationApprox Y t (n + 1)
  have hcovMeas : ∀ n, AEStronglyMeasurable (cov n) P := fun n =>
    aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hYmeas t (n + 1)
  have hqXMeas : ∀ n, AEStronglyMeasurable (qX n) P := fun n =>
    aestronglyMeasurable_quadraticVariationApprox hXmeas t (n + 1)
  have hqYMeas : ∀ n, AEStronglyMeasurable (qY n) P := fun n =>
    aestronglyMeasurable_quadraticVariationApprox hYmeas t (n + 1)
  have hcovSq : TendstoInMeasure P (fun n omega => cov n omega ^ 2)
      atTop (fun omega => C t omega ^ 2) := by
    exact TendstoInMeasure.continuous_comp hcovMeas
      (by simpa only [cov] using hcross t)
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hqProd : TendstoInMeasure P
      (fun n omega => qX n omega * qY n omega) atTop
      (fun omega => QX t omega * QY t omega) := by
    apply TendstoInMeasure.continuous_comp₂ hqXMeas hqYMeas
      (by simpa only [qX, HasQuadraticVariationInProbabilityAt] using hQX t)
      (by simpa only [qY, HasQuadraticVariationInProbabilityAt] using hQY t)
    fun_prop
  have hdiff := hcovSq.sub_real_noMeas hqProd
  have hnonpos : (fun omega => C t omega ^ 2 -
      QX t omega * QY t omega) ≤ᵐ[P] fun _ => 0 :=
    TendstoInMeasure.ae_le_zero_of_forall_le_zero hdiff fun n omega => by
      dsimp only [cov, qX, qY]
      exact sub_nonpos.mpr
        (quadraticCovariationApprox_sq_le X Y t (n + 1) omega)
  filter_upwards [hnonpos] with omega homega
  simpa only [Pi.zero_apply, sub_nonpos] using homega

/-- Continuous real-linear images of Banach-valued martingales are
martingales. -/
theorem Martingale.comp_continuousLinearMap
    {W E F I : Type*} [MeasurableSpace W] [Preorder I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {P : Measure W} {V : Filtration I ‹MeasurableSpace W›}
    {X : I → W → E} (hX : Martingale X V P) (L : E →L[ℝ] F) :
    Martingale (fun t omega ↦ L (X t omega)) V P := by
  refine ⟨fun t ↦ L.continuous.comp_stronglyMeasurable (hX.stronglyMeasurable t),
    fun i j hij ↦ ?_⟩
  exact (L.comp_condExp_comm (hX.integrable j)).symm.trans
    ((hX.condExp_ae_eq hij).fun_comp L)

/-- An integrable density transports an entire process-level
quadratic-variation contract. -/
theorem HasQuadraticVariationProcessInProbability.withDensity_of_integrable_real
    {W : Type*} [MeasurableSpace W] {P : Measure W} [SFinite P]
    {X bracket : ℝ≥0 → W → ℝ} {Z : W → ℝ}
    (hZ : Integrable Z P)
    (hX : HasQuadraticVariationProcessInProbability X bracket P) :
    HasQuadraticVariationProcessInProbability X bracket
      (P.withDensity fun omega ↦ ENNReal.ofReal (Z omega)) :=
  fun t ↦ TendstoInMeasure.withDensity_of_integrable_real hZ (hX t)

/-- An integrable density transports deterministic stopped-process
quadratic variation. -/
theorem HasStoppedQuadraticVariationProcessInProbability.withDensity_of_integrable_real
    {W : Type*} [MeasurableSpace W] {P : Measure W} [SFinite P]
    {X bracket : ℝ≥0 → W → ℝ} {Z : W → ℝ}
    (hZ : Integrable Z P)
    (hX : HasStoppedQuadraticVariationProcessInProbability X bracket P) :
    HasStoppedQuadraticVariationProcessInProbability X bracket
      (P.withDensity fun omega ↦ ENNReal.ofReal (Z omega)) :=
  fun T a ↦ TendstoInMeasure.withDensity_of_integrable_real hZ (hX T a)

/-- The robust completed-cell bracket contract is likewise invariant under
an integrable change of density. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.withDensity_of_integrable_real
    {W : Type*} [MeasurableSpace W] {P : Measure W} [SFinite P]
    {X bracket : ℝ≥0 → W → ℝ} {Z : W → ℝ}
    (hZ : Integrable Z P)
    (hX : HasQuadraticVariationBeforeStopProcessInProbability X bracket P) :
    HasQuadraticVariationBeforeStopProcessInProbability X bracket
      (P.withDensity fun omega ↦ ENNReal.ofReal (Z omega)) :=
  fun T a ↦ TendstoInMeasure.withDensity_of_integrable_real hZ (hX T a)

/-- An integrable density likewise transports uniform-partition cross
variation. -/
theorem HasCrossVariationProcessInProbability.withDensity_of_integrable_real
    {W : Type*} [MeasurableSpace W] {P : Measure W} [SFinite P]
    {X Y covariation : ℝ≥0 → W → ℝ} {Z : W → ℝ}
    (hZ : Integrable Z P)
    (hXY : HasCrossVariationProcessInProbability X Y covariation P) :
    HasCrossVariationProcessInProbability X Y covariation
      (P.withDensity fun omega ↦ ENNReal.ofReal (Z omega)) :=
  fun t ↦ TendstoInMeasure.withDensity_of_integrable_real hZ (hXY t)

/-- A pre-Brownian process plus an absolutely continuous finite-variation
drift has the deterministic clock bracket after every deterministic stop. -/
theorem hasStoppedQuadraticVariation_preBrownian_add_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B mu : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P)
    (hmu : Measurable (Function.uncurry mu))
    (hmuInt : ∀ (t : ℝ≥0) omega, IntegrableOn (fun r : ℝ ↦ mu r.toNNReal omega)
      (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasStoppedQuadraticVariationProcessInProbability
      (fun t omega ↦ B t omega + integratedDrift mu t omega)
      (fun t _omega ↦ (t : ℝ)) P := by
  intro t a
  have hD := quadraticVariation_stopped_integratedDrift_inProbability
    (P := P) hmu a t (hmuInt t)
  have hBa := quadraticVariation_stopped_preBrownianReal_inProbability hB a t
  have hsum := hD.add_of_left_zero_of_aestronglyMeasurable hBa
    (fun s ↦ (stronglyMeasurable_integratedDrift hmu
      (min s a)).aestronglyMeasurable)
    (fun s ↦ (hB.aemeasurable (min s a)).aestronglyMeasurable)
  apply hsum.congr
  · intro s
    exact Filter.Eventually.of_forall fun omega ↦ by
      exact add_comm _ _
  · exact Filter.EventuallyEq.rfl

/-- A pre-Brownian process plus an absolutely continuous finite-variation
drift also has the robust completed-cell clock bracket.  Gaussian second
moments remove the Brownian boundary cell, while continuity of the drift
primitive removes its boundary cell. -/
theorem hasQuadraticVariationBeforeStop_preBrownian_add_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B mu : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P)
    (hmu : Measurable (Function.uncurry mu))
    (hmuInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun r : ℝ ↦ mu r.toNNReal omega)
      (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun t omega ↦ B t omega + integratedDrift mu t omega)
      (fun t _omega ↦ (t : ℝ)) P := by
  have hstopped := hasStoppedQuadraticVariation_preBrownian_add_integratedDrift
    hB hmu hmuInt
  apply hstopped.toBeforeStop_of_crossing
  intro T a haT
  let D : ℝ≥0 → W → ℝ := integratedDrift mu
  have hBmeas : ∀ s, AEStronglyMeasurable (B s) P := fun s =>
    (hB.aemeasurable s).aestronglyMeasurable
  have hDmeas : ∀ s, AEStronglyMeasurable (D s) P := fun s =>
    (stronglyMeasurable_integratedDrift hmu s).aestronglyMeasurable
  have hDself : IsContinuousProcessModification D D P :=
    ⟨fun _ => Filter.Eventually.of_forall fun _ => rfl,
      Filter.Eventually.of_forall
        (continuous_integratedDrift_of_integrableOn mu hmuInt)⟩
  have hBcross :=
    quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
      hB T a
  have hDcross := hDself.quadraticVariationCrossingStopApprox_tendstoInMeasure
    hDmeas T a ⟨bot_le, haT⟩
  have hadd :=
    tendstoInMeasure_quadraticVariationCrossingStopApprox_add_zero
      hBmeas hDmeas T a hBcross hDcross
  apply hadd.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega => by
    unfold quadraticVariationCrossingStopApprox
    rfl

/-- A pre-Brownian process carries the explicit common-localizer bracket
contract in its natural filtration.  The constant-top localizer suffices
because the process is already a true natural-filtration martingale and its
robust clock bracket was proved without path continuity. -/
theorem hasLocalQuadraticVariation_preBrownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    HasLocalQuadraticVariationProcessInProbability B
      (fun t (_omega : W) => (t : ℝ)) (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlocB : localizingStoppedProcess B (fun _ => ⊤) = B := by
    funext t omega
    simp [localizingStoppedProcess]
  have hlocClock : localizingStoppedProcess
      (fun t (_omega : W) => (t : ℝ)) (fun _ => ⊤) =
      (fun (t : ℝ≥0) (_omega : W) => (t : ℝ)) := by
    funext t omega
    simp [localizingStoppedProcess]
  refine ⟨fun _ _ => ⊤,
    isLocalizingSequence_const_top (Filtration.natural B hsm) P, ?_, ?_⟩
  · intro k
    rw [hlocB]
    exact martingale_brownian_natural hB hsm
  · intro k
    rw [hlocB, hlocClock]
    exact hasQuadraticVariationBeforeStop_preBrownianReal hB

/-- The terminal stochastic-exponential density used by Girsanov. -/
def girsanovDensity {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : W → ℝ :=
  doleansDadeExponential M bracket T

/-- The Girsanov measure `Q = Z_T · P`, represented by Mathlib's
`Measure.withDensity`. -/
def girsanovMeasure {W : Type*} [MeasurableSpace W]
    (P : Measure W) (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Measure W :=
  P.withDensity (fun omega => ENNReal.ofReal (girsanovDensity M bracket T omega))

/-- The finite-horizon pathwise drift accumulated from a predictable
integrand. -/
def girsanovIntegratedDrift {W : Type*}
    (theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), theta s omega
    ∂nonnegativeLebesgueMeasure

/-- Integrating a strongly predictable process up to a deterministic stopped
horizon produces an adapted finite-variation process. -/
theorem IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {theta : ℝ≥0 → W → ℝ}
    (htheta : IsStronglyPredictable V theta) (T : ℝ≥0) :
    StronglyAdapted V (girsanovIntegratedDrift theta T) := by
  intro t
  let u : ℝ≥0 := min t T
  let j : Set.Ioc (0 : ℝ≥0) u → Set.Iic t := fun r ↦
    ⟨r, r.prop.2.trans (min_le_left t T)⟩
  have hj : Measurable j := by
    exact measurable_subtype_coe.subtype_mk
  have hprog : StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (fun p : Set.Iic t × W ↦ theta p.1 p.2) :=
    htheta.isStronglyProgressive t
  let F : Set.Ioc (0 : ℝ≥0) u → W → ℝ :=
    fun r omega ↦ theta r omega
  have hF : StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (Function.uncurry F) := by
    have hpair : @Measurable
        (Set.Ioc (0 : ℝ≥0) u × W) (Set.Iic t × W)
        (Subtype.instMeasurableSpace.prod (V t))
        (Subtype.instMeasurableSpace.prod (V t))
        (fun p ↦ (j p.1, p.2)) := Measurable.prodMk
      (hj.comp measurable_fst) measurable_snd
    change StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (fun p : Set.Ioc (0 : ℝ≥0) u × W ↦ theta p.1 p.2)
    exact hprog.comp_measurable hpair
  let restrictedTimeMeasure :=
    nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)
  have hmap := map_nonnegativeLebesgueMeasure_restrict_Ioc u
  let : IsFiniteMeasure restrictedTimeMeasure := by
    have : IsFiniteMeasure
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (u : ℝ))) := inferInstance
    have : IsFiniteMeasure (Measure.map ((↑) : ℝ≥0 → ℝ)
        restrictedTimeMeasure) := by
      rw [show Measure.map ((↑) : ℝ≥0 → ℝ) restrictedTimeMeasure =
          (volume : Measure ℝ).restrict (Set.Ioc 0 (u : ℝ)) by
        simpa only [restrictedTimeMeasure] using hmap]
      infer_instance
    exact Measure.isFiniteMeasure_of_map
      NNReal.continuous_coe.measurable.aemeasurable
  let timeMeasure : Measure (Set.Ioc (0 : ℝ≥0) u) :=
    Measure.comap Subtype.val restrictedTimeMeasure
  have hparam : StronglyMeasurable[V t] (fun omega ↦
      ∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure) := by
    let : MeasurableSpace W := V t
    exact hF.integral_prod_left
  convert hparam using 1
  funext omega
  unfold girsanovIntegratedDrift
  change (∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
      ∂nonnegativeLebesgueMeasure) =
    ∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure
  symm
  calc
    (∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure) =
        ∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
          ∂restrictedTimeMeasure := by
      simpa only [F, timeMeasure] using
        (integral_subtype_comap (μ := restrictedTimeMeasure)
          measurableSet_Ioc (fun r ↦ theta r omega))
    _ = ∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
          ∂nonnegativeLebesgueMeasure := by
      change (∫ r, theta r omega ∂
          (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 u)).restrict
            (Set.Ioc 0 u)) = _
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_self]

/-- The nonnegative-time drift used in the Girsanov statement agrees with
the real-time integral primitive used by the quadratic-variation library. -/
theorem girsanovIntegratedDrift_eq_integratedDrift
    {W : Type*} [MeasurableSpace W]
    (theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      integratedDrift theta (min t T) omega := by
  unfold girsanovIntegratedDrift integratedDrift
  exact integral_nonnegative_Ioc_eq_real_Icc theta (min t T) omega

/-- A path-regular representative of the stopped Girsanov drift.  On the
zero-terminal-bracket event it is set to zero; elsewhere the terminal
square integral is genuine and the original integral has continuous paths. -/
def regularizedGirsanovIntegratedDrift {W : Type*}
    (bracket theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  if bracket T omega = 0 then 0 else girsanovIntegratedDrift theta T t omega

/-- Every deterministic-time section of the regularized drift is strongly
measurable.  The terminal-bracket test is globally measurable, while the
uncut drift section is measurable by predictability. -/
theorem stronglyMeasurable_regularizedGirsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hbracket : StronglyAdapted V bracket)
    (htheta : IsStronglyPredictable V theta) (t : ℝ≥0) :
    StronglyMeasurable
      (regularizedGirsanovIntegratedDrift bracket theta T t) := by
  have hbracketT : StronglyMeasurable (bracket T) :=
    (hbracket T).mono (V.le T)
  have hdrift : StronglyMeasurable (girsanovIntegratedDrift theta T t) :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T t).mono (V.le t)
  have hset : MeasurableSet {omega | bracket T omega = 0} :=
    hbracketT.measurable (measurableSet_singleton 0)
  change StronglyMeasurable
    ({omega | bracket T omega = 0}.piecewise
      (fun _ => 0) (girsanovIntegratedDrift theta T t))
  exact stronglyMeasurable_const.piecewise hset hdrift

/-- The regularized stopped drift has continuous paths.  A nonzero terminal
bracket forces the totalized square integral to be genuinely integrable,
and finite-measure `L²` control then gives the needed `L¹` primitive. -/
theorem continuous_regularizedGirsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) (omega : W) :
    Continuous (fun t =>
      regularizedGirsanovIntegratedDrift bracket theta T t omega) := by
  unfold regularizedGirsanovIntegratedDrift
  by_cases hzero : bracket T omega = 0
  · simp only [hzero, if_pos]
    fun_prop
  · simp only [hzero, if_false]
    have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaInt : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    let g : ℝ → ℝ := fun r => theta r.toNNReal omega
    have hprimitive : ContinuousOn
        (fun u => integratedDrift theta u omega)
        (Set.Icc (0 : ℝ≥0) T) := by
      change ContinuousOn (nnrealIntegralPrimitive g)
        (Set.Icc (0 : ℝ≥0) T)
      exact continuousOn_nnrealIntegralPrimitive hthetaInt
    have hmin : Continuous (fun t : ℝ≥0 => min t T) := by fun_prop
    have hcomp := hprimitive.comp_continuous hmin (fun t =>
      show min t T ∈ Set.Icc (0 : ℝ≥0) T from
        ⟨bot_le, min_le_right _ _⟩)
    apply hcomp.congr
    intro t
    exact (girsanovIntegratedDrift_eq_integratedDrift
      theta T t omega).symm

/-- The process `B_t + ∫₀^{t∧T} theta_s ds` appearing in the
finite-horizon Girsanov theorem.  Brownian motion itself is not stopped after
`T`; only the compensating drift is. -/
def girsanovShiftedBrownian {W : Type*}
    (B theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) : ℝ≥0 → W → ℝ :=
  fun t omega => B t omega + girsanovIntegratedDrift theta T t omega

/-- A predictable drift preserves adaptedness when added to an adapted
driver. -/
theorem stronglyAdapted_girsanovShiftedBrownian
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hB : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta) :
    StronglyAdapted V (girsanovShiftedBrownian B theta T) := by
  intro t
  exact (hB t).add
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T t)

/-- The finite-horizon Girsanov drift shift has the stopped Brownian clock
bracket under the original measure.  The explicit integrability premise is
needed because Bochner integrals are totalized in Lean. -/
theorem hasStoppedQuadraticVariation_girsanovShiftedBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B theta : ℝ≥0 → W → ℝ} (T : ℝ≥0)
    (hB : IsPreBrownianReal B P)
    (htheta : Measurable (Function.uncurry theta))
    (hthetaInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun r : ℝ ↦ theta r.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasStoppedQuadraticVariationProcessInProbability
      (girsanovShiftedBrownian B theta T)
      (fun t _omega ↦ (t : ℝ)) P := by
  let thetaT := stoppedDriftIntegrand theta T
  have hthetaT : Measurable (Function.uncurry thetaT) :=
    measurable_uncurry_stoppedDriftIntegrand htheta T
  have hthetaTInt (t : ℝ≥0) (omega : W) : IntegrableOn
      (fun r : ℝ ↦ thetaT r.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ)) :=
    integrableOn_stoppedDriftIntegrand T t omega (hthetaInt t omega)
  have hqv := hasStoppedQuadraticVariation_preBrownian_add_integratedDrift
    hB hthetaT hthetaTInt
  have hshift : girsanovShiftedBrownian B theta T =
      fun t omega ↦ B t omega + integratedDrift theta (min t T) omega := by
    funext t omega
    exact congrArg (fun x ↦ B t omega + x)
      (girsanovIntegratedDrift_eq_integratedDrift theta T t omega)
  rw [hshift]
  simpa only [thetaT, integratedDrift_stoppedDriftIntegrand] using hqv

@[simp]
theorem girsanovIntegratedDrift_zero {W : Type*}
    (theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift theta T 0 omega = 0 := by
  simp [girsanovIntegratedDrift]

theorem girsanovIntegratedDrift_of_le {W : Type*}
    (theta : ℝ≥0 → W → ℝ) {T t : ℝ≥0} (ht : t ≤ T) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) t, theta s omega
        ∂nonnegativeLebesgueMeasure := by
  simp only [girsanovIntegratedDrift, min_eq_left ht]

theorem girsanovIntegratedDrift_of_horizon_le {W : Type*}
    (theta : ℝ≥0 → W → ℝ) {T t : ℝ≥0} (ht : T ≤ t) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, theta s omega
        ∂nonnegativeLebesgueMeasure := by
  simp only [girsanovIntegratedDrift, min_eq_right ht]

@[simp]
theorem girsanovShiftedBrownian_zero {W : Type*}
    (B theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    girsanovShiftedBrownian B theta T 0 omega = B 0 omega := by
  simp [girsanovShiftedBrownian]

@[simp]
theorem girsanovDensity_eq_exp_log {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    girsanovDensity M bracket T omega =
      Real.exp (doleansDadeLog M bracket T omega) :=
  rfl

theorem girsanovDensity_pos {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    0 < girsanovDensity M bracket T omega :=
  Real.exp_pos _

/-- Once the terminal density has expectation one, the exact density measure
agrees with Mathlib's normalized exponential tilt. -/
theorem girsanovMeasure_eq_tilted
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hone : ∫ omega, girsanovDensity M bracket T omega ∂P = 1) :
    girsanovMeasure P M bracket T =
      P.tilted (doleansDadeLog M bracket T) := by
  have hlog : ∫ omega, Real.exp (doleansDadeLog M bracket T omega) ∂P = 1 := by
    simpa only [girsanovDensity_eq_exp_log] using hone
  unfold girsanovMeasure Measure.tilted
  rw [hlog]
  congr 1
  funext omega
  simp only [div_one, girsanovDensity_eq_exp_log]

/-- The terminal density measure is absolutely continuous with respect to
the original measure, without any integrability assumption. -/
theorem girsanovMeasure_absolutelyContinuous
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) :
    girsanovMeasure P M bracket T ≪ P := by
  unfold girsanovMeasure
  exact withDensity_absolutelyContinuous _ _

/-- Strict positivity of a measurable terminal stochastic exponential makes
the change of measure equivalent to the original measure. -/
theorem girsanovMeasure_mutuallyAbsolutelyContinuous
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) :
    girsanovMeasure P M bracket T ≪ P ∧
      P ≪ girsanovMeasure P M bracket T := by
  refine ⟨girsanovMeasure_absolutelyContinuous P M bracket T, ?_⟩
  unfold girsanovMeasure
  apply withDensity_absolutelyContinuous'
  · exact hint.1.aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun omega => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact girsanovDensity_pos M bracket T omega

/-- Integration under the Girsanov measure is terminal-density weighting
under the original measure. -/
theorem integral_girsanovMeasure
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) (f : W → ℝ) :
    ∫ omega, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega, girsanovDensity M bracket T omega * f omega ∂P := by
  unfold girsanovMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hint.1.aemeasurable.ennreal_ofReal]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      change (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal * f omega =
        girsanovDensity M bracket T omega * f omega
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  · exact Filter.Eventually.of_forall fun omega => ENNReal.ofReal_lt_top

/-- Set integrals under the Girsanov measure are terminal-density-weighted
set integrals under the original measure. -/
theorem setIntegral_girsanovMeasure
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) (f : W → ℝ)
    {s : Set W} (hs : MeasurableSet s) :
    ∫ omega in s, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega in s, girsanovDensity M bracket T omega * f omega ∂P := by
  unfold girsanovMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hint.1.aemeasurable.ennreal_ofReal.restrict]
  · apply setIntegral_congr_ae hs
    exact Filter.Eventually.of_forall fun omega _ => by
      change (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal * f omega =
        girsanovDensity M bracket T omega * f omega
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  · exact Filter.Eventually.of_forall fun omega => ENNReal.ofReal_lt_top
  · exact hs

/-- Vector-valued set integrals under the Girsanov measure are obtained by
real scalar multiplication with the terminal density. -/
theorem setIntegral_girsanovMeasure_smul
    {W E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) (f : W → E)
    {s : Set W} (hs : MeasurableSet s) :
    ∫ omega in s, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega in s, girsanovDensity M bracket T omega • f omega ∂P := by
  unfold girsanovMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hint.1.aemeasurable.ennreal_ofReal.restrict]
  · apply setIntegral_congr_ae hs
    exact Filter.Eventually.of_forall fun omega _ ↦ by
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  · exact Filter.Eventually.of_forall fun omega ↦ ENNReal.ofReal_lt_top
  · exact hs

/-- Any positive integrable normalized stochastic exponential defines a
probability measure. -/
theorem isProbabilityMeasure_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P)
    (hone : ∫ omega, girsanovDensity M bracket T omega ∂P = 1) :
    IsProbabilityMeasure (girsanovMeasure P M bracket T) := by
  rw [girsanovMeasure_eq_tilted P M bracket T hone]
  exact isProbabilityMeasure_tilted (by
    apply hint.congr
    exact Filter.Eventually.of_forall fun _ => rfl)

/-- The exact hypotheses needed from a continuous local martingale and its
bracket to construct the finite-horizon Girsanov density under Novikov's
condition. -/
structure GirsanovDensityData
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop where
  novikov : NovikovCondition bracket P T
  localQuadraticVariation :
    HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P
  continuous_martingale_path : ∀ omega, Continuous (fun t => M t omega)
  adapted_martingale : StronglyAdapted 𝒱 M
  adapted_bracket : StronglyAdapted 𝒱 bracket
  continuous_monotone_bracket : ∀ omega,
    Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega)
  martingale_zero : ∀ omega, M 0 omega = 0
  bracket_zero : ∀ omega, bracket 0 omega = 0

/-- Girsanov density data at a terminal horizon remains valid at every
earlier deterministic horizon. Only the Novikov field depends on the
horizon; bracket monotonicity and adaptedness provide its restriction. -/
theorem GirsanovDensityData.mono_time
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T t : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) (ht : t ≤ T) :
    GirsanovDensityData P V M bracket t := by
  refine
    { novikov := h.novikov.mono_time
        (fun s ↦ ((h.adapted_bracket s).mono (V.le s)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun omega ↦
          (h.continuous_monotone_bracket omega).2) ht
      localQuadraticVariation := h.localQuadraticVariation
      continuous_martingale_path := h.continuous_martingale_path
      adapted_martingale := h.adapted_martingale
      adapted_bracket := h.adapted_bracket
      continuous_monotone_bracket := h.continuous_monotone_bracket
      martingale_zero := h.martingale_zero
      bracket_zero := h.bracket_zero }

/-- The cross variation of Novikov Girsanov data with a pre-Brownian driver
is bounded by the product of the martingale bracket and Brownian clock. -/
theorem GirsanovDensityData.crossVariation_sq_le_bracket_mul_time_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (fun omega => C t omega ^ 2) ≤ᵐ[P]
      fun omega => bracket t omega * (t : ℝ) := by
  exact hcross.sq_le_mul_ae
    (fun s => ((hdata.adapted_martingale s).mono
      (V.le s)).aestronglyMeasurable)
    (fun s => (hB.aemeasurable s).aestronglyMeasurable)
    hdata.localQuadraticVariation.toProcess
    (fun s => quadraticVariation_preBrownianReal_inProbability hB s) t

/-- At a deterministic time, the Girsanov cross variation vanishes almost
everywhere on the event where the martingale bracket is zero. -/
theorem GirsanovDensityData.crossVariation_eq_zero_of_bracket_eq_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, bracket t omega = 0 → C t omega = 0 := by
  filter_upwards [hdata.crossVariation_sq_le_bracket_mul_time_ae
    hcross hB t] with omega homega
  intro hzero
  rw [hzero, zero_mul] at homega
  nlinarith [sq_nonneg (C t omega)]

/-- At each deterministic time, the regularized drift is an almost-everywhere
version of the original totalized drift whenever the latter is the negative
cross variation of the Girsanov martingale and Brownian driver. -/
theorem GirsanovDensityData.regularizedGirsanovIntegratedDrift_ae_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    regularizedGirsanovIntegratedDrift bracket theta T t =ᵐ[P]
      girsanovIntegratedDrift theta T t := by
  by_cases htT : t ≤ T
  · filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae
      hcross hB t] with omega hcrossZero
    unfold regularizedGirsanovIntegratedDrift
    by_cases hzero : bracket T omega = 0
    · rw [if_pos hzero]
      have hbracketNonneg : 0 ≤ bracket t omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      have hbracketLe : bracket t omega ≤ bracket T omega :=
        (hdata.continuous_monotone_bracket omega).2 htT
      have hbracketZero : bracket t omega = 0 := by linarith
      have hdriftZero := hcrossZero hbracketZero
      linarith
    · rw [if_neg hzero]
  · have hTt : T ≤ t := le_of_not_ge htT
    filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae
      hcross hB T] with omega hcrossZero
    unfold regularizedGirsanovIntegratedDrift
    by_cases hzero : bracket T omega = 0
    · rw [if_pos hzero]
      have hterminalZero := hcrossZero hzero
      have hstop : girsanovIntegratedDrift theta T t omega =
          girsanovIntegratedDrift theta T T omega := by
        rw [girsanovIntegratedDrift_of_horizon_le theta hTt,
          girsanovIntegratedDrift_of_horizon_le theta le_rfl]
      rw [hstop]
      linarith
    · rw [if_neg hzero]

/-- The cross-variation contract may use the continuous regularized drift
representative.  Convergence in probability is insensitive to the
deterministic-time null-set changes used by the regularization. -/
theorem GirsanovDensityData.hasCrossVariationProcessInProbability_neg_regularizedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P) :
    HasCrossVariationProcessInProbability M B
      (fun t omega =>
        -regularizedGirsanovIntegratedDrift bracket theta T t omega) P := by
  intro t
  apply (hcross t).congr_right
  exact (hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t).neg.symm

/-- Although the totalized Girsanov drift need not have continuous paths
pointwise, its continuous regularization is a version at every deterministic
time.  Consequently the adapted original drift is stochastically continuous. -/
theorem GirsanovDensityData.tendstoInMeasure_girsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n => girsanovIntegratedDrift theta T (a n)) atTop
      (girsanovIntegratedDrift theta T r) := by
  let R : ℝ≥0 → W → ℝ :=
    regularizedGirsanovIntegratedDrift bracket theta T
  have hReq (t : ℝ≥0) :
      R t =ᵐ[P] girsanovIntegratedDrift theta T t := by
    exact hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R (a n)) P := by
    exact (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable.congr
        (hReq (a n)).symm
  have hR : TendstoInMeasure P (fun n => R (a n)) atTop (R r) := by
    apply tendstoInMeasure_of_tendsto_ae hRmeas
    exact Filter.Eventually.of_forall fun omega =>
      (continuous_regularizedGirsanovIntegratedDrift htheta
        hbracketTerminal omega).continuousAt.tendsto.comp ha
  exact hR.congr (fun n => hReq (a n)) (hReq r)

/-- A pre-Brownian driver plus the predictable Girsanov drift is
stochastically continuous, without choosing a continuous Brownian version. -/
theorem GirsanovDensityData.tendstoInMeasure_girsanovShiftedBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n => girsanovShiftedBrownian B theta T (a n)) atTop
      (girsanovShiftedBrownian B theta T r) := by
  let addReal : ℝ → ℝ → ℝ := fun x y => x + y
  have haddReal : Continuous addReal.uncurry := by
    dsimp only [addReal, Function.uncurry]
    fun_prop
  change TendstoInMeasure P (fun n omega =>
    addReal (B (a n) omega)
      (girsanovIntegratedDrift theta T (a n) omega)) atTop
    (fun omega => addReal (B r omega)
      (girsanovIntegratedDrift theta T r omega))
  exact TendstoInMeasure.continuous_comp₂
    (fun n => (hsm (a n)).aestronglyMeasurable)
    (fun n => (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable)
    (StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha)
    (hdata.tendstoInMeasure_girsanovIntegratedDrift
      htheta hbracketTerminal hcross hB ha) haddReal

/-- The local bracket carried by Girsanov density data promotes to the
global robust completed-cell bracket. -/
theorem GirsanovDensityData.quadraticVariationBeforeStop_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    HasQuadraticVariationBeforeStopProcessInProbability M bracket P :=
  h.localQuadraticVariation.toBeforeStop

/-- Novikov's terminal exponential moment controls the first moment of the
terminal bracket. -/
theorem GirsanovDensityData.integrable_terminalBracket
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    Integrable (bracket T) P := by
  have hmeas : AEStronglyMeasurable (bracket T) P :=
    ((h.adapted_bracket T).mono (V.le T)).aestronglyMeasurable
  have hnonneg : ∀ᵐ omega ∂P, 0 ≤ bracket T omega :=
    Filter.Eventually.of_forall fun omega => by
      rw [← h.bracket_zero omega]
      exact (h.continuous_monotone_bracket omega).2 bot_le
  exact Integrable.of_exp_half_of_ae_nonneg hmeas hnonneg h.novikov

/-- Novikov promotes the stopped density process carried by
`GirsanovDensityData` to a true martingale. -/
theorem GirsanovDensityData.martingale_densityProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) 𝒱 P :=
  h.novikov.martingale_stopAt_doleansDade
    h.localQuadraticVariation h.continuous_martingale_path
    h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
    h.martingale_zero h.bracket_zero

/-- Novikov makes the terminal Girsanov density integrable. -/
theorem GirsanovDensityData.integrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    Integrable (girsanovDensity M bracket T) P := by
  simpa only [girsanovDensity, min_self] using
    h.martingale_densityProcess.integrable T

/-- Quadratic variation is unchanged by the equivalent terminal Girsanov
measure.  This supplies the pathwise-characteristic half of Lévy's
Brownian characterization independently of the martingale transport step. -/
theorem GirsanovDensityData.quadraticVariation_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket X q : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hX : HasQuadraticVariationProcessInProbability X q P) :
    HasQuadraticVariationProcessInProbability X q
      (girsanovMeasure P M bracket T) := by
  simpa only [girsanovMeasure, girsanovDensity] using
    hX.withDensity_of_integrable_real h.integrable

/-- Deterministic stopped quadratic variation is unchanged by the terminal
Girsanov density. -/
theorem GirsanovDensityData.stoppedQuadraticVariation_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket X q : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hX : HasStoppedQuadraticVariationProcessInProbability X q P) :
    HasStoppedQuadraticVariationProcessInProbability X q
      (girsanovMeasure P M bracket T) := by
  simpa only [girsanovMeasure, girsanovDensity] using
    hX.withDensity_of_integrable_real h.integrable

/-- The robust completed-cell bracket is unchanged by the terminal
Girsanov density. -/
theorem GirsanovDensityData.quadraticVariationBeforeStop_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket X q : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hX : HasQuadraticVariationBeforeStopProcessInProbability X q P) :
    HasQuadraticVariationBeforeStopProcessInProbability X q
      (girsanovMeasure P M bracket T) := by
  simpa only [girsanovMeasure, girsanovDensity] using
    hX.withDensity_of_integrable_real h.integrable

/-- Cross variation is also unchanged by the equivalent terminal Girsanov
measure. -/
theorem GirsanovDensityData.crossVariation_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket X Y covariation : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hXY : HasCrossVariationProcessInProbability X Y covariation P) :
    HasCrossVariationProcessInProbability X Y covariation
      (girsanovMeasure P M bracket T) := by
  simpa only [girsanovMeasure, girsanovDensity] using
    hXY.withDensity_of_integrable_real h.integrable

/-- In particular, every pre-Brownian version retains its deterministic
quadratic variation after the Girsanov density change. -/
theorem GirsanovDensityData.quadraticVariation_preBrownian_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hB : IsPreBrownianReal B P) :
    HasQuadraticVariationProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) (girsanovMeasure P M bracket T) := by
  apply h.quadraticVariation_girsanovMeasure
  exact fun t ↦ quadraticVariation_preBrownianReal_inProbability hB t

/-- In fact the pre-Brownian clock bracket remains valid on every completed
prefix of every uniform horizon after the Girsanov change of measure. -/
theorem GirsanovDensityData.quadraticVariationBeforeStop_preBrownian_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hB : IsPreBrownianReal B P) :
    HasQuadraticVariationBeforeStopProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) (girsanovMeasure P M bracket T) := by
  apply h.quadraticVariationBeforeStop_girsanovMeasure
  exact hasQuadraticVariationBeforeStop_preBrownianReal hB

/-- Adding an absolutely continuous finite-variation drift does not change
the deterministic Brownian bracket, and this remains true after the
equivalent Girsanov measure change.  The explicit pathwise integrability
premise records the analytic side condition hidden by Lean's totalized
Bochner integral. -/
theorem GirsanovDensityData.quadraticVariation_preBrownian_add_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B mu : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hB : IsPreBrownianReal B P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun s : ℝ ↦ mu s.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasQuadraticVariationProcessInProbability
      (fun t omega ↦ B t omega + integratedDrift mu t omega)
      (fun t _omega ↦ (t : ℝ)) (girsanovMeasure P M bracket T) := by
  apply h.quadraticVariation_girsanovMeasure
  intro t
  have hD : HasQuadraticVariationInProbabilityAt
      (integratedDrift mu) P t (fun _ ↦ 0) :=
    quadraticVariation_integratedDrift_inProbability hmuMeas t (hmuInt t)
  have hBt := quadraticVariation_preBrownianReal_inProbability hB t
  have hDB := hD.add_of_left_zero_of_aestronglyMeasurable hBt
    (fun s ↦ (stronglyMeasurable_integratedDrift hmuMeas s).aestronglyMeasurable)
    (fun s ↦ (hB.aemeasurable s).aestronglyMeasurable)
  apply hDB.congr
  · intro s
    exact Filter.Eventually.of_forall fun omega ↦ add_comm _ _
  · exact Filter.EventuallyEq.rfl

/-- The drift-shifted process retains the robust completed-cell clock bracket
under the terminal Girsanov measure. -/
theorem
    GirsanovDensityData.quadraticVariationBeforeStop_preBrownian_add_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B mu : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hB : IsPreBrownianReal B P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun s : ℝ ↦ mu s.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun t omega ↦ B t omega + integratedDrift mu t omega)
      (fun t _omega ↦ (t : ℝ)) (girsanovMeasure P M bracket T) := by
  apply h.quadraticVariationBeforeStop_girsanovMeasure
  exact hasQuadraticVariationBeforeStop_preBrownian_add_integratedDrift
    hB hmuMeas hmuInt

/-- Novikov normalizes the terminal Girsanov density to expectation one. -/
theorem GirsanovDensityData.integral_eq_one
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    ∫ omega, girsanovDensity M bracket T omega ∂P = 1 := by
  simpa only [girsanovDensity] using
    h.novikov.integral_doleansDade_eq_one_of_le
      h.localQuadraticVariation h.continuous_martingale_path
      h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
      h.martingale_zero h.bracket_zero (le_refl T)

/-- The Novikov terminal density defines a probability measure. -/
theorem GirsanovDensityData.isProbabilityMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    IsProbabilityMeasure (girsanovMeasure P M bracket T) :=
  isProbabilityMeasure_girsanovMeasure M bracket T h.integrable h.integral_eq_one

/-- Under Novikov, the original and changed measures have the same null
sets. -/
theorem GirsanovDensityData.mutuallyAbsolutelyContinuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    girsanovMeasure P M bracket T ≪ P ∧
      P ≪ girsanovMeasure P M bracket T :=
  girsanovMeasure_mutuallyAbsolutelyContinuous P M bracket T h.integrable

/-- The Bayes weighting formula for a Novikov terminal density. -/
theorem GirsanovDensityData.integral_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) (f : W → ℝ) :
    ∫ omega, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega, girsanovDensity M bracket T omega * f omega ∂P :=
  StochasticCalculus.integral_girsanovMeasure P M bracket T h.integrable f

/-- The conditional expectation of the terminal density is the stopped
density process.  This is the Bayes bridge from the terminal measure to each
filtration time. -/
theorem GirsanovDensityData.condExp_density
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) (t : ℝ≥0) :
    P[girsanovDensity M bracket T | 𝒱 t] =ᵐ[P]
      doleansDadeExponential M bracket (min t T) := by
  have hmart := h.novikov.martingale_stopAt_doleansDade
    h.localQuadraticVariation h.continuous_martingale_path
    h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
    h.martingale_zero h.bracket_zero
  by_cases ht : t ≤ T
  · simpa only [girsanovDensity, min_self, min_eq_left ht] using
      hmart.condExp_ae_eq ht
  · have hTt : T ≤ t := le_of_not_ge ht
    have hmeas : StronglyMeasurable[𝒱 t] (girsanovDensity M bracket T) := by
      simpa only [girsanovDensity, min_self] using
        hmart.stronglyAdapted.stronglyMeasurable_le hTt
    rw [condExp_of_stronglyMeasurable (𝒱.le t) hmeas h.integrable]
    simp only [girsanovDensity, min_eq_right hTt]
    exact Filter.EventuallyEq.rfl

/-- On a time-`t` event, integration under the terminal Girsanov measure can
be performed using the stopped density process at time `t`.  The statement
is vector-valued so it applies in particular to complex characteristic
functions. -/
theorem GirsanovDensityData.setIntegral_girsanovMeasure_eq_densityProcess_smul
    {W E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T t : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    {f : W → E} (hf : StronglyMeasurable[V t] f)
    (hfint : Integrable f (girsanovMeasure P M bracket T))
    {A : Set W} (hA : MeasurableSet[V t] A) :
    ∫ omega in A, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P := by
  let Q := girsanovMeasure P M bracket T
  have hA0 : MeasurableSet A := V.le t A hA
  have hterminalInt : Integrable
      (fun omega ↦ girsanovDensity M bracket T omega • f omega) P := by
    have hraw : Integrable (fun omega ↦
        (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal •
          f omega) P :=
      (integrable_withDensity_iff_integrable_smul₀'
        (E := E) h.integrable.1.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp (by
          simpa only [Q, girsanovMeasure] using hfint)
    apply hraw.congr
    exact Filter.Eventually.of_forall fun omega ↦ by
      change (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal •
        f omega = girsanovDensity M bracket T omega • f omega
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  have hpull := condExp_smul_of_aestronglyMeasurable_right
    h.integrable hterminalInt hf.aestronglyMeasurable
  calc
    ∫ omega in A, f omega ∂Q =
        ∫ omega in A, girsanovDensity M bracket T omega • f omega ∂P := by
      simpa only [Q] using
        setIntegral_girsanovMeasure_smul P M bracket T h.integrable f hA0
    _ = ∫ omega in A,
        P[fun w ↦ girsanovDensity M bracket T w • f w | V t] omega ∂P := by
      symm
      exact setIntegral_condExp (V.le t) hterminalInt hA
    _ = ∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P := by
      apply setIntegral_congr_ae hA0
      filter_upwards [hpull, h.condExp_density t] with omega hp hcond _
      change P[girsanovDensity M bracket T • f | V t] omega = _
      rw [hp]
      change P[girsanovDensity M bracket T | V t] omega • f omega = _
      rw [hcond]

/-- A pathwise-continuous real martingale remains a martingale after replacing
its filtration by its right continuation.  Uniform integrability of the
conditional expectations just above the earlier time supplies the required
`L¹` passage to the limit. -/
theorem Martingale.rightCont_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : Martingale X V P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega)) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t ↦
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((Filtration.rightCont V).le s)
    (hX.integrable t) (fun A _ _ ↦ (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n ↦ min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t) := tendsto_const_nhds
    have hs : Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using
      (Tendsto.min ht hs)
  have hcond (n : ℕ) : P[X t | V (u n)] =ᵐ[P] X (u n) :=
    hX.condExp_ae_eq (hut n)
  have hui : UniformIntegrable (fun n ↦ X (u n)) 1 P :=
    (hX.integrable t).uniformIntegrable_condExp (fun n ↦ V.le (u n)) |>.ae_eq hcond
  have hpoint : ∀ᵐ omega ∂P,
      Tendsto (fun n ↦ X (u n) omega) atTop (nhds (X s omega)) :=
    Filter.Eventually.of_forall fun omega ↦ (hcont omega).continuousAt.tendsto.comp hu
  have hinMeasure : TendstoInMeasure P (fun n ↦ X (u n)) atTop (X s) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hX.integrable (u n)).aestronglyMeasurable) hpoint
  have hL1 : Tendsto (fun n ↦ eLpNorm (X (u n) - X s) 1 P) atTop (nhds 0) :=
    (tendstoInMeasure_iff_tendsto_Lp_finite
      le_rfl ENNReal.one_ne_top
      (fun n ↦ memLp_one_iff_integrable.mpr (hX.integrable (u n)))
      (memLp_one_iff_integrable.mpr (hX.integrable s))).mp
      ⟨hinMeasure, hui.2.1⟩
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n ↦ hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      ∫ omega in A, X (u n) omega ∂P = ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n ↦ ∫ omega in A, X (u n) omega ∂P) =
      fun _ ↦ ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- A continuous common-localizer quadratic-variation contract survives
right-continuation of the filtration.  The stopping times remain stopping
times for the larger filtration, and the preceding theorem transports each
localized martingale. -/
theorem HasLocalQuadraticVariationProcessInProbability.rightCont_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket V P)
    (hcont : ∀ omega, Continuous (fun t ↦ M t omega)) :
    HasLocalQuadraticVariationProcessInProbability M bracket
      (Filtration.rightCont V) P := by
  obtain ⟨tau, htau, hmart, hqv⟩ := h
  refine ⟨tau, ?_, ?_, hqv⟩
  · exact
      { isStoppingTime := fun n t ↦
          V.le_rightCont t _ (htau.isStoppingTime n t)
        tendsto_top := htau.tendsto_top
        mono := htau.mono }
  · intro k
    exact StochasticCalculus.Martingale.rightCont_of_continuous (hmart k)
      (continuous_localizingStoppedProcess hcont (tau k))

/-- All Girsanov density data can be transported from a raw filtration to
its right continuation when the driving local martingale has continuous
paths. -/
theorem GirsanovDensityData.rightCont
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    GirsanovDensityData P (Filtration.rightCont V) M bracket T where
  novikov := h.novikov
  localQuadraticVariation :=
    h.localQuadraticVariation.rightCont_of_continuous h.continuous_martingale_path
  continuous_martingale_path := h.continuous_martingale_path
  adapted_martingale := StochasticCalculus.StronglyAdapted.mono_filtration
    h.adapted_martingale V.le_rightCont
  adapted_bracket := StochasticCalculus.StronglyAdapted.mono_filtration
    h.adapted_bracket V.le_rightCont
  continuous_monotone_bracket := h.continuous_monotone_bracket
  martingale_zero := h.martingale_zero
  bracket_zero := h.bracket_zero

/-- The elementary stochastic integral of an `E`-valued coefficient against
a real martingale on `(a,b]`.  This is the Banach-valued transform needed for
complex Fourier martingales. -/
def elementaryMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → E)
    (t : ℝ≥0) (omega : W) : E :=
  (M (min t b) omega - M (min t a) omega) • Z omega

/-- Banach-valued elementary predictable transforms preserve strong
adaptation without any integrability assumption. -/
theorem stronglyAdapted_elementaryMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted V M)
    {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z) :
    StronglyAdapted V (elementaryMartingaleSmulProcess M a b Z) := by
  intro t
  rcases le_total t a with hta | hat
  · have hzero : elementaryMartingaleSmulProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleSmulProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    rw [hzero]
    exact stronglyMeasurable_zero
  · exact ((hM (min t b)).mono
        (V.mono (min_le_left _ _)) |>.sub
      ((hM (min t a)).mono
        (V.mono (min_le_left _ _)))).smul
      (hZ.mono (V.mono hat))

/-- An integrable elementary predictable transform is a martingale. The
coefficient may be unbounded. -/
theorem martingale_elementaryMartingaleSmulProcess_of_integrable
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (hInt : ∀ t, Integrable (elementaryMartingaleSmulProcess M a b Z t) P) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  have hadapt : StronglyAdapted V
      (elementaryMartingaleSmulProcess M a b Z) := by
    intro t
    rcases le_total t a with hta | hat
    · have hzero : elementaryMartingaleSmulProcess M a b Z t = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hta,
          min_eq_left (hta.trans hab)]
      rw [hzero]
      exact stronglyMeasurable_zero
    · exact ((hM.stronglyMeasurable (min t b)).mono
          (V.mono (min_le_left _ _)) |>.sub
        ((hM.stronglyMeasurable (min t a)).mono
          (V.mono (min_le_left _ _)))).smul
        (hZ.mono (V.mono hat))
  refine ⟨hadapt, ?_⟩
  intro s t hst
  rcases le_total t a with hta | hat
  · have hIt : elementaryMartingaleSmulProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleSmulProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
      funext omega
      have hsa : s ≤ a := hst.trans hta
      simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
    rw [hIt, hIs, condExp_zero]
  · rcases le_total s a with hsa | has
    · have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
          min_eq_left (hsa.trans hab)]
      rw [hIs]
      let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
      have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
        funext omega
        simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
          Pi.smul_apply']
      have hdInt : Integrable d P :=
        (hM.integrable (min t b)).sub (hM.integrable a)
      have hprod : Integrable (d • Z) P := by
        rw [← hprocess]
        exact hInt t
      have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
        hZ.aestronglyMeasurable
      have hdelta := condExp_sub (hM.integrable (min t b))
        (hM.integrable a) (V a)
      have hamin : a ≤ min t b := le_min hat hab
      have hda : P[d | V a] =ᵐ[P] 0 := by
        filter_upwards [hdelta, hM.condExp_ae_eq hamin,
          Filter.Eventually.of_forall (congrFun
            (condExp_of_stronglyMeasurable (V.le a)
              (hM.stronglyMeasurable a) (hM.integrable a)))]
            with omega hd hfuture hpast
        change P[d | V a] omega = 0
        rw [show P[d | V a] omega =
          (P[M (min t b) | V a] - P[M a | V a]) omega by exact hd]
        simp only [Pi.sub_apply, hfuture, hpast, sub_self]
      have hIa : P[d • Z | V a] =ᵐ[P] 0 := by
        filter_upwards [hpull, hda] with omega hp hd
        simpa only [Pi.smul_apply', Pi.zero_apply, hd, zero_smul] using hp
      have htower := condExp_condExp_of_le (μ := P)
        (V.mono hsa) (V.le a) (f := d • Z)
      have hzeroCond : P[d • Z | V s] =ᵐ[P] 0 := by
        filter_upwards [htower, condExp_congr_ae hIa,
          Filter.Eventually.of_forall (congrFun
            (condExp_zero (μ := P) (m := V s) (E := E)))]
            with omega htow hcongr hzero
        rw [← htow, hcongr, hzero]
      rw [hprocess]
      exact hzeroCond
    · rcases le_total b s with hbs | hsb
      · have hconst : elementaryMartingaleSmulProcess M a b Z t =
            elementaryMartingaleSmulProcess M a b Z s := by
          funext omega
          simp [elementaryMartingaleSmulProcess,
            min_eq_right (hbs.trans hst), min_eq_right hbs,
            min_eq_right (has.trans hst), min_eq_right has]
        rw [hconst]
        exact Filter.Eventually.of_forall (congrFun
          (condExp_of_stronglyMeasurable (V.le s) (hadapt s) (hInt s)))
      · let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
        have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
          funext omega
          simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
            Pi.smul_apply']
        have hdInt : Integrable d P :=
          (hM.integrable (min t b)).sub (hM.integrable a)
        have hprod : Integrable (d • Z) P := by
          rw [← hprocess]
          exact hInt t
        have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
          (hZ.mono (V.mono has)).aestronglyMeasurable
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (V s)
        have hsmin : s ≤ min t b := le_min hst hsb
        have hpast := condExp_of_stronglyMeasurable (V.le s)
          ((hM.stronglyMeasurable a).mono (V.mono has)) (hM.integrable a)
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hsmin,
          Filter.Eventually.of_forall (congrFun hpast)]
            with omega hp hd hfuture hpast'
        have hd' : P[d | V s] omega =
            (P[M (min t b) | V s] - P[M a | V s]) omega := hd
        rw [hprocess, hp]
        change P[d | V s] omega • Z omega = _
        rw [hd', Pi.sub_apply, hfuture, hpast']
        simp only [elementaryMartingaleSmulProcess, min_eq_right has,
          min_eq_left hsb]

/-- A bounded Banach-valued coefficient known at the left endpoint defines a
martingale transform against any real martingale. -/
theorem martingale_elementaryMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  apply martingale_elementaryMartingaleSmulProcess_of_integrable hM hab hZ
  intro t
  let d : W → ℝ := fun omega ↦
    M (min t b) omega - M (min t a) omega
  have hd : Integrable d P :=
    (hM.integrable (min t b)).sub (hM.integrable (min t a))
  have hmeas : AEStronglyMeasurable
      (elementaryMartingaleSmulProcess M a b Z t) P := by
    exact hd.aestronglyMeasurable.smul
      (hZ.mono (V.le a)).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  apply (hd.norm.const_mul |C|).mono' hmeas.norm
  filter_upwards with omega
  simp only [elementaryMartingaleSmulProcess, d, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_abs]
  have h := mul_le_mul_of_nonneg_left
    ((hZbound omega).trans (le_abs_self C))
    (abs_nonneg (M (min t b) omega - M (min t a) omega))
  simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using h

/-- A finite sum of Banach-valued elementary transforms against one real
integrator. -/
def elementaryMartingaleSmulSum
    {W E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → E) : ℝ≥0 → W → E :=
  ∑ i ∈ S, elementaryMartingaleSmulProcess M (a i) (b i) (Z i)

/-- Finite Banach-valued elementary predictable transforms preserve strong
adaptation. -/
theorem stronglyAdapted_elementaryMartingaleSmulSum
    {W E I : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted V M)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → E}
    (hZ : ∀ i ∈ S, StronglyMeasurable[V (a i)] (Z i)) :
    StronglyAdapted V (elementaryMartingaleSmulSum M S a b Z) := by
  unfold elementaryMartingaleSmulSum
  intro t
  simpa only [Finset.sum_apply] using
    S.stronglyMeasurable_sum fun i hi =>
      stronglyAdapted_elementaryMartingaleSmulProcess (E := E)
        hM (hab i hi) (hZ i hi) t

/-- Finite sums of bounded predictable Banach-valued transforms are
martingales. -/
theorem martingale_elementaryMartingaleSmulSum
    {W E I : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → E}
    (hZ : ∀ i ∈ S, StronglyMeasurable[V (a i)] (Z i))
    (C : I → ℝ) (hZbound : ∀ i ∈ S, ∀ omega, ‖Z i omega‖ ≤ C i) :
    Martingale (elementaryMartingaleSmulSum M S a b Z) V P := by
  classical
  unfold elementaryMartingaleSmulSum
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using martingale_zero E V P
  | @insert i S hi ih =>
      have hhead : Martingale
          (elementaryMartingaleSmulProcess M (a i) (b i) (Z i)) V P :=
        martingale_elementaryMartingaleSmulProcess (E := E) hM
          (hab i (Finset.mem_insert_self i S))
          (hZ i (Finset.mem_insert_self i S)) (C i)
          (hZbound i (Finset.mem_insert_self i S))
      have htail : Martingale
          (∑ j ∈ S, elementaryMartingaleSmulProcess M (a j) (b j) (Z j))
          V P :=
        ih (fun j hj ↦ hab j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZbound j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hhead.add htail

/-- The coherent uniform-grid Banach-valued transform of a time-dependent
adapted coefficient against a real martingale. -/
def uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  elementaryMartingaleSmulSum M (Finset.range n)
    (fun i ↦ uniformPartitionTime T n i)
    (fun i ↦ uniformPartitionTime T n (i + 1))
    (fun i ↦ H (uniformPartitionTime T n i))

/-- Coherent Banach-valued uniform-grid transforms of adapted inputs are
strongly adapted. -/
theorem stronglyAdapted_uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : StronglyAdapted V M) (hH : StronglyAdapted V H)
    (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted V (uniformAdaptedMartingaleSmulProcess M H T n) := by
  apply stronglyAdapted_elementaryMartingaleSmulSum hM
    (Finset.range n)
    (fun i hi => monotone_uniformPartitionTime_general T n (Nat.le_succ i))
  intro i hi
  exact hH (uniformPartitionTime T n i)

/-- Uniform-grid transforms of a bounded adapted Banach-valued coefficient
against a real martingale are martingales. -/
theorem martingale_uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hH : StronglyAdapted V H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformAdaptedMartingaleSmulProcess M H T n) V P := by
  apply martingale_elementaryMartingaleSmulSum hM (Finset.range n)
    (fun i hi ↦ monotone_uniformPartitionTime_general T n (Nat.le_succ i))
    (fun i hi ↦ hH (uniformPartitionTime T n i))
    (fun _ ↦ K) (fun i hi omega ↦ hHK _ _)

/-- The sum of two coherent Banach-valued left transforms, allowing two
different real martingale integrators and two adapted coefficients. -/
def uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : ℝ≥0 → W → ℝ) (H K : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  uniformAdaptedMartingaleSmulProcess M H T n +
    uniformAdaptedMartingaleSmulProcess N K T n

/-- The two-integrator Banach-valued uniform-grid construction preserves
strong adaptation. -/
theorem stronglyAdapted_uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → E}
    (hM : StronglyAdapted V M) (hN : StronglyAdapted V N)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted V
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T n) :=
  (stronglyAdapted_uniformAdaptedMartingaleSmulProcess hM hH T n).add
    (stronglyAdapted_uniformAdaptedMartingaleSmulProcess hN hK T n)

/-- Bounded adapted coefficients against two real martingales give a
Banach-valued martingale on every deterministic grid. -/
theorem martingale_uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (T : ℝ≥0) (n : ℕ) :
    Martingale
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T n) V P := by
  exact (martingale_uniformAdaptedMartingaleSmulProcess
    hM hH CH hHbound T n).add
      (martingale_uniformAdaptedMartingaleSmulProcess
        hN hK CK hKbound T n)

/-- At the terminal horizon, the coherent Banach-valued transform is the
usual uniform-partition left sum. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T omega =
      ∑ i ∈ Finset.range (n + 1),
        (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
          M (uniformPartitionTime T (n + 1) i) omega) •
            H (uniformPartitionTime T (n + 1) i) omega := by
  simp only [uniformAdaptedMartingaleSmulProcess,
    elementaryMartingaleSmulSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [elementaryMartingaleSmulProcess,
    min_eq_right hright.2, min_eq_right hleft.2]

/-- At the terminal horizon, the two-integrator construction is the sum of
the two ordinary left Riemann sums on the common grid. -/
theorem uniformAdaptedTwoMartingaleSmulProcess_terminal
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : ℝ≥0 → W → ℝ) (H K : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T omega =
      (∑ i ∈ Finset.range (n + 1),
        (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
          M (uniformPartitionTime T (n + 1) i) omega) •
            H (uniformPartitionTime T (n + 1) i) omega) +
      ∑ i ∈ Finset.range (n + 1),
        (N (uniformPartitionTime T (n + 1) (i + 1)) omega -
          N (uniformPartitionTime T (n + 1) i) omega) •
            K (uniformPartitionTime T (n + 1) i) omega := by
  unfold uniformAdaptedTwoMartingaleSmulProcess
  simp only [Pi.add_apply]
  rw [uniformAdaptedMartingaleSmulProcess_terminal,
    uniformAdaptedMartingaleSmulProcess_terminal]

/-- For real coefficients, the Banach-valued scalar-action construction is
the existing real left-sum process at the terminal horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T =
      uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T := by
  funext omega
  rw [uniformAdaptedMartingaleSmulProcess_terminal,
    uniformAdaptedMartingaleLeftSumProcess_terminal]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [smul_eq_mul, mul_comm]

/-- Taking real parts commutes with the coherent uniform-grid transform. -/
theorem uniformAdaptedMartingaleSmulProcess_re
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).re) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).re) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.reCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.reCLM_apply]

/-- Taking imaginary parts commutes with the coherent uniform-grid
transform. -/
theorem uniformAdaptedMartingaleSmulProcess_im
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).im) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).im) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.imCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.imCLM_apply]

/-- The existing real martingale-transform isometry gives the same
grid-independent `L²` bound for the terminal scalar-action construction. -/
theorem eLpNorm_uniformAdaptedMartingaleSmulProcess_terminal_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hH : StronglyAdapted V H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    eLpNorm (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P ≤
      K * eLpNorm (M T - M 0) 2 P := by
  rw [uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum]
  exact eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le
    hM hM2 hH K hHK T n

/-- A bounded complex coefficient has a grid-independent terminal `L²`
transform bound.  Splitting into real and imaginary parts loses only the
harmless factor two and reuses the real martingale-transform isometry. -/
theorem
    eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (T : ℝ≥0) (hMT : MemLp (M T) 2 P)
    (hH : StronglyAdapted V H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (n : ℕ) :
    eLpNorm
      (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P ≤
      2 * K * eLpNorm (M T - M 0) 2 P := by
  let F : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let Fre : W → ℝ := fun omega => (F omega).re
  let Fim : W → ℝ := fun omega => (F omega).im
  have hHre : StronglyAdapted V (fun t omega => (H t omega).re) :=
    fun t => Complex.continuous_re.comp_stronglyMeasurable (hH t)
  have hHim : StronglyAdapted V (fun t omega => (H t omega).im) :=
    fun t => Complex.continuous_im.comp_stronglyMeasurable (hH t)
  have hHreBound (t : ℝ≥0) (omega : W) : ‖(H t omega).re‖ ≤ K :=
    (Complex.abs_re_le_norm (H t omega)).trans (hHK t omega)
  have hHimBound (t : ℝ≥0) (omega : W) : ‖(H t omega).im‖ ≤ K :=
    (Complex.abs_im_le_norm (H t omega)).trans (hHK t omega)
  have hRe :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHre K hHreBound n
  have hIm :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHim K hHimBound n
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hRe
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hIm
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_re M H T (n + 1)) T]
    at hRe
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_im M H T (n + 1)) T]
    at hIm
  have hFmeas : AEStronglyMeasurable F P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hM hH K hHK T (n + 1)).integrable T).1
  have hRemeas : AEStronglyMeasurable Fre P :=
    Complex.continuous_re.comp_aestronglyMeasurable hFmeas
  have hImmeas : AEStronglyMeasurable Fim P :=
    Complex.continuous_im.comp_aestronglyMeasurable hFmeas
  have hcastRe : AEStronglyMeasurable (fun omega => (Fre omega : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hRemeas
  have hcastIm : AEStronglyMeasurable
      (fun omega => (Fim omega : ℂ) * Complex.I) P :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hImmeas).mul_const _
  have hdecomp : F = fun omega =>
      (Fre omega : ℂ) + (Fim omega : ℂ) * Complex.I := by
    funext omega
    apply Complex.ext
    · simp [Fre, Fim]
    · rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im,
        Complex.ofReal_re, zero_add]
  calc
    eLpNorm
        (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P =
        eLpNorm F 2 P := by rfl
    _ = eLpNorm
        ((fun omega => (Fre omega : ℂ)) +
          fun omega => (Fim omega : ℂ) * Complex.I) 2 P := by
      rw [hdecomp]
      rfl
    _ ≤ eLpNorm (fun omega => (Fre omega : ℂ)) 2 P +
          eLpNorm (fun omega => (Fim omega : ℂ) * Complex.I) 2 P :=
      eLpNorm_add_le hcastRe hcastIm (by norm_num)
    _ = eLpNorm Fre 2 P + eLpNorm Fim 2 P := by
      congr 1
      · apply eLpNorm_congr_norm_ae
        filter_upwards with omega
        exact Complex.norm_real (Fre omega)
      · apply eLpNorm_congr_norm_ae
        filter_upwards with omega
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    _ ≤ K * eLpNorm (M T - M 0) 2 P +
          K * eLpNorm (M T - M 0) 2 P := add_le_add hRe hIm
    _ = 2 * K * eLpNorm (M T - M 0) 2 P := by ring

/-- A coherent uniform-grid transform is constant after its deterministic
horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T t : ℝ≥0) (n : ℕ) (ht : T ≤ t) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) t =
      uniformAdaptedMartingaleSmulProcess M H T (n + 1) T := by
  funext omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold elementaryMartingaleSmulProcess
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right (hright.2.trans ht), min_eq_right (hleft.2.trans ht),
    min_eq_right hright.2, min_eq_right hleft.2]

/-- Two complex martingale transforms admit the sum of their terminal
grid-independent `L²` bounds. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK) (n : ℕ) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  let A : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let D : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess N K T (n + 1) T
  have hAmeas : AEStronglyMeasurable A P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hM hH CH hHbound T (n + 1)).integrable T).1
  have hDmeas : AEStronglyMeasurable D P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hN hK CK hKbound T (n + 1)).integrable T).1
  calc
    eLpNorm
        (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T)
          2 P = eLpNorm (A + D) 2 P := by rfl
    _ ≤ eLpNorm A 2 P + eLpNorm D 2 P :=
      eLpNorm_add_le hAmeas hDmeas (by norm_num)
    _ ≤ 2 * CH * eLpNorm (M T - M 0) 2 P +
          2 * CK * eLpNorm (N T - N 0) 2 P := by
      exact add_le_add
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hM T hMT hH CH hHbound n)
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hN T hNT hK CK hKbound n)

/-- The two-transform `L²` bound holds at every observation time because
the transform is a martingale before the grid horizon and constant after it. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  have hterminal :=
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
      hM hN T hMT hNT hH hK CH CK hHbound hKbound n
  rcases le_total t T with ht | ht
  · exact (martingale_eLpNorm_le_of_le
      (martingale_uniformAdaptedTwoMartingaleSmulProcess
        hM hN hH hK CH CK hHbound hKbound T (n + 1))
      ht (by norm_num)).trans hterminal
  · have heq :
        uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t =
          uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T := by
      unfold uniformAdaptedTwoMartingaleSmulProcess
      simp only [Pi.add_apply]
      rw [uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le M H T t n ht,
        uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le N K T t n ht]
    rw [heq]
    exact hterminal

/-- Uniform-partition covariation sums of two bounded martingales are
uniformly integrable.  Discrete integration by parts reduces them to a fixed
bounded product and two transforms with grid-independent `L²` bounds. -/
theorem uniformIntegrable_quadraticCovariationApprox_of_bounded_martingales
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℝ}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (KX KY : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY) (T : ℝ≥0) :
    UniformIntegrable
      (fun n ↦ quadraticCovariationApprox X Y T (n + 1)) 1 P := by
  let R : W → ℝ := fun omega ↦
    X T omega * Y T omega - X 0 omega * Y 0 omega
  let A : ℕ → W → ℝ := fun n ↦
    uniformAdaptedMartingaleSmulProcess Y X T (n + 1) T
  let B : ℕ → W → ℝ := fun n ↦
    uniformAdaptedMartingaleSmulProcess X Y T (n + 1) T
  have hX2 (t : ℝ≥0) : MemLp (X t) 2 P :=
    MemLp.of_bound
      ((hX.stronglyMeasurable t).mono (V.le t)).aestronglyMeasurable KX
      (Filter.Eventually.of_forall (hXbound t))
  have hY2 (t : ℝ≥0) : MemLp (Y t) 2 P :=
    MemLp.of_bound
      ((hY.stronglyMeasurable t).mono (V.le t)).aestronglyMeasurable KY
      (Filter.Eventually.of_forall (hYbound t))
  have hRmeas : AEStronglyMeasurable R P := by
    exact ((((hX.stronglyMeasurable T).mono (V.le T)).aestronglyMeasurable.mul
      ((hY.stronglyMeasurable T).mono (V.le T)).aestronglyMeasurable).sub
      (((hX.stronglyMeasurable 0).mono (V.le 0)).aestronglyMeasurable.mul
        ((hY.stronglyMeasurable 0).mono (V.le 0)).aestronglyMeasurable))
  have hRbound : ∀ omega, ‖R omega‖ ≤ (2 * KX * KY : ℝ≥0) := by
    intro omega
    calc
      ‖R omega‖ ≤ ‖X T omega * Y T omega‖ +
          ‖X 0 omega * Y 0 omega‖ := norm_sub_le _ _
      _ ≤ (KX : ℝ) * KY + (KX : ℝ) * KY := by
        simp only [norm_mul]
        gcongr
        · exact hXbound T omega
        · exact hYbound T omega
        · exact hXbound 0 omega
        · exact hYbound 0 omega
      _ = (2 * KX * KY : ℝ≥0) := by push_cast; ring
  have hR2 : MemLp R 2 P :=
    MemLp.of_bound hRmeas (2 * KX * KY)
      (Filter.Eventually.of_forall hRbound)
  have hAmeas (n : ℕ) : AEStronglyMeasurable (A n) P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess hY hX.stronglyAdapted
      KX (fun t omega ↦ hXbound t omega) T (n + 1)).integrable T).1
  have hBmeas (n : ℕ) : AEStronglyMeasurable (B n) P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess hX hY.stronglyAdapted
      KY (fun t omega ↦ hYbound t omega) T (n + 1)).integrable T).1
  have hAbound (n : ℕ) : eLpNorm (A n) 2 P ≤
      KX * eLpNorm (Y T - Y 0) 2 P := by
    exact eLpNorm_uniformAdaptedMartingaleSmulProcess_terminal_le
      hY hY2 hX.stronglyAdapted KX hXbound T n
  have hBbound (n : ℕ) : eLpNorm (B n) 2 P ≤
      KY * eLpNorm (X T - X 0) 2 P := by
    exact eLpNorm_uniformAdaptedMartingaleSmulProcess_terminal_le
      hX hX2 hY.stronglyAdapted KY hYbound T n
  have hqeq (n : ℕ) : quadraticCovariationApprox X Y T (n + 1) =
      R - (A n + B n) := by
    funext omega
    dsimp only [R, A, B]
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [uniformAdaptedMartingaleSmulProcess_terminal,
      uniformAdaptedMartingaleSmulProcess_terminal]
    unfold quadraticCovariationApprox
    simp only [smul_eq_mul]
    calc
      (∑ i ∈ Finset.range (n + 1),
          (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
            X (uniformPartitionTime T (n + 1) i) omega) *
          (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Y (uniformPartitionTime T (n + 1) i) omega)) =
          ∑ i ∈ Finset.range (n + 1),
            ((X (uniformPartitionTime T (n + 1) (i + 1)) omega *
                Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
              X (uniformPartitionTime T (n + 1) i) omega *
                Y (uniformPartitionTime T (n + 1) i) omega) -
              (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
                Y (uniformPartitionTime T (n + 1) i) omega) *
                  X (uniformPartitionTime T (n + 1) i) omega -
              (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
                X (uniformPartitionTime T (n + 1) i) omega) *
                  Y (uniformPartitionTime T (n + 1) i) omega) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i ∈ Finset.range (n + 1),
            (X (uniformPartitionTime T (n + 1) (i + 1)) omega *
                Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
              X (uniformPartitionTime T (n + 1) i) omega *
                Y (uniformPartitionTime T (n + 1) i) omega)) -
          (∑ i ∈ Finset.range (n + 1),
            (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime T (n + 1) i) omega) *
                X (uniformPartitionTime T (n + 1) i) omega) -
          (∑ i ∈ Finset.range (n + 1),
            (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
              X (uniformPartitionTime T (n + 1) i) omega) *
                Y (uniformPartitionTime T (n + 1) i) omega) := by
        simp only [Finset.sum_sub_distrib]
      _ = X T omega * Y T omega - X 0 omega * Y 0 omega -
          (∑ i ∈ Finset.range (n + 1),
            (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime T (n + 1) i) omega) *
                X (uniformPartitionTime T (n + 1) i) omega) -
          (∑ i ∈ Finset.range (n + 1),
            (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
              X (uniformPartitionTime T (n + 1) i) omega) *
                Y (uniformPartitionTime T (n + 1) i) omega) := by
        have htel := Finset.sum_range_sub
          (fun i ↦ X (uniformPartitionTime T (n + 1) i) omega *
            Y (uniformPartitionTime T (n + 1) i) omega) (n + 1)
        rw [htel]
        have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
        have htop : uniformPartitionTime T (n + 1) (n + 1) = T := by
          rw [uniformPartitionTime]
          exact mul_div_cancel_right₀ T hn
        rw [htop]
        simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      _ = X T omega * Y T omega - X 0 omega * Y 0 omega -
          ((∑ i ∈ Finset.range (n + 1),
            (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime T (n + 1) i) omega) *
                X (uniformPartitionTime T (n + 1) i) omega) +
          (∑ i ∈ Finset.range (n + 1),
            (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
              X (uniformPartitionTime T (n + 1) i) omega) *
                Y (uniformPartitionTime T (n + 1) i) omega)) := by ring
  have hqmeas (n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationApprox X Y T (n + 1)) P := by
    rw [hqeq n]
    exact hRmeas.sub ((hAmeas n).add (hBmeas n))
  let D : ℝ≥0∞ := eLpNorm R 2 P +
    (KX * eLpNorm (Y T - Y 0) 2 P +
      KY * eLpNorm (X T - X 0) 2 P)
  have hDtop : D < ∞ := by
    have hYT : eLpNorm (Y T - Y 0) 2 P < ∞ := ((hY2 T).sub (hY2 0)).2
    have hXT : eLpNorm (X T - X 0) 2 P < ∞ := ((hX2 T).sub (hX2 0)).2
    simp only [D, ENNReal.add_lt_top, ENNReal.mul_lt_top,
      hR2.2, ENNReal.coe_lt_top, hYT, hXT, and_self]
  let C : ℝ≥0 := D.toNNReal
  apply uniformIntegrable_one_of_uniform_eLpNorm_two hqmeas C
  intro n
  rw [hqeq n]
  calc
    eLpNorm (R - (A n + B n)) 2 P ≤
        eLpNorm R 2 P + eLpNorm (A n + B n) 2 P :=
      eLpNorm_sub_le hRmeas ((hAmeas n).add (hBmeas n)) (by norm_num)
    _ ≤ eLpNorm R 2 P + (eLpNorm (A n) 2 P + eLpNorm (B n) 2 P) := by
      gcongr
      exact eLpNorm_add_le (hAmeas n) (hBmeas n) (by norm_num)
    _ ≤ D := by
      dsimp only [D]
      gcongr
      · exact hAbound n
      · exact hBbound n
    _ = C := by
      exact (ENNReal.coe_toNNReal hDtop.ne).symm

/-- Covariation sum on a fixed uniform grid, with every grid endpoint
stopped at the current time.  Unlike a separately repartitioned sum at each
time, this gives a coherent process for martingale approximation. -/
def uniformStoppedCovariationApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (X (min t (uniformPartitionTime T n (i + 1))) omega -
      X (min t (uniformPartitionTime T n i)) omega) *
    (Y (min t (uniformPartitionTime T n (i + 1))) omega -
      Y (min t (uniformPartitionTime T n i)) omega)

/-- Covariation carried by the first `k` cells of one uniform grid. -/
def quadraticCovariationPrefixApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range k,
    (X (uniformPartitionTime T n (i + 1)) omega -
      X (uniformPartitionTime T n i) omega) *
    (Y (uniformPartitionTime T n (i + 1)) omega -
      Y (uniformPartitionTime T n i) omega)

@[simp]
theorem quadraticCovariationPrefixApprox_zero
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n 0 omega = 0 := by
  simp [quadraticCovariationPrefixApprox]

/-- Fixed-time measurability of both processes makes every covariation
prefix measurable. -/
theorem aestronglyMeasurable_quadraticCovariationPrefixApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y : ℝ≥0 → W → ℝ}
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) (n k : ℕ) :
    AEStronglyMeasurable (quadraticCovariationPrefixApprox X Y T n k) P := by
  unfold quadraticCovariationPrefixApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
    (fun i _hi ↦ ((hXmeas (uniformPartitionTime T n (i + 1))).sub
      (hXmeas (uniformPartitionTime T n i))).mul
      ((hYmeas (uniformPartitionTime T n (i + 1))).sub
        (hYmeas (uniformPartitionTime T n i))))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

@[simp]
theorem quadraticCovariationPrefixApprox_full
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n n omega =
      quadraticCovariationApprox X Y T n omega := by
  rfl

/-- Stopping a coherent covariation sum exactly at its `k`-th grid point
turns it into the corresponding prefix sum. -/
theorem uniformStoppedCovariationApprox_uniformPartitionTime
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (hk : k ≤ n) (omega : W) :
    uniformStoppedCovariationApprox X Y T n
        (uniformPartitionTime T n k) omega =
      quadraticCovariationPrefixApprox X Y T n k omega := by
  let increment : ℕ → ℝ := fun i ↦
    (X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega) *
      (Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega)
  have htime : ∀ {i j : ℕ}, i ≤ j →
      uniformPartitionTime T n i ≤ uniformPartitionTime T n j := by
    intro i j hij
    unfold uniformPartitionTime
    gcongr
  have hhead :
      (∑ i ∈ Finset.range k, increment i) =
        quadraticCovariationPrefixApprox X Y T n k omega := by
    unfold quadraticCovariationPrefixApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ k := Finset.mem_range.mp hi
    simp only [increment, min_eq_right (htime hi1),
      min_eq_right (htime ((Nat.le_add_right i 1).trans hi1))]
  have htail : (∑ i ∈ Finset.Ico k n, increment i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k ≤ i := (Finset.mem_Ico.mp hi).1
    simp only [increment, min_eq_left (htime hki),
      min_eq_left (htime (hki.trans (Nat.le_add_right i 1))),
      sub_self, zero_mul]
  unfold uniformStoppedCovariationApprox
  change (∑ i ∈ Finset.range n, increment i) = _
  rw [← Finset.sum_range_add_sum_Ico increment hk, hhead, htail, add_zero]

/-- A point on a rational coarse grid has the same time coordinates on all
of its common uniform refinements. -/
theorem uniformPartitionTime_common_refinement_covariation
    (T : ℝ≥0) {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (i : ℕ) :
    uniformPartitionTime T (k * N) i =
      uniformPartitionTime
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) i := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hj0 : (j : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- A point in the `j`-th coarse block, sampled on an `N`-fold uniform
subdivision, is exactly the corresponding point of the `k*N` common
refinement. -/
theorem uniformPartitionTime_block_common_refinement
    (T : ℝ≥0) {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (j r : ℕ) :
    uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) N r =
      uniformPartitionTime T (k * N) (j * N + r) := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- On a nondegenerate common refinement, the left endpoint of every fine
cell active in a coarse right-endpoint block is one of that block's sampled
subdivision points. -/
theorem uniformPartitionTime_active_block_common_refinement
    (T : ℝ≥0) {k n i j : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (hactive : uniformPartitionTime T k j <
        uniformPartitionTime T (k * n) (i + 1) ∧
      uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T k (j + 1)) :
    ∃ r ∈ Finset.range (n + 1),
      uniformPartitionTime T (k * n) i =
        uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r := by
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hleftTime : uniformPartitionTime T (k * n) (j * n) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hn j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hrightTime : uniformPartitionTime T (k * n) ((j + 1) * n) =
      uniformPartitionTime T k (j + 1) := by
    have h := uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hlo : j * n ≤ i := by
    have hltTime : uniformPartitionTime T (k * n) (j * n) <
        uniformPartitionTime T (k * n) (i + 1) := by
      rw [hleftTime]
      exact hactive.1
    have hlt : j * n < i + 1 := hstrict.lt_iff_lt.mp hltTime
    omega
  have hhi : i < (j + 1) * n := by
    have hleTime : uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T (k * n) ((j + 1) * n) := by
      rw [hrightTime]
      exact hactive.2
    have hle : i + 1 ≤ (j + 1) * n := hstrict.le_iff_le.mp hleTime
    omega
  let r := i - j * n
  have hr : r < n := by
    dsimp only [r]
    rw [add_mul] at hhi
    simp only [one_mul] at hhi
    omega
  have hir : i = j * n + r := by
    dsimp only [r]
    omega
  refine ⟨r, Finset.mem_range.mpr (hr.trans (Nat.lt_succ_self n)), ?_⟩
  rw [hir]
  exact (uniformPartitionTime_block_common_refinement T hk hn j r).symm

/-- A continuous Banach-valued coefficient is uniformly close to its frozen
coarse left-endpoint value on every common refinement.  The bound is uniform
in the number of fine subdivisions inside each coarse cell. -/
theorem commonRefinement_continuousWeight_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E) (hA : Continuous A) (T : ℝ≥0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ, ∀ k, K ≤ k → 0 < k →
      ∀ n, 0 < n → ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
        uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
        ‖A (uniformPartitionTime T (k * n) i) -
          A (uniformPartitionTime T k j)‖ < epsilon := by
  intro epsilon hepsilon
  have huc : UniformContinuousOn A (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hA.continuousOn
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Tendsto
      (fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp
      (tendsto_add_atTop_nat 1)
  have hdiv : Tendsto
      (fun k : ℕ ↦ ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      atTop (nhds (0 : ℝ)) := by
    change Tendsto
      (NNReal.toReal ∘ fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0))
      atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hdiv eta heta
  refine ⟨K + 1, fun k hk hkpos n hn i hi j hj hactive ↦ ?_⟩
  have hkK : K ≤ k - 1 := by omega
  have hmeshNear := hK (k - 1) hkK
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hmesh : ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) < eta := by
    rw [← hkpred]
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hmeshNear
  obtain ⟨r, hr, htime⟩ :=
    uniformPartitionTime_active_block_common_refinement
      T (by by_contra hT; simp_all [uniformPartitionTime]) hkpos hn hactive
  have hkn : 0 < k * n := Nat.mul_pos hkpos hn
  have hi0 : i ≤ k * n := (Finset.mem_range.mp hi).le
  have hfineMem := uniformPartitionTime_mem_Icc_of_le T hkn hi0
  have hj0 : j ≤ k := (Finset.mem_range.mp hj).le
  have hcoarseMem := uniformPartitionTime_mem_Icc_of_le T hkpos hj0
  rw [← dist_eq_norm]
  apply hmod (uniformPartitionTime T (k * n) i) hfineMem
    (uniformPartitionTime T k j) hcoarseMem
  have hstep :
      uniformPartitionTime (T / (k : ℝ≥0)) n r ≤ T / (k : ℝ≥0) := by
    have hrlt : r < n + 1 := Finset.mem_range.mp hr
    exact (uniformPartitionTime_mem_Icc_of_le (T / (k : ℝ≥0)) hn
      (by omega)).2
  rw [htime]
  simp only [NNReal.dist_eq]
  have hnonneg : 0 ≤
      (((uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ≥0) : ℝ) -
        (uniformPartitionTime T k j : ℝ)) := by
    apply sub_nonneg.mpr
    exact_mod_cast (le_add_right (le_refl (uniformPartitionTime T k j)) :
        uniformPartitionTime T k j ≤
          uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r)
  rw [abs_of_nonneg hnonneg]
  have hstepReal :
      (uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ) ≤
        (T / (k : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hstep
  simpa only [NNReal.coe_add, add_sub_cancel_left] using
    hstepReal.trans_lt hmesh

/-- Freezing a continuous complex coefficient times a Lipschitz Brownian
factor separates into a continuous-coefficient error and a Brownian
oscillation error. -/
theorem norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
    {W : Type*} (A : ℝ≥0 → W → ℂ) (B : ℝ≥0 → W → ℝ)
    (g : ℝ → ℂ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) {k n i j : ℕ} (omega : W)
    (alpha R G delta : ℝ)
    (hAclose : ‖A (uniformPartitionTime T (k * n) i) omega -
        A (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ‖A (uniformPartitionTime T k j) omega‖ ≤ R)
    (hgbound : ‖g (B (uniformPartitionTime T (k * n) i) omega)‖ ≤ G)
    (hBclose : |B (uniformPartitionTime T (k * n) i) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta) :
    ‖A (uniformPartitionTime T (k * n) i) omega *
          g (B (uniformPartitionTime T (k * n) i) omega) -
        A (uniformPartitionTime T k j) omega *
          g (B (uniformPartitionTime T k j) omega)‖ ≤
      alpha * G + R * (L : ℝ) * delta := by
  let Af := A (uniformPartitionTime T (k * n) i) omega
  let Ac := A (uniformPartitionTime T k j) omega
  let gf := g (B (uniformPartitionTime T (k * n) i) omega)
  let gc := g (B (uniformPartitionTime T k j) omega)
  have hgclose : ‖gf - gc‖ ≤ (L : ℝ) * delta := by
    have hraw := hg.dist_le_mul
      (B (uniformPartitionTime T (k * n) i) omega)
      (B (uniformPartitionTime T k j) omega)
    rw [Real.dist_eq, dist_eq_norm] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_left hBclose L.coe_nonneg)
  have halpha : 0 ≤ alpha := (norm_nonneg (Af - Ac)).trans hAclose
  have hR : 0 ≤ R := (norm_nonneg Ac).trans hAbound
  calc
    ‖Af * gf - Ac * gc‖ = ‖(Af - Ac) * gf + Ac * (gf - gc)‖ := by
      congr 1
      ring
    _ ≤ ‖(Af - Ac) * gf‖ + ‖Ac * (gf - gc)‖ := norm_add_le _ _
    _ = ‖Af - Ac‖ * ‖gf‖ + ‖Ac‖ * ‖gf - gc‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ alpha * G + R * ((L : ℝ) * delta) := by
      exact add_le_add
        (mul_le_mul hAclose hgbound (norm_nonneg _) halpha)
        (mul_le_mul hAbound hgclose (norm_nonneg _) hR)
    _ = alpha * G + R * (L : ℝ) * delta := by ring

/-- Uniform control of all sampled Brownian oscillations inside coarse
blocks gives uniform control of every Lipschitz fine-grid weight by its
right-endpoint coarse-step freezing. -/
theorem commonRefinement_lipschitzWeight_close_of_blockOscillation
    {W : Type*} (B : ℝ≥0 → W → ℝ) (g : ℝ → ℝ) {L : ℝ≥0}
    (hg : LipschitzWith L g) (T : ℝ≥0) {k n : ℕ}
    (hT : 0 < T) (hk : 0 < k) (hn : 0 < n) (omega : W) (delta : ℝ)
    (hosc : ∀ j ∈ Finset.range k, ∀ r ∈ Finset.range (n + 1),
      |B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta) :
    ∀ i ∈ Finset.range (k * n),
      |g (B (uniformPartitionTime T (k * n) i) omega) -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime T k j <
                uniformPartitionTime T (k * n) (i + 1) ∧
              uniformPartitionTime T (k * n) (i + 1) ≤
                uniformPartitionTime T k (j + 1) then
            g (B (uniformPartitionTime T k j) omega)
          else 0| ≤ (L : ℝ) * delta := by
  intro i hi
  have hkn : 0 < k * n := Nat.mul_pos hk hn
  have hi1 : i + 1 ≤ k * n := Finset.mem_range.mp hi
  have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
  have hr0 : 0 < uniformPartitionTime T (k * n) (i + 1) := by
    have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
      intro a b hab
      unfold uniformPartitionTime
      have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast hkn
      gcongr
    have hpos := hstrict (Nat.zero_lt_succ i)
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      using hpos
  apply abs_sub_uniformPartition_rightEndpoint_step_sum_le
    T (uniformPartitionTime T (k * n) (i + 1)) k hk hr0 hrt
      (g (B (uniformPartitionTime T (k * n) i) omega))
      (fun j => g (B (uniformPartitionTime T k j) omega))
      ((L : ℝ) * delta)
  intro j hj hactive
  obtain ⟨r, hr, htime⟩ :=
    uniformPartitionTime_active_block_common_refinement
      T hT hk hn hactive
  have hdist := hg.dist_le_mul
    (B (uniformPartitionTime T (k * n) i) omega)
    (B (uniformPartitionTime T k j) omega)
  rw [Real.dist_eq, Real.dist_eq] at hdist
  calc
    |g (B (uniformPartitionTime T (k * n) i) omega) -
        g (B (uniformPartitionTime T k j) omega)| ≤
        (L : ℝ) *
          |B (uniformPartitionTime T (k * n) i) omega -
            B (uniformPartitionTime T k j) omega| := by
      simpa only [abs_sub_comm] using hdist
    _ ≤ (L : ℝ) * delta := by
      gcongr
      rw [htime]
      exact hosc j hj r hr

/-- At a coarse boundary of a common refinement, the completed-cell
covariation is exactly the corresponding index prefix. -/
theorem quadraticCovariationBeforeStopApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k N j : ℕ} (hk : 0 < k) (hN : 0 < N) (hj : j ≤ k)
    (omega : W) :
    quadraticCovariationBeforeStopApprox X Y T (k * N)
        (uniformPartitionTime T k j) omega =
      quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega := by
  by_cases hT0 : T = 0
  · subst T
    simp [quadraticCovariationBeforeStopApprox,
      quadraticCovariationPrefixApprox, uniformPartitionTime]
  have hT : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hT0)
  have hkn : 0 < k * N := Nat.mul_pos hk hN
  have hstrict : StrictMono (uniformPartitionTime T (k * N)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * N : ℕ) := by exact_mod_cast hkn
    gcongr
  have hboundary : uniformPartitionTime T (k * N) (j * N) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hN j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hcond (i : ℕ) :
      uniformPartitionTime T (k * N) (i + 1) ≤
          uniformPartitionTime T k j ↔
        i + 1 ≤ j * N := by
    rw [← hboundary]
    exact hstrict.le_iff_le
  have hjN : j * N ≤ k * N := Nat.mul_le_mul_right N hj
  unfold quadraticCovariationBeforeStopApprox
    quadraticCovariationPrefixApprox
  simp_rw [hcond]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A rational covariation prefix on a common refinement is literally the
ordinary covariation sum at the corresponding shorter horizon. -/
theorem quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (omega : W) :
    quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  unfold quadraticCovariationPrefixApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [uniformPartitionTime_common_refinement_covariation T hk hj hN i,
    uniformPartitionTime_common_refinement_covariation T hk hj hN (i + 1)]

/-- At a rational sub-horizon, a coherent stopped common-refinement sum is
exactly the ordinary covariation sum on the shorter horizon. -/
theorem uniformStoppedCovariationApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (hjk : j ≤ k) (omega : W) :
    uniformStoppedCovariationApprox X Y T (k * N)
        (T * (j : ℝ≥0) / (k : ℝ≥0)) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  have hstop := uniformStoppedCovariationApprox_uniformPartitionTime
    X Y T (k * N) (j * N) (Nat.mul_le_mul_right N hjk) omega
  have hprefix := quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj hN omega
  have htime : uniformPartitionTime T (k * N) (j * N) = a := by
    rw [uniformPartitionTime]
    dsimp only [a]
    have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    push_cast
    field_simp
  change uniformStoppedCovariationApprox X Y T (k * N) a omega =
    quadraticCovariationApprox X Y a (j * N) omega
  calc
    uniformStoppedCovariationApprox X Y T (k * N) a omega =
        uniformStoppedCovariationApprox X Y T (k * N)
          (uniformPartitionTime T (k * N) (j * N)) omega := by rw [htime]
    _ = quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega :=
      hstop
    _ = quadraticCovariationApprox X Y a (j * N) omega := by
      simpa only [a] using hprefix

/-- Cross variation at a rational sub-horizon controls the coherent stopped
grid along the common-refinement subsequence.  This is the exact grid bridge
available from the input contract without an additional arbitrary-partition
invariance theorem. -/
theorem HasCrossVariationProcessInProbability.uniformStopped_rational
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    TendstoInMeasure P
      (fun n ↦ uniformStoppedCovariationApprox X Y T (k * (n + 1))
        (T * (j : ℝ≥0) / (k : ℝ≥0))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have hcomp := (h a).comp hns.tendsto_atTop
  apply hcomp.congr_left
  intro n
  filter_upwards with omega
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change quadraticCovariationApprox X Y a (ns n + 1) omega = _
  rw [hcount]
  exact (uniformStoppedCovariationApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) hjk omega).symm

/-- Cross variation at a rational sub-horizon also controls the corresponding
prefix of every common refinement.  Unlike a stopped-process formulation,
this form can be multiplied by random coarse-grid coefficients. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have hcomp := (h a).comp hns.tendsto_atTop
  apply hcomp.congr_left
  intro n
  filter_upwards with omega
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change quadraticCovariationApprox X Y a (ns n + 1) omega = _
  rw [hcount]
  exact (StochasticCalculus.quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) omega).symm

/-- The common-refinement prefix limit, including its zero prefix. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement_all
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  by_cases hj : j = 0
  · subst j
    have hzero : TendstoInMeasure P
        (fun n ↦ quadraticCovariationPrefixApprox X Y T
          (k * (n + 1)) 0) atTop (C 0) := by
      apply (h 0).congr_left
      intro n
      filter_upwards with omega
      rw [quadraticCovariationPrefixApprox_zero]
      unfold quadraticCovariationApprox uniformPartitionTime
      simp
    simpa only [Nat.cast_zero, mul_zero, zero_div, zero_mul] using hzero
  · exact h.quadraticCovariationPrefixApprox_common_refinement T hk
      (Nat.pos_of_ne_zero hj)

/-- Cross-variation mass carried by the cells between two prefix indices. -/
noncomputable def quadraticCovariationBlockApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n lo hi : ℕ) (omega : W) : ℝ :=
  quadraticCovariationPrefixApprox X Y T n hi omega -
    quadraticCovariationPrefixApprox X Y T n lo omega

/-- The complete frozen coarse-step covariation on a common refinement is
literally the prefix-block expression used by the fixed-time limit. -/
theorem quadraticCovariationBeforeStop_blocks_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (c : ℕ → W → ℝ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticCovariationBeforeStopApprox X Y T (k * N)
          (uniformPartitionTime T k (j + 1)) omega -
        quadraticCovariationBeforeStopApprox X Y T (k * N)
          (uniformPartitionTime T k j) omega)) =
      ∑ j ∈ Finset.range k, c j omega *
        quadraticCovariationBlockApprox X Y T (k * N)
          (j * N) ((j + 1) * N) omega := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  rw [quadraticCovariationBeforeStopApprox_common_refinement
      X Y T hk hN (Nat.succ_le_iff.mpr hjlt) omega,
    quadraticCovariationBeforeStopApprox_common_refinement
      X Y T hk hN hjlt.le omega]
  rfl

/-- Two common-refinement prefix limits give the corresponding
cross-variation block limit, with no positivity restriction on either
endpoint. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationBlockApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (lo hi : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (lo * (n + 1)) (hi * (n + 1))) atTop
      (fun omega ↦
        C (T * (hi : ℝ≥0) / (k : ℝ≥0)) omega -
          C (T * (lo : ℝ≥0) / (k : ℝ≥0)) omega) := by
  have hhi := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk hi
  have hlo := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk lo
  exact hhi.sub_real_noMeas hlo

/-- A complete random coarse-step weight can be integrated against the
cross-variation blocks on every common refinement. -/
theorem
    HasCrossVariationProcessInProbability.fullStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℝ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega)) := by
  apply tendstoInMeasure_finset_sum_mul_fixed_real (Finset.range k)
    (fun i n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)))
    (fun i omega ↦ C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega) c
  · intro i _hi
    simpa only [uniformPartitionTime] using
      h.quadraticCovariationBlockApprox_common_refinement T hk i (i + 1)
  · intro i _hi n
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  · exact hcmeas

/-- Fixed-time cross variation therefore controls the completed-cell frozen
coarse-step covariation along every common-refinement sequence. -/
theorem
    HasCrossVariationProcessInProbability.fullStepWeight_beforeStop_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℝ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
            (uniformPartitionTime T k (i + 1)) omega -
          quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
            (uniformPartitionTime T k i) omega)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega)) := by
  have hblock := h.fullStepWeight_common_refinement
    hXmeas hYmeas T hk c hcmeas
  apply hblock.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (quadraticCovariationBeforeStop_blocks_common_refinement
      X Y T hk (Nat.zero_lt_succ n) c omega).symm

/-- Complex random coarse-step weights can likewise be integrated against a
real cross variation on common refinements.  The two real component limits
are synchronized before they are reassembled. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  let R : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let I : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let r : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  let im : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  have hR : TendstoInMeasure P R atTop r := by
    simpa only [R, r] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).re)
        (fun i hi ↦ Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hI : TendstoInMeasure P I atTop im := by
    simpa only [I, im] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).im)
        (fun i hi ↦ Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hblockmeas (i n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (i * (n + 1)) ((i + 1) * (n + 1))) P := by
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) P := by
    dsimp only [R]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hImeas (n : ℕ) : AEStronglyMeasurable (I n) P := by
    dsimp only [I]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  let combine : ℝ → ℝ → ℂ := fun x y ↦ (x : ℂ) + (y : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hparts := TendstoInMeasure.continuous_comp₂ hRmeas hImeas hR hI hcombine
  apply hparts.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, R, I, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, R, I, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add]
  · exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, r, im, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, r, im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_zero, mul_zero,
          zero_add]

/-- Fixed-time cross variation also controls complex frozen coarse-step
weights when the common-refinement sums are written with completed cells.
This is the form used by the complex Girsanov bracket residual. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_beforeStop_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k (i + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k i) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  have hblock := h.fullComplexStepWeight_common_refinement
    hXmeas hYmeas T hk c hcmeas
  apply hblock.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < k := Finset.mem_range.mp hi
    rw [quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) (Nat.succ_le_iff.mpr hilt) omega,
      quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) hilt.le omega]
    unfold quadraticCovariationBlockApprox
    push_cast
    simp only [Nat.succ_eq_add_one]

/-- Completed coarse covariation blocks are exactly a fine-cell
covariation sum with the unique active right-endpoint block weight. -/
theorem quadraticCovariationBeforeStop_uniform_blocks_eq_weighted_cells
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (c : ℕ → W → ℝ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticCovariationBeforeStopApprox X Y t n
          (uniformPartitionTime t k (j + 1)) omega -
        quadraticCovariationBeforeStopApprox X Y t n
          (uniformPartitionTime t k j) omega)) =
      ∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0) *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) := by
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticCovariationBeforeStopApprox
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  let r := uniformPartitionTime t n (i + 1)
  let a := uniformPartitionTime t k j
  let b := uniformPartitionTime t k (j + 1)
  have hab : a ≤ b := hgrid j
  by_cases hra : r ≤ a
  · have hrb : r ≤ b := hra.trans hab
    have hnot : ¬a < r := not_lt_of_ge hra
    simp only [r, a, b] at hra hrb hnot ⊢
    simp only [hra, hrb, hnot, false_and, ↓reduceIte, sub_self,
      zero_mul, mul_zero]
  · by_cases hrb : r ≤ b
    · have har : a < r := lt_of_not_ge hra
      simp only [r, a, b] at hra hrb har ⊢
      simp only [hra, hrb, har, true_and, ↓reduceIte, sub_zero]; ring
    · simp only [r, a, b] at hra hrb ⊢
      simp only [hra, hrb, and_false, ↓reduceIte, sub_self,
        zero_mul, mul_zero]

/-- Complex-valued frozen weights satisfy the same completed-block identity
against a real covariation. -/
theorem quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k j) omega : ℂ)) =
      ∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0) *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ) := by
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticCovariationBeforeStopApprox
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  let r := uniformPartitionTime t n (i + 1)
  let a := uniformPartitionTime t k j
  let b := uniformPartitionTime t k (j + 1)
  have hab : a ≤ b := hgrid j
  by_cases hra : r ≤ a
  · have hrb : r ≤ b := hra.trans hab
    have hnot : ¬a < r := not_lt_of_ge hra
    simp only [r, a, b] at hra hrb hnot ⊢
    simp only [hra, hrb, hnot, false_and, ↓reduceIte, sub_self,
      zero_mul, mul_zero]
  · by_cases hrb : r ≤ b
    · have har : a < r := lt_of_not_ge hra
      simp only [r, a, b] at hra hrb har ⊢
      simp only [hra, hrb, har, true_and, ↓reduceIte]
      push_cast
      ring
    · simp only [r, a, b] at hra hrb ⊢
      simp only [hra, hrb, and_false, ↓reduceIte, sub_self,
        zero_mul, mul_zero]

/-- Uniformly freezing the weights on completed coarse blocks perturbs a
weighted covariation by at most the weight error times the geometric mean
of the two quadratic sums. -/
theorem abs_weightedQuadraticCovariation_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (weight c : ℕ → W → ℝ) (K : ℝ) (hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      |weight i omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0| ≤ K) :
    |(∑ i ∈ Finset.range n, weight i omega *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega)) -
      ∑ j ∈ Finset.range k, c j omega *
        (quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k j) omega)| ≤
      K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
  rw [quadraticCovariationBeforeStop_uniform_blocks_eq_weighted_cells]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ i ∈ Finset.range n,
        (weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range n,
        |(weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, K *
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul]
      gcongr
      exact hweight i hi
    _ = K * (∑ i ∈ Finset.range n,
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_uniformPartition_increment_mul_le_sqrt X Y t n omega) hK

/-- A right endpoint in a positive uniform partition activates exactly one
coarse complex step. -/
theorem uniformPartition_rightEndpoint_complexStep_sum_eq
    (t r : ℝ≥0) (k : ℕ) (ht : 0 < t) (hk : 0 < k)
    (c : ℕ → ℂ) {j : ℕ} (hj : j ∈ Finset.range k)
    (hactive : uniformPartitionTime t k j < r ∧
      r ≤ uniformPartitionTime t k (j + 1)) :
    (∑ l ∈ Finset.range k,
      if uniformPartitionTime t k l < r ∧
          r ≤ uniformPartitionTime t k (l + 1) then c l else 0) = c j := by
  have hstrict : StrictMono (uniformPartitionTime t k) := by
    intro a b hab
    unfold uniformPartitionTime
    have hk' : (0 : ℝ≥0) < (k : ℕ) := by exact_mod_cast hk
    gcongr
  rw [Finset.sum_eq_single j]
  · simp only [hactive, and_self, ↓reduceIte]
  · intro l hl hlj
    have hnot : ¬(uniformPartitionTime t k l < r ∧
        r ≤ uniformPartitionTime t k (l + 1)) := by
      intro hlactive
      rcases lt_trichotomy l j with hlt | heq | hgt
      · have hle : l + 1 ≤ j := by omega
        exact (not_lt_of_ge hlactive.2)
          ((hstrict.monotone hle).trans_lt hactive.1)
      · exact hlj heq
      · have hle : j + 1 ≤ l := by omega
        exact (not_lt_of_ge hactive.2)
          ((hstrict.monotone hle).trans_lt hlactive.1)
    simp only [hnot, ↓reduceIte]
  · exact fun hnot ↦ (hnot hj).elim

/-- A complex scalar close to the unique active coarse block is close to
the corresponding complex right-endpoint step sum. -/
theorem norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    (t r : ℝ≥0) (k : ℕ) (hk : 0 < k) (hr0 : 0 < r) (hrt : r ≤ t)
    (weight : ℂ) (c : ℕ → ℂ) (K : ℝ)
    (hclose : ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < r ∧
        r ≤ uniformPartitionTime t k (j + 1) →
      ‖weight - c j‖ ≤ K) :
    ‖weight - ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        c j
      else 0‖ ≤ K := by
  have hone := uniformPartition_rightEndpoint_blocks_sum_one
    t r k hk hr0 hrt
  have honeC : (∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        (1 : ℂ)
      else 0) = 1 := by
    exact_mod_cast hone
  have hweightSum : weight = ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        weight
      else 0 := by
    calc
      weight = weight * 1 := by ring
      _ = weight * ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            (1 : ℂ)
          else 0 := by rw [honeC]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  have hdiff :
      (weight - (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            c j
          else 0)) =
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            weight - c j
          else 0) := by
    calc
      _ = (∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0 := congrArg (fun z ↦ z - ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then c j else 0)
                hweightSum
      _ = ∑ j ∈ Finset.range k,
          ((if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0) := by rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  rw [hdiff]
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        ‖if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          weight - c j
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          K
        else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hactive
      · exact hclose j hj hactive
      · norm_num
    _ = K := by
      have hscaled := congrArg (fun x : ℝ ↦ K * x) hone
      simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul,
        one_mul] using hscaled

/-- Maximum error made by freezing a complex weight on the coarse cells of
a positive common refinement. -/
noncomputable def commonRefinementMaxComplexStepError
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
  (k n : ℕ) (omega : W) : ℝ :=
  (Finset.range ((k + 1) * (n + 1))).sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖

theorem commonRefinementMaxComplexStepError_nonneg
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
    (k n : ℕ) (omega : W) :
    0 ≤ commonRefinementMaxComplexStepError A T k n omega := by
  unfold commonRefinementMaxComplexStepError
  exact (norm_nonneg _).trans
    (Finset.le_sup' (fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖)
      (Finset.mem_range.mpr (Nat.mul_pos
        (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))))

theorem stronglyMeasurable_commonRefinementMaxComplexStepError
    {W : Type*} [MeasurableSpace W] {A : ℝ≥0 → W → ℂ}
    (hA : ∀ s, StronglyMeasurable (A s)) (T : ℝ≥0) (k n : ℕ) :
    StronglyMeasurable (commonRefinementMaxComplexStepError A T k n) := by
  apply Measurable.stronglyMeasurable
  unfold commonRefinementMaxComplexStepError
  let f : ℕ → W → ℝ := fun i omega ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hf : ∀ i ∈ Finset.range ((k + 1) * (n + 1)), Measurable (f i) := by
    intro i _hi
    let g : ℕ → W → ℂ := fun j omega ↦
      if uniformPartitionTime T (k + 1) j <
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
          uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
            uniformPartitionTime T (k + 1) (j + 1) then
        A (uniformPartitionTime T (k + 1) j) omega
      else 0
    have hg : ∀ j ∈ Finset.range (k + 1), StronglyMeasurable (g j) := by
      intro j _hj
      dsimp only [g]
      split_ifs
      · exact hA _
      · exact stronglyMeasurable_const
    have hsumFun : StronglyMeasurable
        (∑ j ∈ Finset.range (k + 1), g j) :=
      Finset.stronglyMeasurable_sum (Finset.range (k + 1)) hg
    have hsum : StronglyMeasurable (fun omega ↦
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0) := by
      convert hsumFun using 1
      funext omega
      simp only [Finset.sum_apply, g]
    have hnorm :=
      ((hA (uniformPartitionTime T ((k + 1) * (n + 1)) i)).sub hsum)
        |>.norm.measurable
    simpa only [f, Pi.sub_apply] using hnorm
  have hsup := Finset.measurable_sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) hf
  convert hsup using 1
  ext omega
  symm
  exact Finset.sup'_apply _ f omega

/-- The common-refinement freezing error of a continuous complex path
vanishes, uniformly over an arbitrary number of inner subdivisions. -/
theorem commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0) (hT : 0 < T)
    (omega : W) (hA : Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    Tendsto (fun k ↦ commonRefinementMaxComplexStepError A T k (n k) omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := commonRefinement_continuousWeight_close
    (fun s ↦ A s omega) hA T (epsilon / 2) (by positivity)
  refine ⟨K, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (commonRefinementMaxComplexStepError_nonneg
      A T k (n k) omega)]
  let s := Finset.range ((k + 1) * (n k + 1))
  let f : ℕ → ℝ := fun i ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.mul_pos
    (Nat.zero_lt_succ k) (Nat.zero_lt_succ (n k)))⟩
  change s.sup' hs f < epsilon
  rw [Finset.sup'_lt_iff]
  intro i hi
  change i ∈ Finset.range ((k + 1) * (n k + 1)) at hi
  change ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖ < epsilon
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hnpos : 0 < n k + 1 := Nat.zero_lt_succ (n k)
  have hkn : 0 < (k + 1) * (n k + 1) := Nat.mul_pos hkpos hnpos
  have hi1 : i + 1 ≤ (k + 1) * (n k + 1) := Finset.mem_range.mp hi
  have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
  have hr0 :
      0 < uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) := by
    have hstrict : StrictMono
        (uniformPartitionTime T ((k + 1) * (n k + 1))) := by
      intro a b hab
      unfold uniformPartitionTime
      have hden : (0 : ℝ≥0) < ((k + 1) * (n k + 1) : ℕ) := by
        exact_mod_cast hkn
      gcongr
    have hpos := hstrict (Nat.zero_lt_succ i)
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      using hpos
  refine (norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    T (uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1))
      (k + 1) hkpos hr0 hrt
      (A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega)
      (fun j ↦ A (uniformPartitionTime T (k + 1) j) omega)
      (epsilon / 2) ?_).trans_lt (by linarith)
  intro j hj hactive
  exact (hK (k + 1) (by omega) hkpos (n k + 1) hnpos i hi j hj
    hactive).le

/-- Measurable continuous complex paths have vanishing common-refinement
freezing error in probability, uniformly over arbitrary inner counts. -/
theorem commonRefinementMaxComplexStepError_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {A : ℝ≥0 → W → ℂ} (hAmeas : ∀ s, StronglyMeasurable (A s))
    (T : ℝ≥0) (hT : 0 < T)
    (hAcont : ∀ omega, Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    TendstoInMeasure P
      (fun k ↦ commonRefinementMaxComplexStepError A T k (n k))
      atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro k
    exact (stronglyMeasurable_commonRefinementMaxComplexStepError
      hAmeas T k (n k)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
        A T hT omega (hAcont omega) n

/-- The completed-block freezing estimate remains sharp for complex left
weights; no loss from splitting into real and imaginary components is
needed. -/
theorem norm_complexWeightedQuadraticCovariation_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (weight c : ℕ → W → ℂ) (K : ℝ) (hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      ‖weight i omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0‖ ≤ K) :
    ‖(∑ i ∈ Finset.range n, weight i omega *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k (j + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k j) omega : ℂ)‖ ≤
      K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
  rw [quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range n,
        (weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, K *
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, ← Complex.ofReal_sub,
        ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs]
      simp only [Real.norm_eq_abs]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * (∑ i ∈ Finset.range n,
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_uniformPartition_increment_mul_le_sqrt X Y t n omega) hK

/-- The coherent stopped-grid covariation agrees with the ordinary
covariation approximant at its terminal horizon. -/
theorem uniformStoppedCovariationApprox_terminal
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformStoppedCovariationApprox X Y T (n + 1) T omega =
      quadraticCovariationApprox X Y T (n + 1) omega := by
  unfold uniformStoppedCovariationApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right hright.2, min_eq_right hleft.2]

/-- Process-level discrete integration by parts on one fixed uniform grid. -/
theorem uniformStopped_product_decomposition
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T (n + 1) t omega +
        uniformAdaptedMartingaleSmulProcess X Y T (n + 1) t omega +
          uniformStoppedCovariationApprox X Y T (n + 1) t omega := by
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  unfold uniformStoppedCovariationApprox
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  symm
  calc
    (∑ i ∈ Finset.range (n + 1),
        (((Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega) •
              X (uniformPartitionTime T (n + 1) i) omega +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) •
              Y (uniformPartitionTime T (n + 1) i) omega) +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) *
          (Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega))) =
        ∑ i ∈ Finset.range (n + 1),
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega *
              Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega *
              Y (min t (uniformPartitionTime T (n + 1) i)) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : uniformPartitionTime T (n + 1) i ≤ t
      · rw [min_eq_right hi]
        simp only [smul_eq_mul]
        ring
      · have hright : t ≤ uniformPartitionTime T (n + 1) i := le_of_not_ge hi
        have hnext : uniformPartitionTime T (n + 1) i ≤
            uniformPartitionTime T (n + 1) (i + 1) :=
          monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i)
        rw [min_eq_left hright, min_eq_left (hright.trans hnext)]
        simp only [sub_self, zero_smul, zero_mul, add_zero]
    _ = X (min t (uniformPartitionTime T (n + 1) (n + 1))) omega *
          Y (min t (uniformPartitionTime T (n + 1) (n + 1))) omega -
        X (min t (uniformPartitionTime T (n + 1) 0)) omega *
          Y (min t (uniformPartitionTime T (n + 1) 0)) omega := by
      exact Finset.sum_range_sub
        (fun i ↦ X (min t (uniformPartitionTime T (n + 1) i)) omega *
          Y (min t (uniformPartitionTime T (n + 1) i)) omega) (n + 1)
    _ = X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega := by
      have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      have htop : uniformPartitionTime T (n + 1) (n + 1) = T := by
        rw [uniformPartitionTime]
        exact mul_div_cancel_right₀ T hn
      rw [htop]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        min_zero]

/-- Positive-grid form of the coherent discrete product decomposition. -/
theorem uniformStopped_product_decomposition_pos
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T n t omega +
        uniformAdaptedMartingaleSmulProcess X Y T n t omega +
          uniformStoppedCovariationApprox X Y T n t omega := by
  have hn' : 1 ≤ n := hn
  simpa only [Nat.sub_add_cancel hn'] using
    uniformStopped_product_decomposition X Y T (n - 1) t omega

/-- Exact discrete integration by parts on a uniform partition.  The product
increment is the sum of the two predictable left transforms and the
quadratic-covariation approximant. -/
theorem uniformPartition_product_decomposition
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    X T omega * Y T omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T (n + 1) T omega +
        uniformAdaptedMartingaleSmulProcess X Y T (n + 1) T omega +
          quadraticCovariationApprox X Y T (n + 1) omega := by
  rw [uniformAdaptedMartingaleSmulProcess_terminal,
    uniformAdaptedMartingaleSmulProcess_terminal]
  unfold quadraticCovariationApprox
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  symm
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Y (uniformPartitionTime T (n + 1) i) omega) •
              X (uniformPartitionTime T (n + 1) i) omega +
          (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
            X (uniformPartitionTime T (n + 1) i) omega) •
              Y (uniformPartitionTime T (n + 1) i) omega +
          (X (uniformPartitionTime T (n + 1) (i + 1)) omega -
            X (uniformPartitionTime T (n + 1) i) omega) *
          (Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Y (uniformPartitionTime T (n + 1) i) omega))) =
        ∑ i ∈ Finset.range (n + 1),
          (X (uniformPartitionTime T (n + 1) (i + 1)) omega *
              Y (uniformPartitionTime T (n + 1) (i + 1)) omega -
            X (uniformPartitionTime T (n + 1) i) omega *
              Y (uniformPartitionTime T (n + 1) i) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [smul_eq_mul]
      ring
    _ = X (uniformPartitionTime T (n + 1) (n + 1)) omega *
          Y (uniformPartitionTime T (n + 1) (n + 1)) omega -
        X (uniformPartitionTime T (n + 1) 0) omega *
          Y (uniformPartitionTime T (n + 1) 0) omega := by
      exact Finset.sum_range_sub
        (fun i ↦ X (uniformPartitionTime T (n + 1) i) omega *
          Y (uniformPartitionTime T (n + 1) i) omega) (n + 1)
    _ = X T omega * Y T omega - X 0 omega * Y 0 omega := by
      have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      have htop : uniformPartitionTime T (n + 1) (n + 1) = T := by
        rw [uniformPartitionTime]
        exact mul_div_cancel_right₀ T hn
      rw [htop]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]

/-- A measurable Banach-valued `L¹`-norm limit of integrable functions is
integrable. -/
theorem integrable_of_tendsto_eLpNorm_one_sub_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {f : ℕ → W → E} {g : W → E}
    (hf : ∀ n, Integrable (f n) P)
    (hg : AEStronglyMeasurable g P)
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g - f n) 1 P)
      Filter.atTop (nhds 0)) :
    Integrable g P := by
  have hlt : ∀ᶠ n in Filter.atTop,
      eLpNorm (g - f n) 1 P < 1 :=
    (tendsto_order.1 hconv).2 1 (by simp)
  rcases hlt.exists with ⟨n, hn⟩
  have hdiff : Integrable (g - f n) P :=
    memLp_one_iff_integrable.mp
      ⟨hg.sub (hf n).1, hn.trans (by simp)⟩
  simpa only [sub_add_cancel] using hdiff.add (hf n)

/-- A strongly adapted pointwise-in-time `L¹`-norm limit of Banach-valued
martingales is a martingale. -/
theorem martingale_of_tendsto_eLpNorm_one_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hconv : ∀ t, Filter.Tendsto
      (fun n ↦ eLpNorm (Y t - X n t) 1 P) Filter.atTop (nhds 0)) :
    Martingale Y V P := by
  have hYint : ∀ t, Integrable (Y t) P := fun t ↦
    integrable_of_tendsto_eLpNorm_one_sub_banach
      (fun n ↦ (hX n).integrable t)
      ((hYadapt t).mono (V.le t)).aestronglyMeasurable (hconv t)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff
    ((stronglyMeasurable_condExp.mono (V.le s)).sub
      ((hYadapt s).mono (V.le s))).aestronglyMeasurable one_ne_zero]
  apply le_antisymm
  · have hconvS : Filter.Tendsto (fun n ↦ eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      convert hconv s using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Filter.Tendsto (fun n ↦
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      simpa only [add_zero] using (hconv t).add hconvS
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hdecomp :
        P[Y t | V s] - Y s =ᵐ[P]
          P[Y t - X n t | V s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (V s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      abel
    calc
      eLpNorm (P[Y t | V s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | V s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | V s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le
          (integrable_condExp (μ := P) (m := V s)
          (f := Y t - X n t)).1
          ((((hX n).stronglyMeasurable s).mono
            (V.le s)).aestronglyMeasurable.sub (hYint s).1) le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- To close a Banach-valued martingale it is enough to approximate each
ordered pair of times by its own sequence of martingales.  No single
selector has to work simultaneously at every observation time. -/
theorem martingale_of_pairwise_tendsto_eLpNorm_one_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {Y : ℝ≥0 → W → E}
    (hYadapt : StronglyAdapted V Y)
    (hYint : ∀ t, Integrable (Y t) P)
    (happrox : ∀ s t, s ≤ t →
      ∃ X : ℕ → ℝ≥0 → W → E,
        (∀ n, Martingale (X n) V P) ∧
        Tendsto (fun n => eLpNorm (Y s - X n s) 1 P)
          atTop (nhds 0) ∧
        Tendsto (fun n => eLpNorm (Y t - X n t) 1 P)
          atTop (nhds 0)) :
    Martingale Y V P := by
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  obtain ⟨X, hX, hconvS, hconvT⟩ := happrox s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff
    ((stronglyMeasurable_condExp.mono (V.le s)).sub
      ((hYadapt s).mono (V.le s))).aestronglyMeasurable one_ne_zero]
  apply le_antisymm
  · have hconvS' : Tendsto (fun n => eLpNorm (X n s - Y s) 1 P)
        atTop (nhds 0) := by
      convert hconvS using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Tendsto (fun n =>
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        atTop (nhds 0) := by
      simpa only [add_zero] using hconvT.add hconvS'
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n => ?_
    have hdecomp :
        P[Y t | V s] - Y s =ᵐ[P]
          P[Y t - X n t | V s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (V s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      abel
    calc
      eLpNorm (P[Y t | V s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | V s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | V s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le
          (integrable_condExp (μ := P) (m := V s)
            (f := Y t - X n t)).1
          ((((hX n).stronglyMeasurable s).mono
            (V.le s)).aestronglyMeasurable.sub (hYint s).1) le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- Banach-valued Vitali convergence in `L¹`: convergence in measure plus
uniform integrability gives convergence of the `L¹` distance. -/
theorem tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {X : ℕ → W → E} {Y : W → E}
    (hUI : UniformIntegrable X 1 P)
    (hconv : TendstoInMeasure P X atTop Y) :
    Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (nhds 0) := by
  have hYmem : MemLp Y 1 P := hUI.memLp_of_tendstoInMeasure hconv
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ (hUI.memLp n).1) hYmem hUI.unifIntegrable hconv

/-- Banach-valued Vitali closure for martingales: convergence in measure
plus uniform integrability at every time gives the `L¹` convergence required
by `martingale_of_tendsto_eLpNorm_one_banach`. -/
theorem martingale_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hUI : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) :
    Martingale Y V P := by
  apply martingale_of_tendsto_eLpNorm_one_banach hX hYadapt
  intro t
  have hLp : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI t) (hconv t)
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- Uniform integrability passes from one measurable family to any
Banach-valued family whose pointwise norm it dominates.  The source and
target spaces may differ. -/
theorem UniformIntegrable.mono_norm_banach
    {W I E F : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {P : Measure W} {f : I → W → E} {g : I → W → F}
    {p : ℝ≥0∞} (hf : UniformIntegrable f p P)
    (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hgf : ∀ i omega, ‖g i omega‖ ≤ ‖f i omega‖) :
    UniformIntegrable g p P := by
  refine ⟨hg, ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hf.2.1 hepsilon
    refine ⟨delta, hdelta, fun i s hs hPs ↦ ?_⟩
    apply (eLpNorm_mono fun omega ↦ ?_).trans (hbound i s hs hPs)
    by_cases homega : omega ∈ s
    · simp only [Set.indicator_of_mem homega]
      exact hgf i omega
    · simp only [Set.indicator_of_notMem homega, norm_zero]
      exact le_rfl
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun i ↦ (eLpNorm_mono (hgf i)).trans (hC i)⟩

/-- Uniform integrability is preserved when restricting to an arbitrary
reindexed subfamily. -/
theorem UniformIntegrable.comp_index
    {W I J E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (g : J → I) :
    UniformIntegrable (fun j => f (g j)) p P := by
  refine ⟨fun j => hf.1 (g j), ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hf.2.1 hepsilon
    exact ⟨delta, hdelta, fun j => hbound (g j)⟩
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun j => hC (g j)⟩

/-- The sum of two uniformly integrable Banach-valued families is uniformly
integrable. -/
theorem UniformIntegrable.add_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f g : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hg : UniformIntegrable g p P)
    (hp : 1 ≤ p) :
    UniformIntegrable (fun i omega => f i omega + g i omega) p P := by
  refine ⟨fun i => (hf.1 i).add (hg.1 i), ?_, ?_⟩
  · change UnifIntegrable (f + g) p P
    exact hf.2.1.add hg.2.1 hp hf.1 hg.1
  · obtain ⟨Cf, hCf⟩ := hf.2.2
    obtain ⟨Cg, hCg⟩ := hg.2.2
    refine ⟨Cf + Cg, fun i => ?_⟩
    exact (eLpNorm_add_le (hf.1 i) (hg.1 i) hp).trans
      (add_le_add (hCf i) (hCg i))

/-- Uniform integrability is stable under an `L¹`-vanishing perturbation.
This is the diagonal-selection tool needed when the approximating Euler
martingale for the `n`-th cap is chosen increasingly accurately. -/
theorem UniformIntegrable.of_tendsto_eLpNorm_one_sub
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure W} {f g : ℕ → W → E}
    (hg : UniformIntegrable g 1 P)
    (hf : ∀ n, MemLp (f n) 1 P)
    (hfg : Tendsto (fun n => eLpNorm (f n - g n) 1 P)
      atTop (nhds 0)) :
    UniformIntegrable f 1 P := by
  let d : ℕ → W → E := fun n => f n - g n
  have hdMem : ∀ n, MemLp (d n) 1 P := fun n => by
    exact (hf n).sub (hg.memLp n)
  have hdUnif : UnifIntegrable d 1 P := by
    apply unifIntegrable_of_tendsto_Lp_zero le_rfl ENNReal.one_ne_top hdMem
    simpa only [d] using hfg
  have hsmall : ∀ᶠ n in atTop, eLpNorm (d n) 1 P ≤ 1 := by
    have hlt : ∀ᶠ n in atTop, eLpNorm (d n) 1 P < 1 :=
      (tendsto_order.1 (by simpa only [d] using hfg)).2 1 (by simp)
    exact hlt.mono fun _ hn => hn.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  let S : ℝ≥0∞ := ∑ i ∈ Finset.range N, eLpNorm (d i) 1 P
  have hStop : S ≠ ∞ := by
    dsimp only [S]
    exact ENNReal.sum_ne_top.2 fun i _hi => (hdMem i).2.ne
  let C : ℝ≥0 := (S + 1).toNNReal
  have hC (n : ℕ) : eLpNorm (d n) 1 P ≤ (C : ℝ≥0∞) := by
    change eLpNorm (d n) 1 P ≤ ((S + 1).toNNReal : ℝ≥0∞)
    rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.mpr ⟨hStop, by simp⟩)]
    by_cases hn : n < N
    · calc
        eLpNorm (d n) 1 P ≤ S := by
          change eLpNorm (d n) 1 P ≤
            ∑ i ∈ Finset.range N, eLpNorm (d i) 1 P
          exact Finset.single_le_sum
            (f := fun i => eLpNorm (d i) 1 P)
            (s := Finset.range N) (fun i _hi => by exact bot_le)
            (Finset.mem_range.mpr hn)
        _ ≤ S + 1 := le_add_right le_rfl
    · calc
        eLpNorm (d n) 1 P ≤ 1 := hN n (le_of_not_gt hn)
        _ ≤ S + 1 := le_add_left le_rfl
  have hd : UniformIntegrable d 1 P :=
    ⟨fun n => (hdMem n).1, hdUnif, ⟨C, hC⟩⟩
  have hsum := UniformIntegrable.add_banach hg hd le_rfl
  apply hsum.ae_eq
  intro n
  exact Filter.Eventually.of_forall fun omega => by
    simp only [d, Pi.sub_apply]
    abel

/-- `L¹` convergence can be chained through a varying intermediate family. -/
theorem tendsto_eLpNorm_one_sub_of_chain
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure W} {f g h : ℕ → W → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hh : ∀ n, AEStronglyMeasurable (h n) P)
    (hfg : Tendsto (fun n => eLpNorm (f n - g n) 1 P)
      atTop (nhds 0))
    (hgh : Tendsto (fun n => eLpNorm (g n - h n) 1 P)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n - h n) 1 P)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun n =>
      eLpNorm (f n - g n) 1 P + eLpNorm (g n - h n) 1 P)
      atTop (nhds 0) := by
    simpa only [add_zero] using hfg.add hgh
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro n
  calc
    eLpNorm (f n - h n) 1 P =
        eLpNorm ((f n - g n) + (g n - h n)) 1 P := by
      congr 1
      funext omega
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    _ ≤ eLpNorm (f n - g n) 1 P + eLpNorm (g n - h n) 1 P :=
      eLpNorm_add_le ((hf n).sub (hg n)) ((hg n).sub (hh n)) le_rfl

/-- A fixed natural multiple of a uniformly integrable Banach-valued family
is uniformly integrable. -/
theorem UniformIntegrable.nsmul_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hp : 1 ≤ p) (n : ℕ) :
    UniformIntegrable (fun i omega => n • f i omega) p P := by
  induction n with
  | zero =>
      simp only [zero_nsmul]
      refine ⟨fun _ => aestronglyMeasurable_const, ?_, ⟨0, fun _ => by simp⟩⟩
      intro epsilon hepsilon
      exact ⟨1, one_pos, fun _ _ _ _ => by simp⟩
  | succ n hn =>
      simpa only [Nat.succ_eq_add_one, add_nsmul, one_nsmul] using
        UniformIntegrable.add_banach hn hf hp

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right continuation of its filtration when its values are
uniformly integrable along every convergent deterministic-time sequence. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => X (a n)) atTop (X r))
    (hUI : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        UniformIntegrable (fun n => X (a n)) 1 P) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t =>
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ => (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n =>
    min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ => t) atTop (nhds t) :=
      tendsto_const_nhds
    have hs : Tendsto
        (fun n : ℕ => s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by
      simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  have hL1 : Tendsto (fun n => eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI s u hu) (hstoch s u hu)
  have hIntegral : Tendsto
      (fun n => ∫ omega in A, X (u n) omega ∂P) atTop
      (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s)
      (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) =
        ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n => ∫ omega in A, X (u n) omega ∂P) =
      fun _ => ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right-continuation of its filtration when it is bounded on
each deterministic time interval.  The local bound supplies uniform
integrability for the values just to the right of the conditioning time. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n ↦ X (a n)) atTop (X r))
    (hbound : ∀ T : ℝ≥0, ∃ K : ℝ≥0, ∀ t ≤ T, ∀ omega,
      ‖X t omega‖ ≤ K) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t ↦
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ ↦ (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n ↦ min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t) := tendsto_const_nhds
    have hs : Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  obtain ⟨K, hK⟩ := hbound t
  have hmeas (n : ℕ) : AEStronglyMeasurable (X (u n)) P :=
    (hX.integrable (u n)).aestronglyMeasurable
  have hconst : UniformIntegrable
      (fun _ : ℕ ↦ fun _ : W ↦ (K : ℝ)) 1 P :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr (integrable_const (K : ℝ)))
  have hUI : UniformIntegrable (fun n ↦ X (u n)) 1 P :=
    UniformIntegrable.mono_norm_banach hconst hmeas fun n omega ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] using
        hK (u n) (hut n) omega
  have hL1 : Tendsto (fun n ↦ eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      hUI (hstoch s u hu)
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n ↦ hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) = ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n ↦ ∫ omega in A, X (u n) omega ∂P) =
      fun _ ↦ ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- For bounded martingales, a process-level cross-variation limit in
probability automatically improves to `L¹` convergence. -/
theorem
    HasCrossVariationProcessInProbability.tendsto_eLpNorm_one_of_bounded_martingales
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (KX KY : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (quadraticCovariationApprox X Y T (n + 1) - C T) 1 P)
      atTop (nhds 0) := by
  exact tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    (uniformIntegrable_quadraticCovariationApprox_of_bounded_martingales
      hX hY KX KY hXbound hYbound T) (h T)

/-- The rational common-refinement bridge also converges in `L¹` for
bounded martingales.  Thus the coherent stopped-grid product decomposition
has the correct compensator at every positive rational sub-horizon. -/
theorem
    HasCrossVariationProcessInProbability.tendsto_eLpNorm_one_uniformStopped_rational
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (KX KY : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    Tendsto (fun n ↦ eLpNorm
      (uniformStoppedCovariationApprox X Y T (k * (n + 1))
        (T * (j : ℝ≥0) / (k : ℝ≥0)) -
        C (T * (j : ℝ≥0) / (k : ℝ≥0))) 1 P)
      atTop (nhds 0) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have hLp := (h.tendsto_eLpNorm_one_of_bounded_martingales
    hX hY KX KY hXbound hYbound a).comp hns.tendsto_atTop
  apply (tendsto_congr' ?_).2 hLp
  filter_upwards with n
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change eLpNorm
      (uniformStoppedCovariationApprox X Y T (k * (n + 1)) a - C a) 1 P =
    eLpNorm (quadraticCovariationApprox X Y a (ns n + 1) - C a) 1 P
  rw [hcount]
  apply congrArg (fun f : W → ℝ ↦ eLpNorm (f - C a) 1 P)
  funext omega
  exact uniformStoppedCovariationApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) hjk omega

/-- Stochastic integration by parts on rational times.  For two bounded
martingales, the compensated product has equal past-event integrals between a
positive rational sub-horizon and the terminal horizon. -/
theorem
    HasCrossVariationProcessInProbability.setIntegral_stoppedProduct_sub_eq_rational
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (KX KY : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k)
    {Aset : Set W}
    (hAset : MeasurableSet[V (T * (j : ℝ≥0) / (k : ℝ≥0))] Aset) :
    (∫ omega in Aset,
      X (T * (j : ℝ≥0) / (k : ℝ≥0)) omega *
          Y (T * (j : ℝ≥0) / (k : ℝ≥0)) omega -
        X 0 omega * Y 0 omega -
        C (T * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
      ∫ omega in Aset,
        X T omega * Y T omega - X 0 omega * Y 0 omega - C T omega ∂P := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  have hka0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have haT : a ≤ T := by
    dsimp only [a]
    calc
      T * (j : ℝ≥0) / (k : ℝ≥0) ≤
          T * (k : ℝ≥0) / (k : ℝ≥0) := by gcongr
      _ = T := mul_div_cancel_right₀ T hka0
  let S : ℕ → ℝ≥0 → W → ℝ := fun n ↦
    uniformAdaptedMartingaleSmulProcess Y X T (k * (n + 1)) +
      uniformAdaptedMartingaleSmulProcess X Y T (k * (n + 1))
  let F : ℝ≥0 → W → ℝ := fun t omega ↦
    X (min t T) omega * Y (min t T) omega -
      X 0 omega * Y 0 omega - C t omega
  have hS (n : ℕ) : Martingale (S n) V P := by
    apply Martingale.add
    · exact martingale_uniformAdaptedMartingaleSmulProcess
        hY hX.stronglyAdapted KX hXbound T (k * (n + 1))
    · exact martingale_uniformAdaptedMartingaleSmulProcess
        hX hY.stronglyAdapted KY hYbound T (k * (n + 1))
  have hFmeas (t : ℝ≥0) : AEStronglyMeasurable (F t) P := by
    have hXt : AEStronglyMeasurable (X (min t T)) P :=
      (((hX.stronglyMeasurable (min t T)).mono
        (V.mono (min_le_left _ _))).mono (V.le t)).aestronglyMeasurable
    have hYt : AEStronglyMeasurable (Y (min t T)) P :=
      (((hY.stronglyMeasurable (min t T)).mono
        (V.mono (min_le_left _ _))).mono (V.le t)).aestronglyMeasurable
    have hX0 : AEStronglyMeasurable (X 0) P :=
      (((hX.stronglyMeasurable 0).mono
        (V.mono bot_le)).mono (V.le t)).aestronglyMeasurable
    have hY0 : AEStronglyMeasurable (Y 0) P :=
      (((hY.stronglyMeasurable 0).mono
        (V.mono bot_le)).mono (V.le t)).aestronglyMeasurable
    exact ((hXt.mul hYt).sub (hX0.mul hY0)).sub
      ((hC t).mono (V.le t)).aestronglyMeasurable
  have hconvF (r : ℝ≥0) (hrT : r ≤ T)
      (hcov : Tendsto (fun n ↦ eLpNorm
        (uniformStoppedCovariationApprox X Y T (k * (n + 1)) r - C r) 1 P)
        atTop (nhds 0)) :
      Tendsto (fun n ↦ eLpNorm (S n r - F r) 1 P) atTop (nhds 0) := by
    apply (tendsto_congr' ?_).2 hcov
    filter_upwards with n
    apply eLpNorm_congr_norm_ae
    filter_upwards with omega
    have hnpos : 0 < k * (n + 1) := Nat.mul_pos hk (Nat.zero_lt_succ n)
    have hprod := uniformStopped_product_decomposition_pos
      X Y T (k * (n + 1)) hnpos r omega
    change ‖S n r omega - F r omega‖ =
      ‖uniformStoppedCovariationApprox X Y T (k * (n + 1)) r omega -
        C r omega‖
    have heq : S n r omega - F r omega =
        C r omega -
          uniformStoppedCovariationApprox X Y T (k * (n + 1)) r omega := by
      dsimp only [S, F]
      simp only [Pi.add_apply]
      rw [min_eq_left hrT] at hprod
      rw [min_eq_left hrT]
      linarith
    rw [heq, norm_sub_rev]
  have hcovA := h.tendsto_eLpNorm_one_uniformStopped_rational
    hX hY KX KY hXbound hYbound T hk hj hjk
  have hconvA : Tendsto (fun n ↦ eLpNorm (S n a - F a) 1 P)
      atTop (nhds 0) := by
    apply hconvF a haT
    simpa only [a] using hcovA
  have hcovT0 := h.tendsto_eLpNorm_one_uniformStopped_rational
    hX hY KX KY hXbound hYbound T hk hk le_rfl
  have hTk : T * (k : ℝ≥0) / (k : ℝ≥0) = T :=
    mul_div_cancel_right₀ T hka0
  have hconvT : Tendsto (fun n ↦ eLpNorm (S n T - F T) 1 P)
      atTop (nhds 0) := by
    apply hconvF T le_rfl
    simpa only [hTk] using hcovT0
  have hIntA := tendsto_setIntegral_of_L1' (F a) (hFmeas a)
    (Filter.Eventually.of_forall fun n ↦ (hS n).integrable a) hconvA Aset
  have hIntT := tendsto_setIntegral_of_L1' (F T) (hFmeas T)
    (Filter.Eventually.of_forall fun n ↦ (hS n).integrable T) hconvT Aset
  have hseq : (fun n ↦ ∫ omega in Aset, S n a omega ∂P) =
      fun n ↦ ∫ omega in Aset, S n T omega ∂P := by
    funext n
    exact (hS n).setIntegral_eq haT (by simpa only [a] using hAset)
  rw [hseq] at hIntA
  have hlimit := tendsto_nhds_unique hIntA hIntT
  simpa only [F, a, min_eq_left haT, min_self] using hlimit

/-- An adapted integrable process whose past-event integrals agree
at positive rational subdivisions is a martingale as soon as it is
stochastically continuous and uniformly integrable along convergent time
sequences.  This is the unbounded Banach-valued closure needed for normalized
Fourier processes. -/
theorem
    martingale_of_uniformRational_setIntegral_eq_of_tendstoInMeasure_of_uniformIntegrable
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {F : ℝ≥0 → W → E}
    (hF : StronglyAdapted V F) (hFint : ∀ t, Integrable (F t) P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n ↦ F (a n)) atTop (F r))
    (hUI : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        UniformIntegrable (fun n ↦ F (a n)) 1 P)
    (hrational : ∀ (T : ℝ≥0) {k j : ℕ}, 0 < k → 0 < j → j ≤ k →
      ∀ {A : Set W},
        MeasurableSet[V (T * (j : ℝ≥0) / (k : ℝ≥0))] A →
          (∫ omega in A, F (T * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
            ∫ omega in A, F T omega ∂P) :
    Martingale F V P := by
  have hFmeas (t : ℝ≥0) : AEStronglyMeasurable (F t) P :=
    ((hF t).mono (V.le t)).aestronglyMeasurable
  have hlimit (r : ℝ≥0) (a : ℕ → ℝ≥0)
      (ha : Tendsto a atTop (nhds r)) (A : Set W) :
      Tendsto (fun n ↦ ∫ omega in A, F (a n) omega ∂P) atTop
        (nhds (∫ omega in A, F r omega ∂P)) := by
    have hLp :=
      tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
        (hUI r a ha) (hstoch r a ha)
    exact tendsto_setIntegral_of_L1' (F r) (hFmeas r)
      (Filter.Eventually.of_forall fun n ↦ hFint (a n)) hLp A
  refine ⟨hF, ?_⟩
  intro s t hst
  refine (ae_eq_condExp_of_forall_setIntegral_eq (V.le s)
    (hFint t) (fun A _ _ ↦ (hFint s).integrableOn) ?_
    (hF s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases hstEq : s = t
  · subst t
    rfl
  have hslt : s < t := lt_of_le_of_ne hst hstEq
  by_cases hs0 : s = 0
  · subst s
    let a : ℕ → ℝ≥0 := fun n ↦ t / (n + 1 : ℕ)
    have ha : Tendsto a atTop (nhds 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat t).comp
        (tendsto_add_atTop_nat 1)
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hden : 0 < n + 1 := Nat.zero_lt_succ n
      have hraw := hrational t hden Nat.one_pos
        (Nat.succ_le_succ (Nat.zero_le n))
        (V.mono bot_le A hA)
      simpa only [a, Nat.cast_one, mul_one] using hraw
    have hconv := hlimit 0 a ha A
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P)
        atTop (nhds (∫ omega in A, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv hconst
  · let tau : Unit → WithTop ℝ≥0 := fun _ ↦ (s : WithTop ℝ≥0)
    have hbound : ∀ omega, tau omega ≤ (t : WithTop ℝ≥0) :=
      fun _ ↦ WithTop.coe_le_coe.mpr hst
    let j : ℕ → ℕ := fun n ↦ uniformPartitionCeilIndex tau t (n + 1)
      (Nat.zero_lt_succ n) hbound ()
    let a : ℕ → ℝ≥0 := fun n ↦ uniformPartitionTime t (n + 1) (j n)
    have hjpos (n : ℕ) : 0 < j n := by
      by_contra hn
      have hj0 : j n = 0 := Nat.eq_zero_of_not_pos hn
      have hspec := uniformPartitionCeilIndex_spec tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
      change (s : WithTop ℝ≥0) ≤
        (uniformPartitionTime t (n + 1) (j n) : WithTop ℝ≥0) at hspec
      rw [hj0] at hspec
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        WithTop.coe_zero] at hspec
      exact hs0 (nonpos_iff_eq_zero.mp (WithTop.coe_le_coe.mp hspec))
    have hjle (n : ℕ) : j n ≤ n + 1 :=
      uniformPartitionCeilIndex_le tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
    have hsa (n : ℕ) : s ≤ a n := by
      exact WithTop.coe_le_coe.mp
        (uniformPartitionCeilIndex_spec tau t (n + 1)
          (Nat.zero_lt_succ n) hbound ())
    have ha : Tendsto a atTop (nhds s) := by
      have hwith := tendsto_uniformPartitionCeilStoppingTime tau t hbound ()
      have huntop := (WithTop.tendsto_untopA WithTop.coe_ne_top).comp hwith
      have hcoe (x : ℝ≥0) : WithTop.untopA (x : WithTop ℝ≥0) = x := rfl
      change Tendsto (fun n ↦ WithTop.untopA (a n : WithTop ℝ≥0))
        atTop (nhds (WithTop.untopA (s : WithTop ℝ≥0))) at huntop
      simpa only [hcoe] using huntop
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hraw := hrational t (Nat.zero_lt_succ n) (hjpos n) (hjle n)
        (V.mono (hsa n) A hA)
      simpa only [a, uniformPartitionTime] using hraw
    have hconv := hlimit s a ha A
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P)
        atTop (nhds (∫ omega in A, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv hconst

/-- A uniformly bounded specialization of the preceding Banach-valued
rational-grid closure.  The uniform bound supplies both integrability and
uniform integrability along every convergent time sequence. -/
theorem martingale_of_uniformRational_setIntegral_eq_of_tendstoInMeasure
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {F : ℝ≥0 → W → E}
    (hF : StronglyAdapted V F)
    (K : ℝ≥0) (hFbound : ∀ t omega, ‖F t omega‖ ≤ K)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n ↦ F (a n)) atTop (F r))
    (hrational : ∀ (T : ℝ≥0) {k j : ℕ}, 0 < k → 0 < j → j ≤ k →
      ∀ {A : Set W},
        MeasurableSet[V (T * (j : ℝ≥0) / (k : ℝ≥0))] A →
          (∫ omega in A, F (T * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
            ∫ omega in A, F T omega ∂P) :
    Martingale F V P := by
  have hFmeas (r : ℝ≥0) : AEStronglyMeasurable (F r) P :=
    ((hF r).mono (V.le r)).aestronglyMeasurable
  have hFint (r : ℝ≥0) : Integrable (F r) P := by
    refine Integrable.mono' (integrable_const (K : ℝ)) (hFmeas r) ?_
    exact Filter.Eventually.of_forall fun omega ↦ hFbound r omega
  have hlimit (r : ℝ≥0) (a : ℕ → ℝ≥0)
      (ha : Tendsto a atTop (nhds r)) (A : Set W) :
      Tendsto (fun n ↦ ∫ omega in A, F (a n) omega ∂P) atTop
        (nhds (∫ omega in A, F r omega ∂P)) := by
    have hUI : UniformIntegrable (fun n ↦ F (a n)) 1 P := by
      apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := K)
      · exact fun n ↦ hFmeas (a n)
      · intro n
        calc
          eLpNorm (F (a n)) 2 P ≤
              P Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (K : ℝ) :=
            eLpNorm_le_of_ae_bound
              (Filter.Eventually.of_forall fun omega ↦ hFbound (a n) omega)
          _ = K := by simp
    have hLp :=
      tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
        hUI (hstoch r a ha)
    exact tendsto_setIntegral_of_L1' (F r) (hFmeas r)
      (Filter.Eventually.of_forall fun n ↦ hFint (a n)) hLp A
  refine ⟨hF, ?_⟩
  intro s t hst
  refine (ae_eq_condExp_of_forall_setIntegral_eq (V.le s)
    (hFint t) (fun A _ _ ↦ (hFint s).integrableOn) ?_
    (hF s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases hstEq : s = t
  · subst t
    rfl
  have hslt : s < t := lt_of_le_of_ne hst hstEq
  by_cases hs0 : s = 0
  · subst s
    let a : ℕ → ℝ≥0 := fun n ↦ t / (n + 1 : ℕ)
    have ha : Tendsto a atTop (nhds 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat t).comp
        (tendsto_add_atTop_nat 1)
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hden : 0 < n + 1 := Nat.zero_lt_succ n
      have hraw := hrational t hden Nat.one_pos
        (Nat.succ_le_succ (Nat.zero_le n))
        (V.mono bot_le A hA)
      simpa only [a, Nat.cast_one, mul_one] using hraw
    have hconv := hlimit 0 a ha A
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P)
        atTop (nhds (∫ omega in A, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv hconst
  · let tau : Unit → WithTop ℝ≥0 := fun _ ↦ (s : WithTop ℝ≥0)
    have hbound : ∀ omega, tau omega ≤ (t : WithTop ℝ≥0) :=
      fun _ ↦ WithTop.coe_le_coe.mpr hst
    let j : ℕ → ℕ := fun n ↦ uniformPartitionCeilIndex tau t (n + 1)
      (Nat.zero_lt_succ n) hbound ()
    let a : ℕ → ℝ≥0 := fun n ↦ uniformPartitionTime t (n + 1) (j n)
    have hjpos (n : ℕ) : 0 < j n := by
      by_contra hn
      have hj0 : j n = 0 := Nat.eq_zero_of_not_pos hn
      have hspec := uniformPartitionCeilIndex_spec tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
      change (s : WithTop ℝ≥0) ≤
        (uniformPartitionTime t (n + 1) (j n) : WithTop ℝ≥0) at hspec
      rw [hj0] at hspec
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        WithTop.coe_zero] at hspec
      exact hs0 (nonpos_iff_eq_zero.mp (WithTop.coe_le_coe.mp hspec))
    have hjle (n : ℕ) : j n ≤ n + 1 :=
      uniformPartitionCeilIndex_le tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
    have hsa (n : ℕ) : s ≤ a n := by
      exact WithTop.coe_le_coe.mp
        (uniformPartitionCeilIndex_spec tau t (n + 1)
          (Nat.zero_lt_succ n) hbound ())
    have ha : Tendsto a atTop (nhds s) := by
      have hwith := tendsto_uniformPartitionCeilStoppingTime tau t hbound ()
      have huntop := (WithTop.tendsto_untopA WithTop.coe_ne_top).comp hwith
      have hcoe (x : ℝ≥0) : WithTop.untopA (x : WithTop ℝ≥0) = x := rfl
      change Tendsto (fun n ↦ WithTop.untopA (a n : WithTop ℝ≥0))
        atTop (nhds (WithTop.untopA (s : WithTop ℝ≥0))) at huntop
      simpa only [hcoe] using huntop
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hraw := hrational t (Nat.zero_lt_succ n) (hjpos n) (hjle n)
        (V.mono (hsa n) A hA)
      simpa only [a, uniformPartitionTime] using hraw
    have hconv := hlimit s a ha A
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P)
        atTop (nhds (∫ omega in A, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv hconst

/-- The compensated product theorem for bounded real martingales only needs
stochastic continuity of the compensated product.  In particular neither
factor needs a pathwise-continuous representative. -/
theorem
    HasCrossVariationProcessInProbability.martingale_product_sub_of_bounded_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (KX KY KC : ℝ≥0) (hXbound : ∀ r omega, ‖X r omega‖ ≤ KX)
    (hYbound : ∀ r omega, ‖Y r omega‖ ≤ KY)
    (hCbound : ∀ r omega, ‖C r omega‖ ≤ KC)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) → TendstoInMeasure P
        (fun n omega ↦
          X (a n) omega * Y (a n) omega - X 0 omega * Y 0 omega -
            C (a n) omega) atTop
        (fun omega ↦ X r omega * Y r omega - X 0 omega * Y 0 omega -
          C r omega)) :
    Martingale (fun r omega ↦
      X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega) V P := by
  let F : ℝ≥0 → W → ℝ := fun r omega ↦
    X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega
  have hFadapt : StronglyAdapted V F := by
    intro r
    exact (((hX.stronglyMeasurable r).mul (hY.stronglyMeasurable r)).sub
      ((hX.stronglyMeasurable 0).mono (V.mono bot_le) |>.mul
        ((hY.stronglyMeasurable 0).mono (V.mono bot_le)))).sub (hC r)
  let K : ℝ≥0 := 2 * KX * KY + KC
  have hFbound (r : ℝ≥0) (omega : W) : ‖F r omega‖ ≤ K := by
    calc
      ‖F r omega‖ ≤ ‖X r omega * Y r omega‖ +
          ‖X 0 omega * Y 0 omega‖ + ‖C r omega‖ := by
        dsimp only [F]
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (KX : ℝ) * (KY : ℝ) + (KX : ℝ) * (KY : ℝ) +
          (KC : ℝ) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact hXbound r omega
        · exact hYbound r omega
        · exact hXbound 0 omega
        · exact hYbound 0 omega
        · exact hCbound r omega
      _ = K := by simp only [K, NNReal.coe_add, NNReal.coe_mul,
        NNReal.coe_ofNat]; ring
  apply martingale_of_uniformRational_setIntegral_eq_of_tendstoInMeasure
    hFadapt K hFbound
  · intro r a ha
    simpa only [F] using hstoch r a ha
  · intro T k j hk hj hjk A hA
    simpa only [F] using h.setIntegral_stoppedProduct_sub_eq_rational
      hX hY hC KX KY hXbound hYbound T hk hj hjk hA

/-- Doob's fourth-moment maximal estimate for a pre-Brownian process sampled
along an arbitrary monotone deterministic grid. -/
theorem preBrownian_monotoneGrid_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k => (B (u k) omega) ^ 4)} ≤
      ENNReal.ofReal (3 * (u n : ℝ) ^ 2) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒱 := monotoneReindexFiltration (Filtration.natural B hsm) u hu
  have hmart : Martingale (fun k => B (u k)) 𝒱 P := by
    exact martingale_comp_monotone (martingale_brownian_natural hB hsm) u hu
  have hfourth : ∀ k, Integrable (fun omega => (B (u k) omega) ^ 4) P :=
    fun k => integrable_pow_four_of_hasLaw_gaussianReal _ (hB.hasLaw_eval (u k))
  have hmax := martingale_maximal_pow_four_ineq hmart hfourth epsilon n
  rw [integral_pow_four_of_hasLaw_gaussianReal (u n) (hB.hasLaw_eval (u n))]
    at hmax
  exact hmax

/-- Shifted form of the arbitrary-grid fourth-moment maximal estimate. -/
theorem preBrownian_interval_monotoneGrid_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (a : ℝ≥0) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (a + u k) omega - B a omega) ^ 4)} ≤
      ENNReal.ofReal (3 * (u n : ℝ) ^ 2) := by
  let Bs : ℝ≥0 → W → ℝ := fun t omega => B (a + t) omega - B a omega
  have hBs : IsPreBrownianReal Bs P := by
    simpa only [Bs] using hB.shift a
  have hBsmeas : ∀ t, StronglyMeasurable (Bs t) := fun t =>
    (hsm (a + t)).sub (hsm a)
  simpa only [Bs] using
    preBrownian_monotoneGrid_maximal_pow_four_ineq
      hBs hBsmeas u hu n epsilon

/-- Doob's fourth-moment maximal estimate for a pre-Brownian process sampled
on a finite uniform grid.  Applied to a shifted pre-Brownian process, this
uniformly controls all fine-grid oscillations inside one coarse interval. -/
theorem preBrownian_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (uniformPartitionTime t n k) omega) ^ 4)} ≤
      ENNReal.ofReal (3 * (t : ℝ) ^ 2) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒱 := monotoneReindexFiltration (Filtration.natural B hsm)
    (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hmart : Martingale (fun k => B (uniformPartitionTime t n k)) 𝒱 P := by
    exact martingale_comp_monotone (martingale_brownian_natural hB hsm)
      (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hfourth : ∀ k, Integrable
      (fun omega => (B (uniformPartitionTime t n k) omega) ^ 4) P := fun k =>
    integrable_pow_four_of_hasLaw_gaussianReal _
      (hB.hasLaw_eval (uniformPartitionTime t n k))
  have hmax := martingale_maximal_pow_four_ineq hmart hfourth epsilon n
  have htop : uniformPartitionTime t n n = t := by
    unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    exact mul_div_cancel_right₀ t hn0
  rw [htop,
    integral_pow_four_of_hasLaw_gaussianReal t (hB.hasLaw_eval t)] at hmax
  exact hmax

/-- Fourth-moment maximal control for all sampled increments inside a
deterministic interval.  The estimate is independent of the number of fine
grid points. -/
theorem preBrownian_interval_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (a b : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (a + uniformPartitionTime (b - a) n k) omega -
            B a omega) ^ 4)} ≤
      ENNReal.ofReal (3 * ((b - a : ℝ≥0) : ℝ) ^ 2) := by
  let Bs : ℝ≥0 → W → ℝ := fun t omega => B (a + t) omega - B a omega
  have hBs : IsPreBrownianReal Bs P := by
    simpa only [Bs] using hB.shift a
  have hBsmeas : ∀ t, StronglyMeasurable (Bs t) := fun t =>
    (hsm (a + t)).sub (hsm a)
  simpa only [Bs] using preBrownian_uniformPartition_maximal_pow_four_ineq
    hBs hBsmeas (b - a) hn epsilon

/-- A union bound over a coarse uniform partition controls every sampled
Brownian oscillation inside every coarse block.  Its right-hand side is of
order `k * (T/k)²`, hence vanishes as the coarse mesh tends to zero. -/
theorem preBrownian_uniformBlocks_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (T : ℝ≥0) (k : ℕ) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P (⋃ j ∈ Finset.range k, {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T k j +
                uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
              B (uniformPartitionTime T k j) omega) ^ 4)}) ≤
      (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
  let E : ℕ → Set W := fun j => {omega |
    (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4)}
  have hblock (j : ℕ) : epsilon * P (E j) ≤
      ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
    have hraw := preBrownian_interval_uniformPartition_maximal_pow_four_ineq
      hB hsm (uniformPartitionTime T k j)
        (uniformPartitionTime T k j + T / (k : ℝ≥0)) hn epsilon
    simpa only [E, add_tsub_cancel_left] using hraw
  change epsilon * P (⋃ j ∈ Finset.range k, E j) ≤ _
  calc
    epsilon * P (⋃ j ∈ Finset.range k, E j) ≤
        epsilon * ∑ j ∈ Finset.range k, P (E j) := by
      gcongr
      exact measure_biUnion_finset_le (Finset.range k) E
    _ = ∑ j ∈ Finset.range k, epsilon * P (E j) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range k, ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun j _hj => hblock j
    _ = (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Outside the coarse-block maximal event, every sampled oscillation is
bounded by the chosen fourth-root threshold. -/
theorem blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
    {W : Type*} (B : ℝ≥0 → W → ℝ) (T : ℝ≥0) {k n : ℕ}
    (delta : ℝ≥0) (_hdelta : 0 < delta) {omega : W}
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ∀ j ∈ Finset.range k, ∀ r ∈ Finset.range (n + 1),
      |B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta := by
  intro j hj r hr
  have hjnot : omega ∉ {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)} := by
    intro hmem
    apply homega
    simp only [Set.mem_iUnion]
    exact ⟨j, hj, hmem⟩
  simp only [Set.mem_ofPred_eq] at hjnot
  have hsup : (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4) <
      (delta : ℝ) ^ 4 := lt_of_not_ge hjnot
  have hterm := Finset.le_sup'
    (fun r =>
      (B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega) ^ 4) hr
  have hpow : |B (uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
      B (uniformPartitionTime T k j) omega| ^ 4 < (delta : ℝ) ^ 4 := by
    rw [← abs_pow]
    rw [abs_of_nonneg (by positivity)]
    exact hterm.trans_lt hsup
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _)
    delta.coe_nonneg (by norm_num : (4 : ℕ) ≠ 0)).mp hpow |>.le

/-- Outside the Brownian coarse-block maximal event, freezing a Lipschitz
Brownian weight on the common refinement has the expected pathwise
Cauchy--Schwarz error bound. -/
theorem
    abs_weightedQuadraticCovariation_commonRefinement_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (X B : ℝ≥0 → W → ℝ) (g : ℝ → ℝ) {L : ℝ≥0}
    (hg : LipschitzWith L g) (T : ℝ≥0) {k n : ℕ}
    (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (delta : ℝ≥0) (hdelta : 0 < delta) {omega : W}
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    |weightedQuadraticCovariationApprox
        (fun s omega => g (B s omega)) X B T (k * n) omega -
      ∑ j ∈ Finset.range k, g (B (uniformPartitionTime T k j) omega) *
        (quadraticCovariationBeforeStopApprox X B T (k * n)
            (uniformPartitionTime T k (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X B T (k * n)
            (uniformPartitionTime T k j) omega)| ≤
      ((L : ℝ) * delta) *
        √(quadraticVariationApprox X T (k * n) omega *
          quadraticVariationApprox B T (k * n) omega) := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hclose := commonRefinement_lipschitzWeight_close_of_blockOscillation
    B g hg T hT hk hn omega (delta : ℝ) hosc
  simpa only [weightedQuadraticCovariationApprox] using
    abs_weightedQuadraticCovariation_sub_completedBlocks_le
      X B T (k * n) k
      (fun i omega => g (B (uniformPartitionTime T (k * n) i) omega))
      (fun j omega => g (B (uniformPartitionTime T k j) omega))
      ((L : ℝ) * delta) (mul_nonneg L.coe_nonneg delta.coe_nonneg)
      omega hclose

/-- The coarse-block fourth-moment bound vanishes with the coarse mesh.
This is uniform in the number of fine samples inside each block. -/
theorem tendsto_preBrownian_uniformBlocks_maximal_pow_four_bound
    (T : ℝ≥0) :
    Tendsto (fun k : ℕ =>
      ((k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun k : ℕ =>
      3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)) atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (3 * (T : ℝ) ^ 2)
    simpa only [mul_zero, mul_one_div] using h
  have hofReal := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_zero] using hofReal.congr (fun k => by
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (le_of_lt hk)]
    congr 1
    push_cast
    field_simp
    )

/-- The probability of a sampled oscillation exceeding a fixed threshold
in some coarse block vanishes with the coarse mesh, uniformly over an
arbitrary positive number of fine subdivisions in each block. -/
theorem tendsto_measureReal_preBrownian_uniformBlocks_maximal_pow_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (T : ℝ≥0)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (epsilon : ℝ≥0) (hepsilon : 0 < epsilon) :
    Tendsto (fun k => P.real (⋃ j ∈ Finset.range (k + 1), {omega |
      (epsilon : ℝ) ≤ (Finset.range (n k + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T (k + 1) j +
              uniformPartitionTime
                (T / ((k + 1 : ℕ) : ℝ≥0)) (n k) r) omega -
            B (uniformPartitionTime T (k + 1) j) omega) ^ 4)}))
      atTop (nhds 0) := by
  let b : ℕ → ℝ := fun k =>
    (3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)) / (epsilon : ℝ)
  have hb : Tendsto b atTop (nhds 0) := by
    have hbase : Tendsto (fun k : ℕ =>
        3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)) atTop (nhds 0) := by
      have h :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (3 * (T : ℝ) ^ 2)
      convert h using 1 <;> simp only [mul_zero, mul_one_div]
    simpa only [b, zero_div] using hbase.div_const (epsilon : ℝ)
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun k => ?_) hb
  let E : Set W := ⋃ j ∈ Finset.range (k + 1), {omega |
    (epsilon : ℝ) ≤ (Finset.range (n k + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T (k + 1) j +
            uniformPartitionTime
              (T / ((k + 1 : ℕ) : ℝ≥0)) (n k) r) omega -
          B (uniformPartitionTime T (k + 1) j) omega) ^ 4)}
  have hraw := preBrownian_uniformBlocks_maximal_pow_four_ineq
    hB hsm T (k + 1) (hn k) epsilon
  change (epsilon : ℝ≥0∞) * P E ≤ _ at hraw
  have htop : ((k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  have hrhs : (((k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)).toReal =
      3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal]
    · push_cast
      field_simp
    · positivity
  rw [hrhs] at hreal
  rw [ENNReal.toReal_mul] at hreal
  change (epsilon : ℝ) * P.real E ≤
    3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1) at hreal
  change P.real E ≤ b k
  dsimp only [b]
  apply (le_div_iff₀ (show (0 : ℝ) < epsilon by exact_mod_cast hepsilon)).2
  simpa only [mul_comm] using hreal

/-- A concrete diagonal scale: `(k+1)^5` coarse blocks and oscillation
threshold `1/(k+1)` make the exceptional probability vanish, uniformly in
the positive number of inner subdivisions. -/
theorem tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (T : ℝ≥0)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k =>
      let K := (k + 1) ^ 5
      let delta : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0)⁻¹
      P.real (⋃ j ∈ Finset.range K, {omega |
        ((delta : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T K j +
                uniformPartitionTime (T / (K : ℝ≥0)) (n k) r) omega -
              B (uniformPartitionTime T K j) omega) ^ 4)}))
      atTop (nhds 0) := by
  let d : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let b : ℕ → ℝ := fun k => 3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)
  have hb : Tendsto b atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (3 * (T : ℝ) ^ 2)
    have hc := h.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ =>
      3 * (T : ℝ) ^ 2 / ((k + 1 : ℕ) : ℝ)) atTop (nhds 0) at hc
    simpa only [b, Nat.cast_add, Nat.cast_one] using hc
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun k => ?_) hb
  let E : Set W := ⋃ j ∈ Finset.range (K k), {omega |
    ((d k : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T (K k) j +
            uniformPartitionTime (T / (K k : ℝ≥0)) (n k) r) omega -
          B (uniformPartitionTime T (K k) j) omega) ^ 4)}
  have hK : 0 < K k := by
    dsimp only [K]
    positivity
  have hd : 0 < d k := by
    dsimp only [d]
    positivity
  have hraw := preBrownian_uniformBlocks_maximal_pow_four_ineq
    hB hsm T (K k) (hn k) ((d k) ^ 4)
  change ((d k : ℝ≥0∞) ^ 4) * P E ≤ _ at hraw
  have htop : ((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
  change (d k : ℝ) ^ 4 * P.real E ≤
    (((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)).toReal at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  change P.real E ≤ b k
  have hdivide : P.real E ≤
      ((K k : ℝ) *
        (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)) /
        (d k : ℝ) ^ 4 := by
    apply (le_div_iff₀ (pow_pos (show (0 : ℝ) < d k by exact_mod_cast hd) 4)).2
    simpa only [mul_comm] using hreal
  calc
    P.real E ≤ _ := hdivide
    _ = b k := by
      dsimp only [K, d, b]
      simp only [NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_div]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
      push_cast
      ring

/-- Along the concrete polynomial common-refinement diagonal, a Lipschitz
Brownian weight and its frozen coarse-step version differ in probability by
zero whenever the geometric-mean quadratic sums are eventually tight. -/
theorem
    tendstoInMeasure_weightedQuadraticCovariation_sub_polynomialBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (g : ℝ → ℝ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (hqtight : ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
        P.real {omega | C ≤
          √(quadraticVariationApprox X T (((k + 1) ^ 5) * n k) omega *
            quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
          eta) :
    TendstoInMeasure P (fun k omega =>
      let K := (k + 1) ^ 5
      weightedQuadraticCovariationApprox
          (fun s omega => g (B s omega)) X B T (K * n k) omega -
        ∑ j ∈ Finset.range K, g (B (uniformPartitionTime T K j) omega) *
          (quadraticCovariationBeforeStopApprox X B T (K * n k)
              (uniformPartitionTime T K (j + 1)) omega -
            quadraticCovariationBeforeStopApprox X B T (K * n k)
              (uniformPartitionTime T K j) omega))
      atTop (fun _ => 0) := by
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let d : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹
  let bad : ℕ → Set W := fun k => ⋃ j ∈ Finset.range (K k), {omega |
    ((d k : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T (K k) j +
            uniformPartitionTime (T / (K k : ℝ≥0)) (n k) r) omega -
          B (uniformPartitionTime T (K k) j) omega) ^ 4)}
  let q : ℕ → W → ℝ := fun k omega =>
    √(quadraticVariationApprox X T (K k * n k) omega *
      quadraticVariationApprox B T (K k * n k) omega)
  let a : ℕ → ℝ := fun k => (L : ℝ) * (d k : ℝ)
  let f : ℕ → W → ℝ := fun k omega =>
    weightedQuadraticCovariationApprox
        (fun s omega => g (B s omega)) X B T (K k * n k) omega -
      ∑ j ∈ Finset.range (K k),
        g (B (uniformPartitionTime T (K k) j) omega) *
        (quadraticCovariationBeforeStopApprox X B T (K k * n k)
            (uniformPartitionTime T (K k) (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X B T (K k * n k)
            (uniformPartitionTime T (K k) j) omega)
  have hd : Tendsto (fun k => (d k : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun k : ℕ =>
        ((k + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hinv
    change Tendsto (fun k : ℕ =>
      ((((k + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)) atTop (nhds 0) at hcoe
    simpa only [d, NNReal.coe_zero] using hcoe
  have ha : Tendsto a atTop (nhds 0) := by
    simpa only [a, mul_zero] using hd.const_mul (L : ℝ)
  have hbad : Tendsto (fun k => P.real (bad k)) atTop (nhds 0) := by
    simpa only [bad, K, d] using
      tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
        hB hsm T n hn
  have hqnonneg : ∀ k omega, 0 ≤ q k omega := fun k omega => Real.sqrt_nonneg _
  have hatight : ∀ eta : ℝ, 0 < eta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
        P.real {omega | C ≤ q k omega} < eta := by
    simpa only [q, K] using hqtight
  have hconv := TendstoInMeasure.of_norm_sub_le_mul_of_eventually_tight_outside
    (P := P) (f := f) (g := fun _ => 0) (q := q) (a := a) (bad := bad)
      ha (fun k => mul_nonneg L.coe_nonneg (d k).coe_nonneg)
      hqnonneg hatight hbad (fun k omega homega => by
        have hK : 0 < K k := by
          dsimp only [K]
          positivity
        have hdpos : 0 < d k := by
          dsimp only [d]
          positivity
        have hbound :=
          abs_weightedQuadraticCovariation_commonRefinement_sub_completedBlocks_le
            X B g hg T hT hK (hn k) (d k) hdpos homega
        simpa only [f, a, q, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
          using hbound)
  simpa only [f, K] using hconv

/-- Ordinary fixed-time quadratic-variation convergence supplies the
geometric-mean tightness needed by the polynomial two-scale argument.  The
limit assumption is deliberately phrased for the sum: this is exactly the
coercive quantity controlling the geometric mean. -/
theorem HasQuadraticVariationProcessInProbability.polynomialBlocks_eventually_tight_sqrt_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X B QX QB : ℝ≥0 → W → ℝ}
    (hX : HasQuadraticVariationProcessInProbability X QX P)
    (hB : HasQuadraticVariationProcessInProbability B QB P)
    (T : ℝ≥0)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox X T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  intro n hn
  let s : ℕ → ℕ := fun k => ((k + 1) ^ 5) * n k
  let r : ℕ → ℕ := fun k => s k - 1
  have hs_pos : ∀ k, 0 < s k := fun k => by
    dsimp only [s]
    exact Nat.mul_pos (by positivity) (hn k)
  have hr : Tendsto r atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ s a := by
      exact Nat.le_mul_of_pos_right _ (hn a)
    have halt : a < s a := by omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hr_add : ∀ k, r k + 1 = s k := fun k => by
    dsimp only [r]
    exact Nat.sub_add_cancel (hs_pos k)
  have hqX : TendstoInMeasure P
      (fun k => quadraticVariationApprox X T (s k)) atTop (QX T) := by
    convert (hX T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox X T) (hr_add k).symm
  have hqB : TendstoInMeasure P
      (fun k => quadraticVariationApprox B T (s k)) atTop (QB T) := by
    convert (hB T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox B T) (hr_add k).symm
  have htight := hqX.eventually_tight_sqrt_mul hqB
    (fun k omega => quadraticVariationApprox_nonneg X T (s k) omega)
    (fun k omega => quadraticVariationApprox_nonneg B T (s k) omega)
    hQint hQnonneg
  simpa only [s] using htight

/-- Girsanov density data and a pre-Brownian driver automatically satisfy
the polynomial-grid tightness condition for the martingale--Brownian
quadratic sums.  In particular, Novikov supplies the only random first
moment needed here. -/
theorem GirsanovDensityData.polynomialBlocks_eventually_tight_sqrt_martingale_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox M T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  apply h.localQuadraticVariation.toProcess
    |>.polynomialBlocks_eventually_tight_sqrt_mul
      (fun t => quadraticVariation_preBrownianReal_inProbability hB t) T
  · exact h.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← h.bracket_zero omega]
        exact (h.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

/-- The pre-Brownian covariation chain rule remains valid on any cofinal
sequence of positive partition counts.  This is the subsequence form needed
after a two-scale diagonal selection. -/
theorem tendstoInMeasure_quadraticCovariation_comp_of_weighted_preBrownian_counts
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ}
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    (hB : IsPreBrownianReal B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (QX C : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) atTop QX)
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (hN : Tendsto N atTop atTop)
    (hweighted : TendstoInMeasure P
      (fun k => weightedQuadraticCovariationApprox
        (fun s w => deriv f (B s w)) X B t (N k)) atTop C) :
    TendstoInMeasure P
      (fun k => quadraticCovariationApprox X (fun s w => f (B s w))
        t (N k)) atTop C := by
  let r : ℕ → ℕ := fun k => N k - 1
  have hr : Tendsto r atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hN (b + 1)
    refine ⟨i, fun a hia => ?_⟩
    have hba := hi a hia
    exact Nat.le_sub_one_of_lt (by omega : b < N a)
  have hr_add : ∀ k, r k + 1 = N k := fun k => by
    dsimp only [r]
    exact Nat.sub_add_cancel (hNpos k)
  have hremFull :=
    covariationTaylorRemainder_tendstoInMeasure_zero_of_preBrownian
      f hf K hsecond hB hXmeas t QX hQX
  have hrem : TendstoInMeasure P
      (fun k => covariationTaylorRemainderApprox f X B t (N k)) atTop
      (fun _ => 0) := by
    convert hremFull.comp hr using 1
    exact funext fun k => congrArg
      (covariationTaylorRemainderApprox f X B t) (hr_add k).symm
  have hsum := hweighted.add_real_noMeas hrem
  apply hsum.congr
  · intro k
    exact Filter.Eventually.of_forall fun omega =>
      (quadraticCovariationApprox_comp_eq_weighted_add_remainder
        f X B t (N k) omega).symm
  · exact Filter.Eventually.of_forall fun omega => by simp

/-- Residual form of the selected-count chain rule: the comparison target
may vary with the grid index.  This is what lets a Taylor covariation cancel
against the matching coarse cross blocks without first identifying their
limit. -/
theorem tendstoInMeasure_quadraticCovariation_comp_sub_of_weighted_sub_preBrownian_counts
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ}
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    (hB : IsPreBrownianReal B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (QX : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) atTop QX)
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k)
    (hN : Tendsto N atTop atTop) (D : ℕ → W → ℝ)
    (hweighted : TendstoInMeasure P (fun k omega =>
      weightedQuadraticCovariationApprox
          (fun s w => deriv f (B s w)) X B t (N k) omega - D k omega)
      atTop (fun _ => 0)) :
    TendstoInMeasure P (fun k omega =>
      quadraticCovariationApprox X (fun s w => f (B s w)) t (N k) omega -
        D k omega) atTop (fun _ => 0) := by
  let r : ℕ → ℕ := fun k => N k - 1
  have hr : Tendsto r atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hN (b + 1)
    refine ⟨i, fun a hia => ?_⟩
    have hba := hi a hia
    exact Nat.le_sub_one_of_lt (by omega : b < N a)
  have hr_add : ∀ k, r k + 1 = N k := fun k => by
    dsimp only [r]
    exact Nat.sub_add_cancel (hNpos k)
  have hremFull :=
    covariationTaylorRemainder_tendstoInMeasure_zero_of_preBrownian
      f hf K hsecond hB hXmeas t QX hQX
  have hrem : TendstoInMeasure P
      (fun k => covariationTaylorRemainderApprox f X B t (N k)) atTop
      (fun _ => 0) := by
    convert hremFull.comp hr using 1
    exact funext fun k => congrArg
      (covariationTaylorRemainderApprox f X B t) (hr_add k).symm
  have hsum := hweighted.add_real_noMeas hrem
  apply hsum.congr
  · intro k
    exact Filter.Eventually.of_forall fun omega => by
      change weightedQuadraticCovariationApprox
          (fun s w => deriv f (B s w)) X B t (N k) omega - D k omega +
          covariationTaylorRemainderApprox f X B t (N k) omega =
        quadraticCovariationApprox X (fun s w => f (B s w))
          t (N k) omega - D k omega
      rw [quadraticCovariationApprox_comp_eq_weighted_add_remainder]
      ring
  · exact Filter.Eventually.of_forall fun omega => by simp

set_option maxHeartbeats 4000000 in
-- The expanded two-scale processes make elaboration substantially larger.
/-- Without assuming that the coarse cross blocks themselves converge, one
can still select a polynomial common-refinement diagonal on which the fine
Brownian-weighted covariation approaches those very blocks.  This residual
form is tailored to cancellations with a finite-variation term. -/
theorem HasCrossVariationProcessInProbability.exists_polynomial_diagonal_weighted_sub_crossBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (g : ℝ → ℝ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) (hT : 0 < T)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let K := (k + 1) ^ 5
        weightedQuadraticCovariationApprox
            (fun s omega => g (B s omega)) X B T (K * (m k + 1)) omega -
          ∑ j ∈ Finset.range K,
            g (B (uniformPartitionTime T K j) omega) *
              (C (uniformPartitionTime T K (j + 1)) omega -
                C (uniformPartitionTime T K j) omega))
        atTop (fun _ => 0) := by
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let F : ℕ → ℕ → W → ℝ := fun k n omega =>
    ∑ j ∈ Finset.range (K k),
      g (B (uniformPartitionTime T (K k) j) omega) *
        (quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) j) omega)
  let Gk : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range (K k),
      g (B (uniformPartitionTime T (K k) j) omega) *
        (C (uniformPartitionTime T (K k) (j + 1)) omega -
          C (uniformPartitionTime T (K k) j) omega)
  have hFG : ∀ k, TendstoInMeasure P (F k) atTop (Gk k) := by
    intro k
    have hK : 0 < K k := by
      dsimp only [K]
      positivity
    have hraw := h.fullStepWeight_beforeStop_common_refinement
      hXmeas (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      T hK (fun j omega => g (B (uniformPartitionTime T (K k) j) omega))
      (fun j _hj => hg.continuous.comp_aestronglyMeasurable
        (hB.aemeasurable (uniformPartitionTime T (K k) j)
          |>.aestronglyMeasurable))
    simpa only [F, Gk] using hraw
  obtain ⟨m, hm, hdiag⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal_sub hFG
  let n : ℕ → ℕ := fun k => m k + 1
  have hn : ∀ k, 0 < n k := fun k => by
    dsimp only [n]
    positivity
  have hqtight := hQX.polynomialBlocks_eventually_tight_sqrt_mul
    hQB T hQint hQnonneg n hn
  have herr :=
    tendstoInMeasure_weightedQuadraticCovariation_sub_polynomialBlocks
      hB hsm g hg T hT n hn hqtight
  refine ⟨m, hm, ?_⟩
  have hsum := herr.add_real_noMeas hdiag
  apply hsum.congr
  · intro k
    exact Filter.Eventually.of_forall fun omega => by
      simp only [n, F, Gk, K]
      ring
  · exact Filter.Eventually.of_forall fun omega => by
      simp only [zero_add]

set_option maxHeartbeats 4000000 in
-- Both expanded two-scale processes are synchronized on one fine grid.
/-- Two Lipschitz Brownian weights admit one polynomial common-refinement
diagonal on which both weighted covariations approach their matching coarse
cross blocks. -/
theorem
    HasCrossVariationProcessInProbability.exists_polynomial_diagonal_weighted_pair_sub_crossBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (g₁ g₂ : ℝ → ℝ) {L₁ L₂ : ℝ≥0}
    (hg₁ : LipschitzWith L₁ g₁) (hg₂ : LipschitzWith L₂ g₂)
    (T : ℝ≥0) (hT : 0 < T)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let K := (k + 1) ^ 5
        weightedQuadraticCovariationApprox
            (fun s omega => g₁ (B s omega)) X B T (K * (m k + 1)) omega -
          ∑ j ∈ Finset.range K,
            g₁ (B (uniformPartitionTime T K j) omega) *
              (C (uniformPartitionTime T K (j + 1)) omega -
                C (uniformPartitionTime T K j) omega))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun k omega =>
        let K := (k + 1) ^ 5
        weightedQuadraticCovariationApprox
            (fun s omega => g₂ (B s omega)) X B T (K * (m k + 1)) omega -
          ∑ j ∈ Finset.range K,
            g₂ (B (uniformPartitionTime T K j) omega) *
              (C (uniformPartitionTime T K (j + 1)) omega -
                C (uniformPartitionTime T K j) omega))
        atTop (fun _ => 0) := by
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let F₁ : ℕ → ℕ → W → ℝ := fun k n omega =>
    ∑ j ∈ Finset.range (K k),
      g₁ (B (uniformPartitionTime T (K k) j) omega) *
        (quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) j) omega)
  let F₂ : ℕ → ℕ → W → ℝ := fun k n omega =>
    ∑ j ∈ Finset.range (K k),
      g₂ (B (uniformPartitionTime T (K k) j) omega) *
        (quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
            (uniformPartitionTime T (K k) j) omega)
  let G₁ : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range (K k),
      g₁ (B (uniformPartitionTime T (K k) j) omega) *
        (C (uniformPartitionTime T (K k) (j + 1)) omega -
          C (uniformPartitionTime T (K k) j) omega)
  let G₂ : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range (K k),
      g₂ (B (uniformPartitionTime T (K k) j) omega) *
        (C (uniformPartitionTime T (K k) (j + 1)) omega -
          C (uniformPartitionTime T (K k) j) omega)
  have hFG₁ : ∀ k, TendstoInMeasure P (F₁ k) atTop (G₁ k) := by
    intro k
    have hK : 0 < K k := by
      dsimp only [K]
      positivity
    have hraw := h.fullStepWeight_beforeStop_common_refinement
      hXmeas (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      T hK (fun j omega => g₁ (B (uniformPartitionTime T (K k) j) omega))
      (fun j _hj => hg₁.continuous.comp_aestronglyMeasurable
        (hB.aemeasurable (uniformPartitionTime T (K k) j)
          |>.aestronglyMeasurable))
    simpa only [F₁, G₁] using hraw
  have hFG₂ : ∀ k, TendstoInMeasure P (F₂ k) atTop (G₂ k) := by
    intro k
    have hK : 0 < K k := by
      dsimp only [K]
      positivity
    have hraw := h.fullStepWeight_beforeStop_common_refinement
      hXmeas (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      T hK (fun j omega => g₂ (B (uniformPartitionTime T (K k) j) omega))
      (fun j _hj => hg₂.continuous.comp_aestronglyMeasurable
        (hB.aemeasurable (uniformPartitionTime T (K k) j)
          |>.aestronglyMeasurable))
    simpa only [F₂, G₂] using hraw
  obtain ⟨m, hm, hdiag₁, hdiag₂⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal_sub_two hFG₁ hFG₂
  let n : ℕ → ℕ := fun k => m k + 1
  have hn : ∀ k, 0 < n k := fun k => by
    dsimp only [n]
    positivity
  have hqtight := hQX.polynomialBlocks_eventually_tight_sqrt_mul
    hQB T hQint hQnonneg n hn
  have herr₁ :=
    tendstoInMeasure_weightedQuadraticCovariation_sub_polynomialBlocks
      hB hsm g₁ hg₁ T hT n hn hqtight
  have herr₂ :=
    tendstoInMeasure_weightedQuadraticCovariation_sub_polynomialBlocks
      hB hsm g₂ hg₂ T hT n hn hqtight
  refine ⟨m, hm, ?_, ?_⟩
  · have hsum := herr₁.add_real_noMeas hdiag₁
    apply hsum.congr
    · intro k
      exact Filter.Eventually.of_forall fun omega => by
        simp only [n, F₁, G₁, K]
        ring
    · exact Filter.Eventually.of_forall fun omega => by
        simp only [zero_add]
  · have hsum := herr₂.add_real_noMeas hdiag₂
    apply hsum.congr
    · intro k
      exact Filter.Eventually.of_forall fun omega => by
        simp only [n, F₂, G₂, K]
        ring
    · exact Filter.Eventually.of_forall fun omega => by
        simp only [zero_add]

set_option linter.style.longLine false in
set_option maxHeartbeats 4000000 in
-- This combines the two expanded polynomial-diagonal arguments above.
/-- Along a selected polynomial common refinement, covariation with a smooth
Brownian transform approaches the derivative-weighted coarse blocks of the
original cross variation, whether or not those blocks converge separately. -/
theorem HasCrossVariationProcessInProbability.exists_polynomial_diagonal_covariation_comp_sub_crossBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    {L : ℝ≥0} (hderiv : LipschitzWith L (deriv f))
    (T : ℝ≥0) (hT : 0 < T)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox X (fun s w => f (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  obtain ⟨m, hm, hweighted⟩ :=
    h.exists_polynomial_diagonal_weighted_sub_crossBlocks
      hXmeas hB hsm hQX hQB (deriv f) hderiv T hT hQint hQnonneg
  let N : ℕ → ℕ := fun k => ((k + 1) ^ 5) * (m k + 1)
  let D : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range ((k + 1) ^ 5),
      deriv f (B (uniformPartitionTime T ((k + 1) ^ 5) j) omega) *
        (C (uniformPartitionTime T ((k + 1) ^ 5) (j + 1)) omega -
          C (uniformPartitionTime T ((k + 1) ^ 5) j) omega)
  have hNpos : ∀ k, 0 < N k := fun k => by
    dsimp only [N]
    exact Nat.mul_pos (by positivity) (by positivity)
  have hN : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ N a :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact (hba.trans (Nat.le_succ a)).trans (hbase.trans hmul)
  refine ⟨m, hm, ?_⟩
  have hchain :=
    tendstoInMeasure_quadraticCovariation_comp_sub_of_weighted_sub_preBrownian_counts
      f hf K hsecond hB hXmeas T (QX T) (hQX T) N hNpos hN D
        (by simpa only [N, D] using hweighted)
  simpa only [N, D] using hchain

set_option linter.style.longLine false in
set_option maxHeartbeats 4000000 in
-- The paired weighted diagonal and two Taylor expansions are both large.
/-- Two smooth Brownian transforms admit one selected polynomial refinement
on which both covariations match their derivative-weighted coarse cross
blocks. -/
theorem HasCrossVariationProcessInProbability.exists_polynomial_diagonal_covariation_comp_pair_sub_crossBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (K₁ K₂ : ℝ)
    (hsecond₁ : ∀ y, |deriv (deriv f₁) y| ≤ K₁)
    (hsecond₂ : ∀ y, |deriv (deriv f₂) y| ≤ K₂)
    {L₁ L₂ : ℝ≥0}
    (hderiv₁ : LipschitzWith L₁ (deriv f₁))
    (hderiv₂ : LipschitzWith L₂ (deriv f₂))
    (T : ℝ≥0) (hT : 0 < T)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox X (fun s w => f₁ (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f₁ (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox X (fun s w => f₂ (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f₂ (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  obtain ⟨m, hm, hweighted₁, hweighted₂⟩ :=
    h.exists_polynomial_diagonal_weighted_pair_sub_crossBlocks
      hXmeas hB hsm hQX hQB (deriv f₁) (deriv f₂)
      hderiv₁ hderiv₂ T hT hQint hQnonneg
  let N : ℕ → ℕ := fun k => ((k + 1) ^ 5) * (m k + 1)
  let D₁ : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range ((k + 1) ^ 5),
      deriv f₁ (B (uniformPartitionTime T ((k + 1) ^ 5) j) omega) *
        (C (uniformPartitionTime T ((k + 1) ^ 5) (j + 1)) omega -
          C (uniformPartitionTime T ((k + 1) ^ 5) j) omega)
  let D₂ : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range ((k + 1) ^ 5),
      deriv f₂ (B (uniformPartitionTime T ((k + 1) ^ 5) j) omega) *
        (C (uniformPartitionTime T ((k + 1) ^ 5) (j + 1)) omega -
          C (uniformPartitionTime T ((k + 1) ^ 5) j) omega)
  have hNpos : ∀ k, 0 < N k := fun k => by
    dsimp only [N]
    exact Nat.mul_pos (by positivity) (by positivity)
  have hN : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ N a :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact (hba.trans (Nat.le_succ a)).trans (hbase.trans hmul)
  refine ⟨m, hm, ?_, ?_⟩
  · have hchain :=
      tendstoInMeasure_quadraticCovariation_comp_sub_of_weighted_sub_preBrownian_counts
        f₁ hf₁ K₁ hsecond₁ hB hXmeas T (QX T) (hQX T)
        N hNpos hN D₁ (by simpa only [N, D₁] using hweighted₁)
    simpa only [N, D₁] using hchain
  · have hchain :=
      tendstoInMeasure_quadraticCovariation_comp_sub_of_weighted_sub_preBrownian_counts
        f₂ hf₂ K₂ hsecond₂ hB hXmeas T (QX T) (hQX T)
        N hNpos hN D₂ (by simpa only [N, D₂] using hweighted₂)
    simpa only [N, D₂] using hchain

/-- Novikov Girsanov data discharges the quadratic-variation and moment
premises of the paired selected-grid smooth chain rule. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_covariation_comp_pair_sub_crossBlocks_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f₁ f₂ : ℝ → ℝ) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (K₁ K₂ : ℝ)
    (hsecond₁ : ∀ y, |deriv (deriv f₁) y| ≤ K₁)
    (hsecond₂ : ∀ y, |deriv (deriv f₂) y| ≤ K₂)
    {L₁ L₂ : ℝ≥0}
    (hderiv₁ : LipschitzWith L₁ (deriv f₁))
    (hderiv₂ : LipschitzWith L₂ (deriv f₂))
    (hT : 0 < T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M (fun s w => f₁ (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f₁ (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M (fun s w => f₂ (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f₂ (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  apply hcross.exists_polynomial_diagonal_covariation_comp_pair_sub_crossBlocks
    hMmeas hB hsm hdata.localQuadraticVariation.toProcess
    (fun t => quadraticVariation_preBrownianReal_inProbability hB t)
    f₁ f₂ hf₁ hf₂ K₁ K₂ hsecond₁ hsecond₂ hderiv₁ hderiv₂ T hT
  · exact hdata.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

/-- The cancellation-ready smooth-transform residual specialized to a
Novikov Girsanov martingale and a pre-Brownian driver. -/
theorem GirsanovDensityData.exists_polynomial_diagonal_covariation_comp_sub_crossBlocks_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    {L : ℝ≥0} (hderiv : LipschitzWith L (deriv f))
    (hT : 0 < T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M (fun s w => f (B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            deriv f (B (uniformPartitionTime T N j) omega) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  apply hcross.exists_polynomial_diagonal_covariation_comp_sub_crossBlocks
    hMmeas hB hsm hdata.localQuadraticVariation.toProcess
    (fun t => quadraticVariation_preBrownianReal_inProbability hB t)
    f hf K hsecond hderiv T hT
  · exact hdata.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

/-- The derivative of a sine whose argument is scaled by a real constant. -/
theorem deriv_scaledSin (c : ℝ) :
    deriv (fun x : ℝ => Real.sin (c * x)) =
      fun x => c * Real.cos (c * x) := by
  funext x
  have hc : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul c (hasDerivAt_id x)
  change deriv (Real.sin ∘ fun y : ℝ => c * y) x = _
  simpa only [mul_comm] using
    HasDerivAt.deriv (Real.hasDerivAt_sin (c * x) |>.comp x hc)

/-- The derivative of a cosine whose argument is scaled by a real constant. -/
theorem deriv_scaledCos (c : ℝ) :
    deriv (fun x : ℝ => Real.cos (c * x)) =
      fun x => -c * Real.sin (c * x) := by
  funext x
  have hc : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul c (hasDerivAt_id x)
  change deriv (Real.cos ∘ fun y : ℝ => c * y) x = _
  convert HasDerivAt.deriv
    (Real.hasDerivAt_cos (c * x) |>.comp x hc) using 1; ring

/-- The second derivative of a scaled sine. -/
theorem deriv_deriv_scaledSin (c x : ℝ) :
    deriv (deriv (fun x : ℝ => Real.sin (c * x))) x =
      -(c ^ 2) * Real.sin (c * x) := by
  rw [deriv_scaledSin]
  have hc : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul c (hasDerivAt_id x)
  change deriv
    (fun y : ℝ => c * (Real.cos ∘ fun z : ℝ => c * z) y) x = _
  convert HasDerivAt.deriv
    ((Real.hasDerivAt_cos (c * x) |>.comp x hc).const_mul c) using 1; ring

/-- The second derivative of a scaled cosine. -/
theorem deriv_deriv_scaledCos (c x : ℝ) :
    deriv (deriv (fun x : ℝ => Real.cos (c * x))) x =
      -(c ^ 2) * Real.cos (c * x) := by
  rw [deriv_scaledCos]
  have hc : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa only [id_eq, mul_one] using
      HasDerivAt.const_mul c (hasDerivAt_id x)
  change deriv
    (fun y : ℝ => -c * (Real.sin ∘ fun z : ℝ => c * z) y) x = _
  convert HasDerivAt.deriv
    ((Real.hasDerivAt_sin (c * x) |>.comp x hc).const_mul (-c)) using 1; ring

/-- The second derivative of a scaled sine is uniformly bounded by the
square of its frequency. -/
theorem abs_deriv_deriv_scaledSin_le (c x : ℝ) :
    |deriv (deriv (fun x : ℝ => Real.sin (c * x))) x| ≤ c ^ 2 := by
  rw [deriv_deriv_scaledSin, abs_mul]
  simpa only [abs_neg, abs_sq, mul_one] using
    mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one (c * x)) (sq_nonneg c)

/-- The second derivative of a scaled cosine is uniformly bounded by the
square of its frequency. -/
theorem abs_deriv_deriv_scaledCos_le (c x : ℝ) :
    |deriv (deriv (fun x : ℝ => Real.cos (c * x))) x| ≤ c ^ 2 := by
  rw [deriv_deriv_scaledCos, abs_mul]
  simpa only [abs_neg, abs_sq, mul_one] using
    mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one (c * x)) (sq_nonneg c)

/-- The derivative of a scaled sine is Lipschitz with the square of its
frequency as constant. -/
theorem lipschitzWith_deriv_scaledSin (c : ℝ) :
    LipschitzWith (Real.toNNReal (c ^ 2))
      (deriv (fun x : ℝ => Real.sin (c * x))) := by
  rw [deriv_scaledSin]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal (c ^ 2) (sq_nonneg c)]
  simp only [Real.dist_eq]
  calc
    |c * Real.cos (c * x) - c * Real.cos (c * y)| =
        |c| * |Real.cos (c * x) - Real.cos (c * y)| := by
          rw [← mul_sub, abs_mul]
    _ ≤ |c| * |c * x - c * y| := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
          Real.lipschitzWith_cos.dist_le_mul (c * x) (c * y))
        (abs_nonneg c)
    _ = |c| ^ 2 * |x - y| := by rw [← mul_sub, abs_mul]; ring
    _ = c ^ 2 * |x - y| := by rw [sq_abs]

/-- The derivative of a scaled cosine is Lipschitz with the square of its
frequency as constant. -/
theorem lipschitzWith_deriv_scaledCos (c : ℝ) :
    LipschitzWith (Real.toNNReal (c ^ 2))
      (deriv (fun x : ℝ => Real.cos (c * x))) := by
  rw [deriv_scaledCos]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal (c ^ 2) (sq_nonneg c)]
  simp only [Real.dist_eq]
  calc
    |-c * Real.sin (c * x) - -c * Real.sin (c * y)| =
        |c| * |Real.sin (c * x) - Real.sin (c * y)| := by
          rw [show -c * Real.sin (c * x) - -c * Real.sin (c * y) =
            -c * (Real.sin (c * x) - Real.sin (c * y)) by ring,
            abs_mul, abs_neg]
    _ ≤ |c| * |c * x - c * y| := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
          Real.lipschitzWith_sin.dist_le_mul (c * x) (c * y))
        (abs_nonneg c)
    _ = |c| ^ 2 * |x - y| := by rw [← mul_sub, abs_mul]; ring
    _ = c ^ 2 * |x - y| := by rw [sq_abs]

set_option linter.style.longLine false in
/-- The sine and cosine cancellation residuals for one Fourier frequency,
synchronized on a single selected polynomial common refinement. -/
theorem GirsanovDensityData.exists_polynomial_diagonal_covariation_scaledSinCos_sub_crossBlocks_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (c : ℝ) (hT : 0 < T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M
            (fun s w => Real.sin (c * B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            (c * Real.cos (c * B (uniformPartitionTime T N j) omega)) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M
            (fun s w => Real.cos (c * B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            (-c * Real.sin (c * B (uniformPartitionTime T N j) omega)) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  simpa only [deriv_scaledSin c, deriv_scaledCos c] using
    hdata.exists_polynomial_diagonal_covariation_comp_pair_sub_crossBlocks_preBrownian
      hcross hMmeas hB hsm
      (fun x : ℝ => Real.sin (c * x)) (fun x : ℝ => Real.cos (c * x))
      (by fun_prop) (by fun_prop) (c ^ 2) (c ^ 2)
      (abs_deriv_deriv_scaledSin_le c) (abs_deriv_deriv_scaledCos_le c)
      (lipschitzWith_deriv_scaledSin c) (lipschitzWith_deriv_scaledCos c) hT

/-- The cancellation-ready selected-grid residual for a scaled sine of the
pre-Brownian driver.  Its coarse term is exactly `c cos(c B) dC`. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_covariation_scaledSin_sub_crossBlocks_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (c : ℝ) (hT : 0 < T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M
            (fun s w => Real.sin (c * B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            (c * Real.cos (c * B (uniformPartitionTime T N j) omega)) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  simpa only [deriv_scaledSin c] using
    hdata.exists_polynomial_diagonal_covariation_comp_sub_crossBlocks_preBrownian
      hcross hMmeas hB hsm (fun x : ℝ => Real.sin (c * x))
      (by fun_prop) (c ^ 2) (abs_deriv_deriv_scaledSin_le c)
      (lipschitzWith_deriv_scaledSin c) hT

/-- The cancellation-ready selected-grid residual for a scaled cosine of the
pre-Brownian driver.  Its coarse term is exactly `-c sin(c B) dC`. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_covariation_scaledCos_sub_crossBlocks_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (c : ℝ) (hT : 0 < T) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega =>
        let N := (k + 1) ^ 5
        quadraticCovariationApprox M
            (fun s w => Real.cos (c * B s w)) T
            (N * (m k + 1)) omega -
          ∑ j ∈ Finset.range N,
            (-c * Real.sin (c * B (uniformPartitionTime T N j) omega)) *
              (C (uniformPartitionTime T N (j + 1)) omega -
                C (uniformPartitionTime T N j) omega))
        atTop (fun _ => 0) := by
  simpa only [deriv_scaledCos c] using
    hdata.exists_polynomial_diagonal_covariation_comp_sub_crossBlocks_preBrownian
      hcross hMmeas hB hsm (fun x : ℝ => Real.cos (c * x))
      (by fun_prop) (c ^ 2) (abs_deriv_deriv_scaledCos_le c)
      (lipschitzWith_deriv_scaledCos c) hT

set_option maxHeartbeats 4000000 in
-- The expanded two-scale processes make elaboration substantially larger.
/-- Fixed-time cross variation, Brownian coarse-block control, and tight
quadratic sums produce a common-refinement diagonal on which every
Lipschitz Brownian-weighted covariation has the prescribed coarse Riemann
limit.  This is the path-regularity-free weighted-cross bridge. -/
theorem
    HasCrossVariationProcessInProbability.exists_polynomial_diagonal_weighted
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (g : ℝ → ℝ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) (hT : 0 < T) (G : W → ℝ)
    (hG : TendstoInMeasure P (fun k omega =>
      let K := (k + 1) ^ 5
      ∑ j ∈ Finset.range K, g (B (uniformPartitionTime T K j) omega) *
        (C (uniformPartitionTime T K (j + 1)) omega -
          C (uniformPartitionTime T K j) omega)) atTop G)
    (hqtight : ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop,
          P.real {omega | R ≤
            √(quadraticVariationApprox X T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k =>
        weightedQuadraticCovariationApprox
          (fun s omega => g (B s omega)) X B T
          (((k + 1) ^ 5) * (m k + 1))) atTop G := by
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let F : ℕ → ℕ → W → ℝ := fun k n omega =>
    ∑ j ∈ Finset.range (K k),
      g (B (uniformPartitionTime T (K k) j) omega) *
      (quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
          (uniformPartitionTime T (K k) (j + 1)) omega -
        quadraticCovariationBeforeStopApprox X B T (K k * (n + 1))
          (uniformPartitionTime T (K k) j) omega)
  let Gk : ℕ → W → ℝ := fun k omega =>
    ∑ j ∈ Finset.range (K k),
      g (B (uniformPartitionTime T (K k) j) omega) *
      (C (uniformPartitionTime T (K k) (j + 1)) omega -
        C (uniformPartitionTime T (K k) j) omega)
  have hFG : ∀ k, TendstoInMeasure P (F k) atTop (Gk k) := by
    intro k
    have hK : 0 < K k := by
      dsimp only [K]
      positivity
    have hraw := h.fullStepWeight_beforeStop_common_refinement
      hXmeas (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      T hK (fun j omega => g (B (uniformPartitionTime T (K k) j) omega))
      (fun j _hj => hg.continuous.comp_aestronglyMeasurable
        (hB.aemeasurable (uniformPartitionTime T (K k) j)
          |>.aestronglyMeasurable))
    simpa only [F, Gk] using hraw
  have hGk : TendstoInMeasure P Gk atTop G := by
    simpa only [Gk, K] using hG
  obtain ⟨m, hm, hdiag⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal hFG hGk
  let n : ℕ → ℕ := fun k => m k + 1
  have hn : ∀ k, 0 < n k := fun k => by
    dsimp only [n]
    positivity
  have herr :=
    tendstoInMeasure_weightedQuadraticCovariation_sub_polynomialBlocks
      hB hsm g hg T hT n hn (hqtight n hn)
  refine ⟨m, hm, ?_⟩
  have hsum := herr.add_real_noMeas hdiag
  apply hsum.congr
  · intro k
    exact Filter.Eventually.of_forall fun omega => by
      simp only [n, F, K]
      ring
  · exact Filter.Eventually.of_forall fun omega => by
      simp only [zero_add]

set_option linter.style.longLine false in
/-- The polynomial weighted-cross diagonal follows directly from ordinary
quadratic-variation contracts when the two terminal brackets have an
integrable nonnegative sum. -/
theorem HasCrossVariationProcessInProbability.exists_polynomial_diagonal_weighted_of_quadraticVariations
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (g : ℝ → ℝ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) (hT : 0 < T) (G : W → ℝ)
    (hG : TendstoInMeasure P (fun k omega =>
      let K := (k + 1) ^ 5
      ∑ j ∈ Finset.range K, g (B (uniformPartitionTime T K j) omega) *
        (C (uniformPartitionTime T K (j + 1)) omega -
          C (uniformPartitionTime T K j) omega)) atTop G)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k =>
        weightedQuadraticCovariationApprox
          (fun s omega => g (B s omega)) X B T
          (((k + 1) ^ 5) * (m k + 1))) atTop G := by
  apply h.exists_polynomial_diagonal_weighted hXmeas hB hsm g hg T hT G hG
  exact hQX.polynomialBlocks_eventually_tight_sqrt_mul hQB T hQint hQnonneg

set_option linter.style.longLine false in
set_option maxHeartbeats 4000000 in
-- The underlying weighted diagonal carries the same expanded two-scale terms.
/-- A fixed-time cross variation can be chained through a smooth Brownian
transform along a single strictly increasing polynomial common-refinement
diagonal.  Brownian fourth-variation control removes the Taylor remainder. -/
theorem HasCrossVariationProcessInProbability.exists_polynomial_diagonal_covariation_comp_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B X C QX QB : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQB : HasQuadraticVariationProcessInProbability B QB P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    {L : ℝ≥0} (hderiv : LipschitzWith L (deriv f))
    (T : ℝ≥0) (hT : 0 < T) (G : W → ℝ)
    (hG : TendstoInMeasure P (fun k omega =>
      let N := (k + 1) ^ 5
      ∑ j ∈ Finset.range N,
        deriv f (B (uniformPartitionTime T N j) omega) *
          (C (uniformPartitionTime T N (j + 1)) omega -
            C (uniformPartitionTime T N j) omega)) atTop G)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k =>
        quadraticCovariationApprox X (fun s w => f (B s w)) T
          (((k + 1) ^ 5) * (m k + 1))) atTop G := by
  obtain ⟨m, hm, hweighted⟩ :=
    h.exists_polynomial_diagonal_weighted_of_quadraticVariations
      hXmeas hB hsm hQX hQB (deriv f) hderiv T hT G hG hQint hQnonneg
  let N : ℕ → ℕ := fun k => ((k + 1) ^ 5) * (m k + 1)
  have hNpos : ∀ k, 0 < N k := fun k => by
    dsimp only [N]
    exact Nat.mul_pos (by positivity) (by positivity)
  have hN : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ N a := by
      exact Nat.le_mul_of_pos_right _ (by positivity)
    exact hba.trans (Nat.le_succ a) |>.trans (hbase.trans hmul)
  refine ⟨m, hm, ?_⟩
  have hchain :=
    tendstoInMeasure_quadraticCovariation_comp_of_weighted_preBrownian_counts
      f hf K hsecond hB hXmeas T (QX T) G (hQX T) N hNpos hN
        (by simpa only [N] using hweighted)
  simpa only [N] using hchain

/-- Novikov Girsanov data discharges both quadratic-variation and moment
premises of the polynomial Brownian-transform covariation chain rule. -/
theorem GirsanovDensityData.exists_polynomial_diagonal_covariation_comp_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    {L : ℝ≥0} (hderiv : LipschitzWith L (deriv f))
    (hT : 0 < T) (G : W → ℝ)
    (hG : TendstoInMeasure P (fun k omega =>
      let N := (k + 1) ^ 5
      ∑ j ∈ Finset.range N,
        deriv f (B (uniformPartitionTime T N j) omega) *
          (C (uniformPartitionTime T N (j + 1)) omega -
            C (uniformPartitionTime T N j) omega)) atTop G) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k =>
        quadraticCovariationApprox M (fun s w => f (B s w)) T
          (((k + 1) ^ 5) * (m k + 1))) atTop G := by
  apply hcross.exists_polynomial_diagonal_covariation_comp_preBrownian
    hMmeas hB hsm hdata.localQuadraticVariation.toProcess
    (fun t => quadraticVariation_preBrownianReal_inProbability hB t)
    f hf K hsecond hderiv T hT G hG
  · exact hdata.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

/-- The normalized complex character of a Brownian increment. -/
def brownianFourierIncrement
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a b : ℝ≥0) : W → ℂ :=
  fun omega ↦ Complex.exp
    (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I +
      (((((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))

/-- The normalized Brownian character has a deterministic norm. -/
theorem norm_brownianFourierIncrement
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a b : ℝ≥0) (omega : W) :
    ‖brownianFourierIncrement B c a b omega‖ =
      Real.exp (((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2) := by
  rw [brownianFourierIncrement, Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

/-- Measurability of the two endpoint evaluations makes the normalized
Brownian character strongly measurable. -/
theorem stronglyMeasurable_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (a b : ℝ≥0) :
    StronglyMeasurable (brownianFourierIncrement B c a b) := by
  apply Complex.continuous_exp.comp_stronglyMeasurable
  have hinc := ((hsm b).sub (hsm a)).const_mul c
  have himag := (Complex.continuous_ofReal.comp_stronglyMeasurable hinc).mul_const
    Complex.I
  exact himag.add stronglyMeasurable_const

/-- Every normalized Brownian character is integrable. -/
theorem integrable_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hsm : ∀ t, StronglyMeasurable (B t))
    (c : ℝ) (a b : ℝ≥0) :
    Integrable (brownianFourierIncrement B c a b) P := by
  refine Integrable.mono' (integrable_const
    (Real.exp (((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2)))
    (stronglyMeasurable_brownianFourierIncrement hsm c a b).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun omega ↦ by
    rw [norm_brownianFourierIncrement]

/-- The Gaussian characteristic function cancels the deterministic
normalizer, so a normalized Brownian character has mean one. -/
theorem integral_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ omega, brownianFourierIncrement B c a b omega ∂P = 1 := by
  let inc : W → ℝ := fun omega ↦ B b omega - B a omega
  let v : ℝ := ((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2
  have hchar : (∫ omega, Complex.exp
      (((c * inc omega : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp (-(v : ℂ)) := by
    have hlaw := hB.hasLaw_sub b a
    have hcomp := hlaw.integral_comp (E := ℂ)
      (f := fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (by fun_prop)
    calc
      (∫ omega, Complex.exp (((c * inc omega : ℝ) : ℂ) * Complex.I) ∂P) =
          ∫ x, Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)
            ∂gaussianReal 0 (nndist (b : ℝ) (a : ℝ)) := by
        change (∫ omega, Complex.exp
          (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I) ∂P) = _
        change (∫ omega, Complex.exp
          (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I) ∂P) = _ at hcomp
        exact hcomp
      _ = charFun (gaussianReal 0 (nndist (b : ℝ) (a : ℝ))) c := by
        rw [charFun_apply_real]
        apply integral_congr_ae
        filter_upwards with x
        congr 1
        push_cast
        ring
      _ = Complex.exp
          (-((((nndist (b : ℝ) (a : ℝ) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) := by
        rw [charFun_gaussianReal]
        simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
        congr 1
        push_cast
        ring
      _ = Complex.exp (-(v : ℂ)) := by
        congr 1
        dsimp only [v]
        rw [show (nndist (b : ℝ) (a : ℝ) : ℝ) = (b : ℝ) - (a : ℝ) by
          rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (mod_cast hab))],
          NNReal.coe_sub hab]
  have hfactor : brownianFourierIncrement B c a b = fun omega ↦
      Complex.exp (v : ℂ) *
        Complex.exp (((c * inc omega : ℝ) : ℂ) * Complex.I) := by
    funext omega
    rw [brownianFourierIncrement, Complex.exp_add]
    dsimp only [inc, v]
    ring
  rw [hfactor, integral_const_mul, hchar, ← Complex.exp_add]
  simp

/-- A normalized Brownian character is independent of the natural
filtration at the left endpoint. -/
theorem indep_brownianFourierIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep (MeasurableSpace.comap (brownianFourierIncrement B c a b)
      inferInstance) (Filtration.natural B hsm a) P := by
  apply ProbabilityTheory.indep_of_indep_of_le_left
    (indep_brownianIncrement_natural hB hsm hab)
  let f : ℝ → ℂ := fun x ↦ Complex.exp
    (((c * x : ℝ) : ℂ) * Complex.I +
      (((((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hfun : brownianFourierIncrement B c a b =
      f ∘ (fun omega ↦ B b omega - B a omega) := by rfl
  rw [hfun]
  exact (hf.comp (measurable_iff_comap_le.mpr le_rfl)).comap_le

@[simp]
theorem brownianFourierIncrement_self
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a : ℝ≥0) :
    brownianFourierIncrement B c a a = fun _ ↦ 1 := by
  funext omega
  simp [brownianFourierIncrement]

/-- Normalized Brownian characters multiply over adjacent intervals. -/
theorem brownianFourierIncrement_mul
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ)
    {a b d : ℝ≥0} (hab : a ≤ b) (hbd : b ≤ d) (omega : W) :
    brownianFourierIncrement B c a b omega *
        brownianFourierIncrement B c b d omega =
      brownianFourierIncrement B c a d omega := by
  rw [brownianFourierIncrement, brownianFourierIncrement,
    brownianFourierIncrement, ← Complex.exp_add]
  congr 1
  push_cast [NNReal.coe_sub hab, NNReal.coe_sub hbd,
    NNReal.coe_sub (hab.trans hbd)]
  ring

/-- The normalized Brownian character based at `s`; it is one before `s`
and accumulates the normalized character of `B_t-B_s` afterwards. -/
def brownianFourierIncrementProcess
    {W : Type*} (B : ℝ≥0 → W → ℝ) (s : ℝ≥0) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t ↦ brownianFourierIncrement B c (min t s) t

/-- The Brownian Fourier process is strongly adapted to the natural
filtration of the supplied version. -/
theorem stronglyAdapted_brownianFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    StronglyAdapted (Filtration.natural B hsm)
      (brownianFourierIncrementProcess B s c) := by
  intro t
  apply Complex.continuous_exp.comp_stronglyMeasurable
  have hBt : StronglyMeasurable[Filtration.natural B hsm t] (B t) :=
    Filtration.stronglyAdapted_natural hsm t
  have hBs : StronglyMeasurable[Filtration.natural B hsm t] (B (min t s)) :=
    (Filtration.stronglyAdapted_natural hsm (min t s)).mono
      ((Filtration.natural B hsm).mono (min_le_left _ _))
  have hinc := (hBt.sub hBs).const_mul c
  have himag := (Complex.continuous_ofReal.comp_stronglyMeasurable hinc).mul_const
    Complex.I
  exact himag.add stronglyMeasurable_const

/-- The normalized Brownian Fourier process is a complex martingale for
every pre-Brownian version; no sample-path continuity is used. -/
theorem martingale_brownianFourierIncrementProcess_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let V := Filtration.natural B hsm
  let E := brownianFourierIncrementProcess B s c
  have hEadapt : StronglyAdapted V E :=
    stronglyAdapted_brownianFourierIncrementProcess hsm s c
  have hEint (t : ℝ≥0) : Integrable (E t) P := by
    exact integrable_brownianFourierIncrement hsm c (min t s) t
  refine ⟨hEadapt, fun a b hab ↦ ?_⟩
  change P[E b | V a] =ᵐ[P] E a
  by_cases hbs : b ≤ s
  · have has : a ≤ s := hab.trans hbs
    have hEa : E a = fun _ ↦ 1 := by
      simp only [E, brownianFourierIncrementProcess, min_eq_left has,
        brownianFourierIncrement_self]
    have hEb : E b = fun _ ↦ 1 := by
      simp only [E, brownianFourierIncrementProcess, min_eq_left hbs,
        brownianFourierIncrement_self]
    rw [hEa, hEb]
    exact Filter.EventuallyEq.of_eq <| condExp_of_stronglyMeasurable
      (V.le a) (by fun_prop) (integrable_const 1)
  · have hsb : s ≤ b := le_of_not_ge hbs
    by_cases hsa : s ≤ a
    · let future : W → ℂ := brownianFourierIncrement B c a b
      have hfactor : E b = E a * future := by
        funext omega
        dsimp only [E, brownianFourierIncrementProcess, future]
        rw [min_eq_right hsb, min_eq_right hsa]
        exact (brownianFourierIncrement_mul B c hsa hab omega).symm
      have hfutureMeas : StronglyMeasurable future :=
        stronglyMeasurable_brownianFourierIncrement hsm c a b
      have hfutureInt : Integrable future P :=
        integrable_brownianFourierIncrement hsm c a b
      have hind : Indep (MeasurableSpace.comap future inferInstance) (V a) P :=
        indep_brownianFourierIncrement_natural hB hsm c hab
      have hcondFuture : P[future | V a] =ᵐ[P] fun _ ↦ ∫ omega, future omega ∂P :=
        condExp_indep_eq hfutureMeas.measurable.comap_le (V.le a)
          (Measurable.stronglyMeasurable
            (measurable_iff_comap_le.mpr le_rfl)) hind
      have hproductInt : Integrable (E a * future) P := by
        rw [← hfactor]
        exact hEint b
      rw [hfactor]
      calc
        P[E a * future | V a] =ᵐ[P] E a * P[future | V a] :=
          condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) (hEadapt a)
            hproductInt hfutureInt
        _ =ᵐ[P] E a * (fun _ ↦ ∫ omega, future omega ∂P) :=
          Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
        _ =ᵐ[P] E a := by
          have hmean : (∫ omega, future omega ∂P) = 1 :=
            integral_brownianFourierIncrement hB c hab
          filter_upwards with omega
          simp only [Pi.mul_apply, hmean, mul_one]
    · have has : a ≤ s := le_of_not_ge hsa
      let future : W → ℂ := brownianFourierIncrement B c s b
      have hEa : E a = fun _ ↦ 1 := by
        simp only [E, brownianFourierIncrementProcess, min_eq_left has,
          brownianFourierIncrement_self]
      have hEb : E b = future := by
        simp only [E, brownianFourierIncrementProcess, min_eq_right hsb, future]
      have hfutureMeas : StronglyMeasurable future :=
        stronglyMeasurable_brownianFourierIncrement hsm c s b
      have hindS : Indep (MeasurableSpace.comap future inferInstance) (V s) P :=
        indep_brownianFourierIncrement_natural hB hsm c hsb
      have hindA : Indep (MeasurableSpace.comap future inferInstance) (V a) P :=
        ProbabilityTheory.indep_of_indep_of_le_right hindS (V.mono has)
      have hcondFuture : P[future | V a] =ᵐ[P] fun _ ↦ ∫ omega, future omega ∂P :=
        condExp_indep_eq hfutureMeas.measurable.comap_le (V.le a)
          (Measurable.stronglyMeasurable
            (measurable_iff_comap_le.mpr le_rfl)) hindA
      rw [hEa, hEb]
      have hmean : (∫ omega, future omega ∂P) = 1 :=
        integral_brownianFourierIncrement hB c hsb
      filter_upwards [hcondFuture] with omega homega
      simp only [homega, hmean]

/-- A pre-Brownian process is a martingale in the right continuation of its
natural filtration.  Uniform integrability of bounded deterministic-time
families replaces any appeal to pathwise continuity or random-time optional
stopping. -/
theorem martingale_brownian_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale B (Filtration.rightCont (Filtration.natural B hsm)) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let V := Filtration.natural B hsm
  have hmart : Martingale B V P := martingale_brownian_natural hB hsm
  apply StochasticCalculus.Martingale.rightCont_of_tendstoInMeasure_of_uniformIntegrable_banach
    hmart
  · intro r a ha
    exact StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha
  · intro _r a ha
    obtain ⟨R, hR⟩ := ha.bddAbove_range
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic hmart R)
      (fun n => ⟨a n, by
        simpa only [Set.mem_Iic] using hR (Set.mem_range_self n)⟩)
    simpa only [V] using hUI

/-- The normalized Brownian character is stochastically continuous for
every pre-Brownian version.  This follows from stochastic continuity of the
two Brownian endpoint evaluations and continuity of the complex exponential;
no sample-path regularity is used. -/
theorem tendstoInMeasure_brownianFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n ↦ brownianFourierIncrementProcess B s c (a n)) atTop
      (brownianFourierIncrementProcess B s c r) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let inc : ℕ → W → ℝ := fun n omega ↦
    B (a n) omega - B (min (a n) s) omega
  let incLimit : W → ℝ := fun omega ↦ B r omega - B (min r s) omega
  have hmin : Tendsto (fun n ↦ min (a n) s) atTop (nhds (min r s)) :=
    ha.min tendsto_const_nhds
  have hinc : TendstoInMeasure P inc atTop incLimit := by
    apply TendstoInMeasure.continuous_comp₂
      (fun n ↦ (hsm (a n)).aestronglyMeasurable)
      (fun n ↦ (hsm (min (a n) s)).aestronglyMeasurable)
      (StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha)
      (StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB hmin)
    fun_prop
  have htime : TendstoInMeasure P (fun n ↦ fun _ : W ↦ a n) atTop
      (fun _ : W ↦ r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ ↦ aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ ↦ ha
  let f : ℝ → ℝ≥0 → ℂ := fun x t ↦ Complex.exp
    (((c * x : ℝ) : ℂ) * Complex.I +
      (((((t - min t s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))
  have hf : Continuous f.uncurry := by
    dsimp only [f, Function.uncurry]
    fun_prop
  have hresult := TendstoInMeasure.continuous_comp₂
    (fun n ↦ ((hsm (a n)).sub (hsm (min (a n) s))).aestronglyMeasurable)
    (fun _ ↦ aestronglyMeasurable_const) hinc htime hf
  change TendstoInMeasure P (fun n omega ↦ Complex.exp
      (((c * (B (a n) omega - B (min (a n) s) omega) : ℝ) : ℂ) *
        Complex.I +
        (((((a n - min (a n) s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))))
    atTop (fun omega ↦ Complex.exp
      (((c * (B r omega - B (min r s) omega) : ℝ) : ℂ) * Complex.I +
        (((((r - min r s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))))
  simpa only [inc, incLimit, f, Pi.sub_apply] using hresult

/-- The Brownian Fourier martingale remains a martingale after right
continuation of its natural filtration. -/
theorem martingale_brownianFourierIncrementProcess_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      (Filtration.rightCont (Filtration.natural B hsm)) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    (martingale_brownianFourierIncrementProcess_natural hB hsm s c)
  · intro r a ha
    exact tendstoInMeasure_brownianFourierIncrementProcess hB hsm s c ha
  · intro R
    let K : ℝ≥0 := ⟨Real.exp ((R : ℝ) * c ^ 2 / 2),
      (Real.exp_pos _).le⟩
    refine ⟨K, fun t ht omega ↦ ?_⟩
    simp only [brownianFourierIncrementProcess]
    rw [norm_brownianFourierIncrement]
    change Real.exp (((t - min t s : ℝ≥0) : ℝ) * c ^ 2 / 2) ≤
      Real.exp ((R : ℝ) * c ^ 2 / 2)
    apply Real.exp_le_exp.mpr
    have htime : ((t - min t s : ℝ≥0) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (tsub_le_self.trans ht)
    nlinarith [sq_nonneg c]

/-! ## Complex quadratic variation for the Fourier argument -/

/-- The complex local-martingale combination `M + i c B` used in the
Fourier proof of Girsanov's theorem. -/
def complexMartingaleCombination
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ) : ℝ≥0 → W → ℂ :=
  fun t omega ↦ (M t omega : ℂ) + ((c * B t omega : ℝ) : ℂ) * Complex.I

/-- Uniform-partition quadratic variation of a complex-valued process.  The
square is the algebraic complex square, rather than the squared norm. -/
noncomputable def complexQuadraticVariationApprox
    {W : Type*} (X : ℝ≥0 → W → ℂ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    (X (uniformPartitionTime t n (i + 1)) omega -
      X (uniformPartitionTime t n i) omega) ^ 2

/-- The complex bracket of `M + i c B`: the real Brownian quadratic term
changes sign and the real cross variation becomes the imaginary term. -/
def complexMartingaleCombinationBracket
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (bracket t omega : ℂ) - (c ^ 2 * (t : ℝ) : ℝ) +
    ((2 * c * C t omega : ℝ) : ℂ) * Complex.I

/-- Adapted real inputs assemble into the adapted complex martingale
combination. -/
theorem stronglyAdapted_complexMartingaleCombination
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M B : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hB : StronglyAdapted V B) (c : ℝ) :
    StronglyAdapted V (complexMartingaleCombination M B c) := by
  intro t
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable (hM t)).add
    ((Complex.continuous_ofReal.comp_stronglyMeasurable
      ((hB t).const_mul c)).mul_const Complex.I)

/-- Adapted bracket and cross-variation inputs assemble into the adapted
complex bracket. -/
theorem stronglyAdapted_complexMartingaleCombinationBracket
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : StronglyAdapted V bracket)
    (hC : StronglyAdapted V C) (c : ℝ) :
    StronglyAdapted V
      (complexMartingaleCombinationBracket bracket C c) := by
  intro t
  exact ((Complex.continuous_ofReal.comp_stronglyMeasurable
    (hbracket t)).sub stronglyMeasurable_const).add
      ((Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hC t).const_mul (2 * c))).mul_const Complex.I)

/-- Continuous real paths assemble into continuous paths of the complex
martingale combination. -/
theorem continuous_complexMartingaleCombination
    {W : Type*} {M B : ℝ≥0 → W → ℝ}
    (hM : ∀ omega, Continuous (fun t ↦ M t omega))
    (hB : ∀ omega, Continuous (fun t ↦ B t omega)) (c : ℝ) :
    ∀ omega, Continuous (fun t ↦ complexMartingaleCombination M B c t omega) := by
  intro omega
  unfold complexMartingaleCombination
  fun_prop

/-- Continuous bracket and cross-variation paths assemble into continuous
paths of the complex bracket. -/
theorem continuous_complexMartingaleCombinationBracket
    {W : Type*} {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : ∀ omega, Continuous (fun t ↦ bracket t omega))
    (hC : ∀ omega, Continuous (fun t ↦ C t omega)) (c : ℝ) :
    ∀ omega, Continuous (fun t ↦
      complexMartingaleCombinationBracket bracket C c t omega) := by
  intro omega
  unfold complexMartingaleCombinationBracket
  fun_prop

/-- Process-level convergence in probability of algebraic complex
quadratic-variation sums. -/
def HasComplexQuadraticVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (X Q : ℝ≥0 → W → ℂ) (P : Measure W) : Prop :=
  ∀ t, TendstoInMeasure P
    (fun n ↦ complexQuadraticVariationApprox X t (n + 1)) atTop (Q t)

/-- Elementary complex square identity underlying the bracket of
`M + i c B`. -/
private theorem complex_sq_ofReal_add_mul_I (a b c : ℝ) :
    ((a : ℂ) + ((c * b : ℝ) : ℂ) * Complex.I) ^ 2 =
      ((a ^ 2 - c ^ 2 * b ^ 2 : ℝ) : ℂ) +
        ((2 * c * (a * b) : ℝ) : ℂ) * Complex.I := by
  calc
    _ = (a : ℂ) ^ 2 + 2 * (a : ℂ) * ((c * b : ℝ) : ℂ) * Complex.I +
        (((c * b : ℝ) : ℂ) ^ 2) * Complex.I ^ 2 := by ring
    _ = _ := by
      rw [Complex.I_sq]
      push_cast
      ring

/-- Expanding the square of each complex increment gives the two real
quadratic variations and twice the real cross variation. -/
theorem complexQuadraticVariationApprox_complexMartingaleCombination
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    complexQuadraticVariationApprox
        (complexMartingaleCombination M B c) t n omega =
      (quadraticVariationApprox M t n omega : ℂ) -
        (c ^ 2 * quadraticVariationApprox B t n omega : ℝ) +
        ((2 * c * quadraticCovariationApprox M B t n omega : ℝ) : ℂ) *
          Complex.I := by
  unfold complexQuadraticVariationApprox complexMartingaleCombination
    quadraticVariationApprox quadraticCovariationApprox
  calc
    _ = ∑ i ∈ Finset.range n, (
        (((M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega) ^ 2 -
            c ^ 2 * (B (uniformPartitionTime t n (i + 1)) omega -
              B (uniformPartitionTime t n i) omega) ^ 2 : ℝ) : ℂ) +
          ((2 * c * ((M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega) *
            (B (uniformPartitionTime t n (i + 1)) omega -
              B (uniformPartitionTime t n i) omega)) : ℝ) : ℂ) *
            Complex.I) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hdiff :
          (M (uniformPartitionTime t n (i + 1)) omega : ℂ) +
                ((c * B (uniformPartitionTime t n (i + 1)) omega : ℝ) : ℂ) *
                  Complex.I -
              ((M (uniformPartitionTime t n i) omega : ℂ) +
                ((c * B (uniformPartitionTime t n i) omega : ℝ) : ℂ) *
                  Complex.I) =
            ((M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega : ℝ) : ℂ) +
              ((c * (B (uniformPartitionTime t n (i + 1)) omega -
                B (uniformPartitionTime t n i) omega) : ℝ) : ℂ) *
                Complex.I := by
        push_cast
        ring
      rw [hdiff]
      exact complex_sq_ofReal_add_mul_I
        (M (uniformPartitionTime t n (i + 1)) omega -
          M (uniformPartitionTime t n i) omega)
        (B (uniformPartitionTime t n (i + 1)) omega -
          B (uniformPartitionTime t n i) omega) c
    _ = _ := by
      apply Complex.ext
      · change Complex.reCLM (∑ i ∈ Finset.range n, _) = _
        rw [map_sum]
        simp only [Complex.reCLM_apply, Complex.add_re, Complex.sub_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, Finset.mul_sum]
        simp only [zero_mul, sub_zero, add_zero]
        rw [Finset.sum_sub_distrib]
      · change Complex.imCLM (∑ i ∈ Finset.range n, _) = _
        rw [map_sum]
        simp only [Complex.imCLM_apply, Complex.add_im, Complex.sub_im,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, zero_add, mul_one, Finset.mul_sum]
        ring_nf

/-- Quadratic variation and cross variation assemble into the complex
quadratic variation of `M + i c B`.  This is the exact second-order
cancellation required by the characteristic-function proof. -/
theorem HasQuadraticVariationProcessInProbability.complexMartingaleCombination
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hM : HasQuadraticVariationProcessInProbability M bracket P)
    (hB : IsPreBrownianReal B P)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hBmeas : ∀ s, AEStronglyMeasurable (B s) P)
    (c : ℝ) :
    HasComplexQuadraticVariationProcessInProbability
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) P := by
  intro t
  let f : ℝ → ℝ → ℂ := fun x y ↦ (x : ℂ) - (c ^ 2 * y : ℝ)
  have hf : Continuous f.uncurry := by
    dsimp only [f, Function.uncurry]
    fun_prop
  have hqMmeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationApprox M t (n + 1)) P :=
    aestronglyMeasurable_quadraticVariationApprox hMmeas t (n + 1)
  have hqBmeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationApprox B t (n + 1)) P :=
    aestronglyMeasurable_quadraticVariationApprox hBmeas t (n + 1)
  have hfirst := TendstoInMeasure.continuous_comp₂ hqMmeas hqBmeas
    (hM t) (quadraticVariation_preBrownianReal_inProbability hB t) hf
  let F : ℕ → W → ℂ := fun n omega ↦
    f (quadraticVariationApprox M t (n + 1) omega)
      (quadraticVariationApprox B t (n + 1) omega)
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) P := by
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hqMmeas n)).sub
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          (aestronglyMeasurable_const.mul (hqBmeas n)))
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationApprox M B t (n + 1)) P :=
    aestronglyMeasurable_quadraticCovariationApprox
      hMmeas hBmeas t (n + 1)
  let g : ℂ → ℝ → ℂ := fun z x ↦
    z + ((2 * c * x : ℝ) : ℂ) * Complex.I
  have hg : Continuous g.uncurry := by
    dsimp only [g, Function.uncurry]
    fun_prop
  have hresult := TendstoInMeasure.continuous_comp₂ hFmeas hcrossMeas
    (by simpa only [F, f] using hfirst) (hcross t) hg
  apply hresult.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [complexQuadraticVariationApprox_complexMartingaleCombination]
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Girsanov density data and a real cross-variation contract provide the
complex bracket needed for every Fourier frequency. -/
theorem GirsanovDensityData.complexMartingaleCombinationQuadraticVariation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (c : ℝ) :
    HasComplexQuadraticVariationProcessInProbability
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) P := by
  apply hdata.localQuadraticVariation.toProcess.complexMartingaleCombination
    hB hcross
  · intro s
    exact ((hdata.adapted_martingale s).mono
      (V.le s)).aestronglyMeasurable
  · exact fun s ↦ (hsm s).aestronglyMeasurable

/-- Algebraic complex Doléans exponential associated to a complex process
and its algebraic quadratic variation. -/
noncomputable def complexDoleansDadeExponential
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) : ℝ≥0 → W → ℂ :=
  fun t omega ↦ Complex.exp (X t omega - Q t omega / 2)

/-- The complex stochastic exponential of `M + i c B` factors into the
real Doléans density and the normalized Fourier character of `B - C`. -/
theorem complexDoleansDadeExponential_combination_factor
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega =
      (doleansDadeExponential M bracket t omega : ℂ) *
        Complex.exp
          (((c * (B t omega - C t omega) : ℝ) : ℂ) * Complex.I +
            ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ)) := by
  unfold complexDoleansDadeExponential complexMartingaleCombination
    complexMartingaleCombinationBracket doleansDadeExponential doleansDadeLog
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The continuous factor in the complex Girsanov exponential after the
possibly discontinuous pre-Brownian Fourier character has been split off. -/
noncomputable def girsanovComplexDoleansContinuousCoefficient
    {W : Type*} (M bracket C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) : ℂ :=
  (doleansDadeExponential M bracket t omega : ℂ) *
    Complex.exp
      (((-c * C t omega : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))

theorem stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} [MeasurableSpace W] {M bracket C : ℝ≥0 → W → ℝ}
    (hM : ∀ t, StronglyMeasurable (M t))
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hC : ∀ t, StronglyMeasurable (C t)) (c : ℝ) :
    ∀ t, StronglyMeasurable
      (girsanovComplexDoleansContinuousCoefficient M bracket C c t) := by
  intro t
  unfold girsanovComplexDoleansContinuousCoefficient
  have hdensity : StronglyMeasurable
      (doleansDadeExponential M bracket t) := by
    unfold doleansDadeExponential doleansDadeLog
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hM t).sub ((hbracket t).const_mul (1 / 2)))
  have hphase : StronglyMeasurable (fun omega ↦
      (((-c * C t omega : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))) := by
    exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
      ((hC t).const_mul (-c))).mul_const Complex.I).add
        stronglyMeasurable_const)
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable hdensity).mul
    (Complex.continuous_exp.comp_stronglyMeasurable hphase)

/-- The complex Doléans weight is a continuous random coefficient times
the unit-modulus Fourier character of the supplied Brownian representative. -/
theorem complexDoleansDadeExponential_combination_factor_continuous_brownian
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega =
      girsanovComplexDoleansContinuousCoefficient M bracket C c t omega *
        Complex.exp (((c * B t omega : ℝ) : ℂ) * Complex.I) := by
  rw [complexDoleansDadeExponential_combination_factor]
  unfold girsanovComplexDoleansContinuousCoefficient
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Pathwise continuity of the martingale, bracket, and cross term makes the
non-Brownian coefficient in the factorization continuous. -/
theorem continuous_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} {M bracket C : ℝ≥0 → W → ℝ}
    (hM : ∀ omega, Continuous (fun t ↦ M t omega))
    (hbracket : ∀ omega, Continuous (fun t ↦ bracket t omega))
    (hC : ∀ omega, Continuous (fun t ↦ C t omega)) (c : ℝ) :
    ∀ omega, Continuous (fun t ↦
      girsanovComplexDoleansContinuousCoefficient M bracket C c t omega) := by
  intro omega
  unfold girsanovComplexDoleansContinuousCoefficient
    doleansDadeExponential doleansDadeLog
  fun_prop

/-- Removing the Brownian Fourier character does not change the modulus of
the complex Doléans weight. -/
theorem norm_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} (M bracket C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    ‖girsanovComplexDoleansContinuousCoefficient
        M bracket C c t omega‖ =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) := by
  unfold girsanovComplexDoleansContinuousCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (doleansDadeExponential_pos M bracket t omega),
    Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

/-- A real-frequency unit-circle character is Lipschitz with the absolute
frequency as constant. -/
theorem lipschitzWith_complexFourierCharacter (c : ℝ) :
    LipschitzWith (Real.toNNReal |c|)
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal |c| (abs_nonneg c), Real.dist_eq, dist_eq_norm]
  calc
    ‖Complex.exp (((c * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)‖ =
        ‖Complex.exp (((c * y : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    _ = ‖Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)‖ *
        ‖Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [norm_mul]
    _ = ‖Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ ‖c * (x - y)‖ := by
      simpa only [mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := c * (x - y)))
    _ = |c| * |x - y| := by
      rw [Real.norm_eq_abs, abs_mul]

/-- Outside the Brownian block-oscillation event, freezing the full complex
Girsanov weight reduces to freezing its continuous coefficient plus the
unit-circle Fourier error. -/
theorem
    norm_complexDoleansWeightedCovariation_commonRefinement_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (M bracket B C X Y : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    {k n : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (alpha R : ℝ) (halpha : 0 ≤ alpha) (hR : 0 ≤ R)
    (delta : ℝ≥0) (hdelta : 0 < delta) {omega : W}
    (hAclose : ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
      uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T (k * n) i) omega -
        girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ∀ j ∈ Finset.range k,
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T k j) omega‖ ≤ R)
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r ↦
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ‖(∑ i ∈ Finset.range (k * n),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega *
          ((X (uniformPartitionTime T (k * n) (i + 1)) omega -
            X (uniformPartitionTime T (k * n) i) omega) *
          (Y (uniformPartitionTime T (k * n) (i + 1)) omega -
            Y (uniformPartitionTime T (k * n) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range k,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (k * n)
                (uniformPartitionTime T k (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (k * n)
                (uniformPartitionTime T k j) omega : ℂ)‖ ≤
      (alpha + R * |c| * (delta : ℝ)) *
        √(quadraticVariationApprox X T (k * n) omega *
          quadraticVariationApprox Y T (k * n) omega) := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hweight : ∀ i ∈ Finset.range (k * n),
      ‖complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime T k j <
                uniformPartitionTime T (k * n) (i + 1) ∧
              uniformPartitionTime T (k * n) (i + 1) ≤
                uniformPartitionTime T k (j + 1) then
            complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T k j) omega
          else 0‖ ≤ alpha + R * |c| * (delta : ℝ) := by
    intro i hi
    have hkn : 0 < k * n := Nat.mul_pos hk hn
    have hi1 : i + 1 ≤ k * n := Finset.mem_range.mp hi
    have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
    have hr0 : 0 < uniformPartitionTime T (k * n) (i + 1) := by
      have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
        intro a b hab
        unfold uniformPartitionTime
        have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast hkn
        gcongr
      have hpos := hstrict (Nat.zero_lt_succ i)
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
        using hpos
    apply norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
      T (uniformPartitionTime T (k * n) (i + 1)) k hk hr0 hrt
    intro j hj hactive
    obtain ⟨r, hr, htime⟩ :=
      uniformPartitionTime_active_block_common_refinement
        T hT hk hn hactive
    have hBclose := hosc j hj r hr
    rw [← htime] at hBclose
    rw [complexDoleansDadeExponential_combination_factor_continuous_brownian,
      complexDoleansDadeExponential_combination_factor_continuous_brownian]
    have hraw := norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
      (girsanovComplexDoleansContinuousCoefficient M bracket C c) B
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (lipschitzWith_complexFourierCharacter c) T omega alpha R 1
      (delta : ℝ) (hAclose i hi j hj hactive) (hAbound j hj)
      (by rw [Complex.norm_exp_ofReal_mul_I]) hBclose
    simpa only [mul_one, Real.coe_toNNReal |c| (abs_nonneg c)] using hraw
  exact norm_complexWeightedQuadraticCovariation_sub_completedBlocks_le
    X Y T (k * n) k
      (fun i omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (k * n) i) omega)
      (fun j omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T k j) omega)
      (alpha + R * |c| * (delta : ℝ))
      (add_nonneg halpha (mul_nonneg (mul_nonneg hR (abs_nonneg c))
        delta.coe_nonneg)) omega hweight

/-- The pathwise complex common-refinement estimate promotes to convergence
in measure once the coefficient-freezing error vanishes, the coefficient
and quadratic sums are tight, and the Brownian oscillation event becomes
rare.  This separates the deterministic path analysis from the eventual
diagonal selection. -/
theorem
    tendstoInMeasure_complexDoleansWeightedCovariation_sub_completedBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (M bracket B C X Y : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (K N : ℕ → ℕ) (hT : 0 < T) (hK : ∀ r, 0 < K r)
    (hN : ∀ r, 0 < N r)
    (alpha R : ℕ → W → ℝ) (halpha : ∀ r omega, 0 ≤ alpha r omega)
    (hR : ∀ r omega, 0 ≤ R r omega)
    (halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0))
    (hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta)
    (delta : ℕ → ℝ≥0)
    (hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0))
    (hdeltaPos : ∀ r, 0 < delta r)
    (hqtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          √(quadraticVariationApprox X T (K r * N r) omega *
            quadraticVariationApprox Y T (K r * N r) omega)} < eta)
    (hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0))
    (hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r * N r) i) omega -
          girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega)
    (hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega) :
    TendstoInMeasure P (fun r omega ↦
      (∑ i ∈ Finset.range (K r * N r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r * N r) i) omega *
          ((X (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            X (uniformPartitionTime T (K r * N r) i) omega) *
          (Y (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            Y (uniformPartitionTime T (K r * N r) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range (K r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r) j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (K r * N r)
                (uniformPartitionTime T (K r) (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (K r * N r)
                (uniformPartitionTime T (K r) j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun r omega ↦
    √(quadraticVariationApprox X T (K r * N r) omega *
      quadraticVariationApprox Y T (K r * N r) omega)
  let small : ℕ → W → ℝ := fun r _ ↦ |c| * (delta r : ℝ)
  let rq : ℕ → W → ℝ := fun r omega ↦ R r omega * q r omega
  let b₁ : ℕ → W → ℝ := fun r omega ↦ alpha r omega * q r omega
  let b₂ : ℕ → W → ℝ := fun r omega ↦ small r omega * rq r omega
  let b : ℕ → W → ℝ := fun r omega ↦ b₁ r omega + b₂ r omega
  have hq_nonneg : ∀ r omega, 0 ≤ q r omega :=
    fun r omega ↦ Real.sqrt_nonneg _
  have hq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ q r omega} < eta := by
    simpa only [q] using hqtight
  have hb₁ : TendstoInMeasure P b₁ atTop (fun _ ↦ 0) := by
    apply halphaZero.of_norm_sub_le_mul_of_eventually_tight
      hq_nonneg hq_tight
    intro r omega
    simp only [b₁, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (halpha r omega), q]
    rw [abs_of_nonneg (mul_nonneg (halpha r omega) (Real.sqrt_nonneg _))]
  have hrq_nonneg : ∀ r omega, 0 ≤ rq r omega := fun r omega ↦
    mul_nonneg (hR r omega) (hq_nonneg r omega)
  have hrq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ rq r omega} < eta := by
    exact eventually_tight_mul_of_nonneg hR hq_nonneg hRtight hq_tight
  have hsmall : TendstoInMeasure P small atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro r
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ ↦ by
        simpa only [small, mul_zero] using
          hdelta.const_mul |c|
  have hsmall_nonneg : ∀ r omega, 0 ≤ small r omega := fun r omega ↦
    mul_nonneg (abs_nonneg c) (delta r).coe_nonneg
  have hb₂ : TendstoInMeasure P b₂ atTop (fun _ ↦ 0) := by
    apply hsmall.of_norm_sub_le_mul_of_eventually_tight
      hrq_nonneg hrq_tight
    intro r omega
    simp only [b₂, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hsmall_nonneg r omega)]
    rw [abs_of_nonneg
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))]
  have hbZero : TendstoInMeasure P b atTop (fun _ ↦ 0) := by
    simpa only [b, zero_add] using hb₁.add_real_noMeas hb₂
  let bad : ℕ → Set W := fun r ↦
    ⋃ j ∈ Finset.range (K r), {omega |
      ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
        Finset.nonempty_range_add_one (fun u ↦
          (B (uniformPartitionTime T (K r) j +
              uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
            B (uniformPartitionTime T (K r) j) omega) ^ 4)}
  have hbadZero : Tendsto (fun r ↦ P.real (bad r)) atTop (nhds 0) := by
    simpa only [bad] using hbad
  have hb_nonneg : ∀ r omega, 0 ≤ b r omega := fun r omega ↦
    add_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))
  apply hbZero.of_norm_le_nonneg_outside_noMeas hb_nonneg hbadZero
  intro r omega homega
  have hraw :=
    norm_complexDoleansWeightedCovariation_commonRefinement_sub_completedBlocks_le
      M bracket B C X Y c T hT (hK r) (hN r)
      (alpha r omega) (R r omega) (halpha r omega) (hR r omega)
      (delta r) (hdeltaPos r) (hAclose r omega) (hAbound r omega) homega
  calc
    _ ≤ (alpha r omega + R r omega * |c| * (delta r : ℝ)) *
        q r omega := by simpa only [q] using hraw
    _ = b r omega := by
      dsimp only [b, b₁, b₂, small, rq]
      ring

/-- The density maximum used by the early complex-freezing layer.  A
specialized copy is kept here because the more featureful stopped-weight
controls are developed later in the file. -/
noncomputable def complexFreezingDensityLeftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦
    doleansDadeExponential M bracket
      (min (uniformPartitionTime T (n + 1) k) T) omega

theorem complexFreezingDensityLeftMax_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    0 ≤ complexFreezingDensityLeftMax M bracket T n omega := by
  exact (doleansDadeExponential_pos M bracket
    (min (uniformPartitionTime T (n + 1) 0) T) omega).le.trans
      (Finset.le_sup' (fun k ↦ doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) k) T) omega)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem GirsanovDensityData.complexFreezingDensityLeftMax_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ n,
        P.real {omega | K ≤
          complexFreezingDensityLeftMax M bracket T n omega} < delta := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : 0 < N := by
    have honeDiv : 0 < 1 / delta := one_div_pos.mpr hdelta
    exact_mod_cast honeDiv.trans hN
  let K : ℝ≥0 := ⟨(N : ℝ), Nat.cast_nonneg N⟩
  have hKpos : (0 : ℝ) < K := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast hNpos
  refine ⟨(K : ℝ), hKpos, fun n ↦ ?_⟩
  let D : ℝ≥0 → W → ℝ := fun t omega ↦
    doleansDadeExponential M bracket (min t T) omega
  let E : Set W := {omega | (K : ℝ) ≤
    complexFreezingDensityLeftMax M bracket T n omega}
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hsample : Martingale (uniformPartitionSample D T (n + 1))
      (uniformPartitionFiltration V T (n + 1)) P :=
    martingale_uniformPartitionSample hDmart T (n + 1)
  have hnonneg : 0 ≤ uniformPartitionSample D T (n + 1) :=
    fun _k omega ↦ (doleansDadeExponential_pos M bracket _ omega).le
  have hraw := maximal_ineq hsample.submartingale hnonneg (ε := K) n
  have hset : {omega |
      (K : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
          (fun k ↦ uniformPartitionSample D T (n + 1) k omega)} = E := by
    rfl
  rw [hset] at hraw
  have hterminal :
      ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P = 1 := by
    have htime : uniformPartitionTime T (n + 1) n ≤ T :=
      (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
        (Nat.le_succ n)).2
    have heq := StochasticCalculus.Martingale.integral_eq hDmart htime
    rw [show D T = girsanovDensity M bracket T by
      funext omega
      simp only [D, girsanovDensity, min_self]] at heq
    simpa only [uniformPartitionSample, D,
      min_eq_left htime, hdata.integral_eq_one] using heq.symm
  have hsetIntegral :
      ∫ omega in E, uniformPartitionSample D T (n + 1) n omega ∂P ≤ 1 := by
    calc
      _ ≤ ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P :=
        setIntegral_le_integral (hsample.integrable n)
          (Filter.Eventually.of_forall fun omega ↦
            (doleansDadeExponential_pos M bracket _ omega).le)
      _ = 1 := hterminal
  have hbound : (K : ℝ≥0∞) * P E ≤ 1 :=
    hraw.trans ((ENNReal.ofReal_le_ofReal hsetIntegral).trans_eq (by norm_num))
  have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at hreal
  change (K : ℝ) * P.real E ≤ 1 at hreal
  have hKdelta : 1 < (K : ℝ) * delta := by
    apply (div_lt_iff₀ hdelta).mp
    change 1 / delta < (N : ℝ)
    exact hN
  have htail : P.real E < delta := by
    by_contra hnot
    have hdeltaLe : delta ≤ P.real E := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hdeltaLe
      (show 0 ≤ (K : ℝ) by positivity)
    nlinarith
  simpa only [E] using htail

/-- Girsanov density data supplies the coefficient tightness in the complex
freezing theorem.  A master sequence of inner counts is sampled along the
polynomial Brownian scale, so the pathwise coefficient modulus and the
Brownian fourth-moment estimate share one cofinal grid. -/
theorem
    GirsanovDensityData.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (hqtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          √(quadraticVariationApprox X T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega *
            quadraticVariationApprox Y T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega)} < eta) :
    TendstoInMeasure P (fun r omega ↦
      let K := (r + 1) ^ 5
      let N := n (K - 1) + 1
      (∑ i ∈ Finset.range (K * N),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K * N) i) omega *
          ((X (uniformPartitionTime T (K * N) (i + 1)) omega -
            X (uniformPartitionTime T (K * N) i) omega) *
          (Y (uniformPartitionTime T (K * N) (i + 1)) omega -
            Y (uniformPartitionTime T (K * N) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range K,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T K j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (K * N)
                (uniformPartitionTime T K (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (K * N)
                (uniformPartitionTime T K j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let s : ℕ → ℕ := fun r ↦ K r - 1
  let N : ℕ → ℕ := fun r ↦ n (s r) + 1
  let A : ℝ≥0 → W → ℂ :=
    girsanovComplexDoleansContinuousCoefficient M bracket C c
  let alpha : ℕ → W → ℝ := fun r ↦
    commonRefinementMaxComplexStepError A T (s r) (n (s r))
  let e : ℝ := Real.exp (c ^ 2 * (T : ℝ) / 2)
  let R : ℕ → W → ℝ := fun r omega ↦
    e * complexFreezingDensityLeftMax M bracket T (s r) omega
  let delta : ℕ → ℝ≥0 := fun r ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹
  have hKpos : ∀ r, 0 < K r := fun r ↦ by
    dsimp only [K]
    positivity
  have hNpos : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hsadd (r : ℕ) : s r + 1 = K r := by
    dsimp only [s]
    exact Nat.sub_add_cancel (hKpos r)
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have halt : a < K a := by
      dsimp only [K]
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hAmeas : ∀ t, StronglyMeasurable (A t) := by
    intro t
    apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    · intro u
      exact (hdata.adapted_martingale u).mono (V.le u)
    · intro u
      exact (hdata.adapted_bracket u).mono (V.le u)
    · exact hCmeas
  have hAcont : ∀ omega, Continuous (fun t ↦ A t omega) := by
    exact continuous_girsanovComplexDoleansContinuousCoefficient
      hdata.continuous_martingale_path
      (fun omega ↦ (hdata.continuous_monotone_bracket omega).1)
      hCcont c
  have halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0) := by
    have hbase := commonRefinementMaxComplexStepError_tendstoInMeasure_zero
      (P := P) (A := A) hAmeas T hT hAcont n
    change TendstoInMeasure P
      ((fun k ↦ commonRefinementMaxComplexStepError A T k (n k)) ∘ s)
      atTop (fun _ ↦ 0)
    exact hbase.comp hsTop
  have halpha : ∀ r omega, 0 ≤ alpha r omega := fun r omega ↦
    commonRefinementMaxComplexStepError_nonneg A T (s r) (n (s r)) omega
  have hRnonneg : ∀ r omega, 0 ≤ R r omega := fun r omega ↦ by
    exact mul_nonneg (Real.exp_pos _).le
      (complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega)
  have hdensityTight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega} <
            eta := by
    intro eta heta
    obtain ⟨D, hD, htail⟩ :=
      hdata.complexFreezingDensityLeftMax_tight eta heta
    exact ⟨D, hD, Filter.Eventually.of_forall fun r ↦ htail (s r)⟩
  have hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta := by
    exact eventually_tight_const_mul_of_nonneg e (Real.exp_pos _).le
      (fun r omega ↦ complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega) hdensityTight
  have hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun r : ℕ ↦
        ((r + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hinv
    change Tendsto
      (NNReal.toReal ∘ fun r : ℕ ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0)
    exact hcoe
  have hdeltaPos : ∀ r, 0 < delta r := fun r ↦ by
    dsimp only [delta]
    positivity
  have hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0) := by
    simpa only [K, N, s, delta] using
      tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
        hB hsm T N hNpos
  have hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖A (uniformPartitionTime T (K r * N r) i) omega -
          A (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega := by
    intro r omega i hi j hj hactive
    have hcounts : (s r + 1) * (n (s r) + 1) = K r * N r := by
      rw [hsadd]
    have hi' : i ∈ Finset.range ((s r + 1) * (n (s r) + 1)) := by
      simpa only [hcounts] using hi
    have hle :
        ‖A (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) i) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              A (uniformPartitionTime T (s r + 1) l) omega else 0‖ ≤
          commonRefinementMaxComplexStepError A T (s r) (n (s r)) omega := by
      unfold commonRefinementMaxComplexStepError
      exact (le_refl _).trans (Finset.le_sup' (fun u ↦
        ‖A (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) u) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              A (uniformPartitionTime T (s r + 1) l) omega else 0‖) hi')
    have hj' : j ∈ Finset.range (s r + 1) := by
      simpa only [hsadd] using hj
    have hactive' : uniformPartitionTime T (s r + 1) j <
          uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
        uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
          uniformPartitionTime T (s r + 1) (j + 1) := by
      simpa only [hsadd, hcounts] using hactive
    have hsum := uniformPartition_rightEndpoint_complexStep_sum_eq
      T (uniformPartitionTime T
        ((s r + 1) * (n (s r) + 1)) (i + 1)) (s r + 1)
      hT (by positivity)
      (fun l ↦ A (uniformPartitionTime T (s r + 1) l) omega)
      hj' hactive'
    rw [hsum] at hle
    change ‖A (uniformPartitionTime T (K r * N r) i) omega -
        A (uniformPartitionTime T (K r) j) omega‖ ≤
      commonRefinementMaxComplexStepError A T (s r) (n (s r)) omega
    simpa only [hcounts, hsadd] using hle
  have hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖A (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega := by
    intro r omega j hj
    have hjle : j ≤ K r := (Finset.mem_range.mp hj).le
    have ht := (uniformPartitionTime_mem_Icc_of_le T (hKpos r) hjle).2
    have hdensity : doleansDadeExponential M bracket
          (uniformPartitionTime T (K r) j) omega ≤
        complexFreezingDensityLeftMax M bracket T (s r) omega := by
      have hj' : j ∈ Finset.range (s r + 1) := by
        simpa only [hsadd] using hj
      have hmax := Finset.le_sup' (fun u ↦
        doleansDadeExponential M bracket
          (min (uniformPartitionTime T (s r + 1) u) T) omega) hj'
      simpa only [complexFreezingDensityLeftMax, hsadd, min_eq_left ht]
        using hmax
    have hexp : Real.exp
          (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤ e := by
      apply Real.exp_le_exp.mpr
      gcongr
    rw [norm_girsanovComplexDoleansContinuousCoefficient]
    calc
      doleansDadeExponential M bracket
            (uniformPartitionTime T (K r) j) omega *
          Real.exp (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega * e :=
        mul_le_mul hdensity hexp (Real.exp_pos _).le
          (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
      _ = e * complexFreezingDensityLeftMax M bracket T (s r) omega :=
        mul_comm _ _
  apply tendstoInMeasure_complexDoleansWeightedCovariation_sub_completedBlocks
    M bracket B C X Y c T K N hT hKpos hNpos alpha R halpha hRnonneg
      halphaZero hRtight delta hdelta hdeltaPos
  · simpa only [K, N, s] using hqtight
  · exact hbad
  · exact hAclose
  · exact hAbound

set_option maxHeartbeats 4000000 in
-- The two-scale complex sums are large enough to require an expanded budget.
/-- A complex Doleans weight can be frozen on polynomial coarse grids while
the completed fine covariation blocks are simultaneously diagonalized to
their prescribed cross-variation increments.  The resulting fine weighted
covariation therefore approaches the varying coarse Riemann sum itself. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_complexDoleansWeightedCovariation_sub_crossBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y Z : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T)
    (hcross : HasCrossVariationProcessInProbability X Y Z P)
    (hXmeas : ∀ t, AEStronglyMeasurable (X t) P)
    (hYmeas : ∀ t, AEStronglyMeasurable (Y t) P)
    (hqtight : ∀ n : ℕ → ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          √(quadraticVariationApprox X T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega *
            quadraticVariationApprox Y T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega)} < eta) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r omega ↦
        let K := (r + 1) ^ 5
        let N := n (K - 1) + 1
        ( ∑ i ∈ Finset.range (K * N),
          complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T (K * N) i) omega *
            ((X (uniformPartitionTime T (K * N) (i + 1)) omega -
              X (uniformPartitionTime T (K * N) i) omega) *
            (Y (uniformPartitionTime T (K * N) (i + 1)) omega -
              Y (uniformPartitionTime T (K * N) i) omega) : ℂ)) -
        ∑ j ∈ Finset.range K,
          complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T K j) omega *
            (Z (uniformPartitionTime T K (j + 1)) omega -
              Z (uniformPartitionTime T K j) omega : ℂ))
        atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let A : ℝ≥0 → W → ℂ :=
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
  let F : ℕ → ℕ → W → ℂ := fun k n omega ↦
    ∑ j ∈ Finset.range (k + 1),
      A (uniformPartitionTime T (k + 1) j) omega *
        (quadraticCovariationBeforeStopApprox X Y T ((k + 1) * (n + 1))
              (uniformPartitionTime T (k + 1) (j + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y T ((k + 1) * (n + 1))
              (uniformPartitionTime T (k + 1) j) omega : ℂ)
  let G : ℕ → W → ℂ := fun k omega ↦
    ∑ j ∈ Finset.range (k + 1),
      A (uniformPartitionTime T (k + 1) j) omega *
        (Z (uniformPartitionTime T (k + 1) (j + 1)) omega -
          Z (uniformPartitionTime T (k + 1) j) omega : ℂ)
  have hAmeas : ∀ t, StronglyMeasurable (A t) := by
    intro t
    have hcontinuous : StronglyMeasurable
        (girsanovComplexDoleansContinuousCoefficient M bracket C c t) := by
      apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
      · intro u
        exact (hdata.adapted_martingale u).mono (V.le u)
      · intro u
        exact (hdata.adapted_bracket u).mono (V.le u)
      · exact hCmeas
    have hfourier : StronglyMeasurable (fun omega ↦
        Complex.exp (((c * B t omega : ℝ) : ℂ) * Complex.I)) := by
      exact Complex.continuous_exp.comp_stronglyMeasurable
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hsm t).const_mul c)).mul_const Complex.I)
    change StronglyMeasurable (complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t)
    convert hcontinuous.mul hfourier using 1
    exact funext fun omega ↦
      complexDoleansDadeExponential_combination_factor_continuous_brownian
        M bracket B C c t omega
  have hFG : ∀ k, TendstoInMeasure P (F k) atTop (G k) := by
    intro k
    have hraw := hcross.fullComplexStepWeight_beforeStop_common_refinement
      hXmeas hYmeas T (Nat.zero_lt_succ k)
      (fun j omega ↦ A (uniformPartitionTime T (k + 1) j) omega)
      (fun j _hj ↦ (hAmeas _).aestronglyMeasurable)
    simpa only [F, G] using hraw
  obtain ⟨n, hn, hdiag⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal_sub_normed hFG
  have hKpos : ∀ r, 0 < K r := fun r ↦ by
    dsimp only [K]
    positivity
  let s : ℕ → ℕ := fun r ↦ K r - 1
  have hsadd : ∀ r, s r + 1 = K r := fun r ↦ by
    dsimp only [s]
    exact Nat.sub_add_cancel (hKpos r)
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have halt : a < K a := by
      dsimp only [K]
      have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hdiagPoly : TendstoInMeasure P
      (fun r omega ↦ F (s r) (n (s r)) omega - G (s r) omega)
      atTop (fun _ ↦ 0) := hdiag.comp hsTop
  have hfreeze :=
    hdata.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
      hB hsm hCmeas hCcont c hT n (hqtight n)
  refine ⟨n, hn, ?_⟩
  have hsum := TendstoInMeasure.add_normed_noMeas hfreeze hdiagPoly
  apply hsum.congr
  · intro r
    exact Filter.Eventually.of_forall fun omega ↦ by
      simp only [F, G, A, K, s, hsadd]
      ring
  · exact Filter.Eventually.of_forall fun omega ↦ by simp

set_option linter.style.longLine false in
/-- Ordinary quadratic-variation contracts with an integrable terminal
control discharge the tightness premise of the complex weighted diagonal. -/
theorem GirsanovDensityData.exists_polynomial_diagonal_complexDoleansWeightedCovariation_sub_crossBlocks_of_quadraticVariations
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y Z QX QY : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T)
    (hcross : HasCrossVariationProcessInProbability X Y Z P)
    (hXmeas : ∀ t, AEStronglyMeasurable (X t) P)
    (hYmeas : ∀ t, AEStronglyMeasurable (Y t) P)
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQY : HasQuadraticVariationProcessInProbability Y QY P)
    (hQint : Integrable (fun omega ↦ QX T omega + QY T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega ↦ QX T omega + QY T omega) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r omega ↦
        let K := (r + 1) ^ 5
        let N := n (K - 1) + 1
        ( ∑ i ∈ Finset.range (K * N),
          complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T (K * N) i) omega *
            ((X (uniformPartitionTime T (K * N) (i + 1)) omega -
              X (uniformPartitionTime T (K * N) i) omega) *
            (Y (uniformPartitionTime T (K * N) (i + 1)) omega -
              Y (uniformPartitionTime T (K * N) i) omega) : ℂ)) -
        ∑ j ∈ Finset.range K,
          complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T K j) omega *
            (Z (uniformPartitionTime T K (j + 1)) omega -
              Z (uniformPartitionTime T K j) omega : ℂ))
        atTop (fun _ ↦ 0) := by
  apply
    hdata.exists_polynomial_diagonal_complexDoleansWeightedCovariation_sub_crossBlocks
      hB hsm hCmeas hCcont c hT hcross hXmeas hYmeas
  intro n
  exact hQX.polynomialBlocks_eventually_tight_sqrt_mul hQY T hQint hQnonneg
    (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity)

/-- The real part of the complex Girsanov exponential is the real density
times a deterministic Gaussian factor and the shifted cosine character. -/
theorem complexDoleansDadeExponential_combination_re
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega).re =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) *
          Real.cos (c * (B t omega - C t omega)) := by
  rw [complexDoleansDadeExponential_combination_factor, Complex.mul_re,
    Complex.exp_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, sub_zero]
  ring_nf

/-- The imaginary part of the complex Girsanov exponential is the real
density times a deterministic Gaussian factor and the shifted sine
character. -/
theorem complexDoleansDadeExponential_combination_im
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega).im =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) *
          Real.sin (c * (B t omega - C t omega)) := by
  rw [complexDoleansDadeExponential_combination_factor, Complex.mul_im,
    Complex.exp_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, sub_zero]
  ring_nf

/-- The complex Fourier exponential has the Novikov density as its random
modulus, up to the deterministic Gaussian normalization. -/
theorem norm_complexDoleansDadeExponential_combination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega‖ =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) := by
  rw [complexDoleansDadeExponential_combination_factor, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (doleansDadeExponential_pos M bracket t omega),
    Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

/-- Cap only the real Novikov-density factor of the complex Girsanov
exponential.  Its oscillatory factor is left unchanged, so the cap is
bounded without requiring path regularity of the pre-Brownian driver. -/
def cappedComplexDoleansDadeExponentialCombination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) (omega : W) : ℂ :=
  (cappedDoleansDadeExponential M bracket R t omega : ℂ) *
    Complex.exp
      (((c * (B t omega - C t omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))

/-- The capped complex Girsanov exponential has an exact deterministic
modulus bound on every finite time interval. -/
theorem norm_cappedComplexDoleansDadeExponentialCombination_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T t : ℝ≥0) (ht : t ≤ T) (omega : W) :
    ‖cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R t omega‖ ≤
        (R : ℝ) * Real.exp (c ^ 2 * (T : ℝ) / 2) := by
  unfold cappedComplexDoleansDadeExponentialCombination
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · rw [Complex.norm_exp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
      mul_one, neg_zero, zero_add]
    have hexp : Real.exp (c ^ 2 * (t : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      have ht' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg c]
    exact mul_le_mul (min_le_right _ _) hexp
      (Real.exp_pos _).le R.coe_nonneg
  · exact le_min (doleansDadeExponential_pos M bracket t omega).le
      R.coe_nonneg

/-- Density capping can only decrease the norm of the complex Girsanov
exponential. -/
theorem norm_cappedComplexDoleansDadeExponentialCombination_le_uncapped
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) (omega : W) :
    ‖cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R t omega‖ ≤
    ‖complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t omega‖ := by
  unfold cappedComplexDoleansDadeExponentialCombination
  rw [complexDoleansDadeExponential_combination_factor,
    Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg, abs_of_pos (doleansDadeExponential_pos M bracket t omega)]
  · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
  · exact le_min (doleansDadeExponential_pos M bracket t omega).le
      R.coe_nonneg

/-- Integer density caps exhaust the uncapped complex exponential at every
fixed time and sample point. -/
theorem tendsto_cappedComplexDoleansDadeExponentialCombination_nat
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    Tendsto (fun n : ℕ =>
      cappedComplexDoleansDadeExponentialCombination
        M bracket B C c n t omega) atTop
      (nhds (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega)) := by
  rw [complexDoleansDadeExponential_combination_factor]
  apply Tendsto.mul_const
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_cappedDoleansDadeExponential_nat M bracket t omega)

/-- Adapted inputs make the density-capped complex exponential adapted. -/
theorem stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R : ℝ≥0) :
    StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) := by
  intro t
  apply (Complex.continuous_ofReal.comp_stronglyMeasurable
    (stronglyAdapted_cappedDoleansDadeExponential
      hM hbracket R t)).mul
  apply Complex.continuous_exp.comp_stronglyMeasurable
  exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
    ((hB t).sub (hC t) |>.const_mul c)).mul_const Complex.I).add
      stronglyMeasurable_const)

/-- On each compact horizon the density caps are eventually inactive, so
the capped complex family agrees with the algebraic complex exponential.
No continuity assumption on `B` or `C` is needed. -/
theorem
    ae_eventually_cappedComplexDoleansDadeExponentialCombination_eq_on_Icc
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (hM : ∀ᵐ omega ∂P, Continuous (fun t => M t omega))
    (hbracket : ∀ᵐ omega ∂P, Continuous (fun t => bracket t omega)) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      cappedComplexDoleansDadeExponentialCombination
          M bracket B C c n t omega =
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c) t omega := by
  filter_upwards
    [ae_eventually_cappedDoleansDadeExponential_eq_on_Icc
      M bracket T hM hbracket] with omega homega
  filter_upwards [homega] with n hn
  intro t ht
  unfold cappedComplexDoleansDadeExponentialCombination
  rw [hn t ht,
    complexDoleansDadeExponential_combination_factor]

/-- Deterministic norm bound for the density-capped complex coefficient on
the Girsanov horizon. -/
def cappedComplexGirsanovCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  R * Real.toNNReal (Real.exp (c ^ 2 * (T : ℝ) / 2))

/-- Deterministic norm bound for the Brownian coefficient `i c H` in the
two-integrator complex Euler process. -/
def cappedComplexGirsanovBrownianCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal
    (|c| * (cappedComplexGirsanovCoefficientBound c R T : ℝ))

/-- The Euler martingale candidate for the complex Girsanov exponential.
The density factor in the coefficient is capped, while `N` is the chosen
martingale approximation to the local-martingale integrator `M`. -/
def cappedComplexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The uncapped complex Euler process on a uniform grid.  It is the exact
first-order sum whose stochastic Taylor error remains after the increasing
density caps have become inactive. -/
def complexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The canonical complex uniform-grid Doléans left sum, written directly
for a complex integrator and its algebraic complex bracket. -/
noncomputable def complexDoleansEulerProcess
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential X Q (min t U) omega
  fun t omega => H 0 omega +
    ∑ i ∈ Finset.range n,
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          H (uniformPartitionTime U n i) omega

/-- The exact one-step residual sum for the canonical complex Doléans Euler
process.  Its first two terms telescope; the third is the Euler increment. -/
noncomputable def complexDoleansEulerResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  let E := complexDoleansDadeExponential X Q
  ∑ i ∈ Finset.range n,
    ((E (min t (uniformPartitionTime U n (i + 1))) omega -
        E (min t (uniformPartitionTime U n i)) omega) -
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          E (min (uniformPartitionTime U n i) U) omega)

/-- Exact multiplicative form of one complex Doléans Euler residual.  This
isolates the analytic remainder `exp z - 1 - dX` before any probabilistic
estimate is applied. -/
theorem complexDoleansDadeExponential_increment_sub_linear
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (Complex.exp
          ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) -
            1 - (X b omega - X a omega)) := by
  unfold complexDoleansDadeExponential
  have hexp :
      Complex.exp (X b omega - Q b omega / 2) =
        Complex.exp (X a omega - Q a omega / 2) *
          Complex.exp
            ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- The higher-order remainder left after extracting the quadratic-variation
term from one complex Doléans Euler cell. -/
noncomputable def complexDoleansSecondOrderResidual
    (dX dQ : ℂ) : ℂ :=
  Complex.exp (dX - dQ / 2) - 1 - dX - (dX ^ 2 - dQ) / 2

/-- Quantitative higher-order bound for the extracted complex Doléans
remainder.  The first term is cubic in the compensated-log increment; the
second records the finite-variation correction caused by replacing that
increment's square with `dX²`. -/
theorem norm_complexDoleansSecondOrderResidual_le (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        ‖((dX - dQ / 2) ^ 2 - dX ^ 2) / 2‖ := by
  let z : ℂ := dX - dQ / 2
  have hexp :
      ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤
        ‖z‖ ^ 3 * Real.exp ‖z‖ := by
    convert Complex.norm_exp_sub_sum_le_norm_mul_exp z 3 using 1
    congr 1
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  calc
    ‖complexDoleansSecondOrderResidual dX dQ‖ =
        ‖(Complex.exp z - 1 - z - z ^ 2 / 2) +
          (z ^ 2 - dX ^ 2) / 2‖ := by
      congr 1
      unfold complexDoleansSecondOrderResidual z
      ring
    _ ≤ ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := add_le_add hexp le_rfl
    _ = _ := by rfl

/-- A cancellation-ready version of the one-cell remainder bound.  The
correction to the cubic term contains an explicit bracket increment, rather
than an opaque difference of squares. -/
theorem norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket
    (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2 := by
  let z : ℂ := dX - dQ / 2
  have hfactor : z ^ 2 - dX ^ 2 = (-dQ / 2) * (z + dX) := by
    dsimp only [z]
    ring
  apply (norm_complexDoleansSecondOrderResidual_le dX dQ).trans
  gcongr
  rw [hfactor]
  simp only [norm_div, norm_mul, norm_neg]
  have hnormtwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnormtwo]
  calc
    ‖dQ‖ / 2 * ‖z + dX‖ / 2 ≤
        ‖dQ‖ / 2 * (‖z‖ + ‖dX‖) / 2 := by
      gcongr
      exact norm_add_le z dX
    _ = _ := by rfl

/-- The nonnegative scalar majorant for one higher-order Doléans cell. -/
noncomputable def complexDoleansSecondOrderResidualBound
    (dX dQ : ℂ) : ℝ :=
  ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
    (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2

theorem complexDoleansSecondOrderResidualBound_nonneg (dX dQ : ℂ) :
    0 ≤ complexDoleansSecondOrderResidualBound dX dQ := by
  unfold complexDoleansSecondOrderResidualBound
  positivity

/-- The one-cell higher-order remainder is controlled by its explicit
nonnegative scalar majorant. -/
theorem norm_complexDoleansSecondOrderResidual_le_bound (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      complexDoleansSecondOrderResidualBound dX dQ := by
  exact norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket dX dQ

/-- One Doléans Euler cell splits exactly into a weighted bracket discrepancy
and the higher-order exponential remainder. -/
theorem complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (((X b omega - X a omega) ^ 2 -
              (Q b omega - Q a omega)) / 2 +
          complexDoleansSecondOrderResidual
            (X b omega - X a omega) (Q b omega - Q a omega)) := by
  rw [complexDoleansDadeExponential_increment_sub_linear]
  unfold complexDoleansSecondOrderResidual
  ring

/-- At the partition horizon, the canonical residual is the sum of the
explicit multiplicative one-step exponential remainders. -/
theorem complexDoleansEulerResidualApprox_terminal
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexDoleansEulerResidualApprox X Q U (n + 1) U omega =
      ∑ i ∈ Finset.range (n + 1),
        complexDoleansDadeExponential X Q
            (uniformPartitionTime U (n + 1) i) omega *
          (Complex.exp
              ((X (uniformPartitionTime U (n + 1) (i + 1)) omega -
                  X (uniformPartitionTime U (n + 1) i) omega) -
                (Q (uniformPartitionTime U (n + 1) (i + 1)) omega -
                  Q (uniformPartitionTime U (n + 1) i) omega) / 2) -
            1 -
              (X (uniformPartitionTime U (n + 1) (i + 1)) omega -
                X (uniformPartitionTime U (n + 1) i) omega)) := by
  unfold complexDoleansEulerResidualApprox
  simp only
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 :=
    (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n + 1 := by
    exact Finset.mem_range.mp hi
  have hleft := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi0).2
  have hright := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi1).2
  rw [min_eq_right hleft, min_eq_right hright, min_eq_left hleft]
  exact complexDoleansDadeExponential_increment_sub_linear X Q
    (uniformPartitionTime U (n + 1) i)
    (uniformPartitionTime U (n + 1) (i + 1)) omega

/-- Terminal Euler residuals split into the weighted complex bracket error
and a sum of genuinely higher-order one-cell remainders. -/
theorem complexDoleansEulerResidualApprox_terminal_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexDoleansEulerResidualApprox X Q U (n + 1) U omega =
      (1 / 2 : ℂ) * ∑ i ∈ Finset.range (n + 1),
        complexDoleansDadeExponential X Q
            (uniformPartitionTime U (n + 1) i) omega *
          ((X (uniformPartitionTime U (n + 1) (i + 1)) omega -
              X (uniformPartitionTime U (n + 1) i) omega) ^ 2 -
            (Q (uniformPartitionTime U (n + 1) (i + 1)) omega -
              Q (uniformPartitionTime U (n + 1) i) omega)) +
      ∑ i ∈ Finset.range (n + 1),
        complexDoleansDadeExponential X Q
            (uniformPartitionTime U (n + 1) i) omega *
          complexDoleansSecondOrderResidual
            (X (uniformPartitionTime U (n + 1) (i + 1)) omega -
              X (uniformPartitionTime U (n + 1) i) omega)
            (Q (uniformPartitionTime U (n + 1) (i + 1)) omega -
              Q (uniformPartitionTime U (n + 1) i) omega) := by
  unfold complexDoleansEulerResidualApprox
  simp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hleft := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi0).2
  have hright := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi1).2
  rw [min_eq_right hleft, min_eq_right hright, min_eq_left hleft]
  rw [complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder]
  ring

/-- The stopped-grid weighted discrepancy between algebraic squared
increments and increments of the proposed complex bracket. -/
noncomputable def complexDoleansWeightedBracketResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      ((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) ^ 2 -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega))

/-- A complex-weighted real quadratic-variation discrepancy on a stopped
uniform grid.  The complex weight is kept explicit because the Fourier
Doléans exponential is not real-valued. -/
noncomputable def complexWeightedQuadraticResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      (((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ) ^ 2 -
        ((A (min t (uniformPartitionTime U n (i + 1))) omega -
          A (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- A complex-weighted real cross-variation discrepancy on a stopped uniform
grid. -/
noncomputable def complexWeightedCrossResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ)
    (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      ((((X (min t (uniformPartitionTime U n (i + 1))) omega -
            X (min t (uniformPartitionTime U n i)) omega) *
          (Y (min t (uniformPartitionTime U n (i + 1))) omega -
            Y (min t (uniformPartitionTime U n i)) omega) : ℝ) : ℂ) -
        ((C (min t (uniformPartitionTime U n (i + 1))) omega -
          C (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- The real-valued stopped-grid quadratic residual underlying
`complexWeightedQuadraticResidualApprox`. -/
noncomputable def stoppedWeightedQuadraticResidualApprox
    {W : Type*} (H X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      ((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) ^ 2 -
        (A (min t (uniformPartitionTime U n (i + 1))) omega -
          A (min t (uniformPartitionTime U n i)) omega))

/-- The real-valued stopped-grid cross residual underlying
`complexWeightedCrossResidualApprox`. -/
noncomputable def stoppedWeightedCrossResidualApprox
    {W : Type*} (H X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      ((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) *
        (Y (min t (uniformPartitionTime U n (i + 1))) omega -
          Y (min t (uniformPartitionTime U n i)) omega) -
        (C (min t (uniformPartitionTime U n (i + 1))) omega -
          C (min t (uniformPartitionTime U n i)) omega))

/-- A left-point Riemann--Stieltjes sum on a uniform grid. -/
noncomputable def weightedFiniteVariationApprox
    {W : Type*} (H A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    H (uniformPartitionTime U n i) omega *
      (A (uniformPartitionTime U n (i + 1)) omega -
        A (uniformPartitionTime U n i) omega)

/-- The prefix sum of finite-variation increments on a fixed uniform grid.
Unlike quadratic variation, this quantity telescopes exactly. -/
noncomputable def finiteVariationBeforeStopApprox
    {W : Type*} (A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (A (min t (uniformPartitionTime U n (i + 1))) omega -
      A (min t (uniformPartitionTime U n i)) omega)

/-- Finite-variation prefix sums telescope to the stopped endpoint. -/
theorem finiteVariationBeforeStopApprox_eq_sub
    {W : Type*} (A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) {n : ℕ} (hn : 0 < n) (t : ℝ≥0) (omega : W) :
    finiteVariationBeforeStopApprox A U n t omega =
      A (min t U) omega - A 0 omega := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have htop : uniformPartitionTime U n n = U := by
    unfold uniformPartitionTime
    exact mul_div_cancel_right₀ U hn0
  have hzero : uniformPartitionTime U n 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  have hminzero : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
  simpa only [finiteVariationBeforeStopApprox, htop, hzero, hminzero] using
      (Finset.sum_range_sub (fun i ↦
        A (min t (uniformPartitionTime U n i)) omega) n)

/-- A sum over a uniformly subdivided grid can be indexed by its coarse
block and its position inside that block. -/
theorem sum_range_mul_eq_sum_range_sum_range
    {E : Type*} [AddCommMonoid E] (k n : ℕ) (f : ℕ → E) :
    (∑ i ∈ Finset.range (k * n), f i) =
      ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
  calc
    _ = ∑ i : Fin (k * n), f i :=
      (Fin.sum_univ_eq_sum_range f (k * n)).symm
    _ = ∑ p : Fin k × Fin n, f (finProdFinEquiv p) :=
      (Equiv.sum_comp finProdFinEquiv
        (fun i : Fin (k * n) ↦ f i)).symm
    _ = ∑ j : Fin k, ∑ r : Fin n, f (r + n * j) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ j ∈ Finset.range k, ∑ r : Fin n,
        f (r + n * j) := by
      exact Fin.sum_univ_eq_sum_range
        (fun j ↦ ∑ r : Fin n, f (r + n * j)) k
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Fin.sum_univ_eq_sum_range (fun r ↦ f (r + n * j)) n

/-- Frozen complex coarse weights against exact finite-variation increments
are the active right-endpoint step weights against all fine increments. -/
theorem finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (A (uniformPartitionTime U k (j + 1)) omega -
        A (uniformPartitionTime U k j) omega : ℂ)) =
      ∑ i ∈ Finset.range (k * n), c (i / n) omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ) := by
  have hblock (j : ℕ) :
      (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ) =
        ∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
    have hleft : uniformPartitionTime U (k * n) (n * j) =
        uniformPartitionTime U k j := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn j 0).symm
    have hright : uniformPartitionTime U (k * n) (n * (j + 1)) =
        uniformPartitionTime U k (j + 1) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn (j + 1) 0).symm
    have htel := Finset.sum_range_sub (fun r ↦
      (A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) n
    have hindex : n + n * j = n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simp only [zero_add] at htel
    rw [hindex, hright, hleft] at htel
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htel.symm
  calc
    _ = ∑ j ∈ Finset.range k, c j omega *
        (∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hblock]
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        c j omega *
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [sum_range_mul_eq_sum_range_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < n := Finset.mem_range.mp hr
      rw [Nat.add_mul_div_left r j hn, Nat.div_eq_of_lt hrlt,
        zero_add]

/-- Freezing complex weights on completed coarse blocks costs at most the
weight error times the total variation of the real integrator. -/
theorem norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (weight c : ℕ → W → ℂ)
    (K : ℝ) (_hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range (k * n),
      ‖weight i omega - c (i / n) omega‖ ≤ K) :
    ‖(∑ i ∈ Finset.range (k * n), weight i omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ)‖ ≤
      K * totalVariationApprox A U (k * n) omega := by
  rw [finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    A U hk hn c omega, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range (k * n),
        (weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range (k * n),
        ‖(weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k * n), K *
        |A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      rw [show
        ((A (uniformPartitionTime U (k * n) (i + 1)) omega : ℂ) -
            (A (uniformPartitionTime U (k * n) i) omega : ℂ)) =
          ((A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℝ) : ℂ) by
            push_cast
            rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _)
    _ = K * totalVariationApprox A U (k * n) omega := by
      unfold totalVariationApprox
      rw [Finset.mul_sum]

/-- Outside the Brownian block-oscillation event, freezing the complex
Girsanov weight in a finite-variation sum costs its total variation times
the same coefficient-and-Fourier modulus used for covariations. -/
theorem
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
    {W : Type*} [MeasurableSpace W]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    {k n : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (alpha R : ℝ) (halpha : 0 ≤ alpha) (hR : 0 ≤ R)
    (delta : ℝ≥0) (hdelta : 0 < delta) {omega : W}
    (hAclose : ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
      uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T (k * n) i) omega -
        girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ∀ j ∈ Finset.range k,
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T k j) omega‖ ≤ R)
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r ↦
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ‖(∑ i ∈ Finset.range (k * n),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega *
          (A (uniformPartitionTime T (k * n) (i + 1)) omega -
            A (uniformPartitionTime T (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k j) omega *
          (A (uniformPartitionTime T k (j + 1)) omega -
            A (uniformPartitionTime T k j) omega : ℂ)‖ ≤
      (alpha + R * |c| * (delta : ℝ)) *
        totalVariationApprox A T (k * n) omega := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by
      exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hweight : ∀ i ∈ Finset.range (k * n),
      ‖complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega -
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k (i / n)) omega‖ ≤
        alpha + R * |c| * (delta : ℝ) := by
    intro i hi
    let j := i / n
    have hilt : i < k * n := Finset.mem_range.mp hi
    have hjlt : j < k := by
      exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hilt)
    have hj : j ∈ Finset.range k := Finset.mem_range.mpr hjlt
    have hleft : uniformPartitionTime T k j =
        uniformPartitionTime T (k * n) (n * j) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn j 0
    have hright : uniformPartitionTime T k (j + 1) =
        uniformPartitionTime T (k * n) (n * (j + 1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    have hjmul : n * j ≤ i := by
      simpa only [j, Nat.mul_comm] using Nat.div_mul_le_self i n
    have hmod : i % n < n := Nat.mod_lt i hn
    have hdecomp : n * j + i % n = i := by
      exact Nat.div_add_mod i n
    have hiRight : i + 1 ≤ n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hactive : uniformPartitionTime T k j <
          uniformPartitionTime T (k * n) (i + 1) ∧
        uniformPartitionTime T (k * n) (i + 1) ≤
          uniformPartitionTime T k (j + 1) := by
      rw [hleft, hright]
      exact ⟨hstrict (by omega), hstrict.monotone hiRight⟩
    obtain ⟨r, hr, htime⟩ :=
      uniformPartitionTime_active_block_common_refinement
        T hT hk hn hactive
    have hBclose := hosc j hj r hr
    rw [← htime] at hBclose
    rw [complexDoleansDadeExponential_combination_factor_continuous_brownian,
      complexDoleansDadeExponential_combination_factor_continuous_brownian]
    have hraw := norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
      (girsanovComplexDoleansContinuousCoefficient M bracket C c) B
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (lipschitzWith_complexFourierCharacter c) T omega alpha R 1
      (delta : ℝ) (hAclose i hi j hj hactive) (hAbound j hj)
      (by rw [Complex.norm_exp_ofReal_mul_I]) hBclose
    simpa only [j, mul_one,
      Real.coe_toNNReal |c| (abs_nonneg c)] using hraw
  exact norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    A T hk hn
      (fun i omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (k * n) i) omega)
      (fun j omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T k j) omega)
      (alpha + R * |c| * (delta : ℝ))
      (add_nonneg halpha (mul_nonneg (mul_nonneg hR (abs_nonneg c))
        delta.coe_nonneg)) omega hweight

/-- The pathwise complex finite-variation freezing estimate promotes to
convergence in measure when the variation controls are tight and the
Brownian block-oscillation event becomes rare. -/
theorem
    tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (K N : ℕ → ℕ) (hT : 0 < T) (hK : ∀ r, 0 < K r)
    (hN : ∀ r, 0 < N r)
    (alpha R : ℕ → W → ℝ) (halpha : ∀ r omega, 0 ≤ alpha r omega)
    (hR : ∀ r omega, 0 ≤ R r omega)
    (halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0))
    (hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta)
    (delta : ℕ → ℝ≥0)
    (hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0))
    (hdeltaPos : ∀ r, 0 < delta r)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          totalVariationApprox A T (K r * N r) omega} < eta)
    (hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0))
    (hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r * N r) i) omega -
          girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega)
    (hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega) :
    TendstoInMeasure P (fun r omega ↦
      (∑ i ∈ Finset.range (K r * N r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r * N r) i) omega *
          (A (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            A (uniformPartitionTime T (K r * N r) i) omega : ℂ)) -
      ∑ j ∈ Finset.range (K r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r) j) omega *
          (A (uniformPartitionTime T (K r) (j + 1)) omega -
            A (uniformPartitionTime T (K r) j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun r omega ↦
    totalVariationApprox A T (K r * N r) omega
  let small : ℕ → W → ℝ := fun r _ ↦ |c| * (delta r : ℝ)
  let rq : ℕ → W → ℝ := fun r omega ↦ R r omega * q r omega
  let b₁ : ℕ → W → ℝ := fun r omega ↦ alpha r omega * q r omega
  let b₂ : ℕ → W → ℝ := fun r omega ↦ small r omega * rq r omega
  let b : ℕ → W → ℝ := fun r omega ↦ b₁ r omega + b₂ r omega
  have hq_nonneg : ∀ r omega, 0 ≤ q r omega := fun r omega ↦ by
    dsimp only [q, totalVariationApprox]
    exact Finset.sum_nonneg fun _ _hi ↦ abs_nonneg _
  have hq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ q r omega} < eta := by
    simpa only [q] using htvtight
  have hb₁ : TendstoInMeasure P b₁ atTop (fun _ ↦ 0) := by
    apply halphaZero.of_norm_sub_le_mul_of_eventually_tight
      hq_nonneg hq_tight
    intro r omega
    simp only [b₁, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (halpha r omega), q]
    rw [abs_of_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))]
  have hrq_nonneg : ∀ r omega, 0 ≤ rq r omega := fun r omega ↦
    mul_nonneg (hR r omega) (hq_nonneg r omega)
  have hrq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ rq r omega} < eta := by
    exact eventually_tight_mul_of_nonneg hR hq_nonneg hRtight hq_tight
  have hsmall : TendstoInMeasure P small atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro r
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ ↦ by
        simpa only [small, mul_zero] using
          hdelta.const_mul |c|
  have hsmall_nonneg : ∀ r omega, 0 ≤ small r omega := fun r omega ↦
    mul_nonneg (abs_nonneg c) (delta r).coe_nonneg
  have hb₂ : TendstoInMeasure P b₂ atTop (fun _ ↦ 0) := by
    apply hsmall.of_norm_sub_le_mul_of_eventually_tight
      hrq_nonneg hrq_tight
    intro r omega
    simp only [b₂, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hsmall_nonneg r omega)]
    rw [abs_of_nonneg
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))]
  have hbZero : TendstoInMeasure P b atTop (fun _ ↦ 0) := by
    simpa only [b, zero_add] using hb₁.add_real_noMeas hb₂
  let bad : ℕ → Set W := fun r ↦
    ⋃ j ∈ Finset.range (K r), {omega |
      ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
        Finset.nonempty_range_add_one (fun u ↦
          (B (uniformPartitionTime T (K r) j +
              uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
            B (uniformPartitionTime T (K r) j) omega) ^ 4)}
  have hbadZero : Tendsto (fun r ↦ P.real (bad r)) atTop (nhds 0) := by
    simpa only [bad] using hbad
  have hb_nonneg : ∀ r omega, 0 ≤ b r omega := fun r omega ↦
    add_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))
  apply hbZero.of_norm_le_nonneg_outside_noMeas hb_nonneg hbadZero
  intro r omega homega
  have hraw :=
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
      M bracket B C A c T hT (hK r) (hN r)
      (alpha r omega) (R r omega) (halpha r omega) (hR r omega)
      (delta r) (hdeltaPos r) (hAclose r omega) (hAbound r omega) homega
  calc
    _ ≤ (alpha r omega + R r omega * |c| * (delta r : ℝ)) *
        q r omega := by simpa only [q] using hraw
    _ = b r omega := by
      dsimp only [b, b₁, b₂, small, rq]
      ring

/-- Girsanov density data supplies all coefficient and Brownian controls for
finite-variation freezing on the polynomial common-refinement scale. -/
theorem
    GirsanovDensityData.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C A : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox A T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    TendstoInMeasure P (fun r omega ↦
      let K := (r + 1) ^ 5
      let N := n (K - 1) + 1
      (∑ i ∈ Finset.range (K * N),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K * N) i) omega *
          (A (uniformPartitionTime T (K * N) (i + 1)) omega -
            A (uniformPartitionTime T (K * N) i) omega : ℂ)) -
      ∑ j ∈ Finset.range K,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T K j) omega *
          (A (uniformPartitionTime T K (j + 1)) omega -
            A (uniformPartitionTime T K j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let s : ℕ → ℕ := fun r ↦ K r - 1
  let N : ℕ → ℕ := fun r ↦ n (s r) + 1
  let H : ℝ≥0 → W → ℂ :=
    girsanovComplexDoleansContinuousCoefficient M bracket C c
  let alpha : ℕ → W → ℝ := fun r ↦
    commonRefinementMaxComplexStepError H T (s r) (n (s r))
  let e : ℝ := Real.exp (c ^ 2 * (T : ℝ) / 2)
  let R : ℕ → W → ℝ := fun r omega ↦
    e * complexFreezingDensityLeftMax M bracket T (s r) omega
  let delta : ℕ → ℝ≥0 := fun r ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹
  have hKpos : ∀ r, 0 < K r := fun r ↦ by
    dsimp only [K]
    positivity
  have hNpos : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hsadd (r : ℕ) : s r + 1 = K r := by
    dsimp only [s]
    exact Nat.sub_add_cancel (hKpos r)
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have halt : a < K a := by
      dsimp only [K]
      have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hHmeas : ∀ t, StronglyMeasurable (H t) := by
    intro t
    apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    · intro u
      exact (hdata.adapted_martingale u).mono (V.le u)
    · intro u
      exact (hdata.adapted_bracket u).mono (V.le u)
    · exact hCmeas
  have hHcont : ∀ omega, Continuous (fun t ↦ H t omega) := by
    exact continuous_girsanovComplexDoleansContinuousCoefficient
      hdata.continuous_martingale_path
      (fun omega ↦ (hdata.continuous_monotone_bracket omega).1)
      hCcont c
  have halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0) := by
    have hbase := commonRefinementMaxComplexStepError_tendstoInMeasure_zero
      (P := P) (A := H) hHmeas T hT hHcont n
    change TendstoInMeasure P
      ((fun k ↦ commonRefinementMaxComplexStepError H T k (n k)) ∘ s)
      atTop (fun _ ↦ 0)
    exact hbase.comp hsTop
  have halpha : ∀ r omega, 0 ≤ alpha r omega := fun r omega ↦
    commonRefinementMaxComplexStepError_nonneg H T (s r) (n (s r)) omega
  have hRnonneg : ∀ r omega, 0 ≤ R r omega := fun r omega ↦ by
    exact mul_nonneg (Real.exp_pos _).le
      (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
  have hdensityTight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega} < eta := by
    intro eta heta
    obtain ⟨D, hD, htail⟩ :=
      hdata.complexFreezingDensityLeftMax_tight eta heta
    exact ⟨D, hD, Filter.Eventually.of_forall fun r ↦ htail (s r)⟩
  have hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta := by
    exact eventually_tight_const_mul_of_nonneg e (Real.exp_pos _).le
      (fun r omega ↦ complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega) hdensityTight
  have hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun r : ℕ ↦
        ((r + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hinv
    change Tendsto
      (NNReal.toReal ∘ fun r : ℕ ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0)
    exact hcoe
  have hdeltaPos : ∀ r, 0 < delta r := fun r ↦ by
    dsimp only [delta]
    positivity
  have hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0) := by
    simpa only [K, N, s, delta] using
      tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
        hB hsm T N hNpos
  have hHclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖H (uniformPartitionTime T (K r * N r) i) omega -
          H (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega := by
    intro r omega i hi j hj hactive
    have hcounts : (s r + 1) * (n (s r) + 1) = K r * N r := by
      rw [hsadd]
    have hi' : i ∈ Finset.range ((s r + 1) * (n (s r) + 1)) := by
      simpa only [hcounts] using hi
    have hle :
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) i) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖ ≤
          commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega := by
      unfold commonRefinementMaxComplexStepError
      exact (le_refl _).trans (Finset.le_sup' (fun u ↦
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) u) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖) hi')
    have hj' : j ∈ Finset.range (s r + 1) := by
      simpa only [hsadd] using hj
    have hactive' : uniformPartitionTime T (s r + 1) j <
          uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
        uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
          uniformPartitionTime T (s r + 1) (j + 1) := by
      simpa only [hsadd, hcounts] using hactive
    have hsum := uniformPartition_rightEndpoint_complexStep_sum_eq
      T (uniformPartitionTime T
        ((s r + 1) * (n (s r) + 1)) (i + 1)) (s r + 1)
      hT (by positivity)
      (fun l ↦ H (uniformPartitionTime T (s r + 1) l) omega)
      hj' hactive'
    rw [hsum] at hle
    change ‖H (uniformPartitionTime T (K r * N r) i) omega -
        H (uniformPartitionTime T (K r) j) omega‖ ≤
      commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega
    simpa only [hcounts, hsadd] using hle
  have hHbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖H (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega := by
    intro r omega j hj
    have hjle : j ≤ K r := (Finset.mem_range.mp hj).le
    have ht := (uniformPartitionTime_mem_Icc_of_le T (hKpos r) hjle).2
    have hdensity : doleansDadeExponential M bracket
          (uniformPartitionTime T (K r) j) omega ≤
        complexFreezingDensityLeftMax M bracket T (s r) omega := by
      have hj' : j ∈ Finset.range (s r + 1) := by
        simpa only [hsadd] using hj
      have hmax := Finset.le_sup' (fun u ↦
        doleansDadeExponential M bracket
          (min (uniformPartitionTime T (s r + 1) u) T) omega) hj'
      simpa only [complexFreezingDensityLeftMax, hsadd, min_eq_left ht]
        using hmax
    have hexp : Real.exp
          (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤ e := by
      apply Real.exp_le_exp.mpr
      gcongr
    rw [norm_girsanovComplexDoleansContinuousCoefficient]
    calc
      doleansDadeExponential M bracket
            (uniformPartitionTime T (K r) j) omega *
          Real.exp (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega * e :=
        mul_le_mul hdensity hexp (Real.exp_pos _).le
          (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
      _ = e * complexFreezingDensityLeftMax M bracket T (s r) omega :=
        mul_comm _ _
  apply tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    M bracket B C A c T K N hT hKpos hNpos alpha R halpha hRnonneg
      halphaZero hRtight delta hdelta hdeltaPos
  · simpa only [K, N, s] using htvtight
  · exact hbad
  · exact hHclose
  · exact hHbound

/-- At the grid horizon the stopped quadratic residual is the ordinary
weighted quadratic sum minus its proposed weighted bracket sum. -/
theorem stoppedWeightedQuadraticResidualApprox_terminal
    {W : Type*} (H X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    stoppedWeightedQuadraticResidualApprox H X A U n U omega =
      weightedQuadraticVariationApprox H X U n omega -
        weightedFiniteVariationApprox H A U n omega := by
  unfold stoppedWeightedQuadraticResidualApprox
    weightedQuadraticVariationApprox weightedFiniteVariationApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi0).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi1).2]
  ring

/-- At the grid horizon the stopped cross residual is the ordinary weighted
cross sum minus its proposed weighted cross-bracket sum. -/
theorem stoppedWeightedCrossResidualApprox_terminal
    {W : Type*} (H X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    stoppedWeightedCrossResidualApprox H X Y C U n U omega =
      weightedQuadraticCovariationApprox H X Y U n omega -
        weightedFiniteVariationApprox H C U n omega := by
  unfold stoppedWeightedCrossResidualApprox
    weightedQuadraticCovariationApprox weightedFiniteVariationApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi0).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi1).2]
  ring

/-- At the grid horizon a complex-weighted stopped cross residual is the
difference between the ordinary complex-weighted cross and finite-variation
sums. -/
theorem complexWeightedCrossResidualApprox_terminal
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexWeightedCrossResidualApprox H X Y C U n U omega =
      (∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          ((X (uniformPartitionTime U n (i + 1)) omega -
            X (uniformPartitionTime U n i) omega) *
          (Y (uniformPartitionTime U n (i + 1)) omega -
            Y (uniformPartitionTime U n i) omega) : ℂ)) -
      ∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          (C (uniformPartitionTime U n (i + 1)) omega -
            C (uniformPartitionTime U n i) omega : ℂ) := by
  unfold complexWeightedCrossResidualApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi0).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi1).2]
  push_cast
  ring

/-- A complex-weighted quadratic residual is the self-cross residual. -/
theorem complexWeightedQuadraticResidualApprox_eq_cross_self
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexWeightedQuadraticResidualApprox H X A U n t omega =
      complexWeightedCrossResidualApprox H X X A U n t omega := by
  unfold complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  apply Finset.sum_congr rfl
  intro i _hi
  push_cast
  rw [pow_two]

/-- The fine complex-Doleans-weighted covariation minus its polynomial
coarse cross-variation sum. -/
noncomputable def polynomialComplexDoleansWeightedCovariationResidual
    {W : Type*} (M bracket B C X Y Z : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (n : ℕ → ℕ) (r : ℕ) (omega : W) : ℂ :=
  let K := (r + 1) ^ 5
  let N := n (K - 1) + 1
  (∑ i ∈ Finset.range (K * N),
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (K * N) i) omega *
      ((X (uniformPartitionTime T (K * N) (i + 1)) omega -
        X (uniformPartitionTime T (K * N) i) omega) *
      (Y (uniformPartitionTime T (K * N) (i + 1)) omega -
        Y (uniformPartitionTime T (K * N) i) omega) : ℂ)) -
  ∑ j ∈ Finset.range K,
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T K j) omega *
      (Z (uniformPartitionTime T K (j + 1)) omega -
        Z (uniformPartitionTime T K j) omega : ℂ)

/-- The fine complex-Doleans-weighted finite-variation sum minus the same
polynomial coarse Riemann sum. -/
noncomputable def polynomialComplexDoleansWeightedFiniteVariationResidual
    {W : Type*} (M bracket B C A : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (n : ℕ → ℕ) (r : ℕ) (omega : W) : ℂ :=
  let K := (r + 1) ^ 5
  let N := n (K - 1) + 1
  (∑ i ∈ Finset.range (K * N),
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (K * N) i) omega *
      (A (uniformPartitionTime T (K * N) (i + 1)) omega -
        A (uniformPartitionTime T (K * N) i) omega : ℂ)) -
  ∑ j ∈ Finset.range K,
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T K j) omega *
      (A (uniformPartitionTime T K (j + 1)) omega -
        A (uniformPartitionTime T K j) omega : ℂ)

/-- At the terminal horizon the polynomial weighted cross residual is the
difference of the matching covariation and finite-variation residuals. -/
theorem polynomialComplexDoleansWeightedCrossResidual_eq_sub
    {W : Type*} (M bracket B C X Y Z : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (n : ℕ → ℕ) (r : ℕ) (omega : W) :
    complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        X Y Z T (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T omega =
      polynomialComplexDoleansWeightedCovariationResidual
          M bracket B C X Y Z c T n r omega -
        polynomialComplexDoleansWeightedFiniteVariationResidual
          M bracket B C Z c T n r omega := by
  rw [complexWeightedCrossResidualApprox_terminal]
  unfold polynomialComplexDoleansWeightedCovariationResidual
    polynomialComplexDoleansWeightedFiniteVariationResidual
  rw [sub_sub_sub_cancel_right]

set_option maxHeartbeats 2000000 in
-- Three expanded two-scale sums are synchronized in one elaboration.
/-- The martingale, Brownian, and mixed Doleans-weighted covariations share
one polynomial diagonal approaching their respective coarse bracket sums. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_three_complexWeightedCovariations
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (c : ℝ) (hT : 0 < T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r omega ↦
        polynomialComplexDoleansWeightedCovariationResidual
          M bracket B C M M bracket c T n r omega) atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun r omega ↦
        polynomialComplexDoleansWeightedCovariationResidual
          M bracket B C B B (fun t _omega ↦ (t : ℝ)) c T n r omega)
        atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun r omega ↦
        polynomialComplexDoleansWeightedCovariationResidual
          M bracket B C M B C c T n r omega) atTop (fun _ ↦ 0) := by
  let H : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let F₁ : ℕ → ℕ → W → ℂ := fun k n omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      (quadraticCovariationBeforeStopApprox M M T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) (j + 1)) omega -
        quadraticCovariationBeforeStopApprox M M T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) j) omega : ℂ)
  let F₂ : ℕ → ℕ → W → ℂ := fun k n omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      (quadraticCovariationBeforeStopApprox B B T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) (j + 1)) omega -
        quadraticCovariationBeforeStopApprox B B T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) j) omega : ℂ)
  let F₃ : ℕ → ℕ → W → ℂ := fun k n omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      (quadraticCovariationBeforeStopApprox M B T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) (j + 1)) omega -
        quadraticCovariationBeforeStopApprox M B T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) j) omega : ℂ)
  let G₁ : ℕ → W → ℂ := fun k omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      (bracket (uniformPartitionTime T (k + 1) (j + 1)) omega -
        bracket (uniformPartitionTime T (k + 1) j) omega : ℂ)
  let G₂ : ℕ → W → ℂ := fun k omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      ((uniformPartitionTime T (k + 1) (j + 1) : ℝ) -
        (uniformPartitionTime T (k + 1) j : ℝ) : ℂ)
  let G₃ : ℕ → W → ℂ := fun k omega ↦
    ∑ j ∈ Finset.range (k + 1), H (uniformPartitionTime T (k + 1) j) omega *
      (C (uniformPartitionTime T (k + 1) (j + 1)) omega -
        C (uniformPartitionTime T (k + 1) j) omega : ℂ)
  have hHmeas : ∀ t, StronglyMeasurable (H t) := by
    intro t
    have hbase := stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
      (fun u ↦ (hdata.adapted_martingale u).mono (V.le u))
      (fun u ↦ (hdata.adapted_bracket u).mono (V.le u)) hCmeas c t
    have hfourier : StronglyMeasurable (fun omega ↦
        Complex.exp (((c * B t omega : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp_stronglyMeasurable
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hsm t).const_mul c)).mul_const Complex.I)
    change StronglyMeasurable (complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t)
    convert hbase.mul hfourier using 1
    exact funext fun omega ↦
      complexDoleansDadeExponential_combination_factor_continuous_brownian
        M bracket B C c t omega
  have hMmeas : ∀ t, AEStronglyMeasurable (M t) P := fun t ↦
    ((hdata.adapted_martingale t).mono (V.le t)).aestronglyMeasurable
  have hBmeas : ∀ t, AEStronglyMeasurable (B t) P := fun t ↦
    (hsm t).aestronglyMeasurable
  have hQB : HasQuadraticVariationProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) P := fun t ↦
    quadraticVariation_preBrownianReal_inProbability hB t
  have hFG₁ : ∀ k, TendstoInMeasure P (F₁ k) atTop (G₁ k) := by
    intro k
    simpa only [F₁, G₁] using
      hdata.localQuadraticVariation.toProcess.toCrossVariationSelf
        |>.fullComplexStepWeight_beforeStop_common_refinement
          hMmeas hMmeas T (Nat.zero_lt_succ k)
          (fun j omega ↦ H (uniformPartitionTime T (k + 1) j) omega)
          (fun j _hj ↦ (hHmeas _).aestronglyMeasurable)
  have hFG₂ : ∀ k, TendstoInMeasure P (F₂ k) atTop (G₂ k) := by
    intro k
    simpa only [F₂, G₂] using
      hQB.toCrossVariationSelf
        |>.fullComplexStepWeight_beforeStop_common_refinement
          hBmeas hBmeas T (Nat.zero_lt_succ k)
          (fun j omega ↦ H (uniformPartitionTime T (k + 1) j) omega)
          (fun j _hj ↦ (hHmeas _).aestronglyMeasurable)
  have hFG₃ : ∀ k, TendstoInMeasure P (F₃ k) atTop (G₃ k) := by
    intro k
    simpa only [F₃, G₃] using
      hcross.fullComplexStepWeight_beforeStop_common_refinement
        hMmeas hBmeas T (Nat.zero_lt_succ k)
        (fun j omega ↦ H (uniformPartitionTime T (k + 1) j) omega)
        (fun j _hj ↦ (hHmeas _).aestronglyMeasurable)
  obtain ⟨n, hn, hdiag₁, hdiag₂, hdiag₃⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal_sub_three_normed
      hFG₁ hFG₂ hFG₃
  let s : ℕ → ℕ := fun r ↦ (r + 1) ^ 5 - 1
  have hsadd : ∀ r, s r + 1 = (r + 1) ^ 5 := fun r ↦ by
    dsimp only [s]
    apply Nat.sub_add_cancel
    have hpos : 0 < (r + 1) ^ 5 := by positivity
    omega
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    exact hba.trans (Nat.le_sub_one_of_lt (by omega))
  have hd₁ := hdiag₁.comp hsTop
  have hd₂ := hdiag₂.comp hsTop
  have hd₃ := hdiag₃.comp hsTop
  have hf₁ := hdata.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    hB hsm hCmeas hCcont c hT n (by
      exact hdata.localQuadraticVariation.toProcess
        |>.polynomialBlocks_eventually_tight_sqrt_mul
          hdata.localQuadraticVariation.toProcess T
          (hdata.integrable_terminalBracket.add hdata.integrable_terminalBracket)
          (Filter.Eventually.of_forall fun omega ↦ by
            have hq : 0 ≤ bracket T omega := by
              rw [← hdata.bracket_zero omega]
              exact (hdata.continuous_monotone_bracket omega).2 bot_le
            exact add_nonneg hq hq)
          (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity))
  have hf₂ := hdata.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    hB hsm hCmeas hCcont c hT n (by
      exact hQB.polynomialBlocks_eventually_tight_sqrt_mul hQB T
          ((integrable_const (T : ℝ)).add (integrable_const (T : ℝ)))
          (Filter.Eventually.of_forall fun _ ↦ add_nonneg T.coe_nonneg T.coe_nonneg)
          (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity))
  have hf₃ := hdata.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    hB hsm hCmeas hCcont c hT n
      (hdata.polynomialBlocks_eventually_tight_sqrt_martingale_preBrownian
        hB (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity))
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · have hchain := TendstoInMeasure.sub_chain_normed_noMeas hf₁ hd₁
    simpa only [polynomialComplexDoleansWeightedCovariationResidual,
      F₁, G₁, H, s, hsadd]
      using hchain
  · have hchain := TendstoInMeasure.sub_chain_normed_noMeas hf₂ hd₂
    simpa only [polynomialComplexDoleansWeightedCovariationResidual,
      F₂, G₂, H, s, hsadd]
      using hchain
  · have hchain := TendstoInMeasure.sub_chain_normed_noMeas hf₃ hd₃
    simpa only [polynomialComplexDoleansWeightedCovariationResidual,
      F₃, G₃, H, s, hsadd]
      using hchain

set_option linter.style.longLine false in
set_option maxHeartbeats 500000 in
-- The expanded common-grid sums require a larger elaboration budget.
/-- Along a polynomial diagonal, a complex Doleans-weighted cross residual
vanishes at the terminal horizon.  Covariation convergence supplies the
completed-block limit, while finite-variation freezing reaches the identical
coarse Riemann sum on the same selected fine grid. -/
theorem GirsanovDensityData.exists_polynomial_diagonal_complexWeightedCrossResidual_terminal_of_quadraticVariations
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y Z QX QY : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T)
    (hcross : HasCrossVariationProcessInProbability X Y Z P)
    (hXmeas : ∀ t, AEStronglyMeasurable (X t) P)
    (hYmeas : ∀ t, AEStronglyMeasurable (Y t) P)
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQY : HasQuadraticVariationProcessInProbability Y QY P)
    (hQint : Integrable (fun omega ↦ QX T omega + QY T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega ↦ QX T omega + QY T omega)
    (htvtight : ∀ n : ℕ → ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox Z T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦
        complexWeightedCrossResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          X Y Z T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  obtain ⟨n, hn, hcov⟩ := hdata.exists_polynomial_diagonal_complexDoleansWeightedCovariation_sub_crossBlocks_of_quadraticVariations
      hB hsm hCmeas hCcont c hT hcross hXmeas hYmeas
        hQX hQY hQint hQnonneg
  let N : ℕ → ℕ := fun r ↦
    ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)
  let H : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let FQ : ℕ → W → ℂ := fun r omega ↦
    ∑ i ∈ Finset.range (N r), H (uniformPartitionTime T (N r) i) omega *
      ((X (uniformPartitionTime T (N r) (i + 1)) omega -
        X (uniformPartitionTime T (N r) i) omega) *
      (Y (uniformPartitionTime T (N r) (i + 1)) omega -
        Y (uniformPartitionTime T (N r) i) omega) : ℂ)
  let FV : ℕ → W → ℂ := fun r omega ↦
    ∑ i ∈ Finset.range (N r), H (uniformPartitionTime T (N r) i) omega *
      (Z (uniformPartitionTime T (N r) (i + 1)) omega -
        Z (uniformPartitionTime T (N r) i) omega : ℂ)
  let G : ℕ → W → ℂ := fun r omega ↦
    ∑ j ∈ Finset.range ((r + 1) ^ 5),
      H (uniformPartitionTime T ((r + 1) ^ 5) j) omega *
        (Z (uniformPartitionTime T ((r + 1) ^ 5) (j + 1)) omega -
          Z (uniformPartitionTime T ((r + 1) ^ 5) j) omega : ℂ)
  have hcov' : TendstoInMeasure P
      (fun r omega ↦ FQ r omega - G r omega) atTop (fun _ ↦ 0) := by
    simpa only [FQ, G, H, N] using hcov
  have hfv :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n (htvtight n)
  have hfv' : TendstoInMeasure P
      (fun r omega ↦ FV r omega - G r omega) atTop (fun _ ↦ 0) := by
    simpa only [FV, G, H, N] using hfv
  refine ⟨n, hn, ?_⟩
  change TendstoInMeasure P (fun r ↦
    complexWeightedCrossResidualApprox H X Y Z T (N r) T)
      atTop (fun _ ↦ 0)
  have hcancel : TendstoInMeasure P
      (fun r omega ↦ FQ r omega - FV r omega) atTop (fun _ ↦ 0) := by
    exact TendstoInMeasure.sub_of_sub_common_normed_noMeas hcov' hfv'
  have heq : (fun r ↦
      complexWeightedCrossResidualApprox H X Y Z T (N r) T) =
      (fun r omega ↦ FQ r omega - FV r omega) := by
    funext r omega
    rw [complexWeightedCrossResidualApprox_terminal]
  rw [heq]
  exact hcancel

/-- The terminal self-cross result, rewritten as a complex-weighted
quadratic-variation residual. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_complexWeightedQuadraticResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X QX : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T)
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hXmeas : ∀ t, AEStronglyMeasurable (X t) P)
    (hQint : Integrable (QX T) P) (hQnonneg : 0 ≤ᵐ[P] QX T)
    (htvtight : ∀ n : ℕ → ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox QX T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦
        complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          X QX T (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  obtain ⟨n, hn, hcross⟩ :=
    hdata.exists_polynomial_diagonal_complexWeightedCrossResidual_terminal_of_quadraticVariations
      hB hsm hCmeas hCcont c hT hQX.toCrossVariationSelf hXmeas hXmeas
        hQX hQX (hQint.add hQint)
        (hQnonneg.mono fun omega homega ↦ add_nonneg homega homega)
        htvtight
  refine ⟨n, hn, ?_⟩
  apply hcross.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦
    (complexWeightedQuadraticResidualApprox_eq_cross_self
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c))
      X QX T (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T omega).symm

/-- Complex weights split a real quadratic residual into the residuals
weighted by their real and imaginary parts. -/
theorem complexWeightedQuadraticResidualApprox_eq_re_add_im
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexWeightedQuadraticResidualApprox H X A U n t omega =
      (stoppedWeightedQuadraticResidualApprox
          (fun s w ↦ (H s w).re) X A U n t omega : ℂ) +
        (stoppedWeightedQuadraticResidualApprox
          (fun s w ↦ (H s w).im) X A U n t omega : ℂ) * Complex.I := by
  unfold complexWeightedQuadraticResidualApprox
    stoppedWeightedQuadraticResidualApprox
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Complex.ext
  · simp; ring
  · simp

/-- Complex weights split a real cross residual into the residuals weighted
by their real and imaginary parts. -/
theorem complexWeightedCrossResidualApprox_eq_re_add_im
    {W : Type*} (H : ℝ≥0 → W → ℂ)
    (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexWeightedCrossResidualApprox H X Y C U n t omega =
      (stoppedWeightedCrossResidualApprox
          (fun s w ↦ (H s w).re) X Y C U n t omega : ℂ) +
        (stoppedWeightedCrossResidualApprox
          (fun s w ↦ (H s w).im) X Y C U n t omega : ℂ) * Complex.I := by
  unfold complexWeightedCrossResidualApprox
    stoppedWeightedCrossResidualApprox
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Complex.ext <;> simp

/-- The complex second-order discrepancy for `M + i c B` is exactly the
sum of the two real quadratic-variation discrepancies and the real cross
variation discrepancy.  This isolates the three cancellations required by
the Fourier proof without imposing real-valuedness on the left weight. -/
theorem complexDoleansWeightedBracketResidualApprox_combination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U n t omega =
      complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M bracket U n t omega -
        (c ^ 2 : ℂ) *
          complexWeightedQuadraticResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            B (fun s _ ↦ (s : ℝ)) U n t omega +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          complexWeightedCrossResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            M B C U n t omega := by
  unfold complexDoleansWeightedBracketResidualApprox
    complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let s := min t (uniformPartitionTime U n i)
  let u := min t (uniformPartitionTime U n (i + 1))
  let h := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c) s omega
  let dM := M u omega - M s omega
  let dA := bracket u omega - bracket s omega
  let dB := B u omega - B s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have hX :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  have hQ :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  change h *
      ((complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega) ^ 2 -
        (complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega)) = _
  rw [hX, hQ]
  change h *
      (((dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I) ^ 2 -
        ((dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I)) =
    h * ((dM : ℂ) ^ 2 - (dA : ℂ)) -
      (c ^ 2 : ℂ) * (h * ((dB : ℂ) ^ 2 - (dt : ℂ))) +
      (((2 * c : ℝ) : ℂ) * Complex.I) *
        (h * (((dM * dB : ℝ) : ℂ) - (dC : ℂ)))
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The sum of higher-order exponential remainders on a stopped uniform
grid. -/
noncomputable def complexDoleansHigherOrderResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      complexDoleansSecondOrderResidual
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

/-- Explicit scalar majorant for the whole stopped-grid higher-order
remainder.  This is the sum of the left exponential modulus times the
one-cell cubic/bracket bound. -/
noncomputable def complexDoleansHigherOrderResidualBoundApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ *
      complexDoleansSecondOrderResidualBound
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

theorem complexDoleansHigherOrderResidualBoundApprox_nonneg
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualBoundApprox
  exact Finset.sum_nonneg fun i _hi => mul_nonneg (norm_nonneg _)
    (complexDoleansSecondOrderResidualBound_nonneg _ _)

/-- The full higher-order majorant is controlled by scalar aggregate bounds.
This separates the analytic input into uniform cell increments and tight
quadratic/finite-variation sums, which can be estimated independently. -/
theorem complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W)
    (K deltaZ deltaX sumZSq sumQ : ℝ)
    (hK : 0 ≤ K) (hdeltaZ : 0 ≤ deltaZ) (hdeltaX : 0 ≤ deltaX)
    (hweight : ∀ i ∈ Finset.range n,
      ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ ≤ K)
    (hz : ∀ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ≤ deltaZ)
    (hx : ∀ i ∈ Finset.range n,
      ‖X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega‖ ≤ deltaX)
    (hzsq : (∑ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ^ 2) ≤ sumZSq)
    (hqsum : (∑ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖) ≤ sumQ) :
    complexDoleansHigherOrderResidualBoundApprox X Q U n t omega ≤
      K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
  let dX : ℕ → ℂ := fun i =>
    X (min t (uniformPartitionTime U n (i + 1))) omega -
      X (min t (uniformPartitionTime U n i)) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (min t (uniformPartitionTime U n (i + 1))) omega -
      Q (min t (uniformPartitionTime U n i)) omega
  let z : ℕ → ℂ := fun i => dX i - dQ i / 2
  let E : ℕ → ℂ := fun i =>
    complexDoleansDadeExponential X Q
      (min t (uniformPartitionTime U n i)) omega
  change (∑ i ∈ Finset.range n, ‖E i‖ *
      (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
        (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤ _
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖E i‖ *
          (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
            (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2) ≤
        K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) := by
    have hzi : ‖z i‖ ≤ deltaZ := by simpa only [z, dX, dQ] using hz i hi
    have hxi : ‖dX i‖ ≤ deltaX := by simpa only [dX] using hx i hi
    apply mul_le_mul (hweight i hi)
    · apply add_le_add
      · calc
          ‖z i‖ ^ 3 * Real.exp ‖z i‖ =
              ‖z i‖ * ‖z i‖ ^ 2 * Real.exp ‖z i‖ := by ring
          _ ≤ deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ := by
            gcongr
      · gcongr
    · positivity
    · exact hK
  calc
    (∑ i ∈ Finset.range n, ‖E i‖ *
        (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
          (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤
        ∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) :=
      Finset.sum_le_sum hcell
    _ = K * (deltaZ * Real.exp deltaZ *
          (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) +
        ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
          (deltaZ + deltaX) / 2) := by
      have hfirst :
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) =
            K * deltaZ * Real.exp deltaZ *
              (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      have hsecond :
          (∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
            K * ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
              (deltaZ + deltaX) / 2 := by
        calc
          _ = ∑ i ∈ Finset.range n,
              (K * (deltaZ + deltaX) / 4) * ‖dQ i‖ := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = (K * (deltaZ + deltaX) / 4) *
              (∑ i ∈ Finset.range n, ‖dQ i‖) := by
            rw [Finset.mul_sum]
          _ = _ := by ring
      rw [show (∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) +
          ∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      rw [hfirst, hsecond]
      ring
    _ ≤ K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
      gcongr

/-- The fourth-root Brownian mesh control extracted from the fourth
variation.  Two square roots are used to keep the quantity in the real
ordered-field API. -/
noncomputable def fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega))

/-- Every Brownian grid increment is bounded by the fourth-root control of
the whole grid. -/
theorem abs_uniformPartition_increment_le_fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) {n : ℕ}
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range n) :
    |B (uniformPartitionTime U n (i + 1)) omega -
        B (uniformPartitionTime U n i) omega| ≤
      fourthVariationRootApprox B U n omega := by
  let d := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have hterm : d ^ 4 ≤ fourthVariationApprox B U n omega := by
    unfold fourthVariationApprox
    simpa only [d] using Finset.single_le_sum
      (s := Finset.range n)
      (f := fun j => (B (uniformPartitionTime U n (j + 1)) omega -
        B (uniformPartitionTime U n j) omega) ^ 4)
      (fun j _hj => by positivity) hi
  have hfourth : 0 ≤ fourthVariationApprox B U n omega :=
    fourthVariationApprox_nonneg B U n omega
  have hsq : (|d| ^ 2) ^ 2 ≤ fourthVariationApprox B U n omega := by
    calc
      (|d| ^ 2) ^ 2 = d ^ 4 := by rw [sq_abs]; ring
      _ ≤ fourthVariationApprox B U n omega := hterm
  have hfirst : |d| ^ 2 ≤
      Real.sqrt (fourthVariationApprox B U n omega) :=
    Real.le_sqrt_of_sq_le hsq
  have hsecond : |d| ≤
      Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega)) :=
    Real.le_sqrt_of_sq_le hfirst
  simpa only [d, fourthVariationRootApprox] using hsecond

/-- For a pre-Brownian process, the fourth-root mesh control vanishes in
probability without assuming continuity of the chosen sample paths. -/
theorem fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P
      (fun n => fourthVariationRootApprox B U (n + 1)) atTop
      (fun _ => 0) := by
  have hbase := fourthVariationApprox_preBrownianReal_tendstoInMeasure_zero
    hB U
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fourthVariationApprox B U (n + 1)) P :=
    aestronglyMeasurable_fourthVariationApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable) U (n + 1)
  have hfirst := TendstoInMeasure.continuous_comp hmeas hbase
    Real.continuous_sqrt
  have hsqrtMeas (n : ℕ) : AEStronglyMeasurable
      (fun omega => Real.sqrt (fourthVariationApprox B U (n + 1) omega)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hmeas n)
  have hsecond := TendstoInMeasure.continuous_comp hsqrtMeas hfirst
    Real.continuous_sqrt
  change TendstoInMeasure P
    (fun n omega => Real.sqrt
      (Real.sqrt (fourthVariationApprox B U (n + 1) omega))) atTop
    (fun _ => 0)
  simpa only [Real.sqrt_zero] using hsecond

/-- Maximum absolute increment on the positive uniform `(n+1)`-partition.
The shifted indexing makes the defining finite set nonempty at every outer
index. -/
noncomputable def uniformPartitionMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun i =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|

theorem uniformPartitionMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ uniformPartitionMaxAbsIncrement X U n omega := by
  exact (abs_nonneg (X (uniformPartitionTime U (n + 1) 1) omega -
    X (uniformPartitionTime U (n + 1) 0) omega)).trans
      (Finset.le_sup' (fun i =>
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Each cell increment is bounded by the uniform-partition maximum. -/
theorem abs_uniformPartition_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
        X (uniformPartitionTime U (n + 1) i) omega| ≤
      uniformPartitionMaxAbsIncrement X U n omega :=
  Finset.le_sup' (fun j =>
    |X (uniformPartitionTime U (n + 1) (j + 1)) omega -
      X (uniformPartitionTime U (n + 1) j) omega|) hi

theorem stronglyMeasurable_uniformPartitionMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {X : ℝ≥0 → W → ℝ}
    (hX : ∀ s, StronglyMeasurable (X s)) (U : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (uniformPartitionMaxAbsIncrement X U n) := by
  apply Measurable.stronglyMeasurable
  unfold uniformPartitionMaxAbsIncrement
  let f : ℕ → W → ℝ := fun i omega =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|
  have hf : ∀ i ∈ Finset.range (n + 1), Measurable (f i) := by
    intro i _hi
    simpa only [f, Pi.sub_apply, Real.norm_eq_abs] using
      ((hX _).sub (hX _)).norm.measurable
  have hsup := Finset.measurable_sup' Finset.nonempty_range_add_one hf
  convert hsup using 1
  ext omega
  rw [Finset.sup'_apply]

/-- Uniform continuity makes the maximum mesh increment vanish pointwise. -/
theorem uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (omega : W)
    (hX : Continuous fun s => X s omega) :
    Tendsto (fun n => uniformPartitionMaxAbsIncrement X U n omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (continuous_uniformPartition_increments_tendsto
      (fun s => X s omega) hX U epsilon hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (uniformPartitionMaxAbsIncrement_nonneg X U n omega)]
  rw [uniformPartitionMaxAbsIncrement, Finset.sup'_lt_iff]
  intro i hi
  exact hN n hn i hi

/-- A process with measurable time sections and continuous paths has
vanishing maximum uniform-grid increments in probability. -/
theorem uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement X U n)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement
      hXmeas U n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega =>
      uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
        X U omega (hXcont omega)

/-- The pre-Brownian maximum mesh increment is dominated by the fourth-root
variation control, so it vanishes in probability for arbitrary versions. -/
theorem uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement B U n)
      atTop (fun _ => 0) := by
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas
    (fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero hB U)
  · intro n omega
    exact Real.sqrt_nonneg _
  · intro n omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (uniformPartitionMaxAbsIncrement_nonneg B U n omega)]
    rw [uniformPartitionMaxAbsIncrement, Finset.sup'_le_iff]
    intro i hi
    exact abs_uniformPartition_increment_le_fourthVariationRootApprox
      B U omega hi

/-- A stopped-grid mesh control: the endpoint mesh maximum plus the square
root of the sole possible boundary-cell quadratic contribution. -/
noncomputable def uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionMaxAbsIncrement X U n omega +
    Real.sqrt (quadraticVariationCrossingStopApprox
      X U (n + 1) (min t U) omega)

theorem uniformPartitionStoppedMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) :
    0 ≤ uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact add_nonneg
    (uniformPartitionMaxAbsIncrement_nonneg X U n omega)
    (Real.sqrt_nonneg _)

theorem aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℝ≥0 → W → ℝ} (hX : ∀ s, StronglyMeasurable (X s))
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (uniformPartitionStoppedMaxAbsIncrement X U n t) P := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement hX U n
    |>.aestronglyMeasurable).add
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (aestronglyMeasurable_quadraticVariationCrossingStopApprox
          (fun s => (hX s).aestronglyMeasurable) U (n + 1) (min t U)))

/-- Every increment stopped at an arbitrary deterministic observation time
is controlled by the full-cell mesh and the unique crossing-cell term. -/
theorem abs_uniformPartition_stopped_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    |X (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        X (min t (uniformPartitionTime U (n + 1) i)) omega| ≤
      uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  let a := min t U
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hrightU : uniformPartitionTime U (n + 1) (i + 1) ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi1).2
  have hleftU : uniformPartitionTime U (n + 1) i ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi0).2
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  rw [hmin _ hrightU, hmin _ hleftU]
  by_cases hright : uniformPartitionTime U (n + 1) (i + 1) ≤ a
  · have hleft : uniformPartitionTime U (n + 1) i ≤ a :=
      (monotone_uniformPartitionTime_general U (n + 1)
        (Nat.le_succ i)).trans hright
    rw [min_eq_right hright, min_eq_right hleft]
    exact (abs_uniformPartition_increment_le_max X U n omega hi).trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have haright : a ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      le_of_not_ge hright
    by_cases hleft : uniformPartitionTime U (n + 1) i ≤ a
    · rw [min_eq_left haright, min_eq_right hleft]
      have hicross : i ∈ uniformPartitionCrossingCells U (n + 1) a := by
        simp only [uniformPartitionCrossingCells, Finset.mem_filter, hi,
          hleft, hright, not_false_eq_true, and_self]
      have hsquare :
          (X a omega - X (uniformPartitionTime U (n + 1) i) omega) ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        unfold quadraticVariationCrossingStopApprox
        exact Finset.single_le_sum
          (fun j _hj => sq_nonneg
            (X a omega - X (uniformPartitionTime U (n + 1) j) omega))
          hicross
      have habsSquare :
          |X a omega - X (uniformPartitionTime U (n + 1) i) omega| ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        simpa only [sq_abs] using hsquare
      exact (Real.le_sqrt_of_sq_le habsSquare).trans
        (le_add_of_nonneg_left
          (uniformPartitionMaxAbsIncrement_nonneg X U n omega))
    · have haleft : a ≤ uniformPartitionTime U (n + 1) i :=
        le_of_not_ge hleft
      rw [min_eq_left haright, min_eq_left haleft, sub_self, abs_zero]
      exact uniformPartitionStoppedMaxAbsIncrement_nonneg X U n t omega

/-- Continuous measurable paths make the stopped mesh control vanish in
probability at every deterministic observation time. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement X U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement X U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hXmeas hXcont U
  have hmod : IsContinuousProcessModification X X P :=
    ⟨fun _ => Filter.Eventually.of_forall fun _ => rfl,
      Filter.Eventually.of_forall hXcont⟩
  have hcross : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X U (n + 1) a)
      atTop (fun _ => 0) :=
    hmod.quadraticVariationCrossingStopApprox_tendstoInMeasure
      (fun s => (hXmeas s).aestronglyMeasurable) U a
      ⟨bot_le, min_le_right t U⟩
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox X U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hXmeas s).aestronglyMeasurable) U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement X U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        X U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- The stopped mesh control also vanishes for an arbitrary pre-Brownian
representative; Gaussian boundary-cell control replaces path continuity. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement B U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh :=
    uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U
  have hcross :=
    quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
      hB U a
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox B U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement B U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        B U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- Scalar mesh control for the complex martingale combination `M + i c B`.
It uses the continuous-path maximum for `M` and the fourth-variation maximum
for the arbitrary pre-Brownian representative `B`. -/
noncomputable def girsanovComplexCombinationMeshControl
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  uniformPartitionMaxAbsIncrement M U n omega +
    |c| * uniformPartitionMaxAbsIncrement B U n omega

theorem girsanovComplexCombinationMeshControl_nonneg
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ girsanovComplexCombinationMeshControl M B c U n omega := by
  unfold girsanovComplexCombinationMeshControl
  exact add_nonneg
    (uniformPartitionMaxAbsIncrement_nonneg M U n omega)
    (mul_nonneg (abs_nonneg c)
      (uniformPartitionMaxAbsIncrement_nonneg B U n omega))

/-- Every complex-combination cell increment is bounded by its scalar mesh
control. -/
theorem norm_complexMartingaleCombination_uniformPartition_increment_le
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) i) omega‖ ≤
      girsanovComplexCombinationMeshControl M B c U n omega := by
  let dM := M (uniformPartitionTime U (n + 1) (i + 1)) omega -
    M (uniformPartitionTime U (n + 1) i) omega
  let dB := B (uniformPartitionTime U (n + 1) (i + 1)) omega -
    B (uniformPartitionTime U (n + 1) i) omega
  have heq :
      complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) i) omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dM : ℂ)‖ + ‖((c * dB : ℝ) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |dM| + |c| * |dB| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one]
    _ ≤ uniformPartitionMaxAbsIncrement M U n omega +
        |c| * uniformPartitionMaxAbsIncrement B U n omega := by
      apply add_le_add
      · exact abs_uniformPartition_increment_le_max M U n omega hi
      · exact mul_le_mul_of_nonneg_left
          (abs_uniformPartition_increment_le_max B U n omega hi)
          (abs_nonneg c)
    _ = girsanovComplexCombinationMeshControl M B c U n omega := rfl

/-- Under the Challenge hypotheses, the complex martingale-combination mesh
control vanishes in probability. -/
theorem girsanovComplexCombinationMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M B : ℝ≥0 → W → ℝ} (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCombinationMeshControl M B c U n)
      atTop (fun _ => 0) := by
  have hM : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement M U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hMmeas hMcont U
  have hBmesh :=
    uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U
  have hscaled := hBmesh.const_mul_real_noMeas |c|
  have hsum := hM.add_real_noMeas hscaled
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement M U n omega +
      |c| * uniformPartitionMaxAbsIncrement B U n omega) atTop
    (fun _ => 0)
  simpa only [mul_zero, add_zero] using hsum

/-- Stopped-grid mesh control for the complex martingale combination. -/
noncomputable def girsanovComplexCombinationStoppedMeshControl
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement M U n t omega +
    |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega

theorem girsanovComplexCombinationStoppedMeshControl_nonneg
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCombinationStoppedMeshControl
      M B c U n t omega := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact add_nonneg
    (uniformPartitionStoppedMaxAbsIncrement_nonneg M U n t omega)
    (mul_nonneg (abs_nonneg c)
      (uniformPartitionStoppedMaxAbsIncrement_nonneg B U n t omega))

/-- Every stopped complex-combination cell is bounded by the stopped mesh
control. -/
theorem
    norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dM := M u omega - M s omega
  let dB := B u omega - B s omega
  have heq :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dM : ℂ)‖ + ‖((c * dB : ℝ) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |dM| + |c| * |dB| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one]
    _ ≤ uniformPartitionStoppedMaxAbsIncrement M U n t omega +
        |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega := by
      apply add_le_add
      · simpa only [dM, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            M U n t omega hi
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        simpa only [dB, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            B U n t omega hi
    _ = girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := rfl

/-- The stopped complex-combination mesh vanishes in probability under the
Challenge path and pre-Brownian hypotheses. -/
theorem girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M B : ℝ≥0 → W → ℝ} (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCombinationStoppedMeshControl M B c U n t)
      atTop (fun _ => 0) := by
  have hM :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hMmeas hMcont U t
  have hBmesh :=
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U t
  have hsum := hM.add_real_noMeas
    (hBmesh.const_mul_real_noMeas |c|)
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement M U n t omega +
      |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega)
    atTop (fun _ => 0)
  simpa only [mul_zero, add_zero] using hsum

/-- Scalar mesh control for the proposed complex bracket
`A - c² t + 2 i c C`. -/
noncomputable def girsanovComplexBracketMeshControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  uniformPartitionMaxAbsIncrement bracket U n omega +
    c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    2 * |c| * uniformPartitionMaxAbsIncrement C U n omega

theorem girsanovComplexBracketMeshControl_nonneg
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ girsanovComplexBracketMeshControl bracket C c U n omega := by
  unfold girsanovComplexBracketMeshControl
  exact add_nonneg
    (add_nonneg
      (uniformPartitionMaxAbsIncrement_nonneg bracket U n omega)
      (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (uniformPartitionMaxAbsIncrement_nonneg C U n omega))

/-- Every complex-bracket cell increment is bounded by its scalar mesh
control. -/
theorem norm_complexMartingaleCombinationBracket_uniformPartition_increment_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) i) omega‖ ≤
      girsanovComplexBracketMeshControl bracket C c U n omega := by
  let u := uniformPartitionTime U (n + 1) (i + 1)
  let s := uniformPartitionTime U (n + 1) i
  let dA := bracket u omega - bracket s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have htime : |dt| = ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    have hdist := dist_uniformPartitionTime_succ_eq U
      (Nat.zero_lt_succ n) i
    simpa only [u, s, dt, NNReal.dist_eq, Nat.succ_eq_add_one] using hdist
  have heq :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
        ((2 * c * dC : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ)‖ +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ (‖(dA : ℂ)‖ + ‖((c ^ 2 * dt : ℝ) : ℂ)‖) +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = |dA| + c ^ 2 * |dt| + 2 * |c| * |dC| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one, abs_pow]
      rw [sq_abs]
      ring
    _ = |dA| + c ^ 2 *
          ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * |dC| := by rw [htime]
    _ ≤ uniformPartitionMaxAbsIncrement bracket U n omega +
          c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * uniformPartitionMaxAbsIncrement C U n omega := by
      gcongr
      · exact abs_uniformPartition_increment_le_max bracket U n omega hi
      · exact abs_uniformPartition_increment_le_max C U n omega hi
    _ = girsanovComplexBracketMeshControl bracket C c U n omega := rfl

/-- Continuous bracket and drift paths make the complex-bracket mesh
control vanish in probability. -/
theorem girsanovComplexBracketMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (U : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexBracketMeshControl bracket C c U n)
      atTop (fun _ => 0) := by
  have hA : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement bracket U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hbracketMeas hbracketCont U
  have hC : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement C U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hCMeas hCCont U
  have hmesh : Tendsto (fun n : ℕ =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (nhds 0) := by
    have hdiv : Tendsto (fun n : ℕ =>
        ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
        (nhds 0) := by
      have hNN : Tendsto (fun n : ℕ =>
          U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat U)
      have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hNN
      change Tendsto (fun n : ℕ =>
        ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
        (nhds (0 : ℝ)) at hcoe
      exact hcoe
    simpa only [mul_zero] using hdiv.const_mul (c ^ 2)
  have hmeshMeasure : TendstoInMeasure P (fun n _omega =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro _n
      exact aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _omega => hmesh
  have hsum := (hA.add_real_noMeas hmeshMeasure).add_real_noMeas
    (hC.const_mul_real_noMeas (2 * |c|))
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement bracket U n omega +
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
      2 * |c| * uniformPartitionMaxAbsIncrement C U n omega) atTop
    (fun _ => 0)
  simpa only [add_zero, mul_zero] using hsum

/-- Stopping a uniform cell at a deterministic observation time cannot
increase the cell's time width. -/
theorem abs_stopped_uniformPartition_time_increment_le_mesh
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (i : ℕ) :
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
  let u := (uniformPartitionTime U (n + 1) (i + 1) : ℝ)
  let s := (uniformPartitionTime U (n + 1) i : ℝ)
  have hmin := abs_min_sub_min_le_max u (t : ℝ) s (t : ℝ)
  have hdist := dist_uniformPartitionTime_succ_eq U
    (Nat.zero_lt_succ n) i
  calc
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| =
        |min u (t : ℝ) - min s (t : ℝ)| := by
      simp only [u, s, min_comm]
    _ ≤ |u - s| := by
      simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - s))]
        using hmin
    _ = ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      simpa only [u, s, NNReal.dist_eq, Nat.succ_eq_add_one] using hdist

/-- Stopped-grid mesh control for the proposed complex bracket. -/
noncomputable def girsanovComplexBracketStoppedMeshControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
    c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega

theorem girsanovComplexBracketStoppedMeshControl_nonneg
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexBracketStoppedMeshControl
      bracket C c U n t omega := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact add_nonneg
    (add_nonneg
      (uniformPartitionStoppedMaxAbsIncrement_nonneg bracket U n t omega)
      (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (uniformPartitionStoppedMaxAbsIncrement_nonneg C U n t omega))

theorem aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : ∀ s, StronglyMeasurable (bracket s))
    (hC : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c U n t) P := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
      (P := P) hbracket U n t).add aestronglyMeasurable_const).add
    (aestronglyMeasurable_const.mul
      (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        (P := P) hC U n t))

/-- Every stopped complex-bracket cell increment is bounded by its stopped
mesh control. -/
theorem
    norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dA := bracket u omega - bracket s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have htime : |dt| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    dsimp only [dt, u, s]
    rw [NNReal.coe_min, NNReal.coe_min]
    exact abs_stopped_uniformPartition_time_increment_le_mesh U n t i
  have heq :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
        ((2 * c * dC : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ)‖ +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ (‖(dA : ℂ)‖ + ‖((c ^ 2 * dt : ℝ) : ℂ)‖) +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = |dA| + c ^ 2 * |dt| + 2 * |c| * |dC| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one, abs_pow]
      rw [sq_abs]
      ring
    _ ≤ |dA| + c ^ 2 *
          ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * |dC| := by
      gcongr
    _ ≤ uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
          c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega := by
      gcongr
      · simpa only [dA, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            bracket U n t omega hi
      · simpa only [dC, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            C U n t omega hi
    _ = girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := rfl

/-- Continuous bracket and drift paths make the stopped complex-bracket
mesh vanish in probability. -/
theorem girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c U n t) atTop (fun _ => 0) := by
  have hA :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hbracketMeas hbracketCont U t
  have hC :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hCMeas hCCont U t
  have hmesh : Tendsto (fun n : ℕ =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (nhds 0) := by
    have hdiv : Tendsto (fun n : ℕ =>
        ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
        (nhds 0) := by
      have hNN : Tendsto (fun n : ℕ =>
          U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat U)
      change Tendsto (NNReal.toReal ∘ fun n : ℕ =>
        U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds (0 : ℝ))
      simpa only [NNReal.coe_zero] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hNN
    simpa only [mul_zero] using hdiv.const_mul (c ^ 2)
  have hmeshMeasure : TendstoInMeasure P (fun n _omega =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro _n
      exact aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _omega => hmesh
  have hsum := (hA.add_real_noMeas hmeshMeasure).add_real_noMeas
    (hC.const_mul_real_noMeas (2 * |c|))
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
      2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega)
    atTop (fun _ => 0)
  simpa only [add_zero, mul_zero] using hsum

/-- Uniform stopped-grid control for the compensated complex logarithmic
increment `ΔX - ΔQ/2`. -/
noncomputable def girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
    girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2

theorem girsanovComplexCompensatedStoppedMeshControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCompensatedStoppedMeshControl
      M bracket B C c U n t omega := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  exact add_nonneg
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c U n t omega)
    (div_nonneg
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c U n t omega) (by norm_num))

/-- Every stopped compensated complex cell is bounded by the combined
stopped mesh control. -/
theorem norm_girsanov_compensated_stopped_uniformPartition_increment_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖(complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega) -
      (complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ ≤
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := by
  calc
    _ ≤ ‖complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
        ‖complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ / 2 := by
      calc
        _ ≤ ‖complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
            ‖(complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    _ ≤ girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
        girsanovComplexBracketStoppedMeshControl bracket C c U n t omega /
          2 := by
      gcongr
      · exact
          norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
            M B c U n t omega hi
      · exact
          norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
            bracket C c U n t omega hi
    _ = girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := rfl

/-- The stopped compensated mesh vanishes in probability. -/
theorem girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) atTop (fun _ => 0) := by
  have hX :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c U t
  have hQ :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hbracketMeas hbracketCont hCMeas hCCont c U t
  have hsum := hX.add_real_noMeas
    (hQ.const_mul_real_noMeas (1 / 2 : ℝ))
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
      girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2)
    atTop (fun _ => 0)
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by ring
  · exact Filter.Eventually.of_forall fun _omega => by ring

theorem aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M B : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCombinationStoppedMeshControl M B c U n t) P := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    hMmeas U n t).add
      ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        hBmeas U n t).const_mul |c|)

theorem aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) P := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  have hX :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c U n t
  have hQ := aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    (P := P) hbracketMeas hCMeas c U n t
  exact hX.add (by simpa only [div_eq_mul_inv] using hQ.mul_const (2 : ℝ)⁻¹)

/-- Uniform mesh control for the compensated logarithmic increment
`Δ(M + i c B) - Δ(A - c²t + 2 i c C)/2`. -/
noncomputable def girsanovComplexCompensatedMeshControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  girsanovComplexCombinationMeshControl M B c U n omega +
    girsanovComplexBracketMeshControl bracket C c U n omega / 2

theorem girsanovComplexCompensatedMeshControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ girsanovComplexCompensatedMeshControl
      M bracket B C c U n omega := by
  unfold girsanovComplexCompensatedMeshControl
  exact add_nonneg
    (girsanovComplexCombinationMeshControl_nonneg M B c U n omega)
    (div_nonneg
      (girsanovComplexBracketMeshControl_nonneg bracket C c U n omega)
      (by norm_num))

/-- Every compensated complex cell increment is bounded by the combined
mesh control. -/
theorem norm_girsanov_compensated_uniformPartition_increment_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖(complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) i) omega) -
      (complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) i) omega) / 2‖ ≤
      girsanovComplexCompensatedMeshControl
        M bracket B C c U n omega := by
  calc
    ‖(complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U (n + 1) i) omega) -
      (complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) (i + 1)) omega -
        complexMartingaleCombinationBracket bracket C c
          (uniformPartitionTime U (n + 1) i) omega) / 2‖ ≤
        ‖complexMartingaleCombination M B c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombination M B c
            (uniformPartitionTime U (n + 1) i) omega‖ +
        ‖complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) i) omega‖ / 2 := by
      calc
        _ ≤ ‖complexMartingaleCombination M B c
              (uniformPartitionTime U (n + 1) (i + 1)) omega -
            complexMartingaleCombination M B c
              (uniformPartitionTime U (n + 1) i) omega‖ +
            ‖(complexMartingaleCombinationBracket bracket C c
                (uniformPartitionTime U (n + 1) (i + 1)) omega -
              complexMartingaleCombinationBracket bracket C c
                (uniformPartitionTime U (n + 1) i) omega) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    _ ≤ girsanovComplexCombinationMeshControl M B c U n omega +
        girsanovComplexBracketMeshControl bracket C c U n omega / 2 := by
      gcongr
      · exact norm_complexMartingaleCombination_uniformPartition_increment_le
          M B c U n omega hi
      · exact
          norm_complexMartingaleCombinationBracket_uniformPartition_increment_le
            bracket C c U n omega hi
    _ = girsanovComplexCompensatedMeshControl
        M bracket B C c U n omega := rfl

set_option maxHeartbeats 4000000 in
-- Long proof with many intermediate integrability steps.
/-- The compensated logarithmic mesh control vanishes in probability under
the path and pre-Brownian hypotheses. -/
theorem girsanovComplexCompensatedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      girsanovComplexCompensatedMeshControl M bracket B C c U n)
      atTop (fun _ => 0) := by
  have hX : TendstoInMeasure P (fun n =>
      girsanovComplexCombinationMeshControl M B c U n) atTop
      (fun _ => 0) :=
    girsanovComplexCombinationMeshControl_tendstoInMeasure_zero
      hMmeas hMcont hB c U
  have hQ : TendstoInMeasure P (fun n =>
      girsanovComplexBracketMeshControl bracket C c U n) atTop
      (fun _ => 0) :=
    girsanovComplexBracketMeshControl_tendstoInMeasure_zero
      hbracketMeas hbracketCont hCMeas hCCont c U
  have hsum := hX.add_real_noMeas
    (hQ.const_mul_real_noMeas (1 / 2 : ℝ))
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCombinationMeshControl M B c U n omega +
      girsanovComplexBracketMeshControl bracket C c U n omega / 2)
    atTop (fun _ => 0)
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by ring
  · exact Filter.Eventually.of_forall fun _omega => by ring

/-- Discrete total variation of a complex-valued process on a uniform grid. -/
noncomputable def complexTotalVariationApprox
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega‖

theorem complexTotalVariationApprox_nonneg
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ complexTotalVariationApprox Q U n omega := by
  unfold complexTotalVariationApprox
  exact Finset.sum_nonneg fun _i _hi => norm_nonneg _

/-- Stopping a uniform grid at an arbitrary deterministic time can add at
most one partial-cell contribution to its total variation.  The parameter
`delta` is any common bound for the stopped cell increments. -/
theorem complexTotalVariationApprox_stop_le_of_cell_bound
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hinc : ∀ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖ ≤ delta) :
    complexTotalVariationApprox (fun s w => Q (min t s) w)
        U n omega ≤
      complexTotalVariationApprox Q U n omega + delta := by
  classical
  let a := min t U
  let S := uniformPartitionCrossingCells U n a
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖ ≤
        ‖Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega‖ +
          if i ∈ S then delta else 0 := by
    have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
    have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
    have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
    have hrightU : uniformPartitionTime U n (i + 1) ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2
    have hleftU : uniformPartitionTime U n i ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2
    rw [hmin _ hrightU, hmin _ hleftU]
    by_cases hright : uniformPartitionTime U n (i + 1) ≤ a
    · have hleft : uniformPartitionTime U n i ≤ a :=
        (monotone_uniformPartitionTime_general U n
          (Nat.le_succ i)).trans hright
      rw [min_eq_right hright, min_eq_right hleft]
      exact le_add_of_nonneg_right (ite_nonneg hdelta (le_refl 0))
    · have haright : a ≤ uniformPartitionTime U n (i + 1) :=
        le_of_not_ge hright
      by_cases hleft : uniformPartitionTime U n i ≤ a
      · have hicross : i ∈ S := by
          simp only [S, uniformPartitionCrossingCells, Finset.mem_filter,
            hi, hleft, hright, not_false_eq_true, and_self]
        have hpartial := hinc i hi
        rw [hmin _ hrightU, hmin _ hleftU,
          min_eq_left haright, min_eq_right hleft] at hpartial
        rw [min_eq_left haright, min_eq_right hleft, if_pos hicross]
        exact hpartial.trans
          (le_add_of_nonneg_left
            (norm_nonneg (Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega)))
      · have haleft : a ≤ uniformPartitionTime U n i :=
          le_of_not_ge hleft
        rw [min_eq_left haright, min_eq_left haleft, sub_self, norm_zero]
        exact add_nonneg (norm_nonneg _) (ite_nonneg hdelta (le_refl 0))
  unfold complexTotalVariationApprox
  calc
    (∑ i ∈ Finset.range n,
        ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖) ≤
        ∑ i ∈ Finset.range n,
          (‖Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega‖ +
            if i ∈ S then delta else 0) :=
      Finset.sum_le_sum hcell
    _ = (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) +
        ∑ i ∈ Finset.range n, if i ∈ S then delta else 0 := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) + delta := by
      gcongr
      have hcard : S.card ≤ 1 := by
        simpa only [S] using card_uniformPartitionCrossingCells_le_one U n a
      calc
        (∑ i ∈ Finset.range n, if i ∈ S then delta else 0) =
            ∑ _i ∈ (Finset.range n).filter (· ∈ S), delta := by
          rw [Finset.sum_filter]
        _ = ∑ _i ∈ S, delta := by
          congr 1
          ext i
          simp only [Finset.mem_filter, S, uniformPartitionCrossingCells]
          tauto
        _ = S.card * delta := by simp
        _ ≤ 1 * delta := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hdelta
        _ = delta := one_mul delta

/-- The total variation of the time coordinate on a positive uniform
partition is exactly the length of the interval. -/
theorem totalVariationApprox_time_uniformPartition_succ
    (U : ℝ≥0) (n : ℕ) :
    totalVariationApprox (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () =
      (U : ℝ) := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime U (n + 1) i : ℝ)|) =
        ∑ i ∈ Finset.range (n + 1),
          ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr
        (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = (uniformPartitionTime U (n + 1) (n + 1) : ℝ) -
        (uniformPartitionTime U (n + 1) 0 : ℝ) := by
      exact Finset.sum_range_sub
        (fun i => (uniformPartitionTime U (n + 1) i : ℝ)) (n + 1)
    _ = (U : ℝ) := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        NNReal.coe_zero, sub_zero]

/-- Total variation of a nondecreasing real path telescopes on every
positive uniform partition. -/
theorem totalVariationApprox_monotone_uniformPartition_succ
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmono : Monotone fun s => X s omega) :
    totalVariationApprox X U (n + 1) omega = X U omega - X 0 omega := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|) =
        ∑ i ∈ Finset.range (n + 1),
          (X (uniformPartitionTime U (n + 1) (i + 1)) omega -
            X (uniformPartitionTime U (n + 1) i) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr
        (hmono (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = X (uniformPartitionTime U (n + 1) (n + 1)) omega -
        X (uniformPartitionTime U (n + 1) 0) omega := by
      exact Finset.sum_range_sub
        (fun i => X (uniformPartitionTime U (n + 1) i) omega) (n + 1)
    _ = X U omega - X 0 omega := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]

/-- Negating a real process does not change any discrete total-variation
sum. -/
theorem totalVariationApprox_neg_process
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    totalVariationApprox (fun s omega => -X s omega) U n omega =
      totalVariationApprox X U n omega := by
  unfold totalVariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show -X (uniformPartitionTime U n (i + 1)) omega -
      -X (uniformPartitionTime U n i) omega =
      -(X (uniformPartitionTime U n (i + 1)) omega -
        X (uniformPartitionTime U n i) omega) by ring, abs_neg]

/-- The discrete variation of an absolutely continuous drift path is
bounded by the `L¹` norm of its time integrand. -/
theorem totalVariationApprox_integratedDrift_le
    {W : Type*} (mu : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmu : IntegrableOn (fun r : ℝ => mu r.toNNReal omega)
      (Set.Icc (0 : ℝ) (U : ℝ))) :
    totalVariationApprox (integratedDrift mu) U n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |mu r.toNNReal omega| := by
  let g : ℝ → ℝ := fun r => mu r.toNNReal omega
  change totalVariationApprox
      (fun s (_u : Unit) => nnrealIntegralPrimitive g s) U n () ≤
    ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |g r|
  exact totalVariationApprox_nnrealIntegralPrimitive_le hmu n

/-- Up to its terminal horizon, the totalized Girsanov drift has the same
variation bound as its absolutely continuous real-time primitive. -/
theorem totalVariationApprox_girsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    (theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W)
    (htheta : IntegrableOn (fun r : ℝ => theta r.toNNReal omega)
      (Set.Icc (0 : ℝ) (T : ℝ))) :
    totalVariationApprox (girsanovIntegratedDrift theta T) T n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  cases n with
  | zero =>
      unfold totalVariationApprox
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  | succ n =>
      have hn : 0 < n + 1 := Nat.zero_lt_succ n
      calc
        totalVariationApprox (girsanovIntegratedDrift theta T)
            T (n + 1) omega =
            totalVariationApprox (integratedDrift theta) T (n + 1) omega := by
          unfold totalVariationApprox
          apply Finset.sum_congr rfl
          intro i hi
          have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
          have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
          rw [girsanovIntegratedDrift_eq_integratedDrift,
            girsanovIntegratedDrift_eq_integratedDrift,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi1).2,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi0).2]
        _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
              |theta r.toNNReal omega| :=
          totalVariationApprox_integratedDrift_le theta T (n + 1) omega htheta

/-- A scalar control for the total variation of the proposed complex
bracket `A - c² t + 2 i c C` on a positive uniform grid. -/
noncomputable def girsanovComplexBracketVariationControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
    2 * |c| * totalVariationApprox C U (n + 1) omega

theorem girsanovComplexBracketVariationControl_nonneg
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ girsanovComplexBracketVariationControl bracket C c U n omega := by
  unfold girsanovComplexBracketVariationControl totalVariationApprox
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun _i _hi => abs_nonneg _)
      (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg U)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (Finset.sum_nonneg fun _i _hi => abs_nonneg _))

/-- For genuine Girsanov density data, the bracket contribution to the
variation control is exactly its terminal value. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket C c T n omega =
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| * totalVariationApprox C T (n + 1) omega := by
  unfold girsanovComplexBracketVariationControl
  rw [totalVariationApprox_monotone_uniformPartition_succ bracket T n omega
    (hdata.continuous_monotone_bracket omega).2,
    hdata.bracket_zero omega, sub_zero]

/-- The regularized predictable drift has uniformly bounded discrete
variation.  The zero-bracket branch is identically zero; the other branch
uses the terminal square integral to recover the required `L²`, hence `L¹`,
time integrability. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        T (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaInt : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          T (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            T (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          T (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) T (n + 1) omega
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta T (n + 1) omega hthetaInt

/-- The terminally regularized Girsanov drift has the same pathwise
variation bound on every earlier deterministic horizon. This separates the
horizon used in the zero-bracket regularization from the grid horizon. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        U (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaIntT : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    have hthetaIntU : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
      apply hthetaIntT.mono_set
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hUT)
    have hdriftEq : ∀ s, s ≤ U →
        girsanovIntegratedDrift theta T s omega =
          girsanovIntegratedDrift theta U s omega := by
      intro s hs
      unfold girsanovIntegratedDrift
      rw [min_eq_left (hs.trans hUT), min_eq_left hs]
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            U (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          U (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) U (n + 1) omega
      _ = totalVariationApprox (girsanovIntegratedDrift theta U)
          U (n + 1) omega := by
        unfold totalVariationApprox
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
        have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
        rw [hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
          (Nat.zero_lt_succ n) hi1).2,
          hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
            (Nat.zero_lt_succ n) hi0).2]
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (U : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta U (n + 1) omega hthetaIntU

/-- The complex bracket variation for the continuous regularized drift is
bounded uniformly in the grid by an explicit terminal random variable. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| *
          ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| := by
  rw [hdata.girsanovComplexBracketVariationControl_eq]
  gcongr
  exact totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    htheta hbracketTerminal n omega

/-- Terminal random bound for the variation of the regularized complex
Girsanov bracket.  Writing the `L¹` time norm as another predictable drift
keeps measurability available through the existing adaptedness theorem. -/
noncomputable def girsanovComplexTerminalVariationBound
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (omega : W) : ℝ :=
  bracket T omega + c ^ 2 * (T : ℝ) +
    2 * |c| * girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega

theorem GirsanovDensityData.girsanovComplexTerminalVariationBound_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (omega : W) :
    0 ≤ girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbracket : 0 ≤ bracket T omega := by
    rw [← hdata.bracket_zero omega]
    exact (hdata.continuous_monotone_bracket omega).2 bot_le
  have hdrift : 0 ≤ girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega := by
    unfold girsanovIntegratedDrift
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  unfold girsanovComplexTerminalVariationBound
  exact add_nonneg
    (add_nonneg hbracket (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg T)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c)) hdrift)

theorem GirsanovDensityData.stronglyMeasurable_girsanovComplexTerminalVariationBound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta) (c : ℝ) :
    StronglyMeasurable
      (girsanovComplexTerminalVariationBound bracket theta c T) := by
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega => |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W => |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  have hdrift : StronglyMeasurable (girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T) :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs T T).mono (V.le T)
  unfold girsanovComplexTerminalVariationBound
  exact (hbracket.add stronglyMeasurable_const).add
    (stronglyMeasurable_const.mul hdrift)

/-- The grid-dependent bracket-variation control is dominated by its
measurable terminal bound. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbound := hdata.girsanovComplexBracketVariationControl_le
    htheta hbracketTerminal c n omega
  rw [show (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
      |theta r.toNNReal omega|) = girsanovIntegratedDrift
        (fun s omega => |theta s omega|) T T omega by
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega => |theta s omega|) T omega).symm] at hbound
  exact hbound

/-- A convergent envelope for the compensated square sums.  Its only
grid-dependent terms are the two real quadratic-variation approximants. -/
noncomputable def girsanovComplexCompensatedSquareEnvelope
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  2 * (quadraticVariationApprox M T (n + 1) omega +
      c ^ 2 * quadraticVariationApprox B T (n + 1) omega) +
    (girsanovComplexTerminalVariationBound bracket theta c T omega) ^ 2 / 2

/-- Under the two quadratic-variation contracts, the compensated-square
envelope converges in probability to its finite terminal expression. -/
theorem GirsanovDensityData.girsanovComplexCompensatedSquareEnvelope_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta) (c : ℝ) :
    TendstoInMeasure P
      (fun n => girsanovComplexCompensatedSquareEnvelope
        M bracket B theta c T n) atTop
      (fun omega =>
        2 * (bracket T omega + c ^ 2 * (T : ℝ)) +
          (girsanovComplexTerminalVariationBound
            bracket theta c T omega) ^ 2 / 2) := by
  have hqM : TendstoInMeasure P
      (fun n => quadraticVariationApprox M T (n + 1)) atTop (bracket T) :=
    hdata.localQuadraticVariation.toProcess T
  have hqB : TendstoInMeasure P
      (fun n => quadraticVariationApprox B T (n + 1)) atTop
      (fun _ => (T : ℝ)) :=
    quadraticVariation_preBrownianReal_inProbability hB T
  have hquadratic := (hqM.add_real_noMeas
    (hqB.const_mul_real_noMeas (c ^ 2))).const_mul_real_noMeas 2
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  let Hsq : W → ℝ := fun omega => H omega ^ 2 / 2
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hHsq : AEStronglyMeasurable Hsq P := by
    have hmul : StronglyMeasurable (fun omega => H omega * H omega) :=
      hH.mul hH
    have hscaled : StronglyMeasurable
        (fun omega => (1 / 2 : ℝ) * (H omega * H omega)) :=
      stronglyMeasurable_const.mul hmul
    apply hscaled.aestronglyMeasurable.congr
    exact Filter.Eventually.of_forall fun omega => by
      simp only [Hsq]
      ring
  have hconstant : TendstoInMeasure P (fun _ : ℕ => Hsq) atTop Hsq :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hHsq)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hsum := hquadratic.add_real_noMeas hconstant
  change TendstoInMeasure P (fun n omega =>
      2 * (quadraticVariationApprox M T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox B T (n + 1) omega) + Hsq omega)
    atTop (fun omega =>
      2 * (bracket T omega + c ^ 2 * (T : ℝ)) + Hsq omega)
  exact hsum

/-- Every finite-valued strongly measurable real random variable has
vanishing upper tails on a finite measure space. -/
theorem StronglyMeasurable.exists_measureReal_ge_lt_finite
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ P.real {omega | R ≤ Q omega} < delta := by
  intro delta hdelta
  let S : ℕ → Set W := fun n => {omega | (n : ℝ) ≤ Q omega}
  have hSnull (n : ℕ) : NullMeasurableSet (S n) P := by
    change NullMeasurableSet (Q ⁻¹' Set.Ici (n : ℝ)) P
    exact hQ.aemeasurable.nullMeasurable measurableSet_Ici
  have hSanti : Antitone S := by
    intro n m hnm omega homega
    exact (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ)).trans homega
  have hSinter : ⋂ n, S n = ∅ := by
    ext omega
    simp only [Set.mem_iInter, S, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    intro hall
    obtain ⟨n, hn⟩ := exists_nat_gt (Q omega)
    exact (not_lt_of_ge (hall n)) hn
  have hmeasure : Tendsto (fun n => P (S n)) atTop (nhds 0) := by
    have hraw := tendsto_measure_iInter_atTop hSnull hSanti
      ⟨0, measure_ne_top P (S 0)⟩
    rw [hSinter, measure_empty] at hraw
    change Tendsto (P ∘ S) atTop (nhds 0)
    exact hraw
  have hmeasureReal : Tendsto (fun n => P.real (S n)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmeasureReal delta hdelta
  refine ⟨(N + 1 : ℕ), by positivity, ?_⟩
  have hclose := hN (N + 1) (Nat.le_add_right N 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hclose
  simpa only [S, Nat.cast_add, Nat.cast_one] using hclose

/-- A family pointwise dominated by one finite-valued strongly measurable
random variable is uniformly tight. -/
theorem StronglyMeasurable.eventually_tight_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) (q : ℕ → W → ℝ)
    (hle : ∀ n omega, q n omega ≤ Q omega) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ q n omega} < delta := by
  intro delta hdelta
  obtain ⟨R, hR, htail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P)
      hQ delta hdelta
  refine ⟨R, hR, Filter.Eventually.of_forall fun n ↦ ?_⟩
  apply (measureReal_mono ?_).trans_lt htail
  intro omega homega
  exact homega.trans (hle n omega)

/-- The variation of a monotone Girsanov bracket is uniformly tight along
every positive grid schedule. -/
theorem GirsanovDensityData.eventually_tight_totalVariationApprox_bracket
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox bracket T (N n) omega} <
          delta := by
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hbracket
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_monotone_uniformPartition_succ
    bracket T (N n - 1) omega (hdata.continuous_monotone_bracket omega).2
  rw [hpred, hdata.bracket_zero omega, sub_zero] at hvariation
  exact hvariation.le

/-- The variation of the deterministic time coordinate is uniformly tight
along every positive grid schedule. -/
theorem eventually_tight_totalVariationApprox_time
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (T : ℝ≥0) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} < delta := by
  intro delta hdelta
  refine ⟨(T : ℝ) + 1, by positivity,
    Filter.Eventually.of_forall fun n ↦ ?_⟩
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_time_uniformPartition_succ
    T (N n - 1)
  rw [hpred] at hvariation
  have hempty : {omega : W | (T : ℝ) + 1 ≤ totalVariationApprox
      (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} = ∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have heq : totalVariationApprox (fun t (_omega : W) ↦ (t : ℝ))
        T (N n) omega = (T : ℝ) := by
      simpa only [totalVariationApprox] using hvariation
    rw [heq]
    linarith
  rw [hempty, measureReal_empty]
  exact hdelta

/-- The discrete variation of the regularized Girsanov drift is uniformly
tight along every positive grid schedule. -/
theorem eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t omega ↦
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          T (N n) omega} < delta := by
  let H : W → ℝ := girsanovIntegratedDrift
    (fun s omega ↦ |theta s omega|) T T
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega ↦ |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W ↦ |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hH : StronglyMeasurable H := by
    exact (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs T T).mono (V.le T)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hH
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation :=
    totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
      htheta hbracketTerminal (N n - 1) omega
  rw [hpred] at hvariation
  have hIntegral : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
      |theta r.toNNReal omega|) = H omega := by
    dsimp only [H]
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega ↦ |theta s omega|) T omega).symm
  rwa [hIntegral] at hvariation

/-- Uniform tightness of the terminally regularized drift variation persists
when the uniform grids range over an earlier horizon. -/
theorem
    eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t omega ↦
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (N n) omega} < delta := by
  let H : W → ℝ := girsanovIntegratedDrift
    (fun s omega ↦ |theta s omega|) U U
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega ↦ |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W ↦ |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hH : StronglyMeasurable H := by
    exact (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs U U).mono (V.le U)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hH
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation :=
    totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
      htheta hbracketTerminal hUT (N n - 1) omega
  rw [hpred] at hvariation
  have hIntegral : (∫ r in Set.Icc (0 : ℝ) (U : ℝ),
      |theta r.toNNReal omega|) = H omega := by
    dsimp only [H]
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega ↦ |theta s omega|) U omega).symm
  rwa [hIntegral] at hvariation

/-- The Challenge hypotheses close the terminal Doleans-weighted
martingale--Brownian cross residual along a polynomial diagonal. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_girsanovCrossResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hT : 0 < T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦
        complexWeightedCrossResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket
              (fun t omega ↦ -regularizedGirsanovIntegratedDrift
                bracket theta T t omega) c))
          M B (fun t omega ↦ -regularizedGirsanovIntegratedDrift
            bracket theta T t omega) T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hCmeas : ∀ t, StronglyMeasurable (C t) := fun t ↦ by
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg
  have hCcont : ∀ omega, Continuous (fun t ↦ C t omega) := fun omega ↦ by
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  apply
    hdata.exists_polynomial_diagonal_complexWeightedCrossResidual_terminal_of_quadraticVariations
      hB hsm hCmeas hCcont c hT
        (hdata.hasCrossVariationProcessInProbability_neg_regularizedDrift
          hcross hB)
      (fun t ↦ ((hdata.adapted_martingale t).mono
        (V.le t)).aestronglyMeasurable)
      (fun t ↦ (hsm t).aestronglyMeasurable)
      hdata.localQuadraticVariation.toProcess
      (fun t ↦ quadraticVariation_preBrownianReal_inProbability hB t)
  · exact hdata.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega ↦ by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg
  · intro n
    apply
      eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift
        (P := P) htheta hbracketTerminal
          (fun r ↦ ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1))
    intro r
    positivity

/-- The Challenge hypotheses close the terminal Doleans-weighted quadratic
residual of the Girsanov martingale along a polynomial diagonal. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_girsanovMartingaleQuadraticResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (hT : 0 < T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦
        complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket
              (fun t omega ↦ -regularizedGirsanovIntegratedDrift
                bracket theta T t omega) c))
          M bracket T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hCmeas : ∀ t, StronglyMeasurable (C t) := fun t ↦ by
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg
  have hCcont : ∀ omega, Continuous (fun t ↦ C t omega) := fun omega ↦ by
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  apply
    hdata.exists_polynomial_diagonal_complexWeightedQuadraticResidual_terminal
      hB hsm hCmeas hCcont c hT hdata.localQuadraticVariation.toProcess
      (fun t ↦ ((hdata.adapted_martingale t).mono
        (V.le t)).aestronglyMeasurable)
      hdata.integrable_terminalBracket
  · exact Filter.Eventually.of_forall fun omega ↦ by
      change (0 : ℝ) ≤ bracket T omega
      rw [← hdata.bracket_zero omega]
      exact (hdata.continuous_monotone_bracket omega).2 bot_le
  · intro n
    apply hdata.eventually_tight_totalVariationApprox_bracket
      (fun r ↦ ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1))
    intro r
    positivity

/-- The Challenge hypotheses close the terminal Doleans-weighted Brownian
quadratic residual along a polynomial diagonal. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_girsanovBrownianQuadraticResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (hT : 0 < T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦
        complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket
              (fun t omega ↦ -regularizedGirsanovIntegratedDrift
                bracket theta T t omega) c))
          B (fun t _omega ↦ (t : ℝ)) T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hCmeas : ∀ t, StronglyMeasurable (C t) := fun t ↦ by
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg
  have hCcont : ∀ omega, Continuous (fun t ↦ C t omega) := fun omega ↦ by
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  apply
    hdata.exists_polynomial_diagonal_complexWeightedQuadraticResidual_terminal
      hB hsm hCmeas hCcont c hT
      (fun t ↦ quadraticVariation_preBrownianReal_inProbability hB t)
      (fun t ↦ (hsm t).aestronglyMeasurable) (integrable_const (T : ℝ))
      (Filter.Eventually.of_forall fun _ ↦ T.coe_nonneg)
  intro n
  apply eventually_tight_totalVariationApprox_time (P := P) T
    (fun r ↦ ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1))
  intro r
  positivity

set_option maxHeartbeats 2000000 in
-- The synchronized three-component cancellation expands substantial sums.
/-- The Challenge hypotheses close the full complex Doleans weighted-bracket
residual at the terminal horizon along one polynomial diagonal. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_girsanovWeightedBracketResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hT : 0 < T) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega ↦ -regularizedGirsanovIntegratedDrift
            bracket theta T t omega) c)
        T (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hCmeas : ∀ t, StronglyMeasurable (C t) := fun t ↦ by
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg
  have hCcont : ∀ omega, Continuous (fun t ↦ C t omega) := fun omega ↦ by
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hcrossC :=
    hdata.hasCrossVariationProcessInProbability_neg_regularizedDrift hcross hB
  obtain ⟨n, hn, hcovM, hcovB, hcovMB⟩ :=
    hdata.exists_polynomial_diagonal_three_complexWeightedCovariations
      hB hsm hCmeas hCcont hcrossC c hT
  let N : ℕ → ℕ := fun r ↦
    ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)
  have hN : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hfvMraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n
        (hdata.eventually_tight_totalVariationApprox_bracket N hN)
  have hfvM : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C bracket c T n r omega) atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual, C,
      N] using hfvMraw
  have hfvBraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n
        (eventually_tight_totalVariationApprox_time (P := P) T N hN)
  have hfvB : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C (fun t _omega ↦ (t : ℝ)) c T n r omega)
      atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual, C,
      N] using hfvBraw
  have hfvCraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n
        (eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift
          (P := P) htheta hbracketTerminal N hN)
  have hfvC : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C C c T n r omega) atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual, C,
      N] using hfvCraw
  have hresMself : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M M bracket T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovM hfvM
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M M bracket T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C M M bracket c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C bracket c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C M M bracket c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresBself : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B B (fun t _omega ↦ (t : ℝ)) T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovB hfvB
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B B (fun t _omega ↦ (t : ℝ)) T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C B B (fun t _omega ↦ (t : ℝ)) c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C (fun t _omega ↦ (t : ℝ)) c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C B B (fun t _omega ↦ (t : ℝ)) c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresMB : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M B C T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovMB hfvC
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M B C T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C M B C c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C C c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C M B C c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresM : TendstoInMeasure P (fun r ↦
      complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M bracket T (N r) T) atTop (fun _ ↦ 0) := by
    have heq : (fun r ↦ complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M bracket T (N r) T) = (fun r ↦ complexWeightedCrossResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M M bracket T (N r) T) := by
      funext r omega
      exact complexWeightedQuadraticResidualApprox_eq_cross_self _ _ _ _ _ _ _
    rw [heq]
    exact hresMself
  have hresB : TendstoInMeasure P (fun r ↦
      complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B (fun t _omega ↦ (t : ℝ)) T (N r) T) atTop (fun _ ↦ 0) := by
    have heq : (fun r ↦ complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B (fun t _omega ↦ (t : ℝ)) T (N r) T) =
      (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B B (fun t _omega ↦ (t : ℝ)) T (N r) T) := by
      funext r omega
      exact complexWeightedQuadraticResidualApprox_eq_cross_self _ _ _ _ _ _ _
    rw [heq]
    exact hresBself
  have hMminusB := TendstoInMeasure.sub_normed_noMeas hresM
    (TendstoInMeasure.const_mul_complex_noMeas hresB (c ^ 2 : ℂ))
  have hall := TendstoInMeasure.add_normed_noMeas hMminusB
    (TendstoInMeasure.const_mul_complex_noMeas hresMB
      (((2 * c : ℝ) : ℂ) * Complex.I))
  refine ⟨n, hn, ?_⟩
  change TendstoInMeasure P (fun r ↦
    complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) T (N r) T)
      atTop (fun _ ↦ 0)
  have heq : (fun r ↦ complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) T (N r) T) =
    (fun r omega ↦
      complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M bracket T (N r) T omega -
        (c ^ 2 : ℂ) * complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          B (fun t _omega ↦ (t : ℝ)) T (N r) T omega +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          complexWeightedCrossResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            M B C T (N r) T omega) := by
    funext r omega
    exact complexDoleansWeightedBracketResidualApprox_combination
      M bracket B C c T (N r) T omega
  rw [heq]
  simpa only [zero_mul, mul_zero, sub_zero, zero_add] using hall

set_option maxHeartbeats 2000000 in
-- The synchronized three-component cancellation expands substantial sums.
/-- Generic terminal weighted-bracket cancellation for a continuous proposed
cross bracket. The finite-variation tightness premise is exposed so the grid
horizon may differ from the horizon used to regularize a Girsanov drift. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_complexWeightedBracketResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (c : ℝ) (hT : 0 < T)
    (htvC : ∀ n : ℕ → ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox C T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T)
        atTop (fun _ ↦ 0) := by
  obtain ⟨n, hn, hcovM, hcovB, hcovMB⟩ :=
    hdata.exists_polynomial_diagonal_three_complexWeightedCovariations
      hB hsm hCmeas hCcont hcross c hT
  let N : ℕ → ℕ := fun r ↦
    ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)
  have hN : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hfvMraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n
        (hdata.eventually_tight_totalVariationApprox_bracket N hN)
  have hfvM : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C bracket c T n r omega) atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual,
      N] using hfvMraw
  have hfvBraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n
        (eventually_tight_totalVariationApprox_time (P := P) T N hN)
  have hfvB : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C (fun t _omega ↦ (t : ℝ)) c T n r omega)
      atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual,
      N] using hfvBraw
  have hfvCraw :=
    hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
      hB hsm hCmeas hCcont c hT n (htvC n)
  have hfvC : TendstoInMeasure P (fun r omega ↦
      polynomialComplexDoleansWeightedFiniteVariationResidual
        M bracket B C C c T n r omega) atTop (fun _ ↦ 0) := by
    simpa only [polynomialComplexDoleansWeightedFiniteVariationResidual,
      N] using hfvCraw
  have hresMself : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M M bracket T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovM hfvM
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M M bracket T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C M M bracket c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C bracket c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C M M bracket c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresBself : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B B (fun t _omega ↦ (t : ℝ)) T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovB hfvB
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B B (fun t _omega ↦ (t : ℝ)) T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C B B (fun t _omega ↦ (t : ℝ)) c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C (fun t _omega ↦ (t : ℝ)) c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C B B (fun t _omega ↦ (t : ℝ)) c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresMB : TendstoInMeasure P (fun r ↦
      complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M B C T (N r) T) atTop (fun _ ↦ 0) := by
    have hsub := TendstoInMeasure.sub_normed_noMeas hcovMB hfvC
    have heq : (fun r ↦ complexWeightedCrossResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M B C T (N r) T) = (fun r omega ↦
          polynomialComplexDoleansWeightedCovariationResidual
              M bracket B C M B C c T n r omega -
            polynomialComplexDoleansWeightedFiniteVariationResidual
              M bracket B C C c T n r omega) := by
      funext r omega
      exact polynomialComplexDoleansWeightedCrossResidual_eq_sub
        M bracket B C M B C c T n r omega
    rw [heq]
    simpa only [sub_zero] using hsub
  have hresM : TendstoInMeasure P (fun r ↦
      complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        M bracket T (N r) T) atTop (fun _ ↦ 0) := by
    apply hresMself.congr_left
    intro r
    exact Filter.Eventually.of_forall fun omega ↦
      (complexWeightedQuadraticResidualApprox_eq_cross_self _ _ _ _ _ _ _).symm
  have hresB : TendstoInMeasure P (fun r ↦
      complexWeightedQuadraticResidualApprox
        (complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c))
        B (fun t _omega ↦ (t : ℝ)) T (N r) T) atTop (fun _ ↦ 0) := by
    apply hresBself.congr_left
    intro r
    exact Filter.Eventually.of_forall fun omega ↦
      (complexWeightedQuadraticResidualApprox_eq_cross_self _ _ _ _ _ _ _).symm
  have hMminusB := TendstoInMeasure.sub_normed_noMeas hresM
    (TendstoInMeasure.const_mul_complex_noMeas hresB (c ^ 2 : ℂ))
  have hall := TendstoInMeasure.add_normed_noMeas hMminusB
    (TendstoInMeasure.const_mul_complex_noMeas hresMB
      (((2 * c : ℝ) : ℂ) * Complex.I))
  refine ⟨n, hn, ?_⟩
  change TendstoInMeasure P (fun r ↦
    complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) T (N r) T)
      atTop (fun _ ↦ 0)
  have heq : (fun r ↦ complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) T (N r) T) =
    (fun r omega ↦
      complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M bracket T (N r) T omega -
        (c ^ 2 : ℂ) * complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          B (fun t _omega ↦ (t : ℝ)) T (N r) T omega +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          complexWeightedCrossResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            M B C T (N r) T omega) := by
    funext r omega
    exact complexDoleansWeightedBracketResidualApprox_combination
      M bracket B C c T (N r) T omega
  rw [heq]
  simpa only [zero_mul, mul_zero, sub_zero, zero_add] using hall

/-- The synchronized weighted-bracket cancellation can be rerun on every
positive grid horizon `U ≤ T` while retaining the drift representative
regularized at the original Girsanov horizon `T`. -/
theorem
    GirsanovDensityData.exists_polynomial_diagonal_girsanovWeightedBracketResidual_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hUT : U ≤ T) (hU : 0 < U) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega ↦ -regularizedGirsanovIntegratedDrift
            bracket theta T t omega) c)
        U (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) U)
        atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hdataU : GirsanovDensityData P V M bracket U := hdata.mono_time hUT
  have hCmeas : ∀ t, StronglyMeasurable (C t) := fun t ↦ by
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg
  have hCcont : ∀ omega, Continuous (fun t ↦ C t omega) := fun omega ↦ by
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  apply
    hdataU.exists_polynomial_diagonal_complexWeightedBracketResidual_terminal
      hB hsm hCmeas hCcont
        (hdata.hasCrossVariationProcessInProbability_neg_regularizedDrift
          hcross hB) c hU
  intro n
  exact
    eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_of_le
      (P := P) htheta hbracketTerminal hUT
        (fun r ↦ ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1))
        (fun _ ↦ by positivity)

/-- Convergence of the compensated-square envelope makes it eventually
tight, without requiring an integrability moment for its terminal limit. -/
theorem GirsanovDensityData.girsanovComplexCompensatedSquareEnvelope_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta) (c : ℝ) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤ girsanovComplexCompensatedSquareEnvelope
          M bracket B theta c T n omega} < delta := by
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  let L : W → ℝ := fun omega =>
    2 * (bracket T omega + c ^ 2 * (T : ℝ)) + H omega ^ 2 / 2
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hL : StronglyMeasurable L := by
    have hbracket : StronglyMeasurable (bracket T) :=
      (hdata.adapted_bracket T).mono (V.le T)
    have hHsq : StronglyMeasurable (fun omega => H omega ^ 2) := by
      rw [show (fun omega => H omega ^ 2) = H * H by
        funext omega
        simp only [Pi.mul_apply, pow_two]]
      exact hH.mul hH
    have hHhalf : StronglyMeasurable (fun omega => H omega ^ 2 / 2) := by
      rw [show (fun omega => H omega ^ 2 / 2) =
          (fun omega => H omega ^ 2) * fun _ => (2 : ℝ)⁻¹ by
        funext omega
        simp only [Pi.mul_apply, div_eq_mul_inv]]
      exact hHsq.mul stronglyMeasurable_const
    unfold L
    exact (stronglyMeasurable_const.mul
      (hbracket.add stronglyMeasurable_const)).add
      hHhalf
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexCompensatedSquareEnvelope
        M bracket B theta c T n) atTop L := by
    simpa only [L, H] using
      hdata.girsanovComplexCompensatedSquareEnvelope_tendstoInMeasure
        hB htheta c
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hL)

/-- The largest value of the stopped real Girsanov density at the left
endpoints of a uniform grid.  The last terminal endpoint is deliberately
omitted, matching the left weights in the discrete Doleans expansion. -/
noncomputable def girsanovDensityUniformPartitionLeftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k =>
    doleansDadeExponential M bracket
      (min (uniformPartitionTime T (n + 1) k) T) omega

theorem girsanovDensityUniformPartitionLeftMax_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    0 ≤ girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
  exact (doleansDadeExponential_pos M bracket
    (min (uniformPartitionTime T (n + 1) 0) T) omega).le.trans
      (Finset.le_sup' (fun k => doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) k) T) omega)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Doob's nonnegative-submartingale inequality makes the maxima of the
Girsanov density over all deterministic uniform grids uniformly tight. -/
theorem GirsanovDensityData.girsanovDensityUniformPartitionLeftMax_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ n,
        P.real {omega | K ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega} <
            delta := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : 0 < N := by
    have honeDiv : 0 < 1 / delta := one_div_pos.mpr hdelta
    exact_mod_cast honeDiv.trans hN
  let K : ℝ≥0 := ⟨(N : ℝ), Nat.cast_nonneg N⟩
  have hKpos : (0 : ℝ) < K := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast hNpos
  refine ⟨(K : ℝ), hKpos, fun n => ?_⟩
  let D : ℝ≥0 → W → ℝ := fun t omega =>
    doleansDadeExponential M bracket (min t T) omega
  let E : Set W := {omega | (K : ℝ) ≤
    girsanovDensityUniformPartitionLeftMax M bracket T n omega}
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hsample : Martingale (uniformPartitionSample D T (n + 1))
      (uniformPartitionFiltration V T (n + 1)) P :=
    martingale_uniformPartitionSample hDmart T (n + 1)
  have hnonneg : 0 ≤ uniformPartitionSample D T (n + 1) :=
    fun _k omega => (doleansDadeExponential_pos M bracket _ omega).le
  have hraw := maximal_ineq hsample.submartingale hnonneg (ε := K) n
  have hset : {omega |
      (K : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
          (fun k => uniformPartitionSample D T (n + 1) k omega)} = E := by
    rfl
  rw [hset] at hraw
  have hterminal :
      ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P = 1 := by
    have htime : uniformPartitionTime T (n + 1) n ≤ T :=
      (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
        (Nat.le_succ n)).2
    have heq := StochasticCalculus.Martingale.integral_eq hDmart htime
    rw [show D T = girsanovDensity M bracket T by
      funext omega
      simp only [D, girsanovDensity, min_self]] at heq
    simpa only [uniformPartitionSample, D,
      min_eq_left htime, hdata.integral_eq_one] using heq.symm
  have hsetIntegral :
      ∫ omega in E, uniformPartitionSample D T (n + 1) n omega ∂P ≤ 1 := by
    calc
      _ ≤ ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P :=
        setIntegral_le_integral (hsample.integrable n)
          (Filter.Eventually.of_forall fun omega =>
            (doleansDadeExponential_pos M bracket _ omega).le)
      _ = 1 := hterminal
  have hbound : (K : ℝ≥0∞) * P E ≤ 1 :=
    hraw.trans ((ENNReal.ofReal_le_ofReal hsetIntegral).trans_eq (by norm_num))
  have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at hreal
  change (K : ℝ) * P.real E ≤ 1 at hreal
  have hKdelta : 1 < (K : ℝ) * delta := by
    apply (div_lt_iff₀ hdelta).mp
    change 1 / delta < (N : ℝ)
    exact hN
  have htail : P.real E < delta := by
    by_contra hnot
    have hdeltaLe : delta ≤ P.real E := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hdeltaLe (show 0 ≤ (K : ℝ) by positivity)
    nlinarith
  simpa only [E] using htail

/-- A single random bound for all stopped complex Doleans left weights on a
uniform grid.  The extra fixed-time density covers the unique partial cell. -/
noncomputable def girsanovComplexDoleansStoppedWeightControl
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (c ^ 2 * (T : ℝ) / 2) *
    (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
      doleansDadeExponential M bracket (min t T) omega)

theorem girsanovComplexDoleansStoppedWeightControl_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexDoleansStoppedWeightControl
      M bracket c T n t omega := by
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

theorem doleansDadeExponential_uniformPartition_le_leftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) i) T) omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega :=
  Finset.le_sup' (fun k => doleansDadeExponential M bracket
    (min (uniformPartitionTime T (n + 1) k) T) omega) hi

/-- The stopped complex Doleans weight at every left endpoint is bounded by
the density-grid maximum plus the density at the observation time. -/
theorem norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t (uniformPartitionTime T (n + 1) i)) omega‖ ≤
      girsanovComplexDoleansStoppedWeightControl
        M bracket c T n t omega := by
  let s := min t (uniformPartitionTime T (n + 1) i)
  let u := uniformPartitionTime T (n + 1) i
  have hiLe : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have huT : u ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hiLe).2
  have hsT : s ≤ T := (min_le_right t u).trans huT
  have hexp : Real.exp (c ^ 2 * (s : ℝ) / 2) ≤
      Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    have hcoe : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
    nlinarith [sq_nonneg c]
  have hdensity : doleansDadeExponential M bracket s omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega +
        doleansDadeExponential M bracket (min t T) omega := by
    by_cases hut : u ≤ t
    · have hgrid : doleansDadeExponential M bracket s omega ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
        have hsup := doleansDadeExponential_uniformPartition_le_leftMax
          M bracket T n omega hi
        simpa only [s, min_eq_right hut, u, min_eq_left huT] using hsup
      exact hgrid.trans (le_add_of_nonneg_right
        (doleansDadeExponential_pos M bracket (min t T) omega).le)
    · have htu : t ≤ u := le_of_not_ge hut
      have htT : t ≤ T := htu.trans huT
      have hs : s = t := min_eq_left htu
      rw [hs, min_eq_left htT]
      exact le_add_of_nonneg_left
        (girsanovDensityUniformPartitionLeftMax_nonneg
          M bracket T n omega)
  rw [norm_complexDoleansDadeExponential_combination]
  unfold girsanovComplexDoleansStoppedWeightControl
  rw [mul_comm (Real.exp _) _]
  exact mul_le_mul hdensity hexp (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

/-- The random controls for stopped complex Doleans left weights are
eventually tight, uniformly over the deterministic grids. -/
theorem GirsanovDensityData.girsanovComplexDoleansStoppedWeightControl_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexDoleansStoppedWeightControl
            M bracket c T n t omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨A, hA, hAtail⟩ :=
    hdata.girsanovDensityUniformPartitionLeftMax_tight
      (delta / 2) hhalf
  have hDmeas : StronglyMeasurable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega) := by
    have hDadapt := hdata.martingale_densityProcess.stronglyAdapted
    have hmin : min (min t T) T = min t T :=
      min_eq_left (min_le_right t T)
    simpa only [hmin] using
      (hDadapt (min t T)).mono (V.le (min t T))
  obtain ⟨R, hR, hRtail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P) hDmeas
      (delta / 2) hhalf
  let L := max A R
  let e := Real.exp (c ^ 2 * (T : ℝ) / 2)
  refine ⟨e * (2 * L), mul_pos (Real.exp_pos _) (mul_pos (by norm_num)
    (hA.trans_le (le_max_left A R))), ?_⟩
  filter_upwards with n
  have hsubset : {omega | e * (2 * L) ≤
      girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ⊆
        {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
        {omega | R ≤ doleansDadeExponential M bracket (min t T) omega} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hsum :
        girsanovDensityUniformPartitionLeftMax M bracket T n omega +
            doleansDadeExponential M bracket (min t T) omega < 2 * L := by
      have hx : girsanovDensityUniformPartitionLeftMax M bracket T n omega < L :=
        hnot.1.trans_le (le_max_left A R)
      have hy : doleansDadeExponential M bracket (min t T) omega < L :=
        hnot.2.trans_le (le_max_right A R)
      linarith
    have hmul : e *
        (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
          doleansDadeExponential M bracket (min t T) omega) <
        e * (2 * L) :=
      mul_lt_mul_of_pos_left hsum (by
        dsimp only [e]
        exact Real.exp_pos _)
    exact (not_lt_of_ge homega) (by simpa only
      [girsanovComplexDoleansStoppedWeightControl, e] using hmul)
  calc
    P.real {omega | e * (2 * L) ≤
        girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ≤
        P.real ({omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
          {omega | R ≤ doleansDadeExponential M bracket (min t T) omega}) :=
      measureReal_mono hsubset
    _ ≤ P.real {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} +
        P.real {omega | R ≤
          doleansDadeExponential M bracket (min t T) omega} :=
      measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add (hAtail n) hRtail
    _ = delta := by ring

/-- The total variation of the proposed complex bracket is bounded by the
variations of its real finite-variation components. -/
theorem complexTotalVariationApprox_complexMartingaleCombinationBracket_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexTotalVariationApprox
        (complexMartingaleCombinationBracket bracket C c)
        U (n + 1) omega ≤
      girsanovComplexBracketVariationControl bracket C c U n omega := by
  have hcell (i : ℕ) :
      ‖complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) i) omega‖ ≤
        |bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
          bracket (uniformPartitionTime U (n + 1) i) omega| +
        c ^ 2 *
          |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)| +
        2 * |c| *
          |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
            C (uniformPartitionTime U (n + 1) i) omega| := by
    let u := uniformPartitionTime U (n + 1) (i + 1)
    let s := uniformPartitionTime U (n + 1) i
    let dA := bracket u omega - bracket s omega
    let dC := C u omega - C s omega
    let dt := (u : ℝ) - (s : ℝ)
    have heq :
        complexMartingaleCombinationBracket bracket C c u omega -
            complexMartingaleCombinationBracket bracket C c s omega =
          (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
            ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
      unfold complexMartingaleCombinationBracket
      dsimp only [dA, dC, dt]
      push_cast
      ring
    rw [heq]
    dsimp only [dA, dC, dt, u, s]
    calc
      ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
          ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ) +
          ((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ ≤
          ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
            ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖ +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
      _ ≤
          (‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ)‖ +
            ‖((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖) +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_I, mul_one, abs_pow]
        rw [sq_abs]
        ring
  unfold complexTotalVariationApprox girsanovComplexBracketVariationControl
  calc
    (∑ i ∈ Finset.range (n + 1),
        ‖complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) (i + 1)) omega -
            complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) i) omega‖) ≤
        ∑ i ∈ Finset.range (n + 1),
          (|bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega| +
            c ^ 2 *
              |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime U (n + 1) i : ℝ)| +
            2 * |c| *
              |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
                C (uniformPartitionTime U (n + 1) i) omega|) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = totalVariationApprox bracket U (n + 1) omega +
          c ^ 2 * totalVariationApprox
            (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      unfold totalVariationApprox
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      rw [totalVariationApprox_time_uniformPartition_succ]

/-- Stopping the regularized complex bracket at an arbitrary observation
time costs only its single partial-cell mesh increment beyond the terminal
variation envelope. -/
theorem
    GirsanovDensityData.complexTotalVariationApprox_stopped_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexTotalVariationApprox
        (fun s w => complexMartingaleCombinationBracket bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c (min t s) w)
        T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let Q := complexMartingaleCombinationBracket bracket C c
  let delta := girsanovComplexBracketStoppedMeshControl bracket C c T n t omega
  have hstop : complexTotalVariationApprox (fun s w => Q (min t s) w)
      T (n + 1) omega ≤
        complexTotalVariationApprox Q T (n + 1) omega + delta := by
    apply complexTotalVariationApprox_stop_le_of_cell_bound
    · exact girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega
    · intro i hi
      exact
        norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
          bracket C c T n t omega hi
  have hfull : complexTotalVariationApprox Q T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
    exact
      (complexTotalVariationApprox_complexMartingaleCombinationBracket_le
        bracket C c T n omega).trans
        (hdata.girsanovComplexBracketVariationControl_le_terminal
          htheta hbracketTerminal c n omega)
  exact hstop.trans (add_le_add hfull (le_refl delta))

/-- The squared compensated increments are controlled by the squared
martingale increments and the square of the bracket's total variation. -/
theorem sum_norm_compensated_uniformPartition_increment_sq_le
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖(X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega) -
        (Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega) / 2‖ ^ 2) ≤
      2 * (∑ i ∈ Finset.range n,
        ‖X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega‖ ^ 2) +
        (complexTotalVariationApprox Q U n omega) ^ 2 / 2 := by
  let dX : ℕ → ℂ := fun i =>
    X (uniformPartitionTime U n (i + 1)) omega -
      X (uniformPartitionTime U n i) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega
  have hcell (i : ℕ) : ‖dX i - dQ i / 2‖ ^ 2 ≤
      2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
    have hnorm : ‖dX i - dQ i / 2‖ ≤ ‖dX i‖ + ‖dQ i‖ / 2 := by
      calc
        _ ≤ ‖dX i‖ + ‖dQ i / 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    have hsquare := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (by norm_num)))).2
        hnorm
    calc
      ‖dX i - dQ i / 2‖ ^ 2 ≤ (‖dX i‖ + ‖dQ i‖ / 2) ^ 2 := hsquare
      _ ≤ 2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖dX i‖ - ‖dQ i‖ / 2)]
  have hqSq : (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) ≤
      (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun i _hi => norm_nonneg (dQ i))
  change (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤ _
  calc
    (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤
        ∑ i ∈ Finset.range n,
          (2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) / 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 / 2 := by
      gcongr
    _ = _ := by rfl

/-- The squared norms of the `M + i c B` grid increments split exactly into
the two real quadratic-variation sums. -/
theorem sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega‖ ^ 2) =
      quadraticVariationApprox M U n omega +
        c ^ 2 * quadraticVariationApprox B U n omega := by
  unfold quadraticVariationApprox
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let dM := M (uniformPartitionTime U n (i + 1)) omega -
    M (uniformPartitionTime U n i) omega
  let dB := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have heq :
      complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq, Complex.sq_norm, Complex.normSq_add_mul_I]
  dsimp only [dM, dB]
  ring

/-- A single nonnegative control for all squared compensated logarithmic
increments in the complex Girsanov exponential. -/
noncomputable def girsanovComplexCompensatedSquareControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  2 * (quadraticVariationApprox M U (n + 1) omega +
      c ^ 2 * quadraticVariationApprox B U (n + 1) omega) +
    (girsanovComplexBracketVariationControl bracket C c U n omega) ^ 2 / 2

theorem girsanovComplexCompensatedSquareControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ girsanovComplexCompensatedSquareControl
      M bracket B C c U n omega := by
  unfold girsanovComplexCompensatedSquareControl
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (quadraticVariationApprox_nonneg M U (n + 1) omega)
      (mul_nonneg (sq_nonneg c)
        (quadraticVariationApprox_nonneg B U (n + 1) omega))))
    (div_nonneg (sq_nonneg _) (by norm_num))

/-- The compensated square control with regularized drift is bounded by
the terminal envelope on every grid. -/
theorem GirsanovDensityData.girsanovComplexCompensatedSquareControl_le_envelope
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexCompensatedSquareControl M bracket B
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      girsanovComplexCompensatedSquareEnvelope
        M bracket B theta c T n omega := by
  have hvariation :=
    hdata.girsanovComplexBracketVariationControl_le_terminal
      htheta hbracketTerminal c n omega
  have hsquare := (sq_le_sq₀
    (girsanovComplexBracketVariationControl_nonneg bracket
      (fun t omega =>
        -regularizedGirsanovIntegratedDrift bracket theta T t omega)
      c T n omega)
    (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)).2 hvariation
  unfold girsanovComplexCompensatedSquareControl
    girsanovComplexCompensatedSquareEnvelope
  gcongr

/-- The compensated square controls for the regularized complex logarithm
are eventually tight. -/
theorem GirsanovDensityData.girsanovComplexCompensatedSquareControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤ girsanovComplexCompensatedSquareControl
          M bracket B
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          c T n omega} < delta := by
  intro delta hdelta
  obtain ⟨K, hK, hEventually⟩ :=
    hdata.girsanovComplexCompensatedSquareEnvelope_eventually_tight
      hB htheta c delta hdelta
  refine ⟨K, hK, ?_⟩
  filter_upwards [hEventually] with n hn
  apply (measureReal_mono ?_).trans_lt hn
  intro omega homega
  exact homega.trans
    (hdata.girsanovComplexCompensatedSquareControl_le_envelope
      htheta hbracketTerminal c n omega)

/-- The compensated square sum for the complex Girsanov logarithm is
bounded by its explicit quadratic/finite-variation control. -/
theorem sum_norm_girsanov_compensated_uniformPartition_increment_sq_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range (n + 1),
      ‖(complexMartingaleCombination M B c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombination M B c
            (uniformPartitionTime U (n + 1) i) omega) -
        (complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) i) omega) / 2‖ ^ 2) ≤
      girsanovComplexCompensatedSquareControl
        M bracket B C c U n omega := by
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  have hvariation : complexTotalVariationApprox Q U (n + 1) omega ≤
      girsanovComplexBracketVariationControl bracket C c U n omega := by
    simpa only [Q] using
      complexTotalVariationApprox_complexMartingaleCombinationBracket_le
        bracket C c U n omega
  have hsquare : (complexTotalVariationApprox Q U (n + 1) omega) ^ 2 ≤
      (girsanovComplexBracketVariationControl bracket C c U n omega) ^ 2 :=
    (sq_le_sq₀
      (complexTotalVariationApprox_nonneg Q U (n + 1) omega)
      (girsanovComplexBracketVariationControl_nonneg
        bracket C c U n omega)).2 hvariation
  calc
    (∑ i ∈ Finset.range (n + 1),
      ‖(X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega) -
        (Q (uniformPartitionTime U (n + 1) (i + 1)) omega -
          Q (uniformPartitionTime U (n + 1) i) omega) / 2‖ ^ 2) ≤
        2 * (∑ i ∈ Finset.range (n + 1),
          ‖X (uniformPartitionTime U (n + 1) (i + 1)) omega -
            X (uniformPartitionTime U (n + 1) i) omega‖ ^ 2) +
          (complexTotalVariationApprox Q U (n + 1) omega) ^ 2 / 2 :=
      sum_norm_compensated_uniformPartition_increment_sq_le
        X Q U (n + 1) omega
    _ = 2 * (quadraticVariationApprox M U (n + 1) omega +
          c ^ 2 * quadraticVariationApprox B U (n + 1) omega) +
        (complexTotalVariationApprox Q U (n + 1) omega) ^ 2 / 2 := by
      rw [sum_norm_complexMartingaleCombination_uniformPartition_increment_sq]
    _ ≤ 2 * (quadraticVariationApprox M U (n + 1) omega +
          c ^ 2 * quadraticVariationApprox B U (n + 1) omega) +
        (girsanovComplexBracketVariationControl bracket C c U n omega) ^ 2 /
          2 := by
      gcongr
    _ = girsanovComplexCompensatedSquareControl
        M bracket B C c U n omega := rfl

/-- A stopped-grid analogue of the compensated-square control.  Its only
extra term is the vanishing mesh bound for the unique partial bracket cell. -/
noncomputable def girsanovComplexStoppedCompensatedSquareControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  2 * (quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1) omega +
      c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1) omega) +
    (girsanovComplexTerminalVariationBound bracket theta c T omega +
      girsanovComplexBracketStoppedMeshControl bracket
        (fun u z =>
          -regularizedGirsanovIntegratedDrift bracket theta T u z)
        c T n t omega) ^ 2 / 2

theorem GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (_hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedCompensatedSquareControl
      M bracket B theta c T n t omega := by
  unfold girsanovComplexStoppedCompensatedSquareControl
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (quadraticVariationApprox_nonneg
        (fun s w => M (min t s) w) T (n + 1) omega)
      (mul_nonneg (sq_nonneg c)
        (quadraticVariationApprox_nonneg
          (fun s w => B (min t s) w) T (n + 1) omega))))
    (div_nonneg (sq_nonneg _) (by norm_num))

/-- All squared stopped compensated logarithmic increments are bounded by
the stopped terminal envelope. -/
theorem
    GirsanovDensityData.sum_norm_girsanov_compensated_stopped_increment_sq_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    (∑ i ∈ Finset.range (n + 1),
      ‖(complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) i)) omega) -
        (complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) i)) omega) / 2‖ ^ 2) ≤
      girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let Xs : ℝ≥0 → W → ℂ := fun s w => X (min t s) w
  let Qs : ℝ≥0 → W → ℂ := fun s w => Q (min t s) w
  have hvariation : complexTotalVariationApprox Qs T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega := by
    simpa only [Qs, Q, C] using
      hdata.complexTotalVariationApprox_stopped_le_terminal
        htheta hbracketTerminal c n t omega
  have hvariationNonneg : 0 ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega :=
    add_nonneg (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega)
  have hsquare : (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 ≤
      (girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 :=
    (sq_le_sq₀ (complexTotalVariationApprox_nonneg Qs T (n + 1) omega)
      hvariationNonneg).2 hvariation
  have hsplit : (∑ i ∈ Finset.range (n + 1),
      ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
        Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) =
      quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega := by
    simpa only [Xs, X, complexMartingaleCombination] using
      sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
        (fun s w => M (min t s) w) (fun s w => B (min t s) w)
        c T (n + 1) omega
  change (∑ i ∈ Finset.range (n + 1),
      ‖(Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Xs (uniformPartitionTime T (n + 1) i) omega) -
        (Qs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Qs (uniformPartitionTime T (n + 1) i) omega) / 2‖ ^ 2) ≤ _
  calc
    _ ≤ 2 * (∑ i ∈ Finset.range (n + 1),
          ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 :=
      sum_norm_compensated_uniformPartition_increment_sq_le
        Xs Qs T (n + 1) omega
    _ = 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 := by
      rw [hsplit]
    _ ≤ 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (girsanovComplexTerminalVariationBound bracket theta c T omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 /
            2 := by
      gcongr
    _ = girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := rfl

/-- The stopped compensated-square control converges in probability to a
finite random variable.  Thus the single partial cell does not disturb the
terminal tightness argument. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop
      (fun omega =>
        2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
          (girsanovComplexTerminalVariationBound
            bracket theta c T omega) ^ 2 / 2) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s =>
    ((hdata.adapted_martingale s).mono (V.le s)).aestronglyMeasurable
  have hqM : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min s t) w)
        T (n + 1)) atTop (bracket (min T t)) :=
    (hdata.localQuadraticVariation.toBeforeStop.toStopped hMmeas
      (Filter.Eventually.of_forall hdata.continuous_martingale_path)) T t
  have hqM' : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1)) atTop (bracket (min T t)) := by
    apply hqM.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hqB : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1)) atTop (fun _ => ((min T t : ℝ≥0) : ℝ)) := by
    have hraw := quadraticVariation_stopped_preBrownianReal_inProbability
      hB t T
    apply hraw.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hquadratic := (hqM'.add_real_noMeas
    (hqB.const_mul_real_noMeas (c ^ 2))).const_mul_real_noMeas 2
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hHconst : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hHmesh : TendstoInMeasure P
      (fun n omega => H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega)
      atTop H := by
    simpa only [add_zero] using hHconst.add_real_noMeas hmesh
  have hmeshMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c T n t) P :=
    aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
      hbracketMeas hCMeas c T n t
  let sqHalf : ℝ → ℝ := fun x => x ^ 2 / 2
  have hsq : TendstoInMeasure P (fun n omega =>
      sqHalf (H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
      atTop (fun omega => sqHalf (H omega)) := by
    exact TendstoInMeasure.continuous_comp
      (fun n => hH.aestronglyMeasurable.add (hmeshMeas n))
      hHmesh (by simpa only [sqHalf] using
        (by fun_prop : Continuous (fun x : ℝ => x ^ 2 / 2)))
  have hsum := hquadratic.add_real_noMeas hsq
  change TendstoInMeasure P (fun n omega =>
      2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        sqHalf (H omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
    atTop (fun omega =>
      2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
        sqHalf (H omega))
  simpa only [sqHalf, H, C] using hsum

/-- The stopped compensated-square controls are eventually tight at every
deterministic observation time. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedCompensatedSquareControl
            M bracket B theta c T n t omega} < delta := by
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  let L : W → ℝ := fun omega =>
    2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
      H omega ^ 2 / 2
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hL : StronglyMeasurable L := by
    have hbracket : StronglyMeasurable (bracket (min T t)) :=
      (hdata.adapted_bracket (min T t)).mono (V.le (min T t))
    have hHsq : StronglyMeasurable (fun omega => H omega ^ 2) := by
      rw [show (fun omega => H omega ^ 2) = H * H by
        funext omega
        simp only [Pi.mul_apply, pow_two]]
      exact hH.mul hH
    unfold L
    exact (stronglyMeasurable_const.mul
      (hbracket.add stronglyMeasurable_const)).add
      (hHsq.mul stronglyMeasurable_const)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop L := by
    simpa only [L, H] using
      hdata.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
        hB htheta hbracketTerminal c t
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hL)

/-- Total-variation control for the stopped regularized complex bracket. -/
noncomputable def girsanovComplexStoppedVariationControl
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexTerminalVariationBound bracket theta c T omega +
    girsanovComplexBracketStoppedMeshControl bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedVariationControl
      bracket theta c T n t omega := by
  exact add_nonneg
    (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
    (girsanovComplexBracketStoppedMeshControl_nonneg bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤ girsanovComplexStoppedVariationControl
          bracket theta c T n t omega} < delta := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hconstant : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedVariationControl
        bracket theta c T n t) atTop H := by
    have hsum := hconstant.add_real_noMeas hmesh
    change TendstoInMeasure P (fun n omega =>
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z => -regularizedGirsanovIntegratedDrift
            bracket theta T u z) c T n t omega) atTop H
    simpa only [H, C, add_zero] using hsum
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hH)

/-- The scalar factor that vanishes in the stopped higher-order Doleans
estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderVanishingControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  dz * Real.exp dz + dz + dx

theorem girsanovComplexStoppedHigherOrderVanishingControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderVanishingControl
      M bracket B C c T n t omega := by
  unfold girsanovComplexStoppedHigherOrderVanishingControl
  exact add_nonneg (add_nonneg
    (mul_nonneg
      (girsanovComplexCompensatedStoppedMeshControl_nonneg
        M bracket B C c T n t omega) (Real.exp_pos _).le)
    (girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega))
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega)

theorem girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hB : IsPreBrownianReal B P)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) := by
  have hdz :=
    girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
      hMmeas hMcont hbracketMeas hbracketCont hCMeas hCCont hB c T t
  have hdx :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c T t
  have hdzMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
      (P := P) hMmeas hBmeas hbracketMeas hCMeas c T n t
  have hdxMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c T n t
  let finish : ℝ → ℝ → ℝ := fun dz dx =>
    dz * Real.exp dz + dz + dx
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  have hconv := TendstoInMeasure.continuous_comp₂
    hdzMeas hdxMeas hdz hdx hfinish
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega *
        Real.exp (girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega) +
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c T n t omega +
      girsanovComplexCombinationStoppedMeshControl M B c T n t omega)
    atTop (fun _ => 0)
  simpa only [finish, Real.exp_zero, mul_one, zero_add] using hconv

/-- The tight random factor in the stopped higher-order Doleans estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderTightControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega *
    (girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega +
      girsanovComplexStoppedVariationControl bracket theta c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderTightControl
      M bracket B theta c T n t omega := by
  exact mul_nonneg
    (girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega)
    (add_nonneg
      (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
      (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))

theorem
    GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedHigherOrderTightControl
            M bracket B theta c T n t omega} < delta := by
  have hweight :=
    hdata.girsanovComplexDoleansStoppedWeightControl_tight c t
  have hsquare :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
      hB htheta hbracketTerminal c t
  have hvariation :=
    hdata.girsanovComplexStoppedVariationControl_eventually_tight
      htheta hbracketTerminal c t
  have hsum := eventually_tight_add_of_nonneg
    (fun n omega =>
      hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
    (fun n omega =>
      hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega)
    hsquare hvariation
  simpa only [girsanovComplexStoppedHigherOrderTightControl] using
    eventually_tight_mul_of_nonneg
      (fun n omega =>
        girsanovComplexDoleansStoppedWeightControl_nonneg
          M bracket c T n t omega)
      (fun n omega => add_nonneg
        (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
          c n t omega)
        (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))
      hweight hsum

/-- The stopped higher-order exponential majorant factors into a vanishing
mesh term and an eventually tight random term. -/
theorem GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_le_controls
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t omega ≤
      girsanovComplexStoppedHigherOrderVanishingControl M bracket B
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let K := girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  let S := girsanovComplexStoppedCompensatedSquareControl
    M bracket B theta c T n t omega
  let R := girsanovComplexStoppedVariationControl bracket theta c T n t omega
  have hK : 0 ≤ K :=
    girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega
  have hdz : 0 ≤ dz :=
    girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega
  have hdx : 0 ≤ dx :=
    girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega
  have hS : 0 ≤ S :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg c n t omega
  have hR : 0 ≤ R :=
    hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega
  have hraw : complexDoleansHigherOrderResidualBoundApprox
      X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := by
    apply complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    · exact hK
    · exact hdz
    · exact hdx
    · intro i hi
      exact
        norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
          M bracket B C c T n t omega hi
    · intro i hi
      exact norm_girsanov_compensated_stopped_uniformPartition_increment_le
        M bracket B C c T n t omega hi
    · intro i hi
      exact
        norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
          M B c T n t omega hi
    · simpa only [X, Q, C, S] using
        hdata.sum_norm_girsanov_compensated_stopped_increment_sq_le
          htheta hbracketTerminal c n t omega
    · change complexTotalVariationApprox
          (fun s w => Q (min t s) w) T (n + 1) omega ≤ R
      simpa only [Q, C, R, girsanovComplexStoppedVariationControl] using
        hdata.complexTotalVariationApprox_stopped_le_terminal
          htheta hbracketTerminal c n t omega
  calc
    complexDoleansHigherOrderResidualBoundApprox X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := hraw
    _ ≤ (dz * Real.exp dz + dz + dx) * (K * (S + R)) := by
      have hexp : 0 ≤ Real.exp dz := (Real.exp_pos _).le
      nlinarith [mul_nonneg hK hS, mul_nonneg hK hR,
        mul_nonneg hdz hexp, mul_nonneg (add_nonneg hdz hdx) hR]
    _ = girsanovComplexStoppedHigherOrderVanishingControl M bracket B C
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
      rfl

/-- Under the Challenge hypotheses, the explicit stopped-grid higher-order
majorant vanishes in probability. -/
theorem
    GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t) atTop (fun _ => 0) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, StronglyMeasurable (M s) := fun s =>
    (hdata.adapted_martingale s).mono (V.le s)
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hr : TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) :=
    girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
      hMmeas hdata.continuous_martingale_path hbracketMeas
      (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hBmeas hB hCMeas hCcont c T t
  have hqTight :=
    hdata.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
      hB htheta hbracketTerminal c t
  apply hr.of_norm_sub_le_mul_of_eventually_tight
    (fun n omega =>
      hdata.girsanovComplexStoppedHigherOrderTightControl_nonneg
        c n t omega) hqTight
  intro n omega
  rw [sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (complexDoleansHigherOrderResidualBoundApprox_nonneg
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t omega),
    Real.norm_eq_abs,
    abs_of_nonneg
      (girsanovComplexStoppedHigherOrderVanishingControl_nonneg
        M bracket B C c T n t omega)]
  simpa only [C] using
    hdata.complexDoleansHigherOrderResidualBoundApprox_le_controls
      htheta hbracketTerminal c n t omega

/-- The norm of the full higher-order residual is bounded pathwise by the
explicit sum of its one-cell majorants. -/
theorem norm_complexDoleansHigherOrderResidualApprox_le_bound
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    ‖complexDoleansHigherOrderResidualApprox X Q U n t omega‖ ≤
      complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualApprox
    complexDoleansHigherOrderResidualBoundApprox
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun i _hi => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_complexDoleansSecondOrderResidual_le_bound _ _) (norm_nonneg _)

/-- On every observation time, including a crossing cell, the exact Euler
residual is half the weighted bracket discrepancy plus the higher-order
remainder. -/
theorem complexDoleansEulerResidualApprox_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansEulerResidualApprox X Q U (n + 1) t omega =
      (1 / 2 : ℂ) *
          complexDoleansWeightedBracketResidualApprox
            X Q U (n + 1) t omega +
        complexDoleansHigherOrderResidualApprox
          X Q U (n + 1) t omega := by
  unfold complexDoleansEulerResidualApprox
    complexDoleansWeightedBracketResidualApprox
    complexDoleansHigherOrderResidualApprox
  simp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hleftU := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi0).2
  by_cases hleftT : uniformPartitionTime U (n + 1) i ≤ t
  · rw [min_eq_right hleftT, min_eq_left hleftU]
    rw [complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder]
    ring
  · have htleft : t ≤ uniformPartitionTime U (n + 1) i :=
      le_of_not_ge hleftT
    have hmono : uniformPartitionTime U (n + 1) i ≤
        uniformPartitionTime U (n + 1) (i + 1) :=
      monotone_uniformPartitionTime_general U (n + 1) (Nat.le_succ i)
    have htright : t ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      htleft.trans hmono
    rw [min_eq_left htleft, min_eq_left htright]
    simp [complexDoleansSecondOrderResidual]

/-- Endpoint minus the canonical complex Euler process is exactly the sum
of its one-step residuals. -/
theorem complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U t : ℝ≥0) (n : ℕ) (omega : W) :
    complexDoleansDadeExponential X Q (min t U) omega -
        complexDoleansEulerProcess X Q U (n + 1) t omega =
      complexDoleansEulerResidualApprox X Q U (n + 1) t omega := by
  let E := complexDoleansDadeExponential X Q
  have htelescope :
      (∑ i ∈ Finset.range (n + 1),
        (E (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) i)) omega)) =
        E (min t U) omega - E 0 omega := by
    calc
      _ = E (min t (uniformPartitionTime U (n + 1) (n + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) 0)) omega := by
        simpa using (Finset.sum_range_sub (fun i =>
          E (min t (uniformPartitionTime U (n + 1) i)) omega) (n + 1))
      _ = E (min t U) omega - E 0 omega := by
        simp [uniformPartitionTime]
  dsimp only [E] at htelescope
  unfold complexDoleansEulerProcess complexDoleansEulerResidualApprox
  simp only
  rw [Finset.sum_sub_distrib, htelescope]
  rw [min_eq_left (show (0 : ℝ≥0) ≤ U from bot_le)]
  ring

/-- For the Girsanov complex combination, the self-integrator two-transform
Euler process is exactly the canonical single complex Doléans left sum. -/
theorem complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) :
    complexGirsanovEulerProcess M M bracket B C c U n =
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) U n := by
  funext t omega
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min s U) omega
  let A : ℕ → ℂ := fun i =>
    (M (min t (uniformPartitionTime U n (i + 1))) omega -
      M (min t (uniformPartitionTime U n i)) omega) •
        H (uniformPartitionTime U n i) omega
  let D : ℕ → ℂ := fun i =>
    (B (min t (uniformPartitionTime U n (i + 1))) omega -
      B (min t (uniformPartitionTime U n i)) omega) •
        (((c : ℂ) * Complex.I) * H (uniformPartitionTime U n i) omega)
  let F : ℕ → ℂ := fun i =>
    (complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n (i + 1))) omega -
      complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n i)) omega) *
        H (uniformPartitionTime U n i) omega
  unfold complexGirsanovEulerProcess complexDoleansEulerProcess
    uniformAdaptedTwoMartingaleSmulProcess
    uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
    elementaryMartingaleSmulProcess
  simp only [Pi.add_apply, Finset.sum_apply]
  change H 0 omega +
      ((∑ i ∈ Finset.range n, A i) + ∑ i ∈ Finset.range n, D i) =
    H 0 omega + ∑ i ∈ Finset.range n, F i
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [A, D, F, complexMartingaleCombination]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Once the density cap agrees with the real stochastic exponential on a
whole horizon, the capped and uncapped complex Euler processes agree there
on every grid and at every observation time. -/
theorem cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) (omega : W)
    (hcap : ∀ s ∈ Set.Icc (0 : ℝ≥0) U,
      cappedDoleansDadeExponential M bracket R s omega =
        doleansDadeExponential M bracket s omega) :
    ∀ t, cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n t omega =
      complexGirsanovEulerProcess N M bracket B C c U n t omega := by
  have hcomplex (s : ℝ≥0) (hs : s ≤ U) :
      cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R s omega =
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c) s omega := by
    unfold cappedComplexDoleansDadeExponentialCombination
    rw [hcap s ⟨bot_le, hs⟩,
      complexDoleansDadeExponential_combination_factor]
  intro t
  unfold cappedComplexGirsanovEulerProcess complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  · simpa only [min_eq_left (show (0 : ℝ≥0) ≤ U by exact bot_le)] using
      hcomplex 0 bot_le
  · unfold uniformAdaptedTwoMartingaleSmulProcess
    simp only [Pi.add_apply]
    congr 1
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact hcomplex (min (uniformPartitionTime U n i) U) (min_le_right _ _)
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact congrArg (fun z : ℂ => ((c : ℂ) * Complex.I) * z)
        (hcomplex (min (uniformPartitionTime U n i) U)
          (min_le_right _ _))

/-- If two first integrators agree throughout the deterministic horizon,
their uncapped complex Euler processes agree on every grid and at every
observation time. -/
theorem complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
    {W : Type*} (N N' M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hNN' : ∀ s ∈ Set.Icc (0 : ℝ≥0) U, N s omega = N' s omega) :
    ∀ t, complexGirsanovEulerProcess N M bracket B C c U n t omega =
      complexGirsanovEulerProcess N' M bracket B C c U n t omega := by
  intro t
  unfold complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedTwoMartingaleSmulProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
  have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
  unfold elementaryMartingaleSmulProcess
  congr 2
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2⟩
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2⟩

/-- Adapted inputs make the uncapped complex Euler process strongly
adapted; no moment bound is required for this measurability statement. -/
theorem stronglyAdapted_complexGirsanovEulerProcess
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : StronglyAdapted V N) (hM : StronglyAdapted V M)
    (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) :
    StronglyAdapted V
      (complexGirsanovEulerProcess N M bracket B C c U n) := by
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  have hE : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) := by
    intro t
    change StronglyMeasurable[V t]
      (Complex.exp ∘
        (complexMartingaleCombination M B c t -
          (complexMartingaleCombinationBracket bracket C c t /
            fun _ : W => (2 : ℂ))))
    exact Complex.continuous_exp.comp_stronglyMeasurable
      ((stronglyAdapted_complexMartingaleCombination hM hB c t).sub
        ((stronglyAdapted_complexMartingaleCombinationBracket
          hbracket hC c t).div stronglyMeasurable_const))
  have hH : StronglyAdapted V H := fun t =>
    (hE (min t U)).mono (V.mono (min_le_left t U))
  have hK : StronglyAdapted V K := fun t =>
    stronglyMeasurable_const.mul (hH t)
  have hinitial : StronglyAdapted V (fun _ => H 0) := fun t =>
    (hH 0).mono (V.mono bot_le)
  simpa only [complexGirsanovEulerProcess, H, K] using
    hinitial.add
      (stronglyAdapted_uniformAdaptedTwoMartingaleSmulProcess
        hN hB hH hK U n)

/-- Adapted inputs make every density-capped complex Euler process strongly
adapted. -/
theorem stronglyAdapted_cappedComplexGirsanovEulerProcess
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : StronglyAdapted V N) (hM : StronglyAdapted V M)
    (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) :
    StronglyAdapted V
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n) := by
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun t =>
    (hcap (min t U)).mono (V.mono (min_le_left t U))
  have hK : StronglyAdapted V K := fun t =>
    stronglyMeasurable_const.mul (hH t)
  have hinitial : StronglyAdapted V (fun _ => H 0) := fun t =>
    (hH 0).mono (V.mono bot_le)
  simpa only [cappedComplexGirsanovEulerProcess, H, K] using
    hinitial.add
      (stronglyAdapted_uniformAdaptedTwoMartingaleSmulProcess
        hN hB hH hK U n)

/-- Increasing density caps disappear from the complex Euler sums in
probability on every fixed horizon.  The proof uses only continuity of the
real martingale and bracket paths; the Brownian integrator need not have
continuous sample paths. -/
theorem
    tendstoInMeasure_cappedComplexGirsanovEulerProcess_sub_complex
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {N : ℕ → ℝ≥0 → W → ℝ}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hN : ∀ n, StronglyAdapted V (N n))
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s => M s omega))
    (hbracketCont : ∀ᵐ omega ∂P, Continuous (fun s => bracket s omega))
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n omega =>
      cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (n + 1) t omega -
        complexGirsanovEulerProcess
          (N n) M bracket B C c T (n + 1) t omega)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hcapped : AEStronglyMeasurable
        (cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (n + 1) t) P :=
      ((stronglyAdapted_cappedComplexGirsanovEulerProcess
        (hN n) hM hbracket hB hC c (n + 1) T (n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    have hplain : AEStronglyMeasurable
        (complexGirsanovEulerProcess
          (N n) M bracket B C c T (n + 1) t) P :=
      ((stronglyAdapted_complexGirsanovEulerProcess
        (hN n) hM hbracket hB hC c T (n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    exact hcapped.sub hplain
  · filter_upwards
      [ae_eventually_cappedDoleansDadeExponential_eq_on_Icc
        M bracket T hMcont hbracketCont] with omega homega
    have hshift : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ≥0) T,
        cappedDoleansDadeExponential M bracket (n + 1) s omega =
          doleansDadeExponential M bracket s omega :=
      by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_add_atTop_nat 1).eventually homega
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hshift] with n hn
    rw [cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
      (N n) M bracket B C c (n + 1) T (n + 1) omega hn t, sub_self]

/-- Increasing caps disappear independently of the selected positive grid
counts.  This is the form needed by cofinal polynomial Taylor diagonals. -/
theorem
    tendstoInMeasure_cappedComplexGirsanovEulerProcess_sub_complex_counts
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {N : ℕ → ℝ≥0 → W → ℝ} {q : ℕ → ℕ}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hN : ∀ n, StronglyAdapted V (N n))
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s => M s omega))
    (hbracketCont : ∀ᵐ omega ∂P, Continuous (fun s => bracket s omega))
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n omega =>
      cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (q n + 1) t omega -
        complexGirsanovEulerProcess
          (N n) M bracket B C c T (q n + 1) t omega)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hcapped : AEStronglyMeasurable
        (cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (q n + 1) t) P :=
      ((stronglyAdapted_cappedComplexGirsanovEulerProcess
        (hN n) hM hbracket hB hC c (n + 1) T (q n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    have hplain : AEStronglyMeasurable
        (complexGirsanovEulerProcess
          (N n) M bracket B C c T (q n + 1) t) P :=
      ((stronglyAdapted_complexGirsanovEulerProcess
        (hN n) hM hbracket hB hC c T (q n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    exact hcapped.sub hplain
  · filter_upwards
      [ae_eventually_cappedDoleansDadeExponential_eq_on_Icc
        M bracket T hMcont hbracketCont] with omega homega
    have hshift : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ≥0) T,
        cappedDoleansDadeExponential M bracket (n + 1) s omega =
          doleansDadeExponential M bracket s omega :=
      by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_add_atTop_nat 1).eventually homega
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hshift] with n hn
    rw [cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
      (N n) M bracket B C c (n + 1) T (q n + 1) omega hn t, sub_self]

/-- A common localizer disappears from uncapped complex Euler sums in
probability once its stopping times tend to infinity.  Thus the Taylor-limit
half of the proof may be carried out with `M` itself; localization remains
only in the martingale and uniform-integrability half. -/
theorem
    tendstoInMeasure_complexGirsanovEulerProcess_localizing_sub_self
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : ℕ → W → WithTop ℝ≥0}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (htau : IsLocalizingSequence V tau P)
    (hM : StronglyAdapted V M)
    (hMcont : ∀ omega, Continuous (fun s => M s omega))
    (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n omega =>
      complexGirsanovEulerProcess
          (localizingStoppedProcess M (tau n))
          M bracket B C c T (n + 1) t omega -
        complexGirsanovEulerProcess
          M M bracket B C c T (n + 1) t omega)
      atTop (fun _ => 0) := by
  have hMtau (n : ℕ) : StronglyAdapted V
      (localizingStoppedProcess M (tau n)) :=
    stronglyAdapted_localizingStoppedProcess
      hM hMcont (htau.isStoppingTime n)
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (((stronglyAdapted_complexGirsanovEulerProcess
      (hMtau n) hM hbracket hB hC c T (n + 1) t).mono
        (V.le t)).aestronglyMeasurable).sub
      (((stronglyAdapted_complexGirsanovEulerProcess
        hM hM hbracket hB hC c T (n + 1) t).mono
          (V.le t)).aestronglyMeasurable)
  · filter_upwards [htau.tendsto_top] with omega homega
    have heventually : ∀ᶠ n : ℕ in atTop,
        (T : WithTop ℝ≥0) < tau n omega :=
      homega (Ioi_mem_nhds (WithTop.coe_lt_top T))
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [heventually] with n hn
    have hEq (s : ℝ≥0) (hs : s ∈ Set.Icc (0 : ℝ≥0) T) :
        localizingStoppedProcess M (tau n) s omega = M s omega :=
      localizingStoppedProcess_eq_of_lt M (tau n) s omega
        ((WithTop.coe_le_coe.mpr hs.2).trans_lt hn)
    rw [complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
      (localizingStoppedProcess M (tau n)) M M bracket B C
        c T (n + 1) omega hEq t, sub_self]

/-- A common localizer also disappears along arbitrary selected positive
grid counts. -/
theorem
    tendstoInMeasure_complexGirsanovEulerProcess_localizing_sub_self_counts
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : ℕ → W → WithTop ℝ≥0} {q : ℕ → ℕ}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (htau : IsLocalizingSequence V tau P)
    (hM : StronglyAdapted V M)
    (hMcont : ∀ omega, Continuous (fun s => M s omega))
    (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n omega =>
      complexGirsanovEulerProcess
          (localizingStoppedProcess M (tau n))
          M bracket B C c T (q n + 1) t omega -
        complexGirsanovEulerProcess
          M M bracket B C c T (q n + 1) t omega)
      atTop (fun _ => 0) := by
  have hMtau (n : ℕ) : StronglyAdapted V
      (localizingStoppedProcess M (tau n)) :=
    stronglyAdapted_localizingStoppedProcess
      hM hMcont (htau.isStoppingTime n)
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (((stronglyAdapted_complexGirsanovEulerProcess
      (hMtau n) hM hbracket hB hC c T (q n + 1) t).mono
        (V.le t)).aestronglyMeasurable).sub
      (((stronglyAdapted_complexGirsanovEulerProcess
        hM hM hbracket hB hC c T (q n + 1) t).mono
          (V.le t)).aestronglyMeasurable)
  · filter_upwards [htau.tendsto_top] with omega homega
    have heventually : ∀ᶠ n : ℕ in atTop,
        (T : WithTop ℝ≥0) < tau n omega :=
      homega (Ioi_mem_nhds (WithTop.coe_lt_top T))
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [heventually] with n hn
    have hEq (s : ℝ≥0) (hs : s ∈ Set.Icc (0 : ℝ≥0) T) :
        localizingStoppedProcess M (tau n) s omega = M s omega :=
      localizingStoppedProcess_eq_of_lt M (tau n) s omega
        ((WithTop.coe_le_coe.mpr hs.2).trans_lt hn)
    rw [complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
      (localizingStoppedProcess M (tau n)) M M bracket B C
        c T (q n + 1) omega hEq t, sub_self]

/-- Unfolding the capped complex Euler process exposes exactly its initial
value and the two coherent martingale transforms. -/
theorem cappedComplexGirsanovEulerProcess_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T : ℝ≥0) (n : ℕ) :
    cappedComplexGirsanovEulerProcess N M bracket B C c R T n =
      let H : ℝ≥0 → W → ℂ := fun s omega =>
        cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R (min s T) omega
      let J : ℝ≥0 → W → ℂ := fun s omega =>
        ((c : ℂ) * Complex.I) * H s omega
      (fun _ => H 0) +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T n := by
  rfl

/-- For a martingale approximation `N` of `M`, every capped complex Euler
process is a genuine martingale.  This is the discrete probabilistic half of
the remaining Girsanov cancellation argument. -/
theorem martingale_cappedComplexGirsanovEulerProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [IsFiniteMeasure P]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) :
    Martingale
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n) V P := by
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  let CH : ℝ := (R : ℝ) * Real.exp (c ^ 2 * (U : ℝ) / 2)
  let CK : ℝ := |c| * CH
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun t =>
    (hcap (min t U)).mono (V.mono (min_le_left t U))
  have hK : StronglyAdapted V K := fun t => by
    exact stronglyMeasurable_const.mul (hH t)
  have hHbound (t : ℝ≥0) (omega : W) : ‖H t omega‖ ≤ CH := by
    exact norm_cappedComplexDoleansDadeExponentialCombination_le
      M bracket B C c R U (min t U) (min_le_right t U) omega
  have hKbound (t : ℝ≥0) (omega : W) : ‖K t omega‖ ≤ CK := by
    dsimp only [K, CK]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hHbound t omega) (abs_nonneg c)
  have hsum : Martingale
      (uniformAdaptedTwoMartingaleSmulProcess N B H K U n) V P :=
    martingale_uniformAdaptedTwoMartingaleSmulProcess
      hN hBmart hH hK CH CK hHbound hKbound U n
  have hH0meas : StronglyMeasurable (H 0) :=
    (hH 0).mono (V.le 0)
  have hH0int : Integrable (H 0) P := by
    refine Integrable.mono' (integrable_const CH)
      hH0meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun omega => hHbound 0 omega
  have hinitial : Martingale (fun _ => H 0) V P :=
    martingale_const_fun V P (hH 0) hH0int
  simpa only [cappedComplexGirsanovEulerProcess, H, K] using
    hinitial.add hsum

/-- The capped complex Euler process has an explicit grid-independent `L²`
bound whenever both real integrators have square-integrable terminal values.
The estimate holds at every observation time and requires no path continuity
of the Brownian integrator. -/
theorem eLpNorm_cappedComplexGirsanovEulerProcess_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R T : ℝ≥0) (hNT : MemLp (N T) 2 P)
    (hBT : MemLp (B T) 2 P) (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R T (n + 1) t) 2 P ≤
      cappedComplexGirsanovCoefficientBound c R T +
        2 * cappedComplexGirsanovCoefficientBound c R T *
          eLpNorm (N T - N 0) 2 P +
        2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
          eLpNorm (B T - B 0) 2 P := by
  let CH : ℝ≥0 := cappedComplexGirsanovCoefficientBound c R T
  let CK : ℝ≥0 :=
    cappedComplexGirsanovBrownianCoefficientBound c R T
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min s T) omega
  let J : ℝ≥0 → W → ℂ := fun s omega =>
    ((c : ℂ) * Complex.I) * H s omega
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun s =>
    (hcap (min s T)).mono (V.mono (min_le_left s T))
  have hJ : StronglyAdapted V J := fun s =>
    stronglyMeasurable_const.mul (hH s)
  have hHbound (s : ℝ≥0) (omega : W) : ‖H s omega‖ ≤ CH := by
    dsimp only [H, CH, cappedComplexGirsanovCoefficientBound]
    rw [Real.toNNReal_of_nonneg (Real.exp_pos _).le]
    simpa only [NNReal.coe_mul, NNReal.coe_mk] using
      norm_cappedComplexDoleansDadeExponentialCombination_le
        M bracket B C c R T (min s T) (min_le_right s T) omega
  have hJbound (s : ℝ≥0) (omega : W) : ‖J s omega‖ ≤ CK := by
    dsimp only [J]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    dsimp only [CK, cappedComplexGirsanovBrownianCoefficientBound]
    rw [Real.toNNReal_of_nonneg
      (mul_nonneg (abs_nonneg c) CH.coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hHbound s omega) (abs_nonneg c)
  have hinitialMeas : AEStronglyMeasurable (H 0) P :=
    ((hH 0).mono (V.le 0)).aestronglyMeasurable
  have hinitial : eLpNorm (H 0) 2 P ≤ CH := by
    calc
      eLpNorm (H 0) 2 P ≤
          P Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (CH : ℝ) :=
        eLpNorm_le_of_ae_bound
          (Filter.Eventually.of_forall fun omega => hHbound 0 omega)
      _ = CH := by simp
  have htransformMeas : AEStronglyMeasurable
      (uniformAdaptedTwoMartingaleSmulProcess
        N B H J T (n + 1) t) P :=
    ((martingale_uniformAdaptedTwoMartingaleSmulProcess
      hN hBmart hH hJ CH CK hHbound hJbound T (n + 1)).integrable t).1
  rw [congrFun
    (cappedComplexGirsanovEulerProcess_eq
      N M bracket B C c R T (n + 1)) t]
  change eLpNorm (H 0 +
    uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤ _
  calc
    eLpNorm (H 0 +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤
        eLpNorm (H 0) 2 P +
          eLpNorm
            (uniformAdaptedTwoMartingaleSmulProcess
              N B H J T (n + 1) t) 2 P :=
      eLpNorm_add_le hinitialMeas htransformMeas (by norm_num)
    _ ≤ CH +
          (2 * CH * eLpNorm (N T - N 0) 2 P +
            2 * CK * eLpNorm (B T - B 0) 2 P) :=
      add_le_add hinitial
        (eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
          hN hBmart T hNT hBT hH hJ CH CK hHbound hJbound n t)
    _ = CH + 2 * CH * eLpNorm (N T - N 0) 2 P +
          2 * CK * eLpNorm (B T - B 0) 2 P := by ring
    _ = cappedComplexGirsanovCoefficientBound c R T +
          2 * cappedComplexGirsanovCoefficientBound c R T *
            eLpNorm (N T - N 0) 2 P +
          2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
            eLpNorm (B T - B 0) 2 P := by rfl

/-- At its terminal grid time, the capped complex Euler martingale is the
expected pair of left sums against `N` and `B`. -/
theorem cappedComplexGirsanovEulerProcess_terminal
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) (omega : W) :
    cappedComplexGirsanovEulerProcess
        N M bracket B C c R U (n + 1) U omega =
      cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R 0 omega +
      (∑ i ∈ Finset.range (n + 1),
        (N (uniformPartitionTime U (n + 1) (i + 1)) omega -
          N (uniformPartitionTime U (n + 1) i) omega) •
        cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R
            (uniformPartitionTime U (n + 1) i) omega) +
      ∑ i ∈ Finset.range (n + 1),
        (B (uniformPartitionTime U (n + 1) (i + 1)) omega -
          B (uniformPartitionTime U (n + 1) i) omega) •
        (((c : ℂ) * Complex.I) *
          cappedComplexDoleansDadeExponentialCombination
            M bracket B C c R
              (uniformPartitionTime U (n + 1) i) omega) := by
  unfold cappedComplexGirsanovEulerProcess
  simp only [Pi.add_apply]
  rw [uniformAdaptedTwoMartingaleSmulProcess_terminal]
  simp only [min_eq_left (show (0 : ℝ≥0) ≤ U by exact bot_le)]
  have hNsum : (∑ i ∈ Finset.range (n + 1),
      (N (uniformPartitionTime U (n + 1) (i + 1)) omega -
        N (uniformPartitionTime U (n + 1) i) omega) •
      cappedComplexDoleansDadeExponentialCombination M bracket B C c R
        (min (uniformPartitionTime U (n + 1) i) U) omega) =
      ∑ i ∈ Finset.range (n + 1),
        (N (uniformPartitionTime U (n + 1) (i + 1)) omega -
          N (uniformPartitionTime U (n + 1) i) omega) •
        cappedComplexDoleansDadeExponentialCombination M bracket B C c R
          (uniformPartitionTime U (n + 1) i) omega := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [min_eq_left]
    exact (uniformPartitionTime_mem_Icc_of_le U
      (Nat.zero_lt_succ n) ((Nat.le_succ i).trans (Finset.mem_range.mp hi))).2
  have hBsum : (∑ i ∈ Finset.range (n + 1),
      (B (uniformPartitionTime U (n + 1) (i + 1)) omega -
        B (uniformPartitionTime U (n + 1) i) omega) •
      (((c : ℂ) * Complex.I) *
        cappedComplexDoleansDadeExponentialCombination M bracket B C c R
          (min (uniformPartitionTime U (n + 1) i) U) omega)) =
      ∑ i ∈ Finset.range (n + 1),
        (B (uniformPartitionTime U (n + 1) (i + 1)) omega -
          B (uniformPartitionTime U (n + 1) i) omega) •
        (((c : ℂ) * Complex.I) *
          cappedComplexDoleansDadeExponentialCombination M bracket B C c R
            (uniformPartitionTime U (n + 1) i) omega) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [min_eq_left]
    exact (uniformPartitionTime_mem_Icc_of_le U
      (Nat.zero_lt_succ n) ((Nat.le_succ i).trans (Finset.mem_range.mp hi))).2
  rw [hNsum, hBsum]
  abel

/-- Adaptedness of the two inputs makes the complex Doléans exponential
adapted. -/
theorem stronglyAdapted_complexDoleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X Q : ℝ≥0 → W → ℂ}
    (hX : StronglyAdapted V X) (hQ : StronglyAdapted V Q) :
    StronglyAdapted V (complexDoleansDadeExponential X Q) := by
  intro t
  change StronglyMeasurable[V t]
    (Complex.exp ∘ (X t - (Q t / fun _ : W ↦ (2 : ℂ))))
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((hX t).sub ((hQ t).div stronglyMeasurable_const))

/-- Continuous input paths make the complex Doléans exponential pathwise
continuous. -/
theorem continuous_complexDoleansDadeExponential
    {W : Type*} {X Q : ℝ≥0 → W → ℂ}
    (hX : ∀ omega, Continuous (fun t ↦ X t omega))
    (hQ : ∀ omega, Continuous (fun t ↦ Q t omega)) :
    ∀ omega, Continuous (fun t ↦
      complexDoleansDadeExponential X Q t omega) := by
  intro omega
  exact Complex.continuous_exp.comp
    ((hX omega).sub ((hQ omega).div_const 2))

/-- Under the predictable Girsanov contract, the algebraic complex
Doleans exponential is stochastically continuous.  This formulation keeps
the original adapted totalized drift while borrowing path regularity from
its deterministic-time almost-everywhere continuous representative. -/
theorem GirsanovDensityData.tendstoInMeasure_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (a n)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c) r) := by
  have hMlim : TendstoInMeasure P (fun n => M (a n)) atTop (M r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_martingale_path omega).continuousAt.tendsto.comp ha
  have hBlim : TendstoInMeasure P (fun n => B (a n)) atTop (B r) :=
    StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha
  let combine : ℝ → ℝ → ℂ := fun m b =>
    (m : ℂ) + ((c * b : ℝ) : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hXlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombination M B c (a n)) atTop
      (complexMartingaleCombination M B c r) := by
    change TendstoInMeasure P (fun n omega =>
      combine (M (a n) omega) (B (a n) omega)) atTop
        (fun omega => combine (M r omega) (B r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun n => (hsm (a n)).aestronglyMeasurable)
      hMlim hBlim hcombine
  have hbracketLim : TendstoInMeasure P (fun n => bracket (a n)) atTop
      (bracket r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_monotone_bracket omega).1.continuousAt.tendsto.comp ha
  have htimeLim : TendstoInMeasure P
      (fun n => fun _ : W => (a n : ℝ)) atTop (fun _ => (r : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ => aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ =>
        (NNReal.continuous_coe.tendsto r).comp ha
  have hdriftLim := hdata.tendstoInMeasure_girsanovIntegratedDrift
    htheta hbracketTerminal hcross hB ha
  have hdriftMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovIntegratedDrift theta T (a n)) P :=
    (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable
  have hClim : TendstoInMeasure P
      (fun n omega => -girsanovIntegratedDrift theta T (a n) omega)
      atTop (fun omega => -girsanovIntegratedDrift theta T r omega) :=
    TendstoInMeasure.continuous_comp hdriftMeas hdriftLim continuous_neg
  let realPart : ℝ → ℝ → ℂ := fun q t =>
    (q : ℂ) - (c ^ 2 * t : ℝ)
  have hrealPart : Continuous realPart.uncurry := by
    dsimp only [realPart, Function.uncurry]
    fun_prop
  have hrealLim : TendstoInMeasure P (fun n omega =>
      realPart (bracket (a n) omega) (a n : ℝ)) atTop
      (fun omega => realPart (bracket r omega) (r : ℝ)) :=
    TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun _ => aestronglyMeasurable_const)
      hbracketLim htimeLim hrealPart
  let addCross : ℂ → ℝ → ℂ := fun q d =>
    q + ((2 * c * d : ℝ) : ℂ) * Complex.I
  have haddCross : Continuous addCross.uncurry := by
    dsimp only [addCross, Function.uncurry]
    fun_prop
  have hQlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c (a n))
      atTop
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r) := by
    change TendstoInMeasure P (fun n omega =>
      addCross (realPart (bracket (a n) omega) (a n : ℝ))
        (-girsanovIntegratedDrift theta T (a n) omega)) atTop
      (fun omega => addCross (realPart (bracket r omega) (r : ℝ))
        (-girsanovIntegratedDrift theta T r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => (((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hdata.adapted_bracket (a n)).mono
          (V.le (a n))).aestronglyMeasurable)).sub
            (Complex.continuous_ofReal.comp_aestronglyMeasurable
              aestronglyMeasurable_const))))
      (fun n => hdriftMeas n |>.neg)
      hrealLim hClim haddCross
  let finish : ℂ → ℂ → ℂ := fun x q => Complex.exp (x - q / 2)
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  change TendstoInMeasure P (fun n omega =>
    finish (complexMartingaleCombination M B c (a n) omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c
          (a n) omega)) atTop
    (fun omega => finish (complexMartingaleCombination M B c r omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r omega))
  exact TendstoInMeasure.continuous_comp₂
    (fun n => ((stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hBadapt c (a n)).mono
          (V.le (a n))).aestronglyMeasurable)
    (fun n => ((stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket
        (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
          htheta T).neg c (a n)).mono
            (V.le (a n))).aestronglyMeasurable)
    hXlim hQlim hfinish

/-- The algebraic complex exponential stopped at the Girsanov horizon is
integrable.  Its modulus is a bounded deterministic multiple of the stopped
real density. -/
theorem GirsanovDensityData.integrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (t : ℝ≥0) :
    Integrable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P := by
  have hEadapt := stronglyAdapted_complexDoleansDadeExponential
    (stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hB c)
    (stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket hC c)
  have hmeas : AEStronglyMeasurable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P :=
    ((hEadapt (min t T)).mono (V.le (min t T))).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  let k : ℝ := Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2)
  have hrhs : Integrable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega * k) P :=
    (hdata.martingale_densityProcess.integrable t).mul_const k
  apply hrhs.congr
  exact Filter.Eventually.of_forall fun omega => by
    change doleansDadeExponential M bracket (min t T) omega * k =
      ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega‖
    simpa only [k] using
      (norm_complexDoleansDadeExponential_combination
        M bracket B C c (min t T) omega).symm

/-- The complete stopped complex-exponential family is uniformly
integrable.  This supplies the Vitali input for passing deterministic-grid
martingale identities to their continuous-time limit. -/
theorem
    GirsanovDensityData.uniformIntegrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C) (c : ℝ) :
    UniformIntegrable (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) 1 P := by
  have hdensityUI : UniformIntegrable (fun t omega =>
      doleansDadeExponential M bracket (min t T) omega) 1 P := by
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic
        hdata.martingale_densityProcess T)
      (fun t => ⟨min t T, by
        simpa only [Set.mem_Iic] using min_le_right t T⟩)
    simpa only [min_eq_left (min_le_right _ T)] using hUI
  obtain ⟨N, hN⟩ := exists_nat_ge
    (Real.exp (c ^ 2 * (T : ℝ) / 2))
  have hmultiple : UniformIntegrable (fun t omega =>
      N • doleansDadeExponential M bracket (min t T) omega) 1 P :=
    StochasticCalculus.UniformIntegrable.nsmul_banach hdensityUI (by norm_num) N
  apply StochasticCalculus.UniformIntegrable.mono_norm_banach hmultiple
  · intro t
    have hEadapt := stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hB c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
    exact ((hEadapt (min t T)).mono
      (V.le (min t T))).aestronglyMeasurable
  · intro t omega
    rw [norm_complexDoleansDadeExponential_combination]
    have htime : c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2 ≤
        c ^ 2 * (T : ℝ) / 2 := by
      have htime' : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast min_le_right t T
      nlinarith [sq_nonneg c]
    have hexp : Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := Real.exp_le_exp.mpr htime
    have hdensityPos :=
      doleansDadeExponential_pos M bracket (min t T) omega
    calc
      doleansDadeExponential M bracket (min t T) omega *
          Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
          doleansDadeExponential M bracket (min t T) omega *
            Real.exp (c ^ 2 * (T : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hexp hdensityPos.le
      _ ≤ doleansDadeExponential M bracket (min t T) omega * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hdensityPos.le
      _ = ‖N • doleansDadeExponential M bracket (min t T) omega‖ := by
        rw [nsmul_eq_mul, norm_mul, norm_natCast, Real.norm_eq_abs,
          abs_of_pos hdensityPos]
        ring

/-- At a fixed observation time, the increasing family of density-capped
complex Doléans targets is uniformly integrable.  This is the target-family
input for selecting one increasingly accurate Euler approximation per cap. -/
theorem
    GirsanovDensityData.uniformIntegrable_cappedComplexDoleansCombination_nat
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (t : ℝ≥0) :
    UniformIntegrable (fun (n : ℕ) omega =>
      cappedComplexDoleansDadeExponentialCombination
        M bracket B C c (n + 1) (min t T) omega) 1 P := by
  let E : W → ℂ := fun omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hconstant : UniformIntegrable (fun _n : ℕ => E) 1 P :=
    StochasticCalculus.UniformIntegrable.comp_index
      (hdata.uniformIntegrable_stopAt_complexDoleans_combination hB hC c)
      (fun _n : ℕ => t)
  let A : ℕ → W → ℂ := fun n omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c (n + 1) (min t T) omega
  have hA : UniformIntegrable A 1 P := by
    apply StochasticCalculus.UniformIntegrable.mono_norm_banach hconstant
    · intro n
      have hcap :=
        stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
          hdata.adapted_martingale hdata.adapted_bracket hB hC c (n + 1)
      exact ((hcap (min t T)).mono (V.le (min t T))).aestronglyMeasurable
    · intro n omega
      simpa only [A, E] using
        norm_cappedComplexDoleansDadeExponentialCombination_le_uncapped
          M bracket B C c (n + 1) (min t T) omega
  simpa only [A] using hA

/-- The increasing capped complex Doléans targets converge to the uncapped
target in `L¹`. -/
theorem
    GirsanovDensityData.tendsto_eLpNorm_one_complexDoleans_sub_capped_nat
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (t : ℝ≥0) :
    Tendsto (fun (n : ℕ) => eLpNorm
      ((fun omega => complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega) -
        fun omega => cappedComplexDoleansDadeExponentialCombination
          M bracket B C c (n + 1) (min t T) omega) 1 P)
      atTop (nhds 0) := by
  let A : ℕ → W → ℂ := fun n omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c (n + 1) (min t T) omega
  let E : W → ℂ := fun omega => complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
    (min t T) omega
  have hUI : UniformIntegrable A 1 P := by
    simpa only [A] using
      hdata.uniformIntegrable_cappedComplexDoleansCombination_nat hB hC c t
  have hmeasure : TendstoInMeasure P A atTop E := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact hUI.1
    · exact Filter.Eventually.of_forall fun omega => by
        have hraw :=
          (tendsto_cappedComplexDoleansDadeExponentialCombination_nat
            M bracket B C c (min t T) omega).comp
              (tendsto_add_atTop_nat 1)
        change Tendsto (fun n : ℕ =>
          cappedComplexDoleansDadeExponentialCombination
            M bracket B C c ((n : ℝ≥0) + 1) (min t T) omega)
          atTop (nhds (E omega))
        convert hraw using 1
        ext n
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hLp :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      hUI hmeasure
  convert hLp using 1
  ext n
  simpa only [A, E] using eLpNorm_sub_comm (E) (A n) 1 P

/-- Increasing-cap Euler martingales are uniformly integrable once their
`L¹` distance from the matching capped Doléans targets tends to zero.  Thus
the selected-grid UI obligation can be obtained by diagonal approximation,
rather than by a cap-dependent uniform `L²` bound. -/
theorem
    GirsanovDensityData.uniformIntegrable_cappedComplexGirsanovEulerProcess_of_targetL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C) (c : ℝ)
    (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ)
    (hN : ∀ n, Martingale (N n) V P) (t : ℝ≥0)
    (hclose : Tendsto (fun n => eLpNorm
      (cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (q n + 1) t -
        fun omega => cappedComplexDoleansDadeExponentialCombination
          M bracket B C c (n + 1) (min t T) omega) 1 P)
      atTop (nhds 0)) :
    UniformIntegrable (fun n =>
      cappedComplexGirsanovEulerProcess
        (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P := by
  let A : ℕ → W → ℂ := fun n =>
    cappedComplexGirsanovEulerProcess
      (N n) M bracket B C c (n + 1) T (q n + 1) t
  let G : ℕ → W → ℂ := fun n omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c (n + 1) (min t T) omega
  have hG : UniformIntegrable G 1 P := by
    simpa only [G] using
      hdata.uniformIntegrable_cappedComplexDoleansCombination_nat
        hBadapt hC c t
  apply UniformIntegrable.of_tendsto_eLpNorm_one_sub hG
  · intro n
    apply memLp_one_iff_integrable.mpr
    exact (martingale_cappedComplexGirsanovEulerProcess
      (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
        hBadapt hC c (n + 1) T (q n + 1)).integrable t
  · simpa only [A, G] using hclose

/-- Stochastic continuity of the algebraic complex exponential is preserved
when its time parameter is stopped at the deterministic Girsanov horizon. -/
theorem
    GirsanovDensityData.tendstoInMeasure_stopAt_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min (a n) T)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min r T)) := by
  exact hdata.tendstoInMeasure_complexDoleans_neg_integratedDrift
    hB hsm hBadapt htheta hbracketTerminal hcross c
      (ha.min tendsto_const_nhds)

/-- Eventwise martingale identities for the stopped algebraic complex
Doléans family, tested only at positive rational subdivisions.  This is the
exact deterministic-grid statement left to the stochastic Taylor argument. -/
def GirsanovStoppedComplexDoleansRationalCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (U : ℝ≥0) {k j : ℕ},
    0 < k → 0 < j → j ≤ k → ∀ {A : Set W},
    MeasurableSet[V (U * (j : ℝ≥0) / (k : ℝ≥0))] A →
      (∫ omega in A, complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
          (min (U * (j : ℝ≥0) / (k : ℝ≥0)) T) omega ∂P) =
        ∫ omega in A, complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
            (min U T) omega ∂P

/-- Rational-grid identities promote the stopped algebraic complex
exponential to a genuine martingale.  All limiting inputs are derived from
the predictable Girsanov contract. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_rational
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hrational : GirsanovStoppedComplexDoleansRationalCondition P V
      M bracket B
        (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u omega => -girsanovIntegratedDrift theta T u omega) c)
        (min t T) omega) V P := by
  intro c
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hC : StronglyAdapted V C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T).neg
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  apply
    martingale_of_uniformRational_setIntegral_eq_of_tendstoInMeasure_of_uniformIntegrable
      hE
  · intro t
    exact hdata.integrable_stopAt_complexDoleans_combination
      hBadapt hC c t
  · intro r a ha
    exact hdata.tendstoInMeasure_stopAt_complexDoleans_neg_integratedDrift
      hB hsm hBadapt htheta hbracketTerminal hcross c ha
  · intro _r a _ha
    exact StochasticCalculus.UniformIntegrable.comp_index
      (hdata.uniformIntegrable_stopAt_complexDoleans_combination
        hBadapt hC c) a
  · simpa only [E, C] using hrational c

/-- The remaining stochastic Taylor obligation in its most concrete form:
for every density cap and Fourier frequency, genuine two-integrator Euler
martingales converge in `L¹` to the capped complex exponential. -/
def GirsanovCappedComplexEulerL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (R : ℝ≥0),
    ∃ N : ℕ → ℝ≥0 → W → ℝ,
      (∀ n, Martingale (N n) V P) ∧
      ∀ t, Tendsto (fun n => eLpNorm
        ((fun omega =>
          cappedComplexDoleansDadeExponentialCombination
            M bracket B C c R (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c R T (n + 1) t) 1 P)
        atTop (nhds 0)

/-- The viable diagonal complex-Euler obligation: the density cap grows
together with the uniform grid, and the martingale approximants converge
directly to the uncapped complex stochastic exponential.  In contrast to a
fixed-cap target, this condition does not require `min (E_t) R` itself to be
a martingale. -/
def GirsanovDiagonalComplexEulerL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ,
    ∃ N : ℕ → ℝ≥0 → W → ℝ,
      (∀ n, Martingale (N n) V P) ∧
      ∀ t, Tendsto (fun n => eLpNorm
        ((fun omega =>
          complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (n + 1) t) 1 P)
        atTop (nhds 0)

/-- The cofinal selected-grid version of the viable increasing-cap Euler
obligation.  The cap grows with the outer index, while the positive uniform
grid count may follow any cofinal sequence (and may depend on the Fourier
frequency). -/
def GirsanovSelectedComplexEulerL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ,
    ∃ (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ),
      Tendsto q atTop atTop ∧
      (∀ n, Martingale (N n) V P) ∧
      ∀ t, Tendsto (fun n => eLpNorm
        ((fun omega =>
          complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P)
        atTop (nhds 0)

/-- Pairwise selected-grid Euler closure.  The grid and martingale
approximants may depend on the ordered pair `s ≤ t`; this is exactly the
quantifier strength used by the martingale identity, and is weaker than one
selector converging at every time simultaneously. -/
def GirsanovPairwiseSelectedComplexEulerL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (s t : ℝ≥0), s ≤ t →
    ∃ (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ),
      Tendsto q atTop atTop ∧
      (∀ n, Martingale (N n) V P) ∧
      Tendsto (fun (n : ℕ) => eLpNorm
        ((fun omega => complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min s T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (q n + 1) s) 1 P)
        atTop (nhds 0) ∧
      Tendsto (fun (n : ℕ) => eLpNorm
        ((fun omega => complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P)
        atTop (nhds 0)

/-- The pairwise selected-grid obligation with the moving capped Doléans
target exposed.  This is the weakest constructive increasing-cap frontier:
only the two times entering a martingale identity share a selector. -/
def GirsanovPairwiseSelectedComplexEulerTargetL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (s t : ℝ≥0), s ≤ t →
    ∃ (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ),
      Tendsto q atTop atTop ∧
      (∀ n, Martingale (N n) V P) ∧
      Tendsto (fun (n : ℕ) => eLpNorm
        ((fun omega => cappedComplexDoleansDadeExponentialCombination
            M bracket B C c (n + 1) (min s T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (q n + 1) s) 1 P)
        atTop (nhds 0) ∧
      Tendsto (fun (n : ℕ) => eLpNorm
        ((fun omega => cappedComplexDoleansDadeExponentialCombination
            M bracket B C c (n + 1) (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P)
        atTop (nhds 0)

/-- A quantitative form of the minimal pairwise moving-target frontier.
For cap `n + 1`, one may choose the Euler grid finely enough that its `L¹`
error at both times in the martingale identity is at most `(n + 1)⁻¹`.
This is the concrete error budget that an analytic construction can target. -/
def GirsanovPairwiseSelectedComplexEulerRateL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (s t : ℝ≥0), s ≤ t →
    ∃ (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ),
      Tendsto q atTop atTop ∧
      (∀ n, Martingale (N n) V P) ∧
      ∀ n : ℕ,
        eLpNorm
          ((fun omega => cappedComplexDoleansDadeExponentialCombination
              M bracket B C c (n + 1) (min s T) omega) -
            cappedComplexGirsanovEulerProcess
              (N n) M bracket B C c (n + 1) T (q n + 1) s) 1 P
            ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞) ∧
        eLpNorm
          ((fun omega => cappedComplexDoleansDadeExponentialCombination
              M bracket B C c (n + 1) (min t T) omega) -
            cappedComplexGirsanovEulerProcess
              (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P
            ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞)

/-- A one-cap-at-a-time sufficient condition for the quantitative pairwise
frontier.  At cap `n + 1`, the analyst only has to exhibit one martingale
integrator and one grid index `m ≥ n` meeting the two endpoint bounds;
classical choice packages these finite obligations into a cofinal diagonal. -/
def GirsanovPairwiseFiniteComplexEulerRateL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (s t : ℝ≥0), s ≤ t → ∀ n : ℕ,
    ∃ (m : ℕ) (N : ℝ≥0 → W → ℝ),
      n ≤ m ∧ Martingale N V P ∧
      eLpNorm
        ((fun omega => cappedComplexDoleansDadeExponentialCombination
            M bracket B C c (n + 1) (min s T) omega) -
          cappedComplexGirsanovEulerProcess
            N M bracket B C c (n + 1) T (m + 1) s) 1 P
          ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞) ∧
      eLpNorm
        ((fun omega => cappedComplexDoleansDadeExponentialCombination
            M bracket B C c (n + 1) (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            N M bracket B C c (n + 1) T (m + 1) t) 1 P
          ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞)

/-- The flexible-cap finite approximation frontier.  For each error budget,
the density cap is chosen together with the martingale integrator and grid.
The bounds are stated directly against the uncapped complex exponential.
This avoids imposing a universal tail rate at the fixed cap `n + 1`, which
does not follow from uniform integrability alone. -/
def GirsanovPairwiseFiniteComplexEulerDirectRateL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (s t : ℝ≥0), s ≤ t → ∀ n : ℕ,
    ∃ (R : ℝ≥0) (m : ℕ) (N : ℝ≥0 → W → ℝ),
      n ≤ m ∧ Martingale N V P ∧
      eLpNorm
        ((fun omega => complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min s T) omega) -
          cappedComplexGirsanovEulerProcess
            N M bracket B C c R T (m + 1) s) 1 P
          ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞) ∧
      eLpNorm
        ((fun omega => complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min t T) omega) -
          cappedComplexGirsanovEulerProcess
            N M bracket B C c R T (m + 1) t) 1 P
          ≤ (((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0∞)

/-- Independent finite-cap choices with `m ≥ n` assemble into the
cofinal quantitative pairwise Euler diagonal. -/
theorem girsanovPairwiseSelectedComplexEulerRateL1Condition_of_finite
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovPairwiseFiniteComplexEulerRateL1Condition
      P V M bracket B C T) :
    GirsanovPairwiseSelectedComplexEulerRateL1Condition
      P V M bracket B C T := by
  intro c s t hst
  choose q N hqn hN hbound using fun n => h c s t hst n
  refine ⟨q, N, ?_, hN, hbound⟩
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun a hba => hba.trans (hqn a)⟩

/-- The explicit inverse-natural error budget implies pairwise `L¹`
convergence to the matching moving capped targets. -/
theorem girsanovPairwiseSelectedComplexEulerTargetL1Condition_of_rateL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovPairwiseSelectedComplexEulerRateL1Condition
      P V M bracket B C T) :
    GirsanovPairwiseSelectedComplexEulerTargetL1Condition
      P V M bracket B C T := by
  intro c s t hst
  obtain ⟨q, N, hq, hN, hbound⟩ := h c s t hst
  have hrate : Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞))
      atTop (nhds 0) := by
    apply ENNReal.tendsto_coe.2
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine ⟨q, N, hq, hN, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hrate (fun _ => zero_le) ?_
    intro n
    have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    exact (hbound n).1.trans_eq (ENNReal.coe_inv hn).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hrate (fun _ => zero_le) ?_
    intro n
    have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    exact (hbound n).2.trans_eq (ENNReal.coe_inv hn).symm

/-- Pairwise convergence to the moving capped targets implies pairwise
convergence to the uncapped complex Doléans exponential. -/
theorem girsanovPairwiseSelectedComplexEulerL1Condition_of_targetL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (h : GirsanovPairwiseSelectedComplexEulerTargetL1Condition
      P V M bracket B C T) :
    GirsanovPairwiseSelectedComplexEulerL1Condition
      P V M bracket B C T := by
  intro c s t hst
  obtain ⟨q, N, hq, hN, hcloseS, hcloseT⟩ := h c s t hst
  refine ⟨q, N, hq, hN, ?_, ?_⟩
  · let E : W → ℂ := fun omega => complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min s T) omega
    let G : ℕ → W → ℂ := fun n omega =>
      cappedComplexDoleansDadeExponentialCombination
        M bracket B C c (n + 1) (min s T) omega
    let A : ℕ → W → ℂ := fun n =>
      cappedComplexGirsanovEulerProcess
        (N n) M bracket B C c (n + 1) T (q n + 1) s
    apply tendsto_eLpNorm_one_sub_of_chain
      (f := fun _n => E) (g := G) (h := A)
    · intro _n
      exact (hdata.integrable_stopAt_complexDoleans_combination
        hBadapt hC c s).1
    · exact (hdata.uniformIntegrable_cappedComplexDoleansCombination_nat
        hBadapt hC c s).1
    · intro n
      exact ((martingale_cappedComplexGirsanovEulerProcess
        (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
          hBadapt hC c (n + 1) T (q n + 1)).stronglyMeasurable s).mono
            (V.le s) |>.aestronglyMeasurable
    · simpa only [E, G] using
        hdata.tendsto_eLpNorm_one_complexDoleans_sub_capped_nat
          hBadapt hC c s
    · simpa only [G, A] using hcloseS
  · let E : W → ℂ := fun omega => complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
    let G : ℕ → W → ℂ := fun n omega =>
      cappedComplexDoleansDadeExponentialCombination
        M bracket B C c (n + 1) (min t T) omega
    let A : ℕ → W → ℂ := fun n =>
      cappedComplexGirsanovEulerProcess
        (N n) M bracket B C c (n + 1) T (q n + 1) t
    apply tendsto_eLpNorm_one_sub_of_chain
      (f := fun _n => E) (g := G) (h := A)
    · intro _n
      exact (hdata.integrable_stopAt_complexDoleans_combination
        hBadapt hC c t).1
    · exact (hdata.uniformIntegrable_cappedComplexDoleansCombination_nat
        hBadapt hC c t).1
    · intro n
      exact ((martingale_cappedComplexGirsanovEulerProcess
        (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
          hBadapt hC c (n + 1) T (q n + 1)).stronglyMeasurable t).mono
            (V.le t) |>.aestronglyMeasurable
    · simpa only [E, G] using
        hdata.tendsto_eLpNorm_one_complexDoleans_sub_capped_nat
          hBadapt hC c t
    · simpa only [G, A] using hcloseT

/-- Vitali-ready selected-grid Euler data.  It separates convergence of the
uncapped selected sums from uniform integrability of their increasing-cap
martingale counterparts. -/
def GirsanovSelectedComplexEulerInMeasureUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ,
    ∃ (q : ℕ → ℕ) (N : ℕ → ℝ≥0 → W → ℝ),
      Tendsto q atTop atTop ∧
      (∀ n, Martingale (N n) V P) ∧
      (∀ t, UniformIntegrable (fun n =>
        cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (q n + 1) t) 1 P) ∧
      ∀ t, TendstoInMeasure P (fun n =>
        complexGirsanovEulerProcess
          (N n) M bracket B C c T (q n + 1) t) atTop
        (fun omega =>
          complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (min t T) omega)

/-- Common local quadratic variation bundled with the UI obligation along
every cofinal selected grid.  A strict localizer subsequence may be chosen to
match that grid without changing its cells. -/
def GirsanovSelectedComplexEulerLocalQVUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      ∀ (c : ℝ) (q : ℕ → ℕ), Tendsto q atTop atTop →
        ∃ l : ℕ → ℕ, StrictMono l ∧ ∀ t,
          UniformIntegrable (fun n =>
            cappedComplexGirsanovEulerProcess
              (localizingStoppedProcess M (tau (l n)))
              M bracket B C c (n + 1) T (q n + 1) t) 1 P

/-- A constructive replacement for the selected-grid UI premise.  For each
cofinal grid, one chooses a strict localizer subsequence whose increasing-cap
Euler martingales approach the corresponding capped Doléans targets in
`L¹`; uniform integrability then follows from Novikov domination. -/
def GirsanovSelectedComplexEulerLocalQVTargetL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      ∀ (c : ℝ) (q : ℕ → ℕ), Tendsto q atTop atTop →
        ∃ l : ℕ → ℕ, StrictMono l ∧ ∀ t,
          Tendsto (fun n => eLpNorm
            (cappedComplexGirsanovEulerProcess
                (localizingStoppedProcess M (tau (l n)))
                M bracket B C c (n + 1) T (q n + 1) t -
              fun omega => cappedComplexDoleansDadeExponentialCombination
                M bracket B C c (n + 1) (min t T) omega) 1 P)
            atTop (nhds 0)

/-- Increasingly accurate approximation of the capped targets discharges
the selected local-QV uniform-integrability condition. -/
theorem
    girsanovSelectedComplexEulerLocalQVUICondition_of_targetL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (h : GirsanovSelectedComplexEulerLocalQVTargetL1Condition
      P V M bracket B C T) :
    GirsanovSelectedComplexEulerLocalQVUICondition
      P V M bracket B C T := by
  obtain ⟨tau, htau, hmart, hqv, hclose⟩ := h
  refine ⟨tau, htau, hmart, hqv, ?_⟩
  intro c q hq
  obtain ⟨l, hl, hL1⟩ := hclose c q hq
  refine ⟨l, hl, fun t => ?_⟩
  exact
    hdata.uniformIntegrable_cappedComplexGirsanovEulerProcess_of_targetL1
      hBmart hBadapt hC c q
      (fun n => localizingStoppedProcess M (tau (l n)))
      (fun n => hmart (l n)) t (hL1 t)

/-- The all-time local capped-target condition directly supplies the weaker
pairwise moving-target condition.  The local quadratic-variation fields are
retained for construction but are not needed by this projection. -/
theorem
    girsanovPairwiseSelectedComplexEulerTargetL1Condition_of_localQVTargetL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovSelectedComplexEulerLocalQVTargetL1Condition
      P V M bracket B C T) :
    GirsanovPairwiseSelectedComplexEulerTargetL1Condition
      P V M bracket B C T := by
  obtain ⟨tau, _htau, hmart, _hqv, hclose⟩ := h
  intro c s t _hst
  obtain ⟨l, _hl, hL1⟩ := hclose c id tendsto_id
  refine ⟨id, (fun n => localizingStoppedProcess M (tau (l n))),
    tendsto_id, (fun n => hmart (l n)), ?_, ?_⟩
  · convert hL1 s using 1
    ext n
    simpa only [id_eq] using eLpNorm_sub_comm
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c (n + 1) (min s T))
      (cappedComplexGirsanovEulerProcess
        (localizingStoppedProcess M (tau (l n)))
        M bracket B C c (n + 1) T (n + 1) s) 1 P
  · convert hL1 t using 1
    ext n
    simpa only [id_eq] using eLpNorm_sub_comm
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c (n + 1) (min t T))
      (cappedComplexGirsanovEulerProcess
        (localizingStoppedProcess M (tau (l n)))
        M bracket B C c (n + 1) T (n + 1) t) 1 P

/-- Cap disappearance and Vitali promote selected-grid convergence data to
the selected `L¹` condition used by martingale closure. -/
theorem girsanovSelectedComplexEulerL1Condition_of_inMeasure_UI
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hconv : GirsanovSelectedComplexEulerInMeasureUICondition
      P V M bracket B C T) :
    GirsanovSelectedComplexEulerL1Condition P V M bracket B C T := by
  intro c
  obtain ⟨q, N, hq, hN, hUI, hplain⟩ := hconv c
  refine ⟨q, N, hq, hN, fun t => ?_⟩
  let A : ℕ → W → ℂ := fun n =>
    cappedComplexGirsanovEulerProcess
      (N n) M bracket B C c (n + 1) T (q n + 1) t
  let U : ℕ → W → ℂ := fun n =>
    complexGirsanovEulerProcess
      (N n) M bracket B C c T (q n + 1) t
  let E : W → ℂ := fun omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hcap : TendstoInMeasure P (fun n => A n - U n) atTop
      (fun _ => 0) := by
    change TendstoInMeasure P (fun n omega =>
      cappedComplexGirsanovEulerProcess
          (N n) M bracket B C c (n + 1) T (q n + 1) t omega -
        complexGirsanovEulerProcess
          (N n) M bracket B C c T (q n + 1) t omega)
      atTop (fun _ => 0)
    exact tendstoInMeasure_cappedComplexGirsanovEulerProcess_sub_complex_counts
      (fun n => (hN n).stronglyAdapted)
      hdata.adapted_martingale hdata.adapted_bracket hBadapt hC
      (Filter.Eventually.of_forall hdata.continuous_martingale_path)
      (Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_monotone_bracket omega).1) c T t
  have hAmeas (n : ℕ) : AEStronglyMeasurable (A n) P :=
    (hUI t).1 n
  have hUmeas (n : ℕ) : AEStronglyMeasurable (U n) P := by
    exact ((stronglyAdapted_complexGirsanovEulerProcess
      (hN n).stronglyAdapted hdata.adapted_martingale
      hdata.adapted_bracket hBadapt hC c T (q n + 1) t).mono
        (V.le t)).aestronglyMeasurable
  have hsum := TendstoInMeasure.continuous_comp₂
    (fun n => (hAmeas n).sub (hUmeas n)) hUmeas hcap
      (by simpa only [U, E] using hplain t)
      (by fun_prop : Continuous (Function.uncurry (fun x y : ℂ => x + y)))
  have hmeasure : TendstoInMeasure P A atTop E := by
    apply hsum.congr
    · intro n
      exact Filter.Eventually.of_forall fun omega => by
        simp only [Pi.sub_apply]; ring_nf
    · exact Filter.Eventually.of_forall fun omega => by
        dsimp only [E]; simp only [zero_add]
  have hLp :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (by simpa only [A] using hUI t) hmeasure
  convert hLp using 1
  ext n
  simpa only [A, E] using (eLpNorm_sub_comm (A n) E 1 P).symm

/-- Canonical form of the Euler convergence obligation, using a diagonal
through one explicit localizing sequence for `M`. -/
def GirsanovCappedComplexEulerLocalizingL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ (c : ℝ) (R : ℝ≥0),
    ∃ l : ℕ → ℕ, ∀ t, Tendsto (fun n => eLpNorm
      ((fun omega =>
        cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R (min t T) omega) -
        cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c R T (n + 1) t) 1 P)
      atTop (nhds 0)

/-- Canonical localizer form of the diagonal complex-Euler obligation.  A
single subsequence selects the genuine martingale integrator used on each
increasing-cap grid. -/
def GirsanovDiagonalComplexEulerLocalizingL1Condition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ c : ℝ,
    ∃ l : ℕ → ℕ, ∀ t, Tendsto (fun n => eLpNorm
      ((fun omega =>
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega) -
        cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c (n + 1) T (n + 1) t) 1 P)
      atTop (nhds 0)

/-- Vitali-ready form of the viable diagonal Euler obligation.  It separates
the genuine stochastic-Taylor assertion for the uncapped sums (convergence
in probability) from the moment assertion for the increasing-cap martingale
sums (uniform integrability). -/
def GirsanovDiagonalComplexEulerLocalizingInMeasureUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ c : ℝ, ∃ l : ℕ → ℕ,
    (∀ t, UniformIntegrable (fun n =>
      cappedComplexGirsanovEulerProcess
        (localizingStoppedProcess M (tau (l n)))
        M bracket B C c (n + 1) T (n + 1) t) 1 P) ∧
    ∀ t, TendstoInMeasure P (fun n =>
      complexGirsanovEulerProcess
        (localizingStoppedProcess M (tau (l n)))
        M bracket B C c T (n + 1) t) atTop
      (fun omega =>
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega)

/-- The localization-free stochastic-Taylor obligation for the complex
Girsanov exponential. -/
def GirsanovComplexEulerInMeasureCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexGirsanovEulerProcess M M bracket B C c T (n + 1) t) atTop
    (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega)

/-- The exact stochastic-Taylor remainder obligation behind complex
Girsanov Euler convergence.  Unlike a capped target, this condition only
asks that the canonical one-step Doléans residuals vanish in probability. -/
def GirsanovComplexDoleansEulerResidualCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansEulerResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- Cofinal selected-grid form of the exact residual obligation.  The grid
selector may depend on the Fourier frequency, matching the polynomial
diagonals produced by the path-regularity-free Brownian estimates. -/
def GirsanovSelectedComplexDoleansEulerResidualCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ, ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
    ∀ t : ℝ≥0, TendstoInMeasure P (fun n =>
      complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q n + 1) t) atTop (fun _ => 0)

/-- Selected-grid convergence of the self-integrator uncapped complex Euler
sums. -/
def GirsanovSelectedComplexEulerSelfInMeasureCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ, ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
    ∀ t : ℝ≥0, TendstoInMeasure P (fun n =>
      complexGirsanovEulerProcess
        M M bracket B C c T (q n + 1) t) atTop
      (fun omega =>
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega)

/-- A vanishing selected canonical residual is equivalent to the needed
self-integrator Euler convergence along that selected grid. -/
theorem girsanovSelectedComplexEulerSelfInMeasureCondition_of_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hres : GirsanovSelectedComplexDoleansEulerResidualCondition
      P M bracket B C T) :
    GirsanovSelectedComplexEulerSelfInMeasureCondition
      P M bracket B C T := by
  intro c
  obtain ⟨q, hq, hresq⟩ := hres c
  refine ⟨q, hq, fun t => ?_⟩
  have hcanonical : TendstoInMeasure P (fun n =>
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q n + 1) t) atTop
      (fun omega =>
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega) := by
    have hlimit := hresq t
    rw [tendstoInMeasure_iff_norm] at hlimit ⊢
    intro epsilon hepsilon
    have hlimit' := hlimit epsilon hepsilon
    have hmeasureFun :
        (fun n => P {omega | epsilon ≤
          ‖complexDoleansEulerProcess
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                T (q n + 1) t omega -
              complexDoleansDadeExponential
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                (min t T) omega‖}) =
        (fun n => P {omega | epsilon ≤
          ‖complexDoleansEulerResidualApprox
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                T (q n + 1) t omega - 0‖}) := by
      funext n
      congr 1
      ext omega
      simp only [Set.mem_ofPred_eq, sub_zero]
      rw [← complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual]
      rw [norm_sub_rev]
    rw [hmeasureFun]
    exact hlimit'
  apply hcanonical.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (congrFun (congrFun
      (complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
        M bracket B C c T (q n + 1)) t) omega).symm

/-- Selected self-Euler convergence and matching common-localizer UI data
produce the Vitali-ready selected martingale approximation. -/
theorem girsanovSelectedComplexEulerInMeasureUICondition_of_localQVUI_of_self
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hUI : GirsanovSelectedComplexEulerLocalQVUICondition
      P V M bracket B C T)
    (hself : GirsanovSelectedComplexEulerSelfInMeasureCondition
      P M bracket B C T) :
    GirsanovSelectedComplexEulerInMeasureUICondition
      P V M bracket B C T := by
  obtain ⟨tau, htau, hmart, _hqv, hlocalUI⟩ := hUI
  intro c
  obtain ⟨q, hq, hselfq⟩ := hself c
  obtain ⟨l, hl, hselectedUI⟩ := hlocalUI c q hq
  let tau' : ℕ → W → WithTop ℝ≥0 := fun n => tau (l n)
  have htau' : IsLocalizingSequence V tau' P := by
    exact
      { isStoppingTime := fun n => htau.isStoppingTime (l n)
        tendsto_top := by
          filter_upwards [htau.tendsto_top] with omega homega
          exact homega.comp hl.tendsto_atTop
        mono := by
          filter_upwards [htau.mono] with omega homega
          exact homega.comp hl.monotone }
  refine ⟨q, fun n => localizingStoppedProcess M (tau' n), hq,
    fun n => hmart (l n), ?_, ?_⟩
  · intro t
    simpa only [tau'] using hselectedUI t
  · intro t
    let L : ℕ → W → ℂ := fun n =>
      complexGirsanovEulerProcess
        (localizingStoppedProcess M (tau' n))
        M bracket B C c T (q n + 1) t
    let S : ℕ → W → ℂ := fun n =>
      complexGirsanovEulerProcess M M bracket B C c T (q n + 1) t
    let E : W → ℂ := fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega
    have hdiff : TendstoInMeasure P (fun n => L n - S n) atTop
        (fun _ => 0) := by
      change TendstoInMeasure P (fun n omega =>
        complexGirsanovEulerProcess
            (localizingStoppedProcess M (tau' n))
            M bracket B C c T (q n + 1) t omega -
          complexGirsanovEulerProcess
            M M bracket B C c T (q n + 1) t omega)
        atTop (fun _ => 0)
      exact
        tendstoInMeasure_complexGirsanovEulerProcess_localizing_sub_self_counts
          htau' hdata.adapted_martingale
          hdata.continuous_martingale_path hdata.adapted_bracket
          hB hC c T t
    have hsum := TendstoInMeasure.add_normed_noMeas hdiff
      (by simpa only [S, E] using hselfq t)
    apply hsum.congr
    · intro n
      exact Filter.Eventually.of_forall fun omega => by
        simp only [Pi.sub_apply, L, S]; ring_nf
    · exact Filter.Eventually.of_forall fun omega => by
        dsimp only [E]; simp only [zero_add]

/-- The second-order half of the canonical stochastic-Taylor obligation:
the complex squared increments, weighted by the left exponential, converge
to the correspondingly weighted proposed bracket increments. -/
def GirsanovComplexDoleansWeightedBracketCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n omega =>
    (1 / 2 : ℂ) * complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t omega) atTop (fun _ => 0)

/-- The genuinely higher-order half of the canonical stochastic-Taylor
obligation.  Its one-cell summands satisfy
`norm_complexDoleansSecondOrderResidual_le`. -/
def GirsanovComplexDoleansHigherOrderCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- A scalar-majorant formulation of the higher-order stochastic-Taylor
obligation.  It exposes only the explicit nonnegative cellwise bound. -/
def GirsanovComplexDoleansHigherOrderBoundCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualBoundApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- Convergence in measure of the explicit nonnegative majorant closes the
complex higher-order residual. -/
theorem girsanovComplexDoleansHigherOrderCondition_of_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovComplexDoleansHigherOrderBoundCondition
      P M bracket B C T) :
    GirsanovComplexDoleansHigherOrderCondition P M bracket B C T := by
  intro c t
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas (h c t)
  · exact fun n omega =>
      complexDoleansHigherOrderResidualBoundApprox_nonneg
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega
  · exact fun n omega =>
      norm_complexDoleansHigherOrderResidualApprox_le_bound
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega

/-- The Challenge hypotheses discharge the entire higher-order half of the
complex stochastic-Taylor obligation. -/
theorem GirsanovDensityData.girsanovComplexDoleansHigherOrderBoundCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) :
    GirsanovComplexDoleansHigherOrderBoundCondition P M bracket B
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z) T := by
  intro c t
  exact
    hdata.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
      hB hBmeas htheta hbracketTerminal c t

/-- The synchronized terminal bracket diagonal and the all-grid higher-order
estimate close the exact canonical Doleans Euler residual at time `T`. -/
theorem
    GirsanovDensityData.exists_girsanovComplexDoleansEulerResidual_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hT : 0 < T) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega ↦ -regularizedGirsanovIntegratedDrift
            bracket theta T t omega) c)
        T (q r + 1) T) atTop (fun _ ↦ 0) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  obtain ⟨n, _hn, hbracket⟩ :=
    hdata.exists_polynomial_diagonal_girsanovWeightedBracketResidual_terminal
      hB hsm htheta hbracketTerminal hcross c hT
  let N : ℕ → ℕ := fun r ↦
    ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)
  have hN : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  let q : ℕ → ℕ := fun r ↦ N r - 1
  have hqadd : ∀ r, q r + 1 = N r := fun r ↦ by
    dsimp only [q]
    exact Nat.sub_add_cancel (hN r)
  have hq : Tendsto q atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ N a := by
      dsimp only [N]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    exact hba.trans (Nat.le_sub_one_of_lt ((Nat.lt_succ_self a).trans_le
      (hbase.trans hmul)))
  have hbracketq : TendstoInMeasure P (fun r ↦
      complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q r + 1) T) atTop (fun _ ↦ 0) := by
    simpa only [C, hqadd, N] using hbracket
  have hbracketHalf :=
    TendstoInMeasure.const_mul_complex_noMeas hbracketq (1 / 2 : ℂ)
  have hhigherAll : GirsanovComplexDoleansHigherOrderCondition
      P M bracket B C T :=
    girsanovComplexDoleansHigherOrderCondition_of_bound
      (hdata.girsanovComplexDoleansHigherOrderBoundCondition
        hB hsm htheta hbracketTerminal)
  have hhigher := (hhigherAll c T).comp hq
  have hsum := TendstoInMeasure.add_normed_noMeas hbracketHalf hhigher
  refine ⟨q, hq, ?_⟩
  have hsum' : TendstoInMeasure P (fun r omega ↦
      (1 / 2 : ℂ) * complexDoleansWeightedBracketResidualApprox
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          T (q r + 1) T omega +
        complexDoleansHigherOrderResidualApprox
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          T (q r + 1) T omega) atTop (fun _ ↦ 0) := by
    simpa only [Function.comp_apply, mul_zero, zero_add] using hsum
  apply hsum'.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦
    (complexDoleansEulerResidualApprox_eq_secondOrder
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (q r) T omega).symm

/-- Under the Challenge hypotheses, the canonical self-integrator complex
Euler sums converge in probability to the exact Doléans exponential at the
terminal horizon along a cofinal grid. -/
theorem
    GirsanovDensityData.exists_girsanovComplexEulerSelf_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hT : 0 < T) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexGirsanovEulerProcess
        M M bracket B
        (fun t omega ↦ -regularizedGirsanovIntegratedDrift
          bracket theta T t omega)
        c T (q r + 1) T) atTop (fun omega ↦
          complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket
              (fun t omega ↦ -regularizedGirsanovIntegratedDrift
                bracket theta T t omega) c)
            T omega) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦
    -regularizedGirsanovIntegratedDrift bracket theta T t omega
  let E : W → ℂ := fun omega ↦
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) T omega
  obtain ⟨q, hq, hres⟩ :=
    hdata.exists_girsanovComplexDoleansEulerResidual_terminal
      hB hsm htheta hbracketTerminal hcross c hT
  have hresC : TendstoInMeasure P (fun r ↦
      complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q r + 1) T) atTop (fun _ ↦ 0) := by
    simpa only [C] using hres
  have hconst : TendstoInMeasure P (fun _r : ℕ ↦ E) atTop E := by
    rw [tendstoInMeasure_iff_norm]
    intro epsilon hepsilon
    simpa only [sub_self, norm_zero, not_le.mpr hepsilon,
      Set.ofPred_false, measure_empty] using
        (tendsto_const_nhds : Tendsto (fun _r : ℕ ↦ (0 : ℝ≥0∞))
          atTop (nhds 0))
  have hEuler := TendstoInMeasure.sub_normed_noMeas hconst hresC
  refine ⟨q, hq, ?_⟩
  have hcanonical : TendstoInMeasure P (fun r ↦
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q r + 1) T) atTop E := by
    apply hEuler.congr
    · intro r
      exact Filter.Eventually.of_forall fun omega ↦ by
        change E omega - complexDoleansEulerResidualApprox
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            T (q r + 1) T omega =
          complexDoleansEulerProcess
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            T (q r + 1) T omega
        rw [← complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual]
        simp only [E, min_self]
        abel
    · exact Filter.Eventually.of_forall fun omega ↦ by
        dsimp only [E]
        ring
  apply hcanonical.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦
    (congrFun (congrFun
      (complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
        M bracket B C c T (q r + 1)) T) omega).symm

/-- The cofinal selected-grid second-order frontier, with one selector shared
by the weighted bracket cancellation and higher-order mesh remainder. -/
def GirsanovSelectedComplexDoleansSecondOrderCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ c : ℝ, ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
    (∀ t : ℝ≥0, TendstoInMeasure P (fun n omega =>
      (1 / 2 : ℂ) * complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q n + 1) t omega) atTop (fun _ => 0)) ∧
    ∀ t : ℝ≥0, TendstoInMeasure P (fun n =>
      complexDoleansHigherOrderResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (q n + 1) t) atTop (fun _ => 0)

/-- The selected second-order frontier implies the exact selected Euler
residual condition. -/
theorem girsanovSelectedComplexDoleansEulerResidualCondition_of_secondOrder
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovSelectedComplexDoleansSecondOrderCondition
      P M bracket B C T) :
    GirsanovSelectedComplexDoleansEulerResidualCondition
      P M bracket B C T := by
  intro c
  obtain ⟨q, hq, hbracket, hhigher⟩ := h c
  refine ⟨q, hq, fun t => ?_⟩
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  have hsum : TendstoInMeasure P (fun n omega =>
      (1 / 2 : ℂ) *
          complexDoleansWeightedBracketResidualApprox
            X Q T (q n + 1) t omega +
        complexDoleansHigherOrderResidualApprox
          X Q T (q n + 1) t omega) atTop (fun _ => 0) := by
    simpa only [X, Q, zero_add] using
      TendstoInMeasure.add_normed_noMeas (hbracket t) (hhigher t)
  apply hsum.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (complexDoleansEulerResidualApprox_eq_secondOrder
      X Q T (q n) t omega).symm

/-- Weighted bracket convergence and the higher-order mesh estimate combine
to give the exact canonical Doléans residual condition. -/
theorem girsanovComplexDoleansEulerResidualCondition_of_secondOrder
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hbracket : GirsanovComplexDoleansWeightedBracketCondition
      P M bracket B C T)
    (hhigher : GirsanovComplexDoleansHigherOrderCondition
      P M bracket B C T) :
    GirsanovComplexDoleansEulerResidualCondition
      P M bracket B C T := by
  intro c t
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  have hsum : TendstoInMeasure P (fun n omega =>
      (1 / 2 : ℂ) *
          complexDoleansWeightedBracketResidualApprox
            X Q T (n + 1) t omega +
        complexDoleansHigherOrderResidualApprox
          X Q T (n + 1) t omega) atTop (fun _ => 0) := by
    simpa only [X, Q, zero_add] using
      TendstoInMeasure.add_normed_noMeas (hbracket c t) (hhigher c t)
  apply hsum.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (complexDoleansEulerResidualApprox_eq_secondOrder
      X Q T n t omega).symm

/-- Vanishing of the canonical one-step residuals is exactly sufficient for
the localization-free complex Girsanov Euler condition. -/
theorem girsanovComplexEulerInMeasureCondition_of_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hres : GirsanovComplexDoleansEulerResidualCondition
      P M bracket B C T) :
    GirsanovComplexEulerInMeasureCondition P M bracket B C T := by
  intro c t
  have hcanonical : TendstoInMeasure P (fun n =>
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t) atTop
      (fun omega =>
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c)
          (min t T) omega) := by
    have hlimit := hres c t
    rw [tendstoInMeasure_iff_norm] at hlimit ⊢
    intro epsilon hepsilon
    have hlimit' := hlimit epsilon hepsilon
    have hmeasureFun :
        (fun n => P {omega | epsilon ≤
          ‖complexDoleansEulerProcess
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                T (n + 1) t omega -
              complexDoleansDadeExponential
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                (min t T) omega‖}) =
        (fun n => P {omega | epsilon ≤
          ‖complexDoleansEulerResidualApprox
                (complexMartingaleCombination M B c)
                (complexMartingaleCombinationBracket bracket C c)
                T (n + 1) t omega - 0‖}) := by
      funext n
      congr 1
      ext omega
      simp only [Set.mem_ofPred_eq, sub_zero]
      rw [← complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual]
      rw [norm_sub_rev]
    rw [hmeasureFun]
    exact hlimit'
  apply hcanonical.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (congrFun (congrFun
      (complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
        M bracket B C c T (n + 1)) t) omega).symm

/-- The remaining moment obligation along one explicit common localizer:
the increasing-cap genuine Euler martingales are uniformly integrable at
each deterministic time. -/
def GirsanovDiagonalComplexEulerLocalizingUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), UniformIntegrable (fun n =>
    cappedComplexGirsanovEulerProcess
      (localizingStoppedProcess M (tau n))
      M bracket B C c (n + 1) T (n + 1) t) 1 P

/-- A Vitali-ready version of the localized Euler obligation.  It replaces
direct `L¹` convergence by convergence in probability and a uniform `L²`
bound on the genuine martingale transforms. -/
def GirsanovCappedComplexEulerLocalizingL2InMeasureCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ (c : ℝ) (R : ℝ≥0),
    ∃ l : ℕ → ℕ, ∀ t,
      (∃ K : ℝ≥0, ∀ n, eLpNorm
        (cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c R T (n + 1) t) 2 P ≤ K) ∧
      TendstoInMeasure P (fun n =>
        cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c R T (n + 1) t) atTop
        (fun omega =>
          cappedComplexDoleansDadeExponentialCombination
            M bracket B C c R (min t T) omega)

/-- A sharper sufficient condition for the Vitali-ready Euler obligation.
It asks only for convergence in probability and a uniform terminal `L²`
bound on the selected localized martingales; the Brownian and Euler bounds
are then discharged internally. -/
def GirsanovCappedComplexEulerLocalizingTerminalL2InMeasureCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (tau : ℕ → W → WithTop ℝ≥0) : Prop :=
  ∀ (c : ℝ) (R : ℝ≥0),
    ∃ l : ℕ → ℕ, ∃ K : ℝ≥0,
      (∀ n, eLpNorm
        (localizingStoppedProcess M (tau (l n)) T) 2 P ≤ K) ∧
      ∀ t, TendstoInMeasure P (fun n =>
        cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c R T (n + 1) t) atTop
        (fun omega =>
          cappedComplexDoleansDadeExponentialCombination
            M bracket B C c R (min t T) omega)

/-- A canonical localizing-sequence Euler limit supplies the abstract
martingale-approximant condition. -/
theorem girsanovCappedComplexEulerL1Condition_of_localizing
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (hmart : ∀ n, Martingale (localizingStoppedProcess M (tau n)) V P)
    (hconv : GirsanovCappedComplexEulerLocalizingL1Condition
      P M bracket B C T tau) :
    GirsanovCappedComplexEulerL1Condition P V M bracket B C T := by
  intro c R
  obtain ⟨l, hl⟩ := hconv c R
  exact ⟨fun n => localizingStoppedProcess M (tau (l n)),
    fun n => hmart (l n), hl⟩

/-- A diagonal through a common localizing sequence supplies the abstract
increasing-cap martingale approximation. -/
theorem girsanovDiagonalComplexEulerL1Condition_of_localizing
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (hmart : ∀ n, Martingale (localizingStoppedProcess M (tau n)) V P)
    (hconv : GirsanovDiagonalComplexEulerLocalizingL1Condition
      P M bracket B C T tau) :
    GirsanovDiagonalComplexEulerL1Condition P V M bracket B C T := by
  intro c
  obtain ⟨l, hl⟩ := hconv c
  exact ⟨fun n => localizingStoppedProcess M (tau (l n)),
    fun n => hmart (l n), hl⟩

/-- Localizer disappearance combines a localization-free stochastic-Taylor
limit with uniform integrability along the common localizer. -/
theorem
    girsanovDiagonalComplexEulerLocalizingInMeasureUICondition_of_UI_of_self
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence V tau P)
    (hM : StronglyAdapted V M)
    (hMcont : ∀ omega, Continuous (fun s => M s omega))
    (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hUI : GirsanovDiagonalComplexEulerLocalizingUICondition
      P M bracket B C T tau)
    (hself : GirsanovComplexEulerInMeasureCondition
      P M bracket B C T) :
    GirsanovDiagonalComplexEulerLocalizingInMeasureUICondition
      P M bracket B C T tau := by
  intro c
  refine ⟨id, ?_, ?_⟩
  · intro t
    simpa only [id_eq] using hUI c t
  · intro t
    let L : ℕ → W → ℂ := fun n =>
      complexGirsanovEulerProcess
        (localizingStoppedProcess M (tau n))
        M bracket B C c T (n + 1) t
    let S : ℕ → W → ℂ := fun n =>
      complexGirsanovEulerProcess M M bracket B C c T (n + 1) t
    let E : W → ℂ := fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega
    have hdiff : TendstoInMeasure P (fun n => L n - S n) atTop
        (fun _ => 0) := by
      change TendstoInMeasure P (fun n omega =>
        complexGirsanovEulerProcess
            (localizingStoppedProcess M (tau n))
            M bracket B C c T (n + 1) t omega -
          complexGirsanovEulerProcess
            M M bracket B C c T (n + 1) t omega)
        atTop (fun _ => 0)
      exact
        tendstoInMeasure_complexGirsanovEulerProcess_localizing_sub_self
          htau hM hMcont hbracket hB hC c T t
    have hMtau (n : ℕ) : StronglyAdapted V
        (localizingStoppedProcess M (tau n)) :=
      stronglyAdapted_localizingStoppedProcess
        hM hMcont (htau.isStoppingTime n)
    have hLmeas (n : ℕ) : AEStronglyMeasurable (L n) P := by
      exact ((stronglyAdapted_complexGirsanovEulerProcess
        (hMtau n) hM hbracket hB hC c T (n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    have hSmeas (n : ℕ) : AEStronglyMeasurable (S n) P := by
      exact ((stronglyAdapted_complexGirsanovEulerProcess
        hM hM hbracket hB hC c T (n + 1) t).mono
          (V.le t)).aestronglyMeasurable
    have hsum := TendstoInMeasure.continuous_comp₂
      (fun n => (hLmeas n).sub (hSmeas n)) hSmeas hdiff
      (by simpa only [S, E] using hself c t)
      (by fun_prop : Continuous (Function.uncurry (fun x y : ℂ => x + y)))
    apply hsum.congr
    · intro n
      exact Filter.Eventually.of_forall fun omega => by
        simp [L, S]
    · exact Filter.Eventually.of_forall fun omega => by
        dsimp only [E]; simp only [zero_add]

/-- Cap disappearance and Vitali upgrade the separated convergence-in-
probability/uniform-integrability condition to the diagonal `L¹` condition. -/
theorem
    girsanovDiagonalComplexEulerLocalizingL1Condition_of_inMeasure_UI
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (_hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hmart : ∀ n, Martingale (localizingStoppedProcess M (tau n)) V P)
    (hconv : GirsanovDiagonalComplexEulerLocalizingInMeasureUICondition
      P M bracket B C T tau) :
    GirsanovDiagonalComplexEulerLocalizingL1Condition
      P M bracket B C T tau := by
  intro c
  obtain ⟨l, hUI, hplain⟩ := hconv c
  refine ⟨l, fun t => ?_⟩
  let A : ℕ → W → ℂ := fun n =>
    cappedComplexGirsanovEulerProcess
      (localizingStoppedProcess M (tau (l n)))
      M bracket B C c (n + 1) T (n + 1) t
  let U : ℕ → W → ℂ := fun n =>
    complexGirsanovEulerProcess
      (localizingStoppedProcess M (tau (l n)))
      M bracket B C c T (n + 1) t
  let E : W → ℂ := fun omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hcap : TendstoInMeasure P (fun n => A n - U n) atTop
      (fun _ => 0) := by
    change TendstoInMeasure P (fun n omega =>
      cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c (n + 1) T (n + 1) t omega -
        complexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c T (n + 1) t omega) atTop (fun _ => 0)
    exact tendstoInMeasure_cappedComplexGirsanovEulerProcess_sub_complex
      (fun n => (hmart (l n)).stronglyAdapted)
      hdata.adapted_martingale hdata.adapted_bracket hBadapt hC
      (Filter.Eventually.of_forall hdata.continuous_martingale_path)
      (Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_monotone_bracket omega).1) c T t
  have hAmeas (n : ℕ) : AEStronglyMeasurable (A n) P :=
    (hUI t).1 n
  have hUmeas (n : ℕ) : AEStronglyMeasurable (U n) P := by
    exact ((stronglyAdapted_complexGirsanovEulerProcess
      (hmart (l n)).stronglyAdapted hdata.adapted_martingale
      hdata.adapted_bracket hBadapt hC c T (n + 1) t).mono
        (V.le t)).aestronglyMeasurable
  have hsum := TendstoInMeasure.continuous_comp₂
    (fun n => (hAmeas n).sub (hUmeas n)) hUmeas hcap
      (by simpa only [U, E] using hplain t)
      (by fun_prop : Continuous (Function.uncurry (fun x y : ℂ => x + y)))
  have hmeasure : TendstoInMeasure P A atTop E := by
    apply hsum.congr
    · intro n
      exact Filter.Eventually.of_forall fun omega => by
        simp only [Pi.sub_apply]; ring_nf
    · exact Filter.Eventually.of_forall fun omega => by
        dsimp only [E]; simp only [zero_add]
  have hLp :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (by simpa only [A] using hUI t) hmeasure
  convert hLp using 1
  ext n
  simpa only [A, E] using (eLpNorm_sub_comm (A n) E 1 P).symm

/-- Uniform second moments upgrade a localized Euler limit in probability
to the `L¹` limit used by the capped complex-exponential theorem. -/
theorem girsanovCappedComplexEulerLocalizingL1Condition_of_L2_inMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hmart : ∀ n, Martingale (localizingStoppedProcess M (tau n)) V P)
    (hconv : GirsanovCappedComplexEulerLocalizingL2InMeasureCondition
      P M bracket B C T tau) :
    GirsanovCappedComplexEulerLocalizingL1Condition
      P M bracket B C T tau := by
  intro c R
  obtain ⟨l, hl⟩ := hconv c R
  refine ⟨l, fun t => ?_⟩
  obtain ⟨⟨K, hK⟩, hmeasure⟩ := hl t
  let X : ℕ → ℝ≥0 → W → ℂ := fun n =>
    cappedComplexGirsanovEulerProcess
      (localizingStoppedProcess M (tau (l n)))
      M bracket B C c R T (n + 1)
  let Y : ℝ≥0 → W → ℂ := fun s omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min s T) omega
  have hXmart (n : ℕ) : Martingale (X n) V P := by
    exact martingale_cappedComplexGirsanovEulerProcess
      (hmart (l n)) hBmart hdata.adapted_martingale
        hdata.adapted_bracket hBadapt hC c R T (n + 1)
  have hUI : UniformIntegrable (fun n => X n t) 1 P := by
    apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := K)
    · intro n
      exact ((hXmart n).stronglyMeasurable t).mono
        (V.le t) |>.aestronglyMeasurable
    · intro n
      simpa only [X] using hK n
  have hmeasure' : TendstoInMeasure P (fun n => X n t) atTop (Y t) := by
    simpa only [X, Y] using hmeasure
  have hLp :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      hUI hmeasure'
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- A uniform terminal `L²` bound for the chosen localized martingales and
Euler convergence in probability imply the full timewise Euler `L²`/Vitali
condition. -/
theorem
    girsanovCappedComplexEulerLocalizingL2InMeasureCondition_of_terminalL2_inMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    {tau : ℕ → W → WithTop ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBrownian : IsPreBrownianReal B P)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hmart : ∀ n, Martingale (localizingStoppedProcess M (tau n)) V P)
    (hconv :
      GirsanovCappedComplexEulerLocalizingTerminalL2InMeasureCondition
        P M bracket B C T tau) :
    GirsanovCappedComplexEulerLocalizingL2InMeasureCondition
      P M bracket B C T tau := by
  intro c R
  obtain ⟨l, K, hK, hmeasure⟩ := hconv c R
  refine ⟨l, fun t => ⟨?_, hmeasure t⟩⟩
  let N : ℕ → ℝ≥0 → W → ℝ := fun n =>
    localizingStoppedProcess M (tau (l n))
  have hNmart (n : ℕ) : Martingale (N n) V P := hmart (l n)
  have hNT (n : ℕ) : MemLp (N n T) 2 P := by
    refine ⟨((hNmart n).stronglyMeasurable T).mono
      (V.le T) |>.aestronglyMeasurable, ?_⟩
    exact (hK n).trans_lt ENNReal.coe_lt_top
  have hNdiffBound (n : ℕ) :
      eLpNorm (N n T - N n 0) 2 P ≤ 2 * K := by
    have hN0 : MemLp (N n 0) 2 P :=
      martingale_memLp_of_le (hNmart n) bot_le (by norm_num) (hNT n)
    calc
      eLpNorm (N n T - N n 0) 2 P ≤
          eLpNorm (N n T) 2 P + eLpNorm (N n 0) 2 P :=
        eLpNorm_sub_le (hNT n).1 hN0.1 (by norm_num)
      _ ≤ K + K := add_le_add (hK n)
        ((martingale_eLpNorm_le_of_le
          (hNmart n) bot_le (by norm_num)).trans (hK n))
      _ = 2 * K := by ring
  have hBT : MemLp (B T) 2 P :=
    (hBrownian.isGaussianProcess.hasGaussianLaw_eval T).memLp
      ENNReal.ofNat_ne_top
  have hB0 : MemLp (B 0) 2 P :=
    (hBrownian.isGaussianProcess.hasGaussianLaw_eval 0).memLp
      ENNReal.ofNat_ne_top
  have hBdiff : MemLp (B T - B 0) 2 P := hBT.sub hB0
  let L : ℝ≥0∞ :=
    cappedComplexGirsanovCoefficientBound c R T +
      2 * cappedComplexGirsanovCoefficientBound c R T * (2 * K) +
      2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
        eLpNorm (B T - B 0) 2 P
  have hLtop : L ≠ ∞ := by
    dsimp only [L]
    finiteness
  refine ⟨L.toNNReal, fun n => ?_⟩
  calc
    eLpNorm
        (cappedComplexGirsanovEulerProcess
          (localizingStoppedProcess M (tau (l n)))
          M bracket B C c R T (n + 1) t) 2 P ≤
        cappedComplexGirsanovCoefficientBound c R T +
          2 * cappedComplexGirsanovCoefficientBound c R T *
            eLpNorm (N n T - N n 0) 2 P +
          2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
            eLpNorm (B T - B 0) 2 P := by
      simpa only [N] using
        eLpNorm_cappedComplexGirsanovEulerProcess_le_of_memLp_terminal
          (hNmart n) hBmart hdata.adapted_martingale
          hdata.adapted_bracket hBadapt hC c R T (hNT n) hBT n t
    _ ≤ L := by
      dsimp only [L]
      gcongr
      exact hNdiffBound n
    _ = L.toNNReal := (ENNReal.coe_toNNReal hLtop).symm

/-- The localized Euler obligation bundled with the same common localizer
that realizes the quadratic variation of `M`.  This is the canonical shape
available by destructing `GirsanovDensityData.localQuadraticVariation`; the
only extra field is the final `L¹` convergence statement. -/
def GirsanovCappedComplexEulerLocalQVCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      GirsanovCappedComplexEulerLocalizingL1Condition
        P M bracket B C T tau

/-- The common-localizer quadratic-variation contract bundled with the
mathematically viable increasing-cap Euler diagonal. -/
def GirsanovDiagonalComplexEulerLocalQVCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      GirsanovDiagonalComplexEulerLocalizingL1Condition
        P M bracket B C T tau

/-- Common-localizer quadratic variation bundled with the separated,
Vitali-ready diagonal Euler obligations. -/
def GirsanovDiagonalComplexEulerLocalQVInMeasureUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      GirsanovDiagonalComplexEulerLocalizingInMeasureUICondition
        P M bracket B C T tau

/-- The common-localizer quadratic-variation contract bundled only with the
remaining increasing-cap uniform-integrability obligation.  The independent
stochastic-Taylor half is stated by
`GirsanovComplexDoleansEulerResidualCondition`. -/
def GirsanovDiagonalComplexEulerLocalQVUICondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence V tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) V P) ∧
      (∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) ∧
      GirsanovDiagonalComplexEulerLocalizingUICondition
        P M bracket B C T tau

/-- The two irreducible diagonal obligations—vanishing canonical Doléans
residuals and uniform integrability of the increasing-cap martingales—supply
the separated local-quadratic-variation Euler condition. -/
theorem
    girsanovDiagonalComplexEulerLocalQVInMeasureUICondition_of_UI_of_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hUI : GirsanovDiagonalComplexEulerLocalQVUICondition
      P V M bracket B C T)
    (hres : GirsanovComplexDoleansEulerResidualCondition
      P M bracket B C T) :
    GirsanovDiagonalComplexEulerLocalQVInMeasureUICondition
      P V M bracket B C T := by
  obtain ⟨tau, htau, hmart, hqv, hlocalUI⟩ := hUI
  refine ⟨tau, htau, hmart, hqv, ?_⟩
  exact
    girsanovDiagonalComplexEulerLocalizingInMeasureUICondition_of_UI_of_self
      htau hdata.adapted_martingale hdata.continuous_martingale_path
      hdata.adapted_bracket hB hC hlocalUI
      (girsanovComplexEulerInMeasureCondition_of_residual hres)

/-- A common-localizer quadratic-variation/Euler witness supplies the
abstract martingale-approximant condition used by the cap-removal theorem. -/
theorem girsanovCappedComplexEulerL1Condition_of_localQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovCappedComplexEulerLocalQVCondition
      P V M bracket B C T) :
    GirsanovCappedComplexEulerL1Condition P V M bracket B C T := by
  obtain ⟨tau, _htau, hmart, _hqv, hconv⟩ := h
  exact girsanovCappedComplexEulerL1Condition_of_localizing hmart hconv

/-- The common-localizer diagonal condition supplies the abstract
increasing-cap Euler condition. -/
theorem girsanovDiagonalComplexEulerL1Condition_of_localQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDiagonalComplexEulerLocalQVCondition
      P V M bracket B C T) :
    GirsanovDiagonalComplexEulerL1Condition P V M bracket B C T := by
  obtain ⟨tau, _htau, hmart, _hqv, hconv⟩ := h
  exact girsanovDiagonalComplexEulerL1Condition_of_localizing hmart hconv

/-- The separated common-localizer obligations imply the abstract diagonal
`L¹` martingale approximation used by the complex Girsanov endpoint. -/
theorem girsanovDiagonalComplexEulerL1Condition_of_localQV_inMeasure_UI
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (h : GirsanovDiagonalComplexEulerLocalQVInMeasureUICondition
      P V M bracket B C T) :
    GirsanovDiagonalComplexEulerL1Condition P V M bracket B C T := by
  obtain ⟨tau, _htau, hmart, _hqv, hconv⟩ := h
  exact girsanovDiagonalComplexEulerL1Condition_of_localizing hmart
    (girsanovDiagonalComplexEulerLocalizingL1Condition_of_inMeasure_UI
      hdata hBmart hBadapt hC hmart hconv)

/-- Capped Euler `L¹` convergence proves true martingality of the stopped
uncapped complex exponential.  Density domination handles cap removal by
Vitali, so no Brownian path-continuity or optional-stopping premise enters. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_cappedEulerL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovCappedComplexEulerL1Condition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  intro c
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  let X : ℕ → ℝ≥0 → W → ℂ := fun n t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c n (min t T) omega
  have hcapBase (n : ℕ) : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c n) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hdata.adapted_martingale hdata.adapted_bracket hBadapt hC c n
  have hXadapt (n : ℕ) : StronglyAdapted V (X n) := fun t =>
    (hcapBase n (min t T)).mono (V.mono (min_le_left t T))
  have hXmart (n : ℕ) : Martingale (X n) V P := by
    obtain ⟨N, hN, hconv⟩ := hEuler c n
    apply martingale_of_tendsto_eLpNorm_one_banach
      (fun k => martingale_cappedComplexGirsanovEulerProcess
        (hN k) hBmart hdata.adapted_martingale hdata.adapted_bracket
          hBadapt hC c n T (k + 1))
      (hXadapt n)
    intro t
    simpa only [X] using hconv t
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable_banach
    hXmart hE
  · intro t
    have hconstant : UniformIntegrable (fun _n : ℕ => E t) 1 P :=
      StochasticCalculus.UniformIntegrable.comp_index
        (hdata.uniformIntegrable_stopAt_complexDoleans_combination
          hBadapt hC c) (fun _n : ℕ => t)
    apply StochasticCalculus.UniformIntegrable.mono_norm_banach hconstant
    · intro n
      exact ((hXadapt n t).mono (V.le t)).aestronglyMeasurable
    · intro n omega
      exact
        norm_cappedComplexDoleansDadeExponentialCombination_le_uncapped
          M bracket B C c n (min t T) omega
  · intro t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hXadapt n t).mono (V.le t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        tendsto_cappedComplexDoleansDadeExponentialCombination_nat
          M bracket B C c (min t T) omega

/-- Increasing-cap complex Euler `L¹` convergence directly proves true
martingality of the stopped uncapped complex stochastic exponential. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_diagonalEulerL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovDiagonalComplexEulerL1Condition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  intro c
  obtain ⟨N, hN, hconv⟩ := hEuler c
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  apply martingale_of_tendsto_eLpNorm_one_banach
    (fun n => martingale_cappedComplexGirsanovEulerProcess
      (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
        hBadapt hC c (n + 1) T (n + 1)) hE
  intro t
  simpa only [E] using hconv t

/-- Cofinal selected-grid increasing-cap Euler convergence is sufficient for
true martingality of every stopped complex Girsanov exponential. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_selectedEulerL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovSelectedComplexEulerL1Condition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  intro c
  obtain ⟨q, N, _hq, hN, hconv⟩ := hEuler c
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  apply martingale_of_tendsto_eLpNorm_one_banach
    (fun n => martingale_cappedComplexGirsanovEulerProcess
      (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
        hBadapt hC c (n + 1) T (q n + 1)) hE
  intro t
  simpa only [E] using hconv t

/-- Pair-dependent selected Euler approximations suffice for true
martingality.  This endpoint consumes exactly the two-time convergence used
by the martingale identity. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_pairwiseSelectedEulerL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovPairwiseSelectedComplexEulerL1Condition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  intro c
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  apply martingale_of_pairwise_tendsto_eLpNorm_one_banach hE
  · intro t
    exact hdata.integrable_stopAt_complexDoleans_combination
      hBadapt hC c t
  · intro s t hst
    obtain ⟨q, N, _hq, hN, hconvS, hconvT⟩ := hEuler c s t hst
    let X : ℕ → ℝ≥0 → W → ℂ := fun n =>
      cappedComplexGirsanovEulerProcess
        (N n) M bracket B C c (n + 1) T (q n + 1)
    refine ⟨X, fun n => ?_, ?_, ?_⟩
    · exact martingale_cappedComplexGirsanovEulerProcess
        (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
          hBadapt hC c (n + 1) T (q n + 1)
    · simpa only [E, X] using hconvS
    · simpa only [E, X] using hconvT

/-- Flexible-cap finite approximations imply true martingality of the
stopped complex exponential.  Only the two observation times in each
martingale identity share choices, and cofinal grids are obtained from the
explicit lower bound on their indices. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_pairwiseFiniteDirectEulerRateL1
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovPairwiseFiniteComplexEulerDirectRateL1Condition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  intro c
  let E : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t T) omega
  have hEbase : StronglyAdapted V
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBadapt c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
  have hE : StronglyAdapted V E := fun t =>
    (hEbase (min t T)).mono (V.mono (min_le_left t T))
  apply martingale_of_pairwise_tendsto_eLpNorm_one_banach hE
  · intro t
    exact hdata.integrable_stopAt_complexDoleans_combination
      hBadapt hC c t
  · intro s t hst
    choose R q N hqn hN hboundS hboundT using
      fun n => hEuler c s t hst n
    let X : ℕ → ℝ≥0 → W → ℂ := fun n =>
      cappedComplexGirsanovEulerProcess
        (N n) M bracket B C c (R n) T (q n + 1)
    have hrate : Tendsto
        (fun n : ℕ => ((((n + 1 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞))
        atTop (nhds 0) := by
      apply ENNReal.tendsto_coe.2
      exact tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    refine ⟨X, fun n => ?_, ?_, ?_⟩
    · exact martingale_cappedComplexGirsanovEulerProcess
        (hN n) hBmart hdata.adapted_martingale hdata.adapted_bracket
          hBadapt hC c (R n) T (q n + 1)
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hrate (fun _ => zero_le) ?_
      intro n
      have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      simpa only [E, X, ENNReal.coe_inv hn] using hboundS n
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hrate (fun _ => zero_le) ?_
      intro n
      have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      simpa only [E, X, ENNReal.coe_inv hn] using hboundT n

/-- Selected-grid convergence in probability plus uniform integrability is
enough for the stopped complex Girsanov martingales. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_selectedEuler_inMeasure_UI
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovSelectedComplexEulerInMeasureUICondition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  exact hdata.martingale_stopAt_complexDoleans_of_selectedEulerL1
    hBmart hBadapt hC
      (girsanovSelectedComplexEulerL1Condition_of_inMeasure_UI
        hdata hBadapt hC hEuler)

/-- The corrected cofinal frontier—selected canonical residual convergence
plus matching local-quadratic-variation UI—proves all stopped complex
Girsanov exponential martingales. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_selectedLocalQVUI_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hUI : GirsanovSelectedComplexEulerLocalQVUICondition
      P V M bracket B C T)
    (hres : GirsanovSelectedComplexDoleansEulerResidualCondition
      P M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  apply
    hdata.martingale_stopAt_complexDoleans_of_selectedEuler_inMeasure_UI
      hBmart hBadapt hC
  exact girsanovSelectedComplexEulerInMeasureUICondition_of_localQVUI_of_self
    hdata hBadapt hC hUI
      (girsanovSelectedComplexEulerSelfInMeasureCondition_of_residual hres)

/-- Common-localizer quadratic variation together with the increasing-cap
Euler diagonal yields all stopped complex exponential martingales. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_diagonalEulerLocalQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovDiagonalComplexEulerLocalQVCondition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  exact hdata.martingale_stopAt_complexDoleans_of_diagonalEulerL1
    hBmart hBadapt hC
      (girsanovDiagonalComplexEulerL1Condition_of_localQV hEuler)

/-- The separated convergence-in-probability and uniform-integrability
common-localizer obligations suffice for all stopped complex exponentials. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_diagonalEulerLocalQV_inMeasure_UI
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovDiagonalComplexEulerLocalQVInMeasureUICondition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  exact hdata.martingale_stopAt_complexDoleans_of_diagonalEulerL1
    hBmart hBadapt hC
      (girsanovDiagonalComplexEulerL1Condition_of_localQV_inMeasure_UI
        hdata hBmart hBadapt hC hEuler)

/-- The explicit residual/UI factorization proves the stopped complex
Girsanov exponential martingales. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_diagonalEulerLocalQVUI_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hUI : GirsanovDiagonalComplexEulerLocalQVUICondition
      P V M bracket B C T)
    (hres : GirsanovComplexDoleansEulerResidualCondition
      P M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  apply
    hdata.martingale_stopAt_complexDoleans_of_diagonalEulerLocalQV_inMeasure_UI
      hBmart hBadapt hC
  exact
    girsanovDiagonalComplexEulerLocalQVInMeasureUICondition_of_UI_of_residual
      hdata hBadapt hC hUI hres

/-- Common-localizer quadratic variation together with the localized Euler
limit is enough to obtain the stopped complex exponential martingales. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_cappedEulerLocalQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hBmart : Martingale B V P) (hBadapt : StronglyAdapted V B)
    (hC : StronglyAdapted V C)
    (hEuler : GirsanovCappedComplexEulerLocalQVCondition
      P V M bracket B C T) :
    ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  exact hdata.martingale_stopAt_complexDoleans_of_cappedEulerL1
    hBmart hBadapt hC
      (girsanovCappedComplexEulerL1Condition_of_localQV hEuler)

/-- Paste a complex martingale before a deterministic time to a bounded
past-measurable multiple of another martingale after that time. -/
def martingalePasteMul
    {W : Type*} (X Y : ℝ≥0 → W → ℂ) (H : W → ℂ) (s : ℝ≥0) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  if t ≤ s then X t omega else H omega * Y t omega

/-- Deterministic-time martingale pasting with an integrable measurable
multiplier.  The two pieces only have to agree at the pasting time. -/
theorem martingale_martingalePasteMul_of_integrable
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H)
    (hHYint : ∀ t, Integrable (fun omega ↦ H omega * Y t omega) P)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  have hpasteLeft {t : ℝ≥0} (hts : t ≤ s) :
      martingalePasteMul X Y H s t = X t := by
    funext omega
    simp only [martingalePasteMul, hts, ↓reduceIte]
  have hpasteRight {t : ℝ≥0} (hst : s ≤ t) :
      martingalePasteMul X Y H s t =
        fun omega ↦ H omega * Y t omega := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · exact (hpasteLeft (le_refl s)).trans hmatch.symm
    · funext omega
      simp only [martingalePasteMul, not_le.mpr hst', ↓reduceIte]
  have hpasteAdapt : StronglyAdapted V
      (martingalePasteMul X Y H s) := by
    intro t
    rcases le_total t s with hts | hst
    · rw [hpasteLeft hts]
      exact hX.stronglyMeasurable t
    · rw [hpasteRight hst]
      exact (hH.mono (V.mono hst)).mul (hY.stronglyMeasurable t)
  refine ⟨hpasteAdapt, fun i j hij ↦ ?_⟩
  rcases le_total j s with hjs | hsj
  · rw [hpasteLeft hjs, hpasteLeft (hij.trans hjs)]
    exact hX.condExp_ae_eq hij
  rcases le_total s i with hsi | his
  · rw [hpasteRight hsi, hpasteRight (hsi.trans hij)]
    have hpull := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      (hH.mono (V.mono hsi)) (hHYint j) (hY.integrable j)
    exact hpull.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
      (hY.condExp_ae_eq hij))
  · have hpullS := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      hH (hHYint j) (hY.integrable j)
    have hjRight := hpasteRight hsj
    have hsRight := hpasteRight (le_refl s)
    have hcondS : P[martingalePasteMul X Y H s j | V s] =ᵐ[P]
        martingalePasteMul X Y H s s := by
      rw [hjRight, hsRight]
      exact hpullS.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
        (hY.condExp_ae_eq hsj))
    rw [hpasteLeft (le_refl s)] at hcondS
    have htower := condExp_condExp_of_le (μ := P)
      (V.mono his) (V.le s) (f := martingalePasteMul X Y H s j)
    rw [hpasteLeft his]
    filter_upwards [htower, condExp_congr_ae hcondS,
      hX.condExp_ae_eq his] with omega htowerOmega hcongr hmart
    rw [← htowerOmega, hcongr, hmart]

/-- Bounded deterministic-time multipliers satisfy the integrability
premise of `martingale_martingalePasteMul_of_integrable`. -/
theorem martingale_martingalePasteMul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H) (K : ℝ)
    (hHbound : ∀ omega, ‖H omega‖ ≤ K)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  apply martingale_martingalePasteMul_of_integrable hX hY hH _ hmatch
  intro t
  exact (hY.integrable t).bdd_mul
    (hH.mono (V.le s)).aestronglyMeasurable
    (Filter.Eventually.of_forall hHbound)

/-- Uniform-partition covariation of a real process with a complex process,
using the real scalar action on each complex increment. -/
noncomputable def complexCovariationApprox
    {W : Type*} (X : ℝ≥0 → W → ℝ) (Y : ℝ≥0 → W → ℂ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    (X (uniformPartitionTime t n (i + 1)) omega -
      X (uniformPartitionTime t n i) omega) •
    (Y (uniformPartitionTime t n (i + 1)) omega -
      Y (uniformPartitionTime t n i) omega)

/-- Process-level complex covariation in probability. -/
def HasComplexCovariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (X : ℝ≥0 → W → ℝ) (Y C : ℝ≥0 → W → ℂ)
    (P : Measure W) : Prop :=
  ∀ t, TendstoInMeasure P
    (fun n ↦ complexCovariationApprox X Y t (n + 1)) atTop (C t)

/-- Measurability of complex covariation approximants. -/
theorem aestronglyMeasurable_complexCovariationApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℂ}
    (hX : ∀ t, AEStronglyMeasurable (X t) P)
    (hY : ∀ t, AEStronglyMeasurable (Y t) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (complexCovariationApprox X Y t n) P := by
  unfold complexCovariationApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi ↦ ((hX (uniformPartitionTime t n (i + 1))).sub
      (hX (uniformPartitionTime t n i))).smul
      ((hY (uniformPartitionTime t n (i + 1))).sub
        (hY (uniformPartitionTime t n i))))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.smul_apply', Pi.sub_apply]

/-- The real part of real-complex covariation is the ordinary covariation
with the real-part process. -/
theorem complexCovariationApprox_re
    {W : Type*} (X : ℝ≥0 → W → ℝ) (Y : ℝ≥0 → W → ℂ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    (complexCovariationApprox X Y t n omega).re =
      quadraticCovariationApprox X (fun r w ↦ (Y r w).re) t n omega := by
  unfold complexCovariationApprox quadraticCovariationApprox
  change Complex.reCLM (∑ i ∈ Finset.range n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [map_smul, Complex.reCLM_apply, Complex.sub_re, smul_eq_mul]

/-- The imaginary part of real-complex covariation is the ordinary
covariation with the imaginary-part process. -/
theorem complexCovariationApprox_im
    {W : Type*} (X : ℝ≥0 → W → ℝ) (Y : ℝ≥0 → W → ℂ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    (complexCovariationApprox X Y t n omega).im =
      quadraticCovariationApprox X (fun r w ↦ (Y r w).im) t n omega := by
  unfold complexCovariationApprox quadraticCovariationApprox
  change Complex.imCLM (∑ i ∈ Finset.range n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [map_smul, Complex.imCLM_apply, Complex.sub_im, smul_eq_mul]

/-- A complex covariation contract contains the real-part covariation
contract. -/
theorem HasComplexCovariationProcessInProbability.re
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} {Y C : ℝ≥0 → W → ℂ}
    (h : HasComplexCovariationProcessInProbability X Y C P)
    (hX : StronglyAdapted V X) (hY : StronglyAdapted V Y) :
    HasCrossVariationProcessInProbability X (fun t omega ↦ (Y t omega).re)
      (fun t omega ↦ (C t omega).re) P := by
  intro t
  have hmapped := TendstoInMeasure.continuous_comp
    (fun n ↦ aestronglyMeasurable_complexCovariationApprox
      (fun r ↦ ((hX r).mono (V.le r)).aestronglyMeasurable)
      (fun r ↦ ((hY r).mono (V.le r)).aestronglyMeasurable) t (n + 1))
    (h t) Complex.continuous_re
  apply hmapped.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦
    complexCovariationApprox_re X Y t (n + 1) omega

/-- A complex covariation contract contains the imaginary-part covariation
contract. -/
theorem HasComplexCovariationProcessInProbability.im
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} {Y C : ℝ≥0 → W → ℂ}
    (h : HasComplexCovariationProcessInProbability X Y C P)
    (hX : StronglyAdapted V X) (hY : StronglyAdapted V Y) :
    HasCrossVariationProcessInProbability X (fun t omega ↦ (Y t omega).im)
      (fun t omega ↦ (C t omega).im) P := by
  intro t
  have hmapped := TendstoInMeasure.continuous_comp
    (fun n ↦ aestronglyMeasurable_complexCovariationApprox
      (fun r ↦ ((hX r).mono (V.le r)).aestronglyMeasurable)
      (fun r ↦ ((hY r).mono (V.le r)).aestronglyMeasurable) t (n + 1))
    (h t) Complex.continuous_im
  apply hmapped.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦
    complexCovariationApprox_im X Y t (n + 1) omega

/-- Real and imaginary covariation contracts assemble into a complex
covariation contract.  This is the converse interface to `re` and `im` and
lets complex stochastic products be proved componentwise. -/
theorem HasComplexCovariationProcessInProbability.of_re_im
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℂ}
    {Cre Cim : ℝ≥0 → W → ℝ}
    (hre : HasCrossVariationProcessInProbability X
      (fun t omega ↦ (Y t omega).re) Cre P)
    (him : HasCrossVariationProcessInProbability X
      (fun t omega ↦ (Y t omega).im) Cim P)
    (hX : ∀ t, AEStronglyMeasurable (X t) P)
    (hY : ∀ t, AEStronglyMeasurable (Y t) P) :
    HasComplexCovariationProcessInProbability X Y
      (fun t omega ↦ (Cre t omega : ℂ) +
        (Cim t omega : ℂ) * Complex.I) P := by
  intro t
  let combine : ℝ → ℝ → ℂ := fun x y ↦ (x : ℂ) + (y : ℂ) * Complex.I
  have hremeas (n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationApprox X (fun r omega ↦ (Y r omega).re)
        t (n + 1)) P :=
    aestronglyMeasurable_quadraticCovariationApprox hX
      (fun r ↦ Complex.continuous_re.comp_aestronglyMeasurable (hY r))
      t (n + 1)
  have himmeas (n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationApprox X (fun r omega ↦ (Y r omega).im)
        t (n + 1)) P :=
    aestronglyMeasurable_quadraticCovariationApprox hX
      (fun r ↦ Complex.continuous_im.comp_aestronglyMeasurable (hY r))
      t (n + 1)
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hparts := TendstoInMeasure.continuous_comp₂ hremeas himmeas
    (hre t) (him t) hcombine
  apply hparts.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    apply Complex.ext
    · rw [complexCovariationApprox_re]
      simp only [combine, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, add_zero, sub_zero]
    · rw [complexCovariationApprox_im]
      simp only [combine, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
        zero_add, add_zero, zero_mul, mul_one]

/-- The complex product of a real process and a complex process, compensated
by their complex covariation. -/
def realComplexCompensatedProduct
    {W : Type*} (X : ℝ≥0 → W → ℝ) (Y C : ℝ≥0 → W → ℂ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (X t omega : ℂ) * Y t omega - (X 0 omega : ℂ) * Y 0 omega - C t omega

/-- Stochastic integration by parts for a bounded real martingale and a
bounded complex martingale.  Complex covariation and stochastic continuity
are reduced to the real and imaginary component theorems. -/
theorem
    HasComplexCovariationProcessInProbability.martingale_product_sub_of_bounded_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℝ≥0 → W → ℝ} {Y C : ℝ≥0 → W → ℂ}
    (h : HasComplexCovariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (KX KY KC : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY)
    (hCbound : ∀ t omega, ‖C t omega‖ ≤ KC)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) → TendstoInMeasure P
        (fun n ↦ realComplexCompensatedProduct X Y C (a n)) atTop
        (realComplexCompensatedProduct X Y C r)) :
    Martingale (realComplexCompensatedProduct X Y C) V P := by
  let Yre : ℝ≥0 → W → ℝ := fun t omega ↦ (Y t omega).re
  let Yim : ℝ≥0 → W → ℝ := fun t omega ↦ (Y t omega).im
  let Cre : ℝ≥0 → W → ℝ := fun t omega ↦ (C t omega).re
  let Cim : ℝ≥0 → W → ℝ := fun t omega ↦ (C t omega).im
  let Fre : ℝ≥0 → W → ℝ := fun t omega ↦
    X t omega * Yre t omega - X 0 omega * Yre 0 omega - Cre t omega
  let Fim : ℝ≥0 → W → ℝ := fun t omega ↦
    X t omega * Yim t omega - X 0 omega * Yim 0 omega - Cim t omega
  have htargetAdapt : StronglyAdapted V
      (realComplexCompensatedProduct X Y C) := by
    intro t
    exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
      (hX.stronglyMeasurable t)).mul (hY.stronglyMeasurable t)).sub
      ((Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hX.stronglyMeasurable 0).mono (V.mono bot_le))).mul
        ((hY.stronglyMeasurable 0).mono (V.mono bot_le)))).sub (hC t)
  have hYre : Martingale Yre V P := by
    simpa only [Yre, Complex.reCLM_apply] using
      Martingale.comp_continuousLinearMap hY Complex.reCLM
  have hYim : Martingale Yim V P := by
    simpa only [Yim, Complex.imCLM_apply] using
      Martingale.comp_continuousLinearMap hY Complex.imCLM
  have hCre : StronglyAdapted V Cre := fun t ↦ by
    simpa only [Cre] using
      Complex.continuous_re.comp_stronglyMeasurable (hC t)
  have hCim : StronglyAdapted V Cim := fun t ↦ by
    simpa only [Cim] using
      Complex.continuous_im.comp_stronglyMeasurable (hC t)
  have hYreBound (t : ℝ≥0) (omega : W) : ‖Yre t omega‖ ≤ KY := by
    apply (Complex.abs_re_le_norm (Y t omega)).trans (hYbound t omega)
  have hYimBound (t : ℝ≥0) (omega : W) : ‖Yim t omega‖ ≤ KY := by
    apply (Complex.abs_im_le_norm (Y t omega)).trans (hYbound t omega)
  have hCreBound (t : ℝ≥0) (omega : W) : ‖Cre t omega‖ ≤ KC := by
    apply (Complex.abs_re_le_norm (C t omega)).trans (hCbound t omega)
  have hCimBound (t : ℝ≥0) (omega : W) : ‖Cim t omega‖ ≤ KC := by
    apply (Complex.abs_im_le_norm (C t omega)).trans (hCbound t omega)
  have hFreStoch (r : ℝ≥0) (a : ℕ → ℝ≥0)
      (ha : Tendsto a atTop (nhds r)) :
      TendstoInMeasure P (fun n ↦ Fre (a n)) atTop (Fre r) := by
    have hFmeas (n : ℕ) : AEStronglyMeasurable
        (realComplexCompensatedProduct X Y C (a n)) P :=
      ((htargetAdapt (a n)).mono (V.le (a n))).aestronglyMeasurable
    have hmapped := TendstoInMeasure.continuous_comp hFmeas
      (hstoch r a ha) Complex.continuous_re
    simpa only [Fre, Yre, Cre, realComplexCompensatedProduct,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hmapped
  have hFimStoch (r : ℝ≥0) (a : ℕ → ℝ≥0)
      (ha : Tendsto a atTop (nhds r)) :
      TendstoInMeasure P (fun n ↦ Fim (a n)) atTop (Fim r) := by
    have hFmeas (n : ℕ) : AEStronglyMeasurable
        (realComplexCompensatedProduct X Y C (a n)) P :=
      ((htargetAdapt (a n)).mono (V.le (a n))).aestronglyMeasurable
    have hmapped := TendstoInMeasure.continuous_comp hFmeas
      (hstoch r a ha) Complex.continuous_im
    simpa only [Fim, Yim, Cim, realComplexCompensatedProduct,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_add, add_zero] using hmapped
  have hFre : Martingale Fre V P := by
    simpa only [Fre, Yre, Cre] using
      HasCrossVariationProcessInProbability.martingale_product_sub_of_bounded_tendstoInMeasure
        (h.re hX.stronglyAdapted hY.stronglyAdapted) hX hYre hCre
        KX KY KC hXbound hYreBound hCreBound hFreStoch
  have hFim : Martingale Fim V P := by
    simpa only [Fim, Yim, Cim] using
      HasCrossVariationProcessInProbability.martingale_product_sub_of_bounded_tendstoInMeasure
        (h.im hX.stronglyAdapted hY.stronglyAdapted) hX hYim hCim
        KX KY KC hXbound hYimBound hCimBound hFimStoch
  let imToComplex : ℝ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.mul ℝ ℂ) Complex.I).comp Complex.ofRealCLM
  have hparts : Martingale (fun t omega ↦
      Complex.ofRealCLM (Fre t omega) + imToComplex (Fim t omega)) V P :=
    (Martingale.comp_continuousLinearMap hFre Complex.ofRealCLM).add
      (Martingale.comp_continuousLinearMap hFim imToComplex)
  apply hparts.congr htargetAdapt
  intro t
  exact Filter.Eventually.of_forall fun omega ↦ by
    apply Complex.ext
    · simp only [Fre, Fim, Yre, Yim, Cre, Cim, imToComplex,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
        ContinuousLinearMap.mul_apply', Complex.mul_re, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, Complex.add_re,
        realComplexCompensatedProduct, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero]
      ring
    · simp only [Fre, Fim, Yre, Yim, Cre, Cim, imToComplex,
        ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
        ContinuousLinearMap.mul_apply', Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, Complex.add_im,
        realComplexCompensatedProduct, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_add]
      ring

/-- Componentwise stochastic continuity discharges the stochastic-
continuity premise of the bounded real-complex product formula. -/
theorem
    HasComplexCovariationProcessInProbability.martingale_product_sub_of_bounded_stochContinuous
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℝ≥0 → W → ℝ} {Y C : ℝ≥0 → W → ℂ}
    (h : HasComplexCovariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (KX KY KC : ℝ≥0) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY)
    (hCbound : ∀ t omega, ‖C t omega‖ ≤ KC)
    (hXstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => X (a n)) atTop (X r))
    (hYstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => Y (a n)) atTop (Y r))
    (hCstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => C (a n)) atTop (C r)) :
    Martingale (realComplexCompensatedProduct X Y C) V P := by
  apply h.martingale_product_sub_of_bounded_tendstoInMeasure
    hX hY hC KX KY KC hXbound hYbound hCbound
  intro r a ha
  have hXmeas (n : ℕ) : AEStronglyMeasurable (X (a n)) P :=
    ((hX.stronglyMeasurable (a n)).mono
      (V.le (a n))).aestronglyMeasurable
  have hYmeas (n : ℕ) : AEStronglyMeasurable (Y (a n)) P :=
    ((hY.stronglyMeasurable (a n)).mono
      (V.le (a n))).aestronglyMeasurable
  let mulXY : ℝ → ℂ → ℂ := fun x y => (x : ℂ) * y
  have hmulXY : Continuous mulXY.uncurry := by
    dsimp only [mulXY, Function.uncurry]
    fun_prop
  have hprod : TendstoInMeasure P
      (fun n omega => mulXY (X (a n) omega) (Y (a n) omega)) atTop
      (fun omega => mulXY (X r omega) (Y r omega)) :=
    TendstoInMeasure.continuous_comp₂ hXmeas hYmeas
      (hXstoch r a ha) (hYstoch r a ha) hmulXY
  let initial : W → ℂ := fun omega => (X 0 omega : ℂ) * Y 0 omega
  have hinitialMeas : AEStronglyMeasurable initial P := by
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hX.stronglyMeasurable 0).mono
        (V.le 0)).aestronglyMeasurable).mul
      (((hY.stronglyMeasurable 0).mono
        (V.le 0)).aestronglyMeasurable)
  have hinitial : TendstoInMeasure P (fun _ : ℕ => initial) atTop initial :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hinitialMeas)
      (Filter.Eventually.of_forall fun omega => tendsto_const_nhds)
  let subComplex : ℂ → ℂ → ℂ := fun x y => x - y
  have hsubComplex : Continuous subComplex.uncurry := by
    dsimp only [subComplex, Function.uncurry]
    fun_prop
  have hprodMeas (n : ℕ) : AEStronglyMeasurable
      (fun omega => mulXY (X (a n) omega) (Y (a n) omega)) P :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hXmeas n)).mul (hYmeas n)
  have hfirst : TendstoInMeasure P (fun n omega =>
      subComplex (mulXY (X (a n) omega) (Y (a n) omega))
        (initial omega)) atTop
      (fun omega => subComplex (mulXY (X r omega) (Y r omega))
        (initial omega)) :=
    TendstoInMeasure.continuous_comp₂ hprodMeas
      (fun _ => hinitialMeas) hprod hinitial hsubComplex
  have hfirstMeas (n : ℕ) : AEStronglyMeasurable (fun omega =>
      subComplex (mulXY (X (a n) omega) (Y (a n) omega))
        (initial omega)) P :=
    (hprodMeas n).sub hinitialMeas
  change TendstoInMeasure P (fun n omega =>
    subComplex
      (subComplex (mulXY (X (a n) omega) (Y (a n) omega))
        (initial omega)) (C (a n) omega)) atTop
    (fun omega => subComplex
      (subComplex (mulXY (X r omega) (Y r omega)) (initial omega))
        (C r omega))
  exact TendstoInMeasure.continuous_comp₂ hfirstMeas
    (fun n => ((hC (a n)).mono (V.le (a n))).aestronglyMeasurable)
    hfirst (hCstoch r a ha) hsubComplex

/-- Stochastic integration by parts at arbitrary deterministic times.  The
rational common-refinement identity extends to all times by path continuity
and dominated convergence. -/
theorem
    HasCrossVariationProcessInProbability.setIntegral_product_sub_eq_of_continuous_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (hXcont : ∀ omega, Continuous (fun r ↦ X r omega))
    (hYcont : ∀ omega, Continuous (fun r ↦ Y r omega))
    (hCcont : ∀ omega, Continuous (fun r ↦ C r omega))
    (KX KY KC : ℝ≥0) (hXbound : ∀ r omega, ‖X r omega‖ ≤ KX)
    (hYbound : ∀ r omega, ‖Y r omega‖ ≤ KY)
    (hCbound : ∀ r omega, ‖C r omega‖ ≤ KC)
    {s t : ℝ≥0} (hst : s ≤ t) {Aset : Set W}
    (hAset : MeasurableSet[V s] Aset) :
    (∫ omega in Aset,
      X s omega * Y s omega - X 0 omega * Y 0 omega - C s omega ∂P) =
      ∫ omega in Aset,
        X t omega * Y t omega - X 0 omega * Y 0 omega - C t omega ∂P := by
  let F : ℝ≥0 → W → ℝ := fun r omega ↦
    X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega
  have hFmeas (r : ℝ≥0) : AEStronglyMeasurable (F r) P := by
    have hXr : AEStronglyMeasurable (X r) P :=
      ((hX.stronglyMeasurable r).mono (V.le r)).aestronglyMeasurable
    have hYr : AEStronglyMeasurable (Y r) P :=
      ((hY.stronglyMeasurable r).mono (V.le r)).aestronglyMeasurable
    have hX0 : AEStronglyMeasurable (X 0) P :=
      ((hX.stronglyMeasurable 0).mono (V.le 0)).aestronglyMeasurable
    have hY0 : AEStronglyMeasurable (Y 0) P :=
      ((hY.stronglyMeasurable 0).mono (V.le 0)).aestronglyMeasurable
    have hCr : AEStronglyMeasurable (C r) P :=
      ((hC r).mono (V.le r)).aestronglyMeasurable
    exact ((hXr.mul hYr).sub (hX0.mul hY0)).sub hCr
  have hFbound (r : ℝ≥0) (omega : W) :
      ‖F r omega‖ ≤ 2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ) := by
    calc
      ‖F r omega‖ ≤ ‖X r omega * Y r omega‖ +
          ‖X 0 omega * Y 0 omega‖ + ‖C r omega‖ := by
        dsimp only [F]
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (KX : ℝ) * (KY : ℝ) + (KX : ℝ) * (KY : ℝ) +
          (KC : ℝ) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact hXbound r omega
        · exact hYbound r omega
        · exact hXbound 0 omega
        · exact hYbound 0 omega
        · exact hCbound r omega
      _ = 2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ) := by ring
  have hlimit {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds s)) :
      Tendsto (fun n ↦ ∫ omega in Aset, F (a n) omega ∂P) atTop
        (nhds (∫ omega in Aset, F s omega ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (μ := P.restrict Aset)
      (fun _ ↦ 2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ))
    · intro n
      exact (hFmeas (a n)).mono_measure Measure.restrict_le_self
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun omega ↦ hFbound (a n) omega
    · exact Filter.Eventually.of_forall fun omega ↦ by
        have hXa : Tendsto (fun n ↦ X (a n) omega) atTop
            (nhds (X s omega)) :=
          (hXcont omega).continuousAt.tendsto.comp ha
        have hYa : Tendsto (fun n ↦ Y (a n) omega) atTop
            (nhds (Y s omega)) :=
          (hYcont omega).continuousAt.tendsto.comp ha
        have hCa : Tendsto (fun n ↦ C (a n) omega) atTop
            (nhds (C s omega)) :=
          (hCcont omega).continuousAt.tendsto.comp ha
        simpa only [F] using
          ((hXa.mul hYa).sub tendsto_const_nhds).sub hCa
  by_cases hstEq : s = t
  · subst t
    rfl
  have hslt : s < t := lt_of_le_of_ne hst hstEq
  by_cases hs0 : s = 0
  · subst s
    let a : ℕ → ℝ≥0 := fun n ↦ t / (n + 1 : ℕ)
    have ha : Tendsto a atTop (nhds 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat t).comp
        (tendsto_add_atTop_nat 1)
    have heq (n : ℕ) :
        (∫ omega in Aset, F (a n) omega ∂P) =
          ∫ omega in Aset, F t omega ∂P := by
      have hden : 0 < n + 1 := Nat.zero_lt_succ n
      have hraw := h.setIntegral_stoppedProduct_sub_eq_rational
        hX hY hC KX KY hXbound hYbound t hden Nat.one_pos
        (Nat.succ_le_succ (Nat.zero_le n))
        (V.mono bot_le Aset hAset)
      simpa only [F, a, Nat.cast_one, mul_one] using hraw
    have hconv := hlimit ha
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in Aset, F t omega ∂P)
        atTop (nhds (∫ omega in Aset, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in Aset, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in Aset, F t omega ∂P) from funext heq] at hconv
    have := tendsto_nhds_unique hconv hconst
    simpa only [F] using this
  · let tau : Unit → WithTop ℝ≥0 := fun _ ↦ (s : WithTop ℝ≥0)
    have hbound : ∀ omega, tau omega ≤ (t : WithTop ℝ≥0) :=
      fun _ ↦ WithTop.coe_le_coe.mpr hst
    let j : ℕ → ℕ := fun n ↦ uniformPartitionCeilIndex tau t (n + 1)
      (Nat.zero_lt_succ n) hbound ()
    let a : ℕ → ℝ≥0 := fun n ↦ uniformPartitionTime t (n + 1) (j n)
    have hjpos (n : ℕ) : 0 < j n := by
      by_contra hn
      have hj0 : j n = 0 := Nat.eq_zero_of_not_pos hn
      have hspec := uniformPartitionCeilIndex_spec tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
      change (s : WithTop ℝ≥0) ≤
        (uniformPartitionTime t (n + 1) (j n) : WithTop ℝ≥0) at hspec
      rw [hj0] at hspec
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        WithTop.coe_zero] at hspec
      exact hs0 (nonpos_iff_eq_zero.mp (WithTop.coe_le_coe.mp hspec))
    have hjle (n : ℕ) : j n ≤ n + 1 :=
      uniformPartitionCeilIndex_le tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
    have hsa (n : ℕ) : s ≤ a n := by
      exact WithTop.coe_le_coe.mp
        (uniformPartitionCeilIndex_spec tau t (n + 1)
          (Nat.zero_lt_succ n) hbound ())
    have ha : Tendsto a atTop (nhds s) := by
      have hwith := tendsto_uniformPartitionCeilStoppingTime tau t hbound ()
      have huntop := (WithTop.tendsto_untopA WithTop.coe_ne_top).comp hwith
      have hcoe (x : ℝ≥0) : WithTop.untopA (x : WithTop ℝ≥0) = x := rfl
      change Tendsto (fun n ↦ WithTop.untopA (a n : WithTop ℝ≥0))
        atTop (nhds (WithTop.untopA (s : WithTop ℝ≥0))) at huntop
      simpa only [hcoe] using huntop
    have heq (n : ℕ) :
        (∫ omega in Aset, F (a n) omega ∂P) =
          ∫ omega in Aset, F t omega ∂P := by
      have hraw := h.setIntegral_stoppedProduct_sub_eq_rational
        hX hY hC KX KY hXbound hYbound t (Nat.zero_lt_succ n)
        (hjpos n) (hjle n) (V.mono (hsa n) Aset hAset)
      simpa only [F, a, uniformPartitionTime] using hraw
    have hconv := hlimit ha
    have hconst : Tendsto (fun _ : ℕ ↦ ∫ omega in Aset, F t omega ∂P)
        atTop (nhds (∫ omega in Aset, F t omega ∂P)) := tendsto_const_nhds
    rw [show (fun n ↦ ∫ omega in Aset, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in Aset, F t omega ∂P) from funext heq] at hconv
    have := tendsto_nhds_unique hconv hconst
    simpa only [F] using this

/-- The compensated product of two bounded continuous martingales is a
martingale when `C` is their continuous process-level cross variation. -/
theorem
    HasCrossVariationProcessInProbability.martingale_product_sub_of_continuous_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C)
    (hXcont : ∀ omega, Continuous (fun r ↦ X r omega))
    (hYcont : ∀ omega, Continuous (fun r ↦ Y r omega))
    (hCcont : ∀ omega, Continuous (fun r ↦ C r omega))
    (KX KY KC : ℝ≥0) (hXbound : ∀ r omega, ‖X r omega‖ ≤ KX)
    (hYbound : ∀ r omega, ‖Y r omega‖ ≤ KY)
    (hCbound : ∀ r omega, ‖C r omega‖ ≤ KC) :
    Martingale (fun r omega ↦
      X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega) V P := by
  let F : ℝ≥0 → W → ℝ := fun r omega ↦
    X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega
  have hFadapt : StronglyAdapted V F := by
    intro r
    exact (((hX.stronglyMeasurable r).mul (hY.stronglyMeasurable r)).sub
      ((hX.stronglyMeasurable 0).mono (V.mono bot_le) |>.mul
        ((hY.stronglyMeasurable 0).mono (V.mono bot_le)))).sub (hC r)
  have hFbound (r : ℝ≥0) (omega : W) :
      ‖F r omega‖ ≤ 2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ) := by
    calc
      ‖F r omega‖ ≤ ‖X r omega * Y r omega‖ +
          ‖X 0 omega * Y 0 omega‖ + ‖C r omega‖ := by
        dsimp only [F]
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (KX : ℝ) * (KY : ℝ) + (KX : ℝ) * (KY : ℝ) +
          (KC : ℝ) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact hXbound r omega
        · exact hYbound r omega
        · exact hXbound 0 omega
        · exact hYbound 0 omega
        · exact hCbound r omega
      _ = 2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ) := by ring
  have hFint (r : ℝ≥0) : Integrable (F r) P := by
    refine Integrable.mono' (integrable_const
      (2 * (KX : ℝ) * (KY : ℝ) + (KC : ℝ)))
      ((hFadapt r).mono (V.le r)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun omega ↦ hFbound r omega
  have hset (s t : ℝ≥0) (hst : s ≤ t) (Aset : Set W)
      (hAset : MeasurableSet[V s] Aset) :
      (∫ omega in Aset, F s omega ∂P) =
        ∫ omega in Aset, F t omega ∂P := by
    simpa only [F] using
      h.setIntegral_product_sub_eq_of_continuous_bounded hX hY hC
        hXcont hYcont hCcont KX KY KC hXbound hYbound hCbound hst hAset
  have hsub : Submartingale F V P :=
    submartingale_of_setIntegral_le hFadapt hFint fun s t hst Aset hAset ↦
      (hset s t hst Aset hAset).le
  have hnegSub : Submartingale (-F) V P :=
    submartingale_of_setIntegral_le hFadapt.neg (fun r ↦ (hFint r).neg)
      fun s t hst Aset hAset ↦ by
        change ∫ omega in Aset, -F s omega ∂P ≤
          ∫ omega in Aset, -F t omega ∂P
        rw [integral_neg, integral_neg, neg_le_neg_iff]
        exact (hset s t hst Aset hAset).symm.le
  have hsuper : Supermartingale F V P := by
    simpa only [Pi.neg_apply, neg_neg] using hnegSub.neg
  exact martingale_iff.mpr ⟨hsuper, hsub⟩

/-- A globally bounded adapted local martingale on a probability space is a
true martingale.  Its canonical stopped localizations inherit the same bound,
so their fixed-time values are uniformly integrable. -/
theorem IsLocalMartingale.martingale_of_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℝ≥0 → W → ℝ}
    (hX : IsLocalMartingale X V P) (hadapt : StronglyAdapted V X)
    (K : ℝ≥0) (hbound : ∀ t omega, ‖X t omega‖ ≤ K) :
    Martingale X V P := by
  apply hX.martingale_of_uniformIntegrable_localizations hadapt
  intro t
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := K)
  · intro n
    exact ((hX.stoppedProcess_localSeq n).integrable t).aestronglyMeasurable
  · intro n
    calc
      eLpNorm (localizingStoppedProcess X (hX.localSeq n) t) 2 P ≤
          P Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (K : ℝ) :=
        eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall fun omega ↦
          norm_localizingStoppedProcess_le K hbound t omega)
      _ = K := by simp

/-- Bounded continuous local martingales satisfy the same stochastic product
identity as bounded true martingales. -/
theorem
    HasCrossVariationProcessInProbability.martingale_product_sub_of_continuous_bounded_local
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hX : IsLocalMartingale X V P) (hY : IsLocalMartingale Y V P)
    (hXadapt : StronglyAdapted V X) (hYadapt : StronglyAdapted V Y)
    (hC : StronglyAdapted V C)
    (hXcont : ∀ omega, Continuous (fun r ↦ X r omega))
    (hYcont : ∀ omega, Continuous (fun r ↦ Y r omega))
    (hCcont : ∀ omega, Continuous (fun r ↦ C r omega))
    (KX KY KC : ℝ≥0) (hXbound : ∀ r omega, ‖X r omega‖ ≤ KX)
    (hYbound : ∀ r omega, ‖Y r omega‖ ≤ KY)
    (hCbound : ∀ r omega, ‖C r omega‖ ≤ KC) :
    Martingale (fun r omega ↦
      X r omega * Y r omega - X 0 omega * Y 0 omega - C r omega) V P := by
  exact h.martingale_product_sub_of_continuous_bounded
    (hX.martingale_of_bounded hXadapt KX hXbound)
    (hY.martingale_of_bounded hYadapt KY hYbound) hC
    hXcont hYcont hCcont KX KY KC hXbound hYbound hCbound

/-- Stochastic integration by parts for two bounded real martingales.  If
the coherent stopped-grid covariation sums converge in `L¹` to an adapted
process `C`, then the stopped product, compensated by `C` and its initial
value, is a martingale. -/
theorem martingale_stoppedProduct_sub_covariation_of_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (KX KY : ℝ) (hXbound : ∀ t omega, ‖X t omega‖ ≤ KX)
    (hYbound : ∀ t omega, ‖Y t omega‖ ≤ KY)
    (hC : StronglyAdapted V C) (T : ℝ≥0)
    (hconv : ∀ t, Tendsto (fun n ↦ eLpNorm
      (uniformStoppedCovariationApprox X Y T (n + 1) t - C t) 1 P)
      atTop (nhds 0)) :
    Martingale (fun t omega ↦
      X (min t T) omega * Y (min t T) omega -
        X 0 omega * Y 0 omega - C t omega) V P := by
  let A : ℕ → ℝ≥0 → W → ℝ := fun n ↦
    uniformAdaptedMartingaleSmulProcess Y X T (n + 1) +
      uniformAdaptedMartingaleSmulProcess X Y T (n + 1)
  have hA (n : ℕ) : Martingale (A n) V P := by
    apply Martingale.add
    · exact martingale_uniformAdaptedMartingaleSmulProcess
        hY hX.stronglyAdapted KX hXbound T (n + 1)
    · exact martingale_uniformAdaptedMartingaleSmulProcess
        hX hY.stronglyAdapted KY hYbound T (n + 1)
  have hadapt : StronglyAdapted V (fun t omega ↦
      X (min t T) omega * Y (min t T) omega -
        X 0 omega * Y 0 omega - C t omega) := by
    intro t
    have hXt : StronglyMeasurable[V t] (X (min t T)) :=
      (hX.stronglyMeasurable (min t T)).mono (V.mono (min_le_left _ _))
    have hYt : StronglyMeasurable[V t] (Y (min t T)) :=
      (hY.stronglyMeasurable (min t T)).mono (V.mono (min_le_left _ _))
    have hX0 : StronglyMeasurable[V t] (X 0) :=
      (hX.stronglyMeasurable 0).mono (V.mono bot_le)
    have hY0 : StronglyMeasurable[V t] (Y 0) :=
      (hY.stronglyMeasurable 0).mono (V.mono bot_le)
    exact ((hXt.mul hYt).sub (hX0.mul hY0)).sub (hC t)
  apply martingale_of_tendsto_eLpNorm_one_banach hA hadapt
  intro t
  convert hconv t using 1
  ext n
  apply congrArg (fun f : W → ℝ ↦ eLpNorm f 1 P)
  funext omega
  simp only [Pi.sub_apply, Pi.add_apply, A]
  rw [uniformStopped_product_decomposition X Y T n t omega]
  ring

/-- A strongly adapted `L¹` limit of the coherent Banach-valued uniform-grid
transforms is a martingale. -/
theorem martingale_of_uniformAdaptedMartingaleSmulProcess_tendsto_eLpNorm_one
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hH : StronglyAdapted V H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (T : ℝ≥0)
    {Y : ℝ≥0 → W → E} (hYadapt : StronglyAdapted V Y)
    (hconv : ∀ t, Filter.Tendsto (fun n ↦ eLpNorm
      (Y t - uniformAdaptedMartingaleSmulProcess M H T (n + 1) t) 1 P)
      Filter.atTop (nhds 0)) :
    Martingale Y V P := by
  apply martingale_of_tendsto_eLpNorm_one_banach
    (fun n ↦ martingale_uniformAdaptedMartingaleSmulProcess
      hM hH K hHK T (n + 1)) hYadapt hconv

/-- Banach-valued local martingales, using Mathlib's local-property
localization convention. -/
def IsBanachLocalMartingale
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → E) (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) : Prop :=
  Locally (fun N ↦ Martingale N V P) V M P

/-- The stopped-and-indicated localization of a Banach-valued process. -/
noncomputable def localizingStoppedProcessBanach
    {W E : Type*} [NormedAddCommGroup E]
    (X : ℝ≥0 → W → E) (tau : W → WithTop ℝ≥0) :
    ℝ≥0 → W → E :=
  stoppedProcess
    (fun t ↦ {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator (X t)) tau

/-- Deterministically stopping a Banach-valued martingale at `T` again
gives a martingale. -/
theorem Martingale.stopAt_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → E} (hM : Martingale M V P) (T : ℝ≥0) :
    Martingale (fun t => M (min t T)) V P := by
  refine ⟨?_, ?_⟩
  · intro t
    exact (hM.stronglyMeasurable (min t T)).mono
      (V.mono (min_le_left t T))
  · intro s t hst
    change P[M (min t T) | V s] =ᵐ[P] M (min s T)
    by_cases hsT : s ≤ T
    · rw [min_eq_left hsT]
      exact hM.condExp_ae_eq (le_min hst hsT)
    · have hTs : T ≤ s := le_of_not_ge hsT
      rw [min_eq_right hTs, min_eq_right (hTs.trans hst)]
      have heq := condExp_of_stronglyMeasurable (V.le s)
        ((hM.stronglyMeasurable T).mono (V.mono hTs)) (hM.integrable T)
      exact Filter.Eventually.of_forall fun omega => congrFun heq omega

/-- A Banach-valued local martingale is genuine through `T` when its
canonical stopped localizations are uniformly integrable at each time up
to `T`.  No path regularity is needed: the localizing sequence is eventually
strictly beyond every deterministic time. -/
theorem
    IsBanachLocalMartingale.martingale_stopAt_of_uniformIntegrable_localizations
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → E} (hM : IsBanachLocalMartingale M V P)
    (hMadapt : StronglyAdapted V M) (T : ℝ≥0)
    (hUI : ∀ t, t ≤ T → UniformIntegrable
      (fun n => localizingStoppedProcessBanach M (hM.localSeq n) t) 1 P) :
    Martingale (fun t => M (min t T)) V P := by
  let X : ℕ → ℝ≥0 → W → E := fun n t =>
    localizingStoppedProcessBanach M (hM.localSeq n) (min t T)
  have hX (n : ℕ) : Martingale (X n) V P :=
    Martingale.stopAt_banach (hM.stoppedProcess_localSeq n) T
  have hYadapt : StronglyAdapted V (fun t => M (min t T)) := by
    intro t
    exact (hMadapt (min t T)).mono (V.mono (min_le_left t T))
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable_banach hX hYadapt
  · intro t
    exact hUI (min t T) (min_le_right t T)
  · intro t
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hX n).integrable t |>.1)
    filter_upwards [hM.isLocalizingSequence_localSeq.tendsto_top] with omega htau
    have hevent : ∀ᶠ n : ℕ in atTop,
        ((((min t T) + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ hM.localSeq n omega) :=
      ((tendsto_order.1 htau).1 (((min t T) + 1 : ℝ≥0) : WithTop ℝ≥0)
        (WithTop.coe_lt_top ((min t T) + 1))).mono fun n hn => hn.le
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hevent] with n hn
    unfold X localizingStoppedProcessBanach stoppedProcess
    have htlt : ((min t T : ℝ≥0) : WithTop ℝ≥0) < hM.localSeq n omega := by
      exact (WithTop.coe_lt_coe.mpr (lt_add_one (min t T))).trans_le hn
    have hpos : (⊥ : WithTop ℝ≥0) < hM.localSeq n omega :=
      bot_le.trans_lt htlt
    rw [min_eq_left htlt.le,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    have hne : hM.localSeq n omega ≠ 0 := ne_of_gt hpos
    simp [Set.indicator, hne]

/-- Stopped-value uniform integrability is a convenient sufficient form of
the Banach-valued finite-horizon local-to-true criterion. -/
theorem
    IsBanachLocalMartingale.martingale_stopAt_of_uniformIntegrable_stoppedValue
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → E} (hM : IsBanachLocalMartingale M V P)
    (hMadapt : StronglyAdapted V M) (T : ℝ≥0)
    (hUI : ∀ t, t ≤ T → UniformIntegrable (fun n =>
      stoppedValue M (fun omega => min (hM.localSeq n omega)
        (t : WithTop ℝ≥0))) 1 P) :
    Martingale (fun t => M (min t T)) V P := by
  apply hM.martingale_stopAt_of_uniformIntegrable_localizations hMadapt T
  intro t ht
  apply UniformIntegrable.mono_norm_banach (hUI t ht)
  · intro n
    exact ((hM.stoppedProcess_localSeq n).integrable t).aestronglyMeasurable
  · intro n omega
    unfold localizingStoppedProcessBanach stoppedProcess stoppedValue
    simp only [Set.indicator_apply]
    split_ifs
    · rw [min_comm]
    · simpa only [norm_zero] using
        (norm_nonneg (M (min (hM.localSeq n omega)
          (t : WithTop ℝ≥0)).untopA omega))

/-- Once the algebraic complex Doléans exponential is known to be a local
martingale, the genuine Novikov density promotes it to a true martingale
through the Girsanov horizon.  Its exact norm is bounded by a deterministic
multiple of the density stopped at the same localization. -/
theorem
    GirsanovDensityData.martingale_stopAt_complexDoleans_of_isBanachLocalMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ)
    (hlocal : IsBanachLocalMartingale
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) V P) :
    Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P := by
  let E : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let D : ℝ≥0 → W → ℝ := fun t omega =>
    doleansDadeExponential M bracket (min t T) omega
  have hEadapt : StronglyAdapted V E := by
    apply stronglyAdapted_complexDoleansDadeExponential
    · exact stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hB c
    · exact stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hDcont (omega : W) : Continuous (fun t => D t omega) := by
    exact (continuous_doleansDadeExponential M bracket omega
      (hdata.continuous_martingale_path omega)
      (hdata.continuous_monotone_bracket omega).1).comp
        (continuous_id.min continuous_const)
  change Martingale (fun t omega => E (min t T) omega) V P
  apply hlocal.martingale_stopAt_of_uniformIntegrable_localizations hEadapt T
  intro t ht
  let tau : ℕ → W → WithTop ℝ≥0 := fun n omega =>
    min (hlocal.localSeq n omega) (t : WithTop ℝ≥0)
  let K : ℝ := Real.exp (c ^ 2 * (t : ℝ) / 2)
  let KD : ℝ≥0 → W → ℝ := fun s omega => K * D s omega
  have hKDmart : Martingale KD V P := by
    change Martingale (K • D) V P
    exact Martingale.smul K hDmart
  have hKDcont : ∀ᵐ omega ∂P, Continuous (fun s => KD s omega) :=
    Filter.Eventually.of_forall fun omega =>
      continuous_const.mul (hDcont omega)
  have htau (n : ℕ) : IsStoppingTime V (tau n) := by
    exact (hlocal.isLocalizingSequence_localSeq.isStoppingTime n).min_const t
  have htau_le (n : ℕ) (omega : W) :
      tau n omega ≤ (t : WithTop ℝ≥0) := min_le_right _ _
  have hUI : UniformIntegrable
      (fun n => stoppedValue KD (tau n)) 1 P :=
    StochasticCalculus.Martingale.uniformIntegrable_stoppedValue_of_bounded hKDmart
      hKDcont t tau htau htau_le
  apply UniformIntegrable.mono_norm_banach hUI
  · intro n
    exact ((hlocal.stoppedProcess_localSeq n).integrable t).aestronglyMeasurable
  · intro n omega
    have hsigma_ne : tau n omega ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (htau_le n omega)
    have hsigma_coe :
        (((tau n omega).untopA : ℝ≥0) : WithTop ℝ≥0) = tau n omega := by
      rw [WithTop.untopA_eq_untop hsigma_ne]
      exact WithTop.coe_untop (tau n omega) hsigma_ne
    have hrle : (tau n omega).untopA ≤ t := by
      apply WithTop.coe_le_coe.mp
      rw [hsigma_coe]
      exact htau_le n omega
    unfold localizingStoppedProcessBanach stoppedProcess stoppedValue
    simp only [Set.indicator_apply]
    split_ifs with hpos
    · have htime :
          (min (t : WithTop ℝ≥0) (hlocal.localSeq n omega)).untopA =
            (tau n omega).untopA := by
          simp only [tau, min_comm]
      rw [htime]
      change ‖E (tau n omega).untopA omega‖ ≤
        ‖K * D (tau n omega).untopA omega‖
      rw [show E (tau n omega).untopA omega =
          complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (tau n omega).untopA omega by rfl,
        norm_complexDoleansDadeExponential_combination]
      have hrT : (tau n omega).untopA ≤ T := hrle.trans ht
      rw [show D (tau n omega).untopA omega =
          doleansDadeExponential M bracket (tau n omega).untopA omega by
        simp only [D, min_eq_left hrT]]
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _)
        (doleansDadeExponential_pos M bracket _ omega))]
      calc
        doleansDadeExponential M bracket (tau n omega).untopA omega *
            Real.exp (c ^ 2 * ((tau n omega).untopA : ℝ) / 2) ≤
          doleansDadeExponential M bracket (tau n omega).untopA omega * K := by
            apply mul_le_mul_of_nonneg_left _
              (doleansDadeExponential_pos M bracket _ omega).le
            apply Real.exp_le_exp.mpr
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left
              (NNReal.coe_le_coe.mpr hrle) (sq_nonneg c)
        _ = K * doleansDadeExponential M bracket
            (tau n omega).untopA omega := by ring
    · simpa only [norm_zero] using
        (norm_nonneg (KD (tau n omega).untopA omega))

/-- Banach-valued stopped evaluation is continuous under pointwise
convergence of stopping times when the underlying path is continuous. -/
theorem tendsto_stoppedProcess_banach_of_tendsto_of_continuous
    {W E : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → W → E}
    {tauN : ℕ → W → WithTop ℝ≥0} {tau : W → WithTop ℝ≥0}
    (hXcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (htau : ∀ omega, Tendsto (fun n ↦ tauN n omega)
      atTop (nhds (tau omega))) (t : ℝ≥0) (omega : W) :
    Tendsto (fun n ↦ stoppedProcess X (tauN n) t omega)
      atTop (nhds (stoppedProcess X tau t omega)) := by
  have htime : Tendsto
      (fun n ↦ min (t : WithTop ℝ≥0) (tauN n omega)) atTop
      (nhds (min (t : WithTop ℝ≥0) (tau omega))) :=
    tendsto_const_nhds.min (htau omega)
  have hne : min (t : WithTop ℝ≥0) (tau omega) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have huntop : Tendsto
      (fun n ↦ (min (t : WithTop ℝ≥0) (tauN n omega)).untopA) atTop
      (nhds ((min (t : WithTop ℝ≥0) (tau omega)).untopA)) :=
    (WithTop.tendsto_untopA hne).comp htime
  exact (hXcont omega).continuousAt.tendsto.comp huntop

/-- The stopped-and-indicated Banach-valued localization inherits the same
pathwise convergence at a strictly positive limiting stop. -/
theorem tendsto_localizingStoppedProcessBanach_of_tendsto_of_continuous_of_pos
    {W E : Type*} [NormedAddCommGroup E]
    {X : ℝ≥0 → W → E}
    {tauN : ℕ → W → WithTop ℝ≥0} {tau : W → WithTop ℝ≥0}
    (hXcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (htau : ∀ omega, Tendsto (fun n ↦ tauN n omega)
      atTop (nhds (tau omega)))
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega)
    (t : ℝ≥0) (omega : W) :
    Tendsto (fun n ↦ localizingStoppedProcessBanach X (tauN n) t omega)
      atTop (nhds (localizingStoppedProcessBanach X tau t omega)) := by
  have hstop := tendsto_stoppedProcess_banach_of_tendsto_of_continuous
    hXcont htau t omega
  have heventually : ∀ᶠ n in atTop,
      (⊥ : WithTop ℝ≥0) < tauN n omega :=
    (htau omega) (Ioi_mem_nhds (hpos omega))
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
    hpos omega
  unfold localizingStoppedProcessBanach
  simp_rw [stoppedProcess_indicator_comm]
  rw [Set.indicator_of_mem hmem]
  apply (tendsto_congr' ?_).2 hstop
  filter_upwards [heventually] with n hn
  have hnmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tauN n omega} := hn
  rw [Set.indicator_of_mem hnmem]

/-- A continuous adapted Banach-valued process remains adapted after the
stopped-and-indicated localization used by `Locally`. -/
theorem stronglyAdapted_localizingStoppedProcessBanach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} {tau : W → WithTop ℝ≥0}
    (hX : StronglyAdapted V X)
    (hXcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (htau : IsStoppingTime V tau) :
    StronglyAdapted V (localizingStoppedProcessBanach X tau) := by
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[V 0] A := by
    change MeasurableSet[V 0] {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  intro t
  rw [show localizingStoppedProcessBanach X tau t =
      A.indicator (stoppedProcess X tau t) by
    unfold localizingStoppedProcessBanach
    exact stoppedProcess_indicator_comm t]
  exact (hX.stoppedProcess hXcont htau t).indicator (V.mono bot_le A hA)

/-- Along any localizing sequence, the indicated localization of a
continuous adapted Banach-valued process converges in measure back to the
original process at each deterministic time. -/
theorem IsLocalizingSequence.tendstoInMeasure_localizingStoppedProcessBanach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence V tau P)
    (hX : StronglyAdapted V X)
    (hXcont : ∀ omega, Continuous (fun t ↦ X t omega)) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ localizingStoppedProcessBanach X (tau n) t) atTop (X t) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact ((stronglyAdapted_localizingStoppedProcessBanach
      hX hXcont (htau.isStoppingTime n) t).mono (V.le t)).aestronglyMeasurable
  · filter_upwards [htau.tendsto_top] with omega homega
    have hconv :=
      tendsto_localizingStoppedProcessBanach_of_tendsto_of_continuous_of_pos
        hXcont (fun _ ↦ homega) (fun _ ↦ by simp) t omega
    have htop : localizingStoppedProcessBanach X (fun _ ↦ ⊤) t omega =
        X t omega := by
      unfold localizingStoppedProcessBanach stoppedProcess
      change {omega : W | (⊥ : WithTop ℝ≥0) < ⊤}.indicator (X t) omega =
        X t omega
      simp
    rw [htop] at hconv
    exact hconv

/-- Banach-valued elementary transforms commute exactly with the indicated
stopping convention, so they can reuse the real integrator's localizer. -/
theorem localizingStoppedProcessBanach_elementaryMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → E)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcessBanach
        (elementaryMartingaleSmulProcess M a b Z) tau =
      elementaryMartingaleSmulProcess
        (localizingStoppedProcess M tau) a b Z := by
  funext t omega
  unfold localizingStoppedProcessBanach localizingStoppedProcess stoppedProcess
  by_cases hA : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  · simp only [Set.indicator_of_mem hA]
    simp only [elementaryMartingaleSmulProcess]
    congr 1
    have hcoe_untopA (x : WithTop ℝ≥0) (hx : x ≠ ⊤) :
        ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
      rw [WithTop.untopA_eq_untop hx, WithTop.coe_untop]
    have hcoe_min (x y : ℝ≥0) :
        ((min x y : ℝ≥0) : WithTop ℝ≥0) =
          min (x : WithTop ℝ≥0) (y : WithTop ℝ≥0) := by
      norm_cast
    have hstopmin (c : ℝ≥0) :
        min (min (t : WithTop ℝ≥0) (tau omega)).untopA c =
          (min ((min t c : ℝ≥0) : WithTop ℝ≥0) (tau omega)).untopA := by
      apply WithTop.coe_injective
      rw [hcoe_min, hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)),
        hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)), hcoe_min]
      ac_rfl
    rw [hstopmin b, hstopmin a]
    simp only [Set.indicator_of_mem hA]
  · simp only [elementaryMartingaleSmulProcess,
      Set.indicator_of_notMem hA, sub_self, zero_smul]

/-- A bounded Banach-valued elementary transform against a real local
martingale is a Banach-valued local martingale. -/
theorem IsLocalMartingale.elementaryMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : IsLocalMartingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    IsBanachLocalMartingale
      (elementaryMartingaleSmulProcess M a b Z) V P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun n ↦ ?_⟩
  let N : ℝ≥0 → W → ℝ := localizingStoppedProcess M (tau n)
  have hN : Martingale N V P := hstopped n
  have hIntegral : Martingale
      (StochasticCalculus.elementaryMartingaleSmulProcess N a b Z) V P :=
    martingale_elementaryMartingaleSmulProcess
      hN hab hZ C hZbound
  change Martingale (localizingStoppedProcessBanach
    (StochasticCalculus.elementaryMartingaleSmulProcess M a b Z) (tau n)) V P
  rw [localizingStoppedProcessBanach_elementaryMartingaleSmulProcess]
  exact hIntegral

/-- Indicated stopping distributes over finite sums of Banach-valued
processes. -/
theorem localizingStoppedProcessBanach_finset_sum
    {W E I : Type*} [NormedAddCommGroup E]
    (X : I → ℝ≥0 → W → E) (S : Finset I)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcessBanach (∑ i ∈ S, X i) tau =
      ∑ i ∈ S, localizingStoppedProcessBanach (X i) tau := by
  classical
  funext t omega
  unfold localizingStoppedProcessBanach stoppedProcess
  by_cases hA : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  · simp only [Set.indicator_of_mem hA, Finset.sum_apply]
  · simp only [Set.indicator_of_notMem hA]
    simp only [Finset.sum_apply, Set.indicator_of_notMem hA,
      Finset.sum_const_zero]

/-- Finite Banach-valued elementary transforms commute with the indicated
stopping convention term by term. -/
theorem localizingStoppedProcessBanach_elementaryMartingaleSmulSum
    {W E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → E)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcessBanach
        (elementaryMartingaleSmulSum M S a b Z) tau =
      elementaryMartingaleSmulSum
        (localizingStoppedProcess M tau) S a b Z := by
  classical
  unfold elementaryMartingaleSmulSum
  rw [localizingStoppedProcessBanach_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact localizingStoppedProcessBanach_elementaryMartingaleSmulProcess
    M (a i) (b i) (Z i) tau

/-- Uniform-grid Banach-valued transforms of a bounded adapted coefficient
against a real local martingale are local martingales, with the integrator's
own localizing sequence. -/
theorem IsLocalMartingale.uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : IsLocalMartingale M V P) (hH : StronglyAdapted V H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    IsBanachLocalMartingale
      (uniformAdaptedMartingaleSmulProcess M H T n) V P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun k ↦ ?_⟩
  let N : ℝ≥0 → W → ℝ := localizingStoppedProcess M (tau k)
  have hN : Martingale N V P := hstopped k
  have hsum : Martingale
      (StochasticCalculus.uniformAdaptedMartingaleSmulProcess N H T n) V P :=
    martingale_uniformAdaptedMartingaleSmulProcess hN hH K hHK T n
  change Martingale (localizingStoppedProcessBanach
    (StochasticCalculus.uniformAdaptedMartingaleSmulProcess M H T n) (tau k)) V P
  unfold StochasticCalculus.uniformAdaptedMartingaleSmulProcess
  rw [localizingStoppedProcessBanach_elementaryMartingaleSmulSum]
  exact hsum

/-- A fixed localizing sequence passes local martingality through
Banach-valued pointwise-in-time `L¹` limits. -/
theorem isLocalMartingale_of_stopped_tendsto_eLpNorm_one_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence V tau P)
    (hX : ∀ n k, Martingale
      (localizingStoppedProcessBanach (X n) (tau k)) V P)
    (hYadapt : ∀ k, StronglyAdapted V
      (localizingStoppedProcessBanach Y (tau k)))
    (hconv : ∀ k t, Filter.Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcessBanach Y (tau k) t -
        localizingStoppedProcessBanach (X n) (tau k) t) 1 P)
      Filter.atTop (nhds 0)) :
    IsBanachLocalMartingale Y V P := by
  refine ⟨tau, htau, fun k ↦ ?_⟩
  exact martingale_of_tendsto_eLpNorm_one_banach
    (fun n ↦ hX n k) (hYadapt k) (hconv k)

/-- A continuous Banach-valued local martingale is a true martingale once
its stopped values along an explicit localizing sequence are uniformly
integrable at each deterministic time.  This packages the localization,
convergence-in-measure, and Vitali steps needed for complex exponential
martingales. -/
theorem martingale_of_localizingSequence_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {Y : ℝ≥0 → W → E} {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence V tau P)
    (hmart : ∀ n, Martingale
      (localizingStoppedProcessBanach Y (tau n)) V P)
    (hadapt : StronglyAdapted V Y)
    (hcont : ∀ omega, Continuous (fun t ↦ Y t omega))
    (hUI : ∀ t, UniformIntegrable
      (fun n ↦ localizingStoppedProcessBanach Y (tau n) t) 1 P) :
    Martingale Y V P := by
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable_banach
    hmart hadapt hUI
  exact fun t ↦
    StochasticCalculus.IsLocalizingSequence.tendstoInMeasure_localizingStoppedProcessBanach
      htau hadapt hcont t

/-- Fourier-increment form of the stochastic-exponential martingale
identity.  It is the exact stochastic-calculus input needed by the
characteristic-function proof of Girsanov: on each past event, the current
density weighted by the increment character evolves by the deterministic
Gaussian factor. -/
def GirsanovFourierIncrementCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W}, MeasurableSet[V s] A → ∀ c : ℝ,
    (∫ omega in A,
      doleansDadeExponential M bracket (min t T) omega •
        Complex.exp (((c * (X t omega - X s omega) : ℝ) : ℂ) *
          Complex.I) ∂P) =
      Complex.exp
          (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P

/-- The normalized complex exponential based at time `s`.  Before `s` this
is just the Girsanov density process; after `s` it tests the characteristic
function of the increment of `X`. -/
def girsanovFourierIncrementProcess
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ) (T s : ℝ≥0) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (doleansDadeExponential M bracket (min t T) omega : ℂ) *
    Complex.exp
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I +
        (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))

/-- Before its base time, the normalized Fourier-increment process is just
the stopped density process. -/
theorem girsanovFourierIncrementProcess_of_le_base
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hts : t ≤ s) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        (doleansDadeExponential M bracket (min t T) omega : ℂ) := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_left hts, tsub_eq_zero_of_le hts]
  simp only [sub_self, mul_zero, Complex.ofReal_zero, zero_mul,
    NNReal.coe_zero, zero_div, add_zero, Complex.exp_zero, mul_one]

/-- After its base time, a Fourier-increment process is a bounded
past-measurable multiple of the base-zero process. -/
theorem girsanovFourierIncrementProcess_of_base_le
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hst : s ≤ t) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        Complex.exp
            (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
              ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ))) *
          girsanovFourierIncrementProcess M bracket X T 0 c t omega := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_right hst]
  have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
  rw [hmin0, tsub_zero]
  rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← Complex.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  push_cast
  ring_nf

/-- Adaptedness of the density, bracket, and tested process makes every
normalized Fourier-increment process adapted. -/
theorem stronglyAdapted_girsanovFourierIncrementProcess
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket X : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X) (T s : ℝ≥0) (c : ℝ) :
    StronglyAdapted V (girsanovFourierIncrementProcess M bracket X T s c) := by
  intro t
  have hdensity : StronglyMeasurable[V t]
      (doleansDadeExponential M bracket (min t T)) :=
    (stronglyAdapted_doleansDadeExponential hM hbracket (min t T)).mono
      (V.mono (min_le_left _ _))
  have hdensityC : StronglyMeasurable[V t] (fun omega ↦
      (doleansDadeExponential M bracket (min t T) omega : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hdensity
  have hinc : StronglyMeasurable[V t]
      (fun omega ↦ X t omega - X (min t s) omega) :=
    (hX t).sub ((hX (min t s)).mono (V.mono (min_le_left _ _)))
  have hchar : StronglyMeasurable[V t] (fun omega ↦
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I
  exact hdensityC.mul (Complex.continuous_exp.comp_stronglyMeasurable
    (hchar.add stronglyMeasurable_const))

/-- The normalized Fourier-increment process is stochastically continuous
when the tested process is.  Continuous density paths and continuity of all
deterministic time operations handle the remaining factors. -/
theorem tendstoInMeasure_girsanovFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket X : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (hXstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => X (a n)) atTop (X r))
    (T s : ℝ≥0) (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n => girsanovFourierIncrementProcess M bracket X T s c (a n))
      atTop (girsanovFourierIncrementProcess M bracket X T s c r) := by
  have hminT : Tendsto (fun n => min (a n) T) atTop (nhds (min r T)) :=
    ha.min tendsto_const_nhds
  have hdensityMeas (n : ℕ) : AEStronglyMeasurable
      (doleansDadeExponential M bracket (min (a n) T)) P :=
    ((stronglyAdapted_doleansDadeExponential hM hbracket
      (min (a n) T)).mono (V.le (min (a n) T))).aestronglyMeasurable
  have hdensityLim : TendstoInMeasure P (fun n =>
      doleansDadeExponential M bracket (min (a n) T)) atTop
      (doleansDadeExponential M bracket (min r T)) := by
    apply tendstoInMeasure_of_tendsto_ae hdensityMeas
    exact Filter.Eventually.of_forall fun omega =>
      (continuous_doleansDadeExponential M bracket omega
        (hMcont omega) (hbracketCont omega)).continuousAt.tendsto.comp hminT
  have hminS : Tendsto (fun n => min (a n) s) atTop (nhds (min r s)) :=
    ha.min tendsto_const_nhds
  have hXleft := hXstoch r a ha
  have hXright := hXstoch (min r s) (fun n => min (a n) s) hminS
  let subReal : ℝ → ℝ → ℝ := fun x y => x - y
  have hsubReal : Continuous subReal.uncurry := by
    dsimp only [subReal, Function.uncurry]
    fun_prop
  have hincLim : TendstoInMeasure P (fun n omega =>
      subReal (X (a n) omega) (X (min (a n) s) omega)) atTop
      (fun omega => subReal (X r omega) (X (min r s) omega)) :=
    TendstoInMeasure.continuous_comp₂
      (fun n => ((hX (a n)).mono (V.le (a n))).aestronglyMeasurable)
      (fun n => ((hX (min (a n) s)).mono
        (V.le (min (a n) s))).aestronglyMeasurable)
      hXleft hXright hsubReal
  have htsub : Tendsto (fun n => a n - s) atTop (nhds (r - s)) := by
    exact ha.sub tendsto_const_nhds
  have htime : Tendsto (fun n => ((a n - s : ℝ≥0) : ℝ)) atTop
      (nhds ((r - s : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.tendsto (r - s)).comp htsub
  have htimeLim : TendstoInMeasure P
      (fun n => fun _ : W => ((a n - s : ℝ≥0) : ℝ)) atTop
      (fun _ => ((r - s : ℝ≥0) : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ => aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ => htime
  let phase : ℝ → ℝ → ℂ := fun inc dt =>
    Complex.exp
      (((c * inc : ℝ) : ℂ) * Complex.I +
        (((dt * c ^ 2 / 2 : ℝ) : ℂ)))
  have hphase : Continuous phase.uncurry := by
    dsimp only [phase, Function.uncurry]
    fun_prop
  have hincMeas (n : ℕ) : AEStronglyMeasurable (fun omega =>
      subReal (X (a n) omega) (X (min (a n) s) omega)) P :=
    (((hX (a n)).mono (V.le (a n))).aestronglyMeasurable).sub
      (((hX (min (a n) s)).mono
        (V.le (min (a n) s))).aestronglyMeasurable)
  have hphaseLim : TendstoInMeasure P (fun n omega =>
      phase (subReal (X (a n) omega) (X (min (a n) s) omega))
        ((a n - s : ℝ≥0) : ℝ)) atTop
      (fun omega => phase (subReal (X r omega) (X (min r s) omega))
        ((r - s : ℝ≥0) : ℝ)) :=
    TendstoInMeasure.continuous_comp₂ hincMeas
      (fun _ => aestronglyMeasurable_const)
      hincLim htimeLim hphase
  let finish : ℝ → ℂ → ℂ := fun d z => (d : ℂ) * z
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  change TendstoInMeasure P (fun n omega =>
    finish (doleansDadeExponential M bracket (min (a n) T) omega)
      (phase (subReal (X (a n) omega) (X (min (a n) s) omega))
        ((a n - s : ℝ≥0) : ℝ))) atTop
    (fun omega =>
      finish (doleansDadeExponential M bracket (min r T) omega)
        (phase (subReal (X r omega) (X (min r s) omega))
          ((r - s : ℝ≥0) : ℝ)))
  exact TendstoInMeasure.continuous_comp₂ hdensityMeas
    (fun n => hphase.comp_aestronglyMeasurable
      ((hincMeas n).prodMk aestronglyMeasurable_const))
    hdensityLim hphaseLim hfinish

/-- Predictable Girsanov data discharge stochastic continuity of every
normalized Fourier process for the drift-shifted pre-Brownian driver. -/
theorem
    GirsanovDensityData.tendstoInMeasure_girsanovFourierIncrementProcess_shifted
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (s : ℝ≥0) (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      girsanovFourierIncrementProcess M bracket
        (girsanovShiftedBrownian B theta T) T s c (a n)) atTop
      (girsanovFourierIncrementProcess M bracket
        (girsanovShiftedBrownian B theta T) T s c r) := by
  apply tendstoInMeasure_girsanovFourierIncrementProcess
    hdata.adapted_martingale hdata.adapted_bracket
    (stronglyAdapted_girsanovShiftedBrownian hBadapt htheta)
    hdata.continuous_martingale_path
    (fun omega => (hdata.continuous_monotone_bracket omega).1)
    (fun r a ha => hdata.tendstoInMeasure_girsanovShiftedBrownian
      hB hsm htheta hbracketTerminal hcross ha) T s c ha

/-- The oscillatory character has unit modulus, so the exact norm of the
normalized Fourier process is the density times its deterministic Gaussian
factor. -/
theorem norm_girsanovFourierIncrementProcess
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (omega : W) :
    ‖girsanovFourierIncrementProcess M bracket X T s c t omega‖ =
      doleansDadeExponential M bracket (min t T) omega *
        Real.exp (((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2) := by
  unfold girsanovFourierIncrementProcess
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (doleansDadeExponential_pos M bracket (min t T) omega),
    Complex.norm_exp]
  apply congrArg (fun r : ℝ ↦
    doleansDadeExponential M bracket (min t T) omega * r)
  apply congrArg Real.exp
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_sub, mul_one, neg_zero, zero_add]

/-- If the stopped density is a martingale, every time section of the
normalized Fourier process is integrable.  The proof uses its exact modulus,
not a separate moment assumption on the tested process. -/
theorem integrable_girsanovFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (s : ℝ≥0) (c : ℝ) (t : ℝ≥0) :
    Integrable (girsanovFourierIncrementProcess M bracket X T s c t) P := by
  have hmeas : AEStronglyMeasurable
      (girsanovFourierIncrementProcess M bracket X T s c t) P :=
    ((stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T s c t).mono (V.le t)).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  let k : ℝ := Real.exp (((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2)
  have hrhs : Integrable (fun omega ↦
      doleansDadeExponential M bracket (min t T) omega * k) P :=
    (hdensity.integrable t).mul_const k
  apply hrhs.congr
  exact Filter.Eventually.of_forall fun omega ↦ by
    change doleansDadeExponential M bracket (min t T) omega * k =
      ‖girsanovFourierIncrementProcess M bracket X T s c t omega‖
    simpa only [k] using
      (norm_girsanovFourierIncrementProcess M bracket X T s t c omega).symm

/-- The exact Girsanov density hypotheses supply integrability of every
time section of the normalized Fourier process. -/
theorem GirsanovDensityData.integrable_fourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hX : StronglyAdapted V X) (s : ℝ≥0) (c : ℝ) (t : ℝ≥0) :
    Integrable (girsanovFourierIncrementProcess M bracket X T s c t) P :=
  integrable_girsanovFourierIncrementProcess
    h.adapted_martingale h.adapted_bracket hX h.martingale_densityProcess s c t

/-- Along every convergent sequence of deterministic times, the normalized
Girsanov Fourier process is uniformly integrable.  Its exact modulus is a
bounded deterministic multiple of the stopped density, whose values before
the terminal horizon are uniformly integrable by the martingale property. -/
theorem GirsanovDensityData.uniformIntegrable_fourierIncrementProcess_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hX : StronglyAdapted V X) (s : ℝ≥0) (c : ℝ)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    UniformIntegrable
      (fun n => girsanovFourierIncrementProcess M bracket X T s c (a n))
      1 P := by
  obtain ⟨R, hR⟩ := ha.bddAbove_range
  have hdensityUI : UniformIntegrable (fun n omega =>
      doleansDadeExponential M bracket (min (a n) T) omega) 1 P := by
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic h.martingale_densityProcess T)
        (fun n => ⟨min (a n) T, by
          simpa only [Set.mem_Iic] using min_le_right (a n) T⟩)
    simpa only [min_eq_left (min_le_right _ T)] using hUI
  obtain ⟨N, hN⟩ := exists_nat_ge
    (Real.exp ((R : ℝ) * c ^ 2 / 2))
  have hmultiple : UniformIntegrable (fun n omega =>
      N • doleansDadeExponential M bracket (min (a n) T) omega) 1 P :=
    StochasticCalculus.UniformIntegrable.nsmul_banach hdensityUI (by norm_num) N
  apply StochasticCalculus.UniformIntegrable.mono_norm_banach hmultiple
  · intro n
    exact ((stronglyAdapted_girsanovFourierIncrementProcess
      h.adapted_martingale h.adapted_bracket hX T s c (a n)).mono
        (V.le (a n))).aestronglyMeasurable
  · intro n omega
    rw [norm_girsanovFourierIncrementProcess]
    have htimeNN : a n - s ≤ R :=
      (tsub_le_self.trans (hR (Set.mem_range_self n)))
    have htime : (((a n - s : ℝ≥0) : ℝ) * c ^ 2 / 2) ≤
        (R : ℝ) * c ^ 2 / 2 := by
      have htime' : ((a n - s : ℝ≥0) : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast htimeNN
      nlinarith [sq_nonneg c]
    have hexp : Real.exp (((a n - s : ℝ≥0) : ℝ) * c ^ 2 / 2) ≤
        Real.exp ((R : ℝ) * c ^ 2 / 2) := Real.exp_le_exp.mpr htime
    have hdensityPos :=
      doleansDadeExponential_pos M bracket (min (a n) T) omega
    calc
      doleansDadeExponential M bracket (min (a n) T) omega *
          Real.exp (((a n - s : ℝ≥0) : ℝ) * c ^ 2 / 2) ≤
          doleansDadeExponential M bracket (min (a n) T) omega *
            Real.exp ((R : ℝ) * c ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hexp hdensityPos.le
      _ ≤ doleansDadeExponential M bracket (min (a n) T) omega * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hdensityPos.le
      _ = ‖N • doleansDadeExponential M bracket (min (a n) T) omega‖ := by
        rw [nsmul_eq_mul, norm_mul, norm_natCast, Real.norm_eq_abs,
          abs_of_pos hdensityPos]
        ring

/-- Martingale form of the Fourier-increment input. -/
def GirsanovFourierIncrementMartingaleCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ s c, Martingale (girsanovFourierIncrementProcess M bracket X T s c) V P

/-- Eventwise martingale identities for every normalized Fourier process,
tested only at positive rational subdivisions of a deterministic horizon. -/
def GirsanovFourierIncrementRationalCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (s : ℝ≥0) (c : ℝ) (U : ℝ≥0) {k j : ℕ},
    0 < k → 0 < j → j ≤ k → ∀ {A : Set W},
    MeasurableSet[V (U * (j : ℝ≥0) / (k : ℝ≥0))] A →
      (∫ omega in A, girsanovFourierIncrementProcess M bracket X T s c
        (U * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
        ∫ omega in A,
          girsanovFourierIncrementProcess M bracket X T s c U omega ∂P

/-- It suffices to prove the normalized Fourier martingale identity on
positive rational subdivisions.  Stochastic continuity and uniform
integrability, both consequences of the Girsanov hypotheses, extend those
identities to every pair of deterministic times. -/
theorem GirsanovDensityData.girsanovFourierIncrementMartingaleCondition_of_rational
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hrational : GirsanovFourierIncrementRationalCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T := by
  intro s c
  let X := girsanovShiftedBrownian B theta T
  have hX : StronglyAdapted V X :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt htheta
  apply
    martingale_of_uniformRational_setIntegral_eq_of_tendstoInMeasure_of_uniformIntegrable
      (stronglyAdapted_girsanovFourierIncrementProcess
        hdata.adapted_martingale hdata.adapted_bracket hX T s c)
      (fun t => hdata.integrable_fourierIncrementProcess hX s c t)
  · intro r a ha
    exact hdata.tendstoInMeasure_girsanovFourierIncrementProcess_shifted
      hB hsm hBadapt htheta hbracketTerminal hcross s c ha
  · intro r a ha
    exact hdata.uniformIntegrable_fourierIncrementProcess_tendsto
      hX s c ha
  · exact hrational s c

/-- A stopped complex Doléans martingale supplies the base-zero Girsanov
Fourier martingale up to the horizon; after the horizon it is pasted to the
ordinary Brownian Fourier martingale. -/
theorem
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0} (c : ℝ)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hcomplex : Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : Martingale (brownianFourierIncrementProcess B T c) V P) :
    Martingale (girsanovFourierIncrementProcess M bracket X T 0 c) V P := by
  let E : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let Estop : ℝ≥0 → W → ℂ := fun t omega ↦ E (min t T) omega
  let Y := brownianFourierIncrementProcess B T c
  let H : W → ℂ := E T
  have hEstop : Martingale Estop V P := by
    simpa only [Estop, E] using hcomplex
  have hY : Martingale Y V P := by simpa only [Y] using hBrownian
  have hHmeas : StronglyMeasurable[V T] H := by
    simpa only [H, Estop, min_self] using hEstop.stronglyMeasurable T
  have hHint : Integrable H P := by
    simpa only [H, Estop, min_self] using hEstop.integrable T
  have hHYint (t : ℝ≥0) :
      Integrable (fun omega ↦ H omega * Y t omega) P := by
    apply hHint.mul_bdd
    · exact ((hY.stronglyMeasurable t).mono
        (V.le t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega ↦ by
        rw [show ‖Y t omega‖ =
            Real.exp (((t - min t T : ℝ≥0) : ℝ) * c ^ 2 / 2) by
          exact norm_brownianFourierIncrement B c (min t T) t omega]
  have hmatch : (fun omega ↦ H omega * Y T omega) = Estop T := by
    funext omega
    simp only [H, Y, Estop, min_self, brownianFourierIncrementProcess,
      brownianFourierIncrement_self, mul_one]
  have hpaste : Martingale (martingalePasteMul Estop Y H T) V P :=
    martingale_martingalePasteMul_of_integrable
      hEstop hY hHmeas hHYint hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T 0 c)
  intro t
  filter_upwards [hXzero] with omega hzero
  by_cases htT : t ≤ T
  · have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, Estop,
        min_eq_left htT]
    rw [hpasteEq]
    change complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold girsanovFourierIncrementProcess
    rw [min_eq_left htT]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_left htT]
    congr 2
    push_cast
    ring
  · have hTt : T ≤ t := le_of_not_ge htT
    have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E T omega * brownianFourierIncrement B c T t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, H, Y,
        brownianFourierIncrementProcess, min_eq_right hTt]
    rw [hpasteEq]
    change complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) T omega *
      brownianFourierIncrement B c T t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold brownianFourierIncrement girsanovFourierIncrementProcess
    rw [min_eq_right hTt]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_right hTt]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    rw [NNReal.coe_sub hTt]
    push_cast
    ring_nf

/-- It suffices to construct the complex exponential martingale at base
time zero.  Every other base time is obtained by deterministic-time pasting:
the density martingale is used before the base, and a bounded
past-measurable multiple of the base-zero martingale is used afterward. -/
theorem girsanovFourierIncrementMartingaleCondition_of_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hzero : ∀ c, Martingale
      (girsanovFourierIncrementProcess M bracket X T 0 c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  intro s c
  let Z : ℝ≥0 → W → ℂ := fun t omega ↦
    (doleansDadeExponential M bracket (min t T) omega : ℂ)
  let Y := girsanovFourierIncrementProcess M bracket X T 0 c
  let H : W → ℂ := fun omega ↦
    Complex.exp
      (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ)))
  have hZ : Martingale Z V P := by
    simpa only [Z, Complex.ofRealCLM_apply] using
      Martingale.comp_continuousLinearMap hdensity Complex.ofRealCLM
  have hH : StronglyMeasurable[V s] H := by
    have hinc : StronglyMeasurable[V s] (fun omega ↦
        X s omega - X 0 omega) :=
      (hX s).sub ((hX 0).mono (V.mono bot_le))
    exact Complex.continuous_exp.comp_stronglyMeasurable
      (((Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I).add
          stronglyMeasurable_const).neg
  let K : ℝ := Real.exp (-(c ^ 2 * (s : ℝ) / 2))
  have hHbound (omega : W) : ‖H omega‖ ≤ K := by
    dsimp only [H, K]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_sub, mul_one, neg_zero, zero_add, le_refl]
  have hmatch : (fun omega ↦ H omega * Y s omega) = Z s := by
    have hright := girsanovFourierIncrementProcess_of_base_le
      M bracket X T s s c (le_refl s)
    have hleft := girsanovFourierIncrementProcess_of_le_base
      M bracket X T s s c (le_refl s)
    exact hright.symm.trans hleft
  have hpaste : Martingale (martingalePasteMul Z Y H s) V P :=
    martingale_martingalePasteMul hZ (hzero c) hH K hHbound hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T s c)
  intro t
  exact Filter.Eventually.of_forall fun omega ↦ by
    by_cases hts : t ≤ s
    · rw [show martingalePasteMul Z Y H s t omega = Z t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_le_base
        M bracket X T s t c hts).symm omega
    · have hst : s ≤ t := le_of_not_ge hts
      rw [show martingalePasteMul Z Y H s t omega = H omega * Y t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_base_le
        M bracket X T s t c hst).symm omega

/-- A family of stopped complex Doléans martingales, together with the
ordinary post-horizon Brownian Fourier martingales, yields the full
Girsanov Fourier family. -/
theorem
    girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hcomplex : ∀ c, Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : ∀ c,
      Martingale (brownianFourierIncrementProcess B T c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  apply girsanovFourierIncrementMartingaleCondition_of_zero
    hM hbracket hX hdensity
  intro c
  exact
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
      c hM hbracket hX hXeq hXzero (hcomplex c) (hBrownian c)

/-- The full Fourier martingale condition follows as soon as each algebraic
complex Doléans exponential is locally a martingale.  Novikov promotes the
local family through `T`, after which deterministic-time pasting supplies
all base times and the ordinary Brownian Fourier martingale supplies the
post-horizon continuation. -/
theorem GirsanovDensityData.girsanovFourierIncrementMartingaleCondition_of_localComplexDoleans
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hlocal : ∀ c, IsBanachLocalMartingale
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)) V P)
    (hBrownian : ∀ c,
      Martingale (brownianFourierIncrementProcess B T c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  apply girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
    hdata.adapted_martingale hdata.adapted_bracket hX hXeq hXzero
    hdata.martingale_densityProcess
  · intro c
    exact hdata.martingale_stopAt_complexDoleans_of_isBanachLocalMartingale
      hB hC c (hlocal c)
  · exact hBrownian

/-- The complex exponential martingale family implies the eventwise
Fourier-increment identity used by the Girsanov endpoint. -/
theorem girsanovFourierIncrementCondition_of_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovFourierIncrementMartingaleCondition P V M bracket X T) :
    GirsanovFourierIncrementCondition P V M bracket X T := by
  intro s t hst A hA c
  let v : ℂ := (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))
  let char : W → ℂ := fun omega ↦
    (((c * (X t omega - X s omega) : ℝ) : ℂ) * Complex.I)
  have hmartEq := (h s c).setIntegral_eq hst hA
  have hmartEq' :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
      ∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
          Complex.exp (char omega + v) ∂P := by
    simpa only [girsanovFourierIncrementProcess, min_self, sub_self,
      zero_mul, mul_zero, Complex.ofReal_zero, zero_mul, tsub_self, NNReal.coe_zero,
      zero_div, add_zero, Complex.exp_zero, mul_one, min_eq_right hst,
      char, v] using hmartEq
  change (∫ omega in A,
      (doleansDadeExponential M bracket (min t T) omega : ℝ) •
        Complex.exp (char omega) ∂P) =
    Complex.exp (-v) *
      ∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P
  calc
    (∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) ∂P) =
        ∫ omega in A, Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v)) ∂P := by
      apply setIntegral_congr_fun (V.le s A hA)
      intro omega _
      change (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) =
        Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v))
      rw [Complex.real_smul]
      calc
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega) =
            (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              Complex.exp (-v + (char omega + v)) := by
          congr 2
          ring
        _ = (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              (Complex.exp (-v) * Complex.exp (char omega + v)) := by
          rw [Complex.exp_add]
        _ = Complex.exp (-v) *
              ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
                Complex.exp (char omega + v)) := by
          ring
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v) ∂P := by
      rw [integral_const_mul]
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
      rw [hmartEq']

/-- The Fourier-increment stochastic-exponential identity gives the full
pre-Brownian law under the terminal Girsanov measure.  In particular this
route needs neither a separate integrability assumption for the shifted
process nor an all-path continuity representative. -/
theorem GirsanovDensityData.isPreBrownianReal_of_fourierIncrementCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket X T) :
    IsPreBrownianReal X (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hzeroQ : X 0 =ᵐ[Q] fun _ ↦ 0 :=
    h.mutuallyAbsolutelyContinuous.1.ae_eq hzero
  apply isPreBrownianReal_of_map_restrict_increment_eq_of_ae_zero
    hadapt hzeroQ
  intro s t hst A hA
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc Q := by
    exact ((((hadapt t).mono (V.le t)).aemeasurable).sub
      (((hadapt s).mono (V.le s)).aemeasurable)).mono_ac
        (show Q ≪ P from girsanovMeasure_absolutelyContinuous P M bracket T)
  have hincR : AEMeasurable inc (Q.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  let : IsFiniteMeasure (Q A • gaussianReal 0 (t - s)) :=
    (gaussianReal 0 (t - s)).smul_finite (measure_ne_top Q A)
  apply Measure.ext_of_charFun
  funext c
  rw [charFun_apply_real]
  change (∫ x, Complex.exp ((c : ℂ) * (x : ℂ) * Complex.I)
    ∂((Q.restrict A).map inc)) = _
  rw [integral_map hincR (by fun_prop)]
  let f : W → ℂ := fun omega ↦
    Complex.exp ((c : ℂ) * (inc omega : ℂ) * Complex.I)
  have hf : StronglyMeasurable[V t] f := by
    have hincStrong : StronglyMeasurable[V t] inc :=
      (hadapt t).sub ((hadapt s).mono (V.mono hst))
    apply Complex.continuous_exp.comp_stronglyMeasurable
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hincStrong.const_mul c)).mul_const Complex.I
  have hfint : Integrable f Q :=
    (integrable_const (1 : ℝ)).mono
      ((hf.mono (V.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [f, ← Complex.ofReal_mul,
          Complex.norm_exp_ofReal_mul_I, norm_one] using (le_refl (1 : ℝ)))
  have hAt : MeasurableSet[V t] A := V.mono hst A hA
  have hcurrent :=
    h.setIntegral_girsanovMeasure_eq_densityProcess_smul hf hfint hAt
  have hmass :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
        (Q A).toReal := by
    have honeMeas : StronglyMeasurable[V s] (fun _ : W ↦ (1 : ℂ)) := by
      fun_prop
    have honeInt : Integrable (fun _ : W ↦ (1 : ℂ)) Q :=
      integrable_const 1
    have hone := h.setIntegral_girsanovMeasure_eq_densityProcess_smul
      honeMeas honeInt hA
    calc
      (∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
          ∫ omega in A,
            doleansDadeExponential M bracket (min s T) omega • (1 : ℂ) ∂P := by
        apply setIntegral_congr_fun (V.le s A hA)
        intro omega _
        simp only [Complex.real_smul, mul_one]
      _ = ∫ _omega in A, (1 : ℂ) ∂Q := hone.symm
      _ = (Q A).toReal := by
        rw [setIntegral_const]
        simp only [measureReal_def, Complex.real_smul, mul_one]
  have hfourier' :
      (∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P) =
        Complex.exp
            (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
          ∫ omega in A,
            (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
    simpa only [f, inc, Complex.ofReal_mul] using hfourier hst hA c
  change (∫ omega in A, f omega ∂Q) =
    charFun (Q A • gaussianReal 0 (t - s)) c
  have hcharSmul : charFun (Q A • gaussianReal 0 (t - s)) c =
      (Q A).toReal • charFun (gaussianReal 0 (t - s)) c := by
    simp only [charFun_apply_real]
    rw [integral_smul_measure]
  rw [hcurrent, hfourier', hmass, hcharSmul, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
    Complex.real_smul]
  rw [mul_comm]
  congr 1
  push_cast
  ring

/-- Martingale-family form of the Fourier Girsanov endpoint. -/
theorem
    GirsanovDensityData.isPreBrownianReal_of_fourierIncrementMartingaleCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hmart : GirsanovFourierIncrementMartingaleCondition
      P V M bracket X T) :
    IsPreBrownianReal X (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_of_fourierIncrementCondition hadapt hzero
    (girsanovFourierIncrementCondition_of_martingale hmart)

/-- Predictable-drift specialization of the Fourier Girsanov endpoint.
Predictability supplies shifted-process adaptedness, while almost-sure
normalization of the driver suffices at time zero. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  have hshiftAdapt : StronglyAdapted V
      (girsanovShiftedBrownian B theta T) :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt htheta
  have hshiftZero : girsanovShiftedBrownian B theta T 0 =ᵐ[P]
      fun _ ↦ 0 := by
    filter_upwards [hBzero] with omega homega
    simp only [girsanovShiftedBrownian, homega, girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  exact h.isPreBrownianReal_of_fourierIncrementCondition
    hshiftAdapt hshiftZero hfourier

/-- Natural-filtration form of the predictable Fourier endpoint. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    [SigmaFiniteFiltration P (Filtration.natural B hsm)]
    [(Filtration.natural B hsm).IsRightContinuous]
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hfourier : GirsanovFourierIncrementCondition P
      (Filtration.natural B hsm) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
    (Filtration.stronglyAdapted_natural hsm) hB.eval_zero_ae_eq_zero
      htheta hfourier

/-- Raw-natural-filtration version of the Fourier endpoint.  The density
data and predictable drift are transported internally to the right
continuation, avoiding a right-continuity assumption on the natural
filtration supplied by the caller. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hfourier : GirsanovFourierIncrementCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  have hdata : GirsanovDensityData P (Filtration.rightCont V) M bracket T :=
    h.rightCont
  apply hdata.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
  · exact StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  · exact hB.eval_zero_ae_eq_zero
  · exact StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  · exact hfourier

/-- Predictable-drift specialization with the Fourier input presented as a
family of complex martingales. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourierMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hmart : GirsanovFourierIncrementMartingaleCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier hBadapt hBzero htheta
    (girsanovFourierIncrementCondition_of_martingale hmart)

/-- Natural-filtration form with the Fourier input presented as a family of
complex martingales. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourierMartingale_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    [SigmaFiniteFiltration P (Filtration.natural B hsm)]
    [(Filtration.natural B hsm).IsRightContinuous]
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.natural B hsm) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_natural
    hsm hB htheta (girsanovFourierIncrementCondition_of_martingale hmart)

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint from true martingality of the stopped
algebraic complex Doléans family.  This is the common final assembly for
both local-martingale and deterministic-grid constructions. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hcomplex : ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u omega => -girsanovIntegratedDrift theta T u omega) c)
        (min t T) omega)
      (Filtration.rightCont (Filtration.natural B hsm)) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  let X := girsanovShiftedBrownian B theta T
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hX : StronglyAdapted (Filtration.rightCont V) X :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt hthetaR
  have hXeq (t : ℝ≥0) (omega : W) :
      X t omega = B t omega - C (min t T) omega := by
    change B t omega + girsanovIntegratedDrift theta T t omega =
      B t omega - -girsanovIntegratedDrift theta T (min t T) omega
    rw [sub_neg_eq_add]
    congr 1
    unfold girsanovIntegratedDrift
    rw [min_eq_left (min_le_right t T)]
  have hXzero : X 0 =ᵐ[P] fun _ => 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simp only [X, girsanovShiftedBrownian, homega,
      girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket X T := by
    apply girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
      hdataR.adapted_martingale hdataR.adapted_bracket hX hXeq hXzero
      hdataR.martingale_densityProcess
    · simpa only [C, V] using hcomplex
    · intro c
      exact martingale_brownianFourierIncrementProcess_rightCont_natural
        hB hsm T c
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
      hsm hB htheta
  exact girsanovFourierIncrementCondition_of_martingale hmart

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from capped complex Euler
`L¹` convergence.  The discrete approximants are genuine martingales in the
right-continuous natural filtration, including their Brownian integrator. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_cappedComplexEulerL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovCappedComplexEulerL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hcomplex := hdataR.martingale_stopAt_complexDoleans_of_cappedEulerL1
    (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
      (by simpa only [C, V] using hEuler)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  simpa only [C, V] using hcomplex

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from the canonical common
localizer quadratic-variation/Euler convergence condition. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_cappedEulerLocalQV_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovCappedComplexEulerLocalQVCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_cappedComplexEulerL1_rightCont_natural
      hsm hB htheta
  exact girsanovCappedComplexEulerL1Condition_of_localQV hEuler

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from the viable increasing-cap
complex Euler diagonal. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalComplexEulerL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovDiagonalComplexEulerL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hcomplex :=
    hdataR.martingale_stopAt_complexDoleans_of_diagonalEulerL1
      (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
        (by simpa only [C, V] using hEuler)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  simpa only [C, V] using hcomplex

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from a cofinal selected-grid
increasing-cap Euler approximation. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedComplexEulerL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovSelectedComplexEulerL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hcomplex :=
    hdataR.martingale_stopAt_complexDoleans_of_selectedEulerL1
      (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
        (by simpa only [C, V] using hEuler)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  simpa only [C, V] using hcomplex

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from pair-dependent selected
Euler approximations. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovPairwiseSelectedComplexEulerL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hcomplex :=
    hdataR.martingale_stopAt_complexDoleans_of_pairwiseSelectedEulerL1
      (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
        (by simpa only [C, V] using hEuler)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  simpa only [C, V] using hcomplex

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint at the minimal pairwise moving-target
Euler frontier. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerTargetL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovPairwiseSelectedComplexEulerTargetL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerL1_rightCont_natural
      hsm hB htheta
  exact girsanovPairwiseSelectedComplexEulerL1Condition_of_targetL1
    hdataR (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
      (by simpa only [C, V] using hEuler)

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint with the concrete pairwise
inverse-natural `L¹` error budget exposed to the analytic layer. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerRateL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovPairwiseSelectedComplexEulerRateL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerTargetL1_rightCont_natural
      hsm hB htheta
  exact girsanovPairwiseSelectedComplexEulerTargetL1Condition_of_rateL1
    hEuler

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from independent finite-cap,
two-time Euler error estimates. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseFiniteComplexEulerRateL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovPairwiseFiniteComplexEulerRateL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerRateL1_rightCont_natural
      hsm hB htheta
  exact girsanovPairwiseSelectedComplexEulerRateL1Condition_of_finite
    hEuler

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint from pairwise finite-grid estimates in
which the truncation cap is selected together with the grid.  Unlike the
fixed-cap rate interface above, this statement does not impose a universal
rate on the tails of the Doléans exponential. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseFiniteDirectComplexEulerRateL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovPairwiseFiniteComplexEulerDirectRateL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hcomplex :=
    hdataR.martingale_stopAt_complexDoleans_of_pairwiseFiniteDirectEulerRateL1
      (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
        (by simpa only [C, V] using hEuler)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  simpa only [C, V] using hcomplex

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint from the Vitali-ready selected-grid
condition. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedEuler_inMeasure_UI_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovSelectedComplexEulerInMeasureUICondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_selectedComplexEulerL1_rightCont_natural
      hsm hB htheta
  exact girsanovSelectedComplexEulerL1Condition_of_inMeasure_UI
    hdataR hBadapt hC (by simpa only [C, V] using hEuler)

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint at the corrected cofinal
frontier: selected Doléans residual convergence plus matching common-
localizer uniform integrability. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVUI_residual_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hUI : GirsanovSelectedComplexEulerLocalQVUICondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T)
    (hres : GirsanovSelectedComplexDoleansEulerResidualCondition
      P M bracket B
        (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_selectedEuler_inMeasure_UI_rightCont_natural
      hsm hB htheta
  exact girsanovSelectedComplexEulerInMeasureUICondition_of_localQVUI_of_self
    hdataR hBadapt hC (by simpa only [C, V] using hUI)
      (girsanovSelectedComplexEulerSelfInMeasureCondition_of_residual
        (by simpa only [C] using hres))

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint in which selected-grid uniform
integrability is derived from increasingly accurate `L¹` approximation of
the matching capped Doléans targets. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVTargetL1_residual_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hL1 : GirsanovSelectedComplexEulerLocalQVTargetL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T)
    (hres : GirsanovSelectedComplexDoleansEulerResidualCondition
      P M bracket B
        (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hUI : GirsanovSelectedComplexEulerLocalQVUICondition P
      (Filtration.rightCont V) M bracket B C T :=
    girsanovSelectedComplexEulerLocalQVUICondition_of_targetL1
      hdataR (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
        (by simpa only [V, C] using hL1)
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVUI_residual_rightCont_natural
      hsm hB htheta
  · simpa only [V, C] using hUI
  · simpa only [C] using hres

set_option linter.style.longLine false in
/-- The local capped-target approximation already proves the raw-natural
Girsanov endpoint; no separate all-time residual or UI premise is needed. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVTargetL1_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hL1 : GirsanovSelectedComplexEulerLocalQVTargetL1Condition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_pairwiseSelectedComplexEulerTargetL1_rightCont_natural
      hsm hB htheta
  exact
    girsanovPairwiseSelectedComplexEulerTargetL1Condition_of_localQVTargetL1
      hL1

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint with the selected Taylor obligation
split into weighted bracket cancellation and higher-order mesh control. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVUI_secondOrder_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hUI : GirsanovSelectedComplexEulerLocalQVUICondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T)
    (hsecond : GirsanovSelectedComplexDoleansSecondOrderCondition
      P M bracket B
        (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_selectedLocalQVUI_residual_rightCont_natural
      hsm hB htheta hUI
  exact
    girsanovSelectedComplexDoleansEulerResidualCondition_of_secondOrder
      hsecond

set_option linter.style.longLine false in
/-- Common-localizer version of the increasing-cap complex Euler endpoint. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalEulerLocalQV_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovDiagonalComplexEulerLocalQVCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalComplexEulerL1_rightCont_natural
      hsm hB htheta
  exact girsanovDiagonalComplexEulerL1Condition_of_localQV hEuler

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint from the separated diagonal
convergence-in-probability and uniform-integrability obligations. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalEulerLocalQV_inMeasure_UI_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hEuler : GirsanovDiagonalComplexEulerLocalQVInMeasureUICondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalComplexEulerL1_rightCont_natural
      hsm hB htheta
  exact girsanovDiagonalComplexEulerL1Condition_of_localQV_inMeasure_UI
    hdataR (martingale_brownian_rightCont_natural hB hsm) hBadapt hC
      (by simpa only [C, V] using hEuler)

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint with the corrected diagonal
frontier split into canonical Doléans residual convergence and increasing-cap
uniform integrability. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalEulerLocalQVUI_residual_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hUI : GirsanovDiagonalComplexEulerLocalQVUICondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T)
    (hres : GirsanovComplexDoleansEulerResidualCondition P M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_diagonalEulerLocalQV_inMeasure_UI_rightCont_natural
      hsm hB htheta
  exact
    girsanovDiagonalComplexEulerLocalQVInMeasureUICondition_of_UI_of_residual
      hdataR hBadapt hC (by simpa only [C, V] using hUI)
        (by simpa only [C] using hres)

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov theorem reduced to the single
deterministic-grid condition for the base-zero stopped complex exponential. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_stoppedComplexDoleans_rational_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hrational : GirsanovStoppedComplexDoleansRationalCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
      hsm hB htheta
  let V := Filtration.natural B hsm
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hcomplex :=
    hdataR.martingale_stopAt_complexDoleans_of_rational
      hB hsm hBadapt hthetaR hbracketTerminal hcross
        (by simpa only [V] using hrational)
  simpa only [V] using hcomplex

/-- Raw-natural-filtration Girsanov endpoint reduced to deterministic-grid
identities at positive rational subdivisions.  The analytic extension from
those identities to all times is discharged internally by stochastic
continuity and uniform integrability. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_rational_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hrational : GirsanovFourierIncrementRationalCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket
      (girsanovShiftedBrownian B theta T) T := by
    apply hdataR.girsanovFourierIncrementMartingaleCondition_of_rational
      hB hsm hBadapt hthetaR hbracketTerminal hcross
    simpa only [V] using hrational
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
      hsm hB htheta
  exact girsanovFourierIncrementCondition_of_martingale hmart

set_option linter.style.longLine false in
/-- Raw-natural-filtration Girsanov endpoint reduced to the one remaining
stochastic-calculus statement: local martingality of the complex Doléans
family.  The right continuation, Novikov promotion, Brownian continuation,
Fourier pasting, and characteristic-function endpoint are all discharged
internally. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_localComplexDoleans_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hlocal : ∀ c, IsBanachLocalMartingale
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c))
      (Filtration.rightCont (Filtration.natural B hsm)) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  let X := girsanovShiftedBrownian B theta T
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C := by
    exact (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hX : StronglyAdapted (Filtration.rightCont V) X := by
    exact stronglyAdapted_girsanovShiftedBrownian hBadapt hthetaR
  have hXeq (t : ℝ≥0) (omega : W) :
      X t omega = B t omega - C (min t T) omega := by
    change B t omega + girsanovIntegratedDrift theta T t omega =
      B t omega - -girsanovIntegratedDrift theta T (min t T) omega
    rw [sub_neg_eq_add]
    congr 1
    unfold girsanovIntegratedDrift
    rw [min_eq_left (min_le_right t T)]
  have hXzero : X 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simp only [X, girsanovShiftedBrownian, homega, girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket X T := by
    apply hdataR.girsanovFourierIncrementMartingaleCondition_of_localComplexDoleans
      hBadapt hC hX hXeq hXzero
    · simpa only [C, V] using hlocal
    · intro c
      exact martingale_brownianFourierIncrementProcess_rightCont_natural
        hB hsm T c
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
    hsm hB htheta
  exact girsanovFourierIncrementCondition_of_martingale hmart

/-- Abstract Bayes transport specialized to a Novikov Girsanov density.  If
the density-times-process product is a `P`-martingale, then the process is a
martingale under the changed measure. -/
theorem GirsanovDensityData.martingale_girsanovMeasure_of_density_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    {X : ℝ≥0 → W → ℝ}
    (hXadapt : StronglyAdapted 𝒱 X)
    (hXint : ∀ t, Integrable (X t) (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega =>
      doleansDadeExponential M bracket (min t T) omega * X t omega) 𝒱 P) :
    Martingale X 𝒱 (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hset (i j : ℝ≥0) (hij : i ≤ j) (s : Set W)
      (hs : MeasurableSet[𝒱 i] s) :
      ∫ omega in s, X i omega ∂Q = ∫ omega in s, X j omega ∂Q := by
    have hsP : MeasurableSet s := 𝒱.le i s hs
    have hsJ : MeasurableSet[𝒱 j] s := 𝒱.mono hij s hs
    have hweighted (t : ℝ≥0) (hsT : MeasurableSet[𝒱 t] s) :
        ∫ omega in s, girsanovDensity M bracket T omega * X t omega ∂P =
          ∫ omega in s,
            doleansDadeExponential M bracket (min t T) omega * X t omega ∂P := by
      have hterminalInt : Integrable
          (fun omega => girsanovDensity M bracket T omega * X t omega) P := by
        have hraw : Integrable (fun omega =>
            (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal •
              X t omega) P :=
          (integrable_withDensity_iff_integrable_smul₀'
            (E := ℝ) h.integrable.1.aemeasurable.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp (by
              simpa only [Q, girsanovMeasure] using hXint t)
        apply hraw.congr
        exact Filter.Eventually.of_forall fun omega => by
          change (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal *
              X t omega = girsanovDensity M bracket T omega * X t omega
          rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
      have hpull := condExp_mul_of_stronglyMeasurable_left
        (hXadapt t) (by
          apply hterminalInt.congr
          exact Filter.Eventually.of_forall fun omega => mul_comm _ _)
        h.integrable
      calc
        ∫ omega in s, girsanovDensity M bracket T omega * X t omega ∂P =
            ∫ omega in s, X t omega * girsanovDensity M bracket T omega ∂P := by
          apply setIntegral_congr_fun hsP
          intro omega _
          exact mul_comm _ _
        _ = ∫ omega in s,
            P[fun w => X t w * girsanovDensity M bracket T w | 𝒱 t] omega ∂P := by
          symm
          exact setIntegral_condExp (𝒱.le t) (by
            apply hterminalInt.congr
            exact Filter.Eventually.of_forall fun omega => mul_comm _ _) hsT
        _ = ∫ omega in s,
            X t omega * doleansDadeExponential M bracket (min t T) omega ∂P := by
          apply setIntegral_congr_ae hsP
          filter_upwards [hpull, h.condExp_density t] with omega hp hcond _
          change (P[X t * girsanovDensity M bracket T | 𝒱 t]) omega =
            X t omega * doleansDadeExponential M bracket (min t T) omega
          rw [hp]
          change X t omega * P[girsanovDensity M bracket T | 𝒱 t] omega = _
          rw [hcond]
        _ = ∫ omega in s,
            doleansDadeExponential M bracket (min t T) omega * X t omega ∂P := by
          apply setIntegral_congr_fun hsP
          intro omega _
          exact mul_comm _ _
    calc
      ∫ omega in s, X i omega ∂Q =
          ∫ omega in s, girsanovDensity M bracket T omega * X i omega ∂P := by
        simpa only [Q] using
          setIntegral_girsanovMeasure P M bracket T h.integrable (X i) hsP
      _ = ∫ omega in s,
          doleansDadeExponential M bracket (min i T) omega * X i omega ∂P :=
        hweighted i hs
      _ = ∫ omega in s,
          doleansDadeExponential M bracket (min j T) omega * X j omega ∂P :=
        hprod.setIntegral_eq hij hs
      _ = ∫ omega in s, girsanovDensity M bracket T omega * X j omega ∂P :=
        (hweighted j hsJ).symm
      _ = ∫ omega in s, X j omega ∂Q := by
        simpa only [Q] using
          (setIntegral_girsanovMeasure P M bracket T h.integrable (X j) hsP).symm
  have hsub : Submartingale X 𝒱 Q :=
    submartingale_of_setIntegral_le hXadapt hXint fun i j hij s hs =>
      (hset i j hij s hs).le
  have hnegSub : Submartingale (-X) 𝒱 Q :=
    submartingale_of_setIntegral_le hXadapt.neg (fun t => (hXint t).neg) fun i j hij s hs => by
      change ∫ omega in s, -X i omega ∂Q ≤ ∫ omega in s, -X j omega ∂Q
      rw [integral_neg, integral_neg, neg_le_neg_iff]
      exact (hset i j hij s hs).symm.le
  have hsuper : Supermartingale X 𝒱 Q := by
    simpa only [Pi.neg_apply, neg_neg] using hnegSub.neg
  exact martingale_iff.mpr ⟨hsuper, hsub⟩

/-- The Bayes bridge specialized to Girsanov's drift-shifted Brownian
process.  The product-martingale premise is precisely the stochastic
integration-by-parts identity that remains to be supplied by the stochastic
calculus layer. -/
theorem GirsanovDensityData.martingale_girsanovShiftedBrownian_of_density_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hadapt : StronglyAdapted 𝒱 (girsanovShiftedBrownian B theta T))
    (hint : ∀ t, Integrable (girsanovShiftedBrownian B theta T t)
      (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega =>
      doleansDadeExponential M bracket (min t T) omega *
        girsanovShiftedBrownian B theta T t omega) 𝒱 P) :
    Martingale (girsanovShiftedBrownian B theta T) 𝒱
      (girsanovMeasure P M bracket T) :=
  h.martingale_girsanovMeasure_of_density_mul hadapt hint hprod

/-- Complete Girsanov endgame once stochastic integration by parts supplies
the weighted-product martingale and the shifted process has its stopped clock
bracket.  The conclusion is the exact pre-Brownian finite-dimensional law
under the terminal density measure. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hadapt : StronglyAdapted 𝒱 (girsanovShiftedBrownian B theta T))
    (hint : ∀ t, Integrable (girsanovShiftedBrownian B theta T t)
      (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega *
        girsanovShiftedBrownian B theta T t omega) 𝒱 P)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability
      (girsanovShiftedBrownian B theta T)
      (fun t _omega ↦ (t : ℝ)) (girsanovMeasure P M bracket T))
    (hcont : ∀ omega, Continuous
      (fun t ↦ girsanovShiftedBrownian B theta T t omega))
    (hzero : ∀ omega, girsanovShiftedBrownian B theta T 0 omega = 0) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hmart : Martingale (girsanovShiftedBrownian B theta T) 𝒱 Q := by
    simpa only [Q] using
      h.martingale_girsanovShiftedBrownian_of_density_mul hadapt hint hprod
  exact Martingale.isPreBrownianReal_of_stoppedQuadraticVariation_clock hmart
    (by simpa only [Q] using hstopped) hcont hzero

/-- Version of the complete endgame whose stopped clock bracket is supplied
under `P`; invariance of convergence in probability transports it to the
terminal Girsanov measure internally. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul_P
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hadapt : StronglyAdapted 𝒱 (girsanovShiftedBrownian B theta T))
    (hint : ∀ t, Integrable (girsanovShiftedBrownian B theta T t)
      (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega *
        girsanovShiftedBrownian B theta T t omega) 𝒱 P)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability
      (girsanovShiftedBrownian B theta T)
      (fun t _omega ↦ (t : ℝ)) P)
    (hcont : ∀ omega, Continuous
      (fun t ↦ girsanovShiftedBrownian B theta T t omega))
    (hzero : girsanovShiftedBrownian B theta T 0 =ᵐ[P] fun _ ↦ 0) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hmart : Martingale (girsanovShiftedBrownian B theta T) 𝒱 Q := by
    simpa only [Q] using
      h.martingale_girsanovShiftedBrownian_of_density_mul hadapt hint hprod
  have hstoppedQ : HasStoppedQuadraticVariationProcessInProbability
      (girsanovShiftedBrownian B theta T) (fun t _omega ↦ (t : ℝ)) Q := by
    simpa only [Q] using h.stoppedQuadraticVariation_girsanovMeasure hstopped
  have hzeroQ : girsanovShiftedBrownian B theta T 0 =ᵐ[Q] fun _ ↦ 0 :=
    h.mutuallyAbsolutelyContinuous.1.ae_eq hzero
  exact Martingale.isPreBrownianReal_of_stoppedQuadraticVariation_clock_of_ae_zero
    hmart hstoppedQ hcont hzeroQ

/-- The Girsanov endgame with the stopped clock bracket discharged from the
pre-Brownian law and pathwise integrability of the finite-variation drift.
Only the density-product martingale and regularity/integrability of the
shifted process remain as stochastic-calculus premises. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul_integrableDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : Measurable (Function.uncurry theta))
    (hthetaInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun r : ℝ ↦ theta r.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ)))
    (hadapt : StronglyAdapted 𝒱 (girsanovShiftedBrownian B theta T))
    (hint : ∀ t, Integrable (girsanovShiftedBrownian B theta T t)
      (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega *
        girsanovShiftedBrownian B theta T t omega) 𝒱 P)
    (hcont : ∀ omega, Continuous
      (fun t ↦ girsanovShiftedBrownian B theta T t omega)) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul_P
    hadapt hint hprod
  · exact hasStoppedQuadraticVariation_girsanovShiftedBrownian
      T hB htheta hthetaInt
  · exact hcont
  · filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simpa [girsanovShiftedBrownian] using homega

/-- Predictable-drift specialization of the Girsanov endgame.  Strong
predictability supplies the joint measurability needed to identify the
finite-variation drift's quadratic variation. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul_predictableDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hthetaInt : ∀ (t : ℝ≥0) omega, IntegrableOn
      (fun r : ℝ ↦ theta r.toNNReal omega) (Set.Icc (0 : ℝ) (t : ℝ)))
    (hadapt : StronglyAdapted V (girsanovShiftedBrownian B theta T))
    (hint : ∀ t, Integrable (girsanovShiftedBrownian B theta T t)
      (girsanovMeasure P M bracket T))
    (hprod : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega *
        girsanovShiftedBrownian B theta T t omega) V P)
    (hcont : ∀ omega, Continuous
      (fun t ↦ girsanovShiftedBrownian B theta T t omega)) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_density_mul_integrableDrift
    hB (IsStronglyPredictable.measurable_uncurry_nnreal htheta) hthetaInt
      hadapt hint hprod hcont

section PredictableIntegral

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- A continuous modification of the natural Itô integral has the same
completed-cell quadratic variation as the selected representative.  This is
the representative bridge needed before applying the process-level Novikov
theorem. -/
theorem IsContinuousProcessModification.hasQuadraticVariationBeforeStop_naturalIto
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P) :
    HasQuadraticVariationBeforeStopProcessInProbability M
      (predictableQuadraticVariation hsm U) P := by
  let N : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  intro t a
  have hNM (b : ℝ≥0) (n : ℕ) :
      quadraticVariationBeforeStopApprox N t (n + 1) b =ᵐ[P]
        quadraticVariationBeforeStopApprox M t (n + 1) b := by
    have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    filter_upwards [hgrid] with omega homega
    unfold quadraticVariationBeforeStopApprox
    apply Finset.sum_congr rfl
    intro i hi
    simp only [N]
    rw [homega n (i + 1), homega n i]
  by_cases ha : a ≤ t
  · exact (quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t a ha).congr_left (hNM a)
  · have hN := quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t t (le_refl t)
    have hsource (n : ℕ) :
        quadraticVariationBeforeStopApprox N t (n + 1) t =ᵐ[P]
          quadraticVariationBeforeStopApprox M t (n + 1) a := by
      filter_upwards [hNM t n] with omega hEq
      calc
        quadraticVariationBeforeStopApprox N t (n + 1) t omega =
            quadraticVariationBeforeStopApprox M t (n + 1) t omega := hEq
        _ = quadraticVariationBeforeStopApprox M t (n + 1) a omega := by
          have hmin := quadraticVariationBeforeStopApprox_min_horizon
            M t a (n + 1) omega
          rw [min_eq_left (le_of_not_ge ha)] at hmin
          exact hmin.symm
    simpa only [min_self, min_eq_left (le_of_not_ge ha)] using
      hN.congr_left hsource

/-- A strongly adapted continuous modification of a natural predictable
Itô integral carries the common-localizer quadratic-variation contract. -/
theorem hasLocalQuadraticVariationProcessInProbability_naturalItoModification
    [IsProbabilityMeasure P]
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P)
    (hMadapt : StronglyAdapted (Filtration.natural B hsm) M) :
    HasLocalQuadraticVariationProcessInProbability M
      (predictableQuadraticVariation hsm U) (Filtration.natural B hsm) P := by
  have hmartNatural := martingale_naturalItoProcessRepresentative
    hB.toIsPreBrownianReal hsm rfl U
  have hmart : Martingale M (Filtration.natural B hsm) P :=
    hmartNatural.congr hMadapt hmod.fixedTime_ae_eq
  have hqv := hmod.hasQuadraticVariationBeforeStop_naturalIto hB hsm U
  have hlocM : localizingStoppedProcess M (fun _ => ⊤) = M := by
    funext t omega
    simp [localizingStoppedProcess]
  have hlocBracket : localizingStoppedProcess
      (predictableQuadraticVariation hsm U) (fun _ => ⊤) =
        predictableQuadraticVariation hsm U := by
    funext t omega
    simp [localizingStoppedProcess]
  refine ⟨fun _ _ => ⊤, isLocalizingSequence_const_top _ _, ?_, ?_⟩
  · intro k
    rw [hlocM]
    exact hmart
  · intro k
    rw [hlocM, hlocBracket]
    exact hqv

/-- Predictable-integral data sufficient to instantiate the Novikov density
construction.  The explicit continuous representative and bracket path
conditions make all representative choices visible at this boundary. -/
structure PredictableGirsanovDensityData
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop where
  modification : IsContinuousProcessModification
    (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P
  adapted : StronglyAdapted (Filtration.natural B hsm) M
  continuous_path : ∀ omega, Continuous (fun t => M t omega)
  bracket_adapted : StronglyAdapted (Filtration.natural B hsm)
    (predictableQuadraticVariation hsm U)
  bracket_continuous_monotone : ∀ omega,
    Continuous (fun t => predictableQuadraticVariation hsm U t omega) ∧
      Monotone (fun t => predictableQuadraticVariation hsm U t omega)
  martingale_zero : ∀ omega, M 0 omega = 0
  bracket_zero : ∀ omega, predictableQuadraticVariation hsm U 0 omega = 0
  novikov : NovikovCondition (predictableQuadraticVariation hsm U) P T

/-- Predictable integral data produces the generic normalized Girsanov
density contract. -/
theorem PredictableGirsanovDensityData.toGirsanovDensityData
    {hB : IsBrownianMotion B P} {hsm : ∀ t, StronglyMeasurable (B t)}
    [IsProbabilityMeasure P]
    {U : PredictableProcessL2 (Filtration.natural B hsm) P}
    {M : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : PredictableGirsanovDensityData hB hsm U M T) :
    GirsanovDensityData P (Filtration.natural B hsm) M
      (predictableQuadraticVariation hsm U) T where
  novikov := h.novikov
  localQuadraticVariation :=
    hasLocalQuadraticVariationProcessInProbability_naturalItoModification
      hB hsm U h.modification h.adapted
  continuous_martingale_path := h.continuous_path
  adapted_martingale := h.adapted
  adapted_bracket := h.bracket_adapted
  continuous_monotone_bracket := h.bracket_continuous_monotone
  martingale_zero := h.martingale_zero
  bracket_zero := h.bracket_zero

end PredictableIntegral

end StochasticCalculus
