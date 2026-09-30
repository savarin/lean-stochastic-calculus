/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.CrossVariationProcess

/-!
# The Girsanov density, measure and drift

The terminal density `Z_T` from the Doléans--Dade exponential, the
unnormalised measure `Z_T · P`, the integrated and regularised drift, and
the shifted driver.  `GirsanovDensityData` collects the continuous
local-martingale contract together with Novikov's condition; its first
consequences are integrability and expectation one of the density, the
probability and equivalence of the new measure, and passage to the
right-continuous filtration.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The terminal stochastic-exponential density used by Girsanov. -/
@[expose] def girsanovDensity {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : W → ℝ :=
  doleansDadeExponential M bracket T

/-- The Girsanov measure `Q = Z_T · P`, represented by Mathlib's
`Measure.withDensity`. -/
@[expose] def girsanovMeasure {W : Type*} [MeasurableSpace W]
    (P : Measure W) (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Measure W :=
  P.withDensity (fun omega => ENNReal.ofReal (girsanovDensity M bracket T omega))

/-- The finite-horizon pathwise drift accumulated from a predictable
integrand. -/
@[expose] def girsanovIntegratedDrift {W : Type*}
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
@[expose] def regularizedGirsanovIntegratedDrift {W : Type*}
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
  · simp only [hzero, ite_eq_left]
    fun_prop
  · simp only [hzero, ite_false]
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
@[expose] def girsanovShiftedBrownian {W : Type*}
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

theorem girsanovIntegratedDrift_of_horizon_le {W : Type*}
    (theta : ℝ≥0 → W → ℝ) {T t : ℝ≥0} (ht : T ≤ t) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, theta s omega
        ∂nonnegativeLebesgueMeasure := by
  simp only [girsanovIntegratedDrift, min_eq_right ht]

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
    · rw [ite_eq_left hzero]
      have hbracketNonneg : 0 ≤ bracket t omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      have hbracketLe : bracket t omega ≤ bracket T omega :=
        (hdata.continuous_monotone_bracket omega).2 htT
      have hbracketZero : bracket t omega = 0 := by linarith
      have hdriftZero := hcrossZero hbracketZero
      linarith
    · rw [ite_eq_right hzero]
  · have hTt : T ≤ t := le_of_not_ge htT
    filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae
      hcross hB T] with omega hcrossZero
    unfold regularizedGirsanovIntegratedDrift
    by_cases hzero : bracket T omega = 0
    · rw [ite_eq_left hzero]
      have hterminalZero := hcrossZero hzero
      have hstop : girsanovIntegratedDrift theta T t omega =
          girsanovIntegratedDrift theta T T omega := by
        rw [girsanovIntegratedDrift_of_horizon_le theta hTt,
          girsanovIntegratedDrift_of_horizon_le theta le_rfl]
      rw [hstop]
      linarith
    · rw [ite_eq_right hzero]

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
      ⟨hinMeasure, hui.unifIntegrable⟩
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s)
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

end StochasticCalculus
