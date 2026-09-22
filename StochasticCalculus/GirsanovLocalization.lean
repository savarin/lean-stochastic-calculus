/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.StoppedCrossVariation

/-!
# Localization of predictable Girsanov data

The terminally stopped bracket gives global polynomial moments of the real
integrator. Continuous exits then allow the bounded-density closure to apply.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- A bound by the original terminal bracket supplies Novikov at any new
horizon, preserving all process-level fields. -/
theorem GirsanovDensityData.change_horizon_of_bracket_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hbracket : ∀ omega, bracket U omega ≤ bracket T omega) :
    GirsanovDensityData P V M bracket U := by
  refine { h with novikov := ?_ }
  apply h.novikov.mono
  · have hmeas : AEStronglyMeasurable (bracket U) P :=
      ((h.adapted_bracket U).mono (V.le U)).aestronglyMeasurable
    change AEStronglyMeasurable (fun omega ↦ Real.exp (bracket U omega / 2)) P
    simpa only [div_eq_mul_inv] using Real.continuous_exp.comp_aestronglyMeasurable
      (hmeas.mul_const (2 : ℝ)⁻¹)
  · filter_upwards with omega
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hbracket omega) (by norm_num))

/-- A bracket bounded by its Novikov terminal value makes the original
real integrator a true martingale at every time. -/
theorem GirsanovDensityData.martingale_of_bracket_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hbracket : ∀ t omega, bracket t omega ≤ bracket T omega) :
    Martingale M V P := by
  refine ⟨h.adapted_martingale, ?_⟩
  intro s t hst
  have hmart := (h.change_horizon_of_bracket_le (hbracket t)).martingale_stopAt_martingale
  simpa only [min_eq_left hst, min_self] using hmart.condExp_ae_eq hst

/-- Every deterministic value of that integrator has a fourth moment. -/
theorem GirsanovDensityData.memLp_four_martingale_of_bracket_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hbracket : ∀ t omega, bracket t omega ≤ bracket T omega) (t : ℝ≥0) :
    MemLp (M t) 4 P := by
  have ht := h.change_horizon_of_bracket_le (hbracket t)
  have hint := (ht.integrable_stoppedValue_norm_pow (isStoppingTime_const V t)
    (fun _ ↦ le_rfl) 4).1
  change Integrable (fun omega ↦ ‖M t omega‖ ^ 4) P at hint
  apply (memLp_four_iff_integrable_pow_four
    ((h.adapted_martingale t).mono (V.le t)).aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, (show Even 4 from ⟨2, by norm_num⟩).pow_abs] using hint

/-- The literal stopped-integrated-square identity bounds the bracket at
all times by its original terminal value, including after the horizon. -/
theorem GirsanovDensityData.bracket_le_terminal_of_integratedSquare
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) (t : ℝ≥0) (omega : W) :
    bracket t omega ≤ bracket T omega := by
  have heq : bracket t omega = bracket (min t T) omega := by
    rw [hbracketTheta, hbracketTheta, min_assoc, min_self]
  rw [heq]
  exact (h.continuous_monotone_bracket omega).2 (min_le_right t T)

/-- The stochastic interval through a stopping time is predictable. -/
theorem measurableSet_predictable_le_stoppingTime
    {W : Type*} [MeasurableSpace W] {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0))) :
    MeasurableSet[V.predictable] {p : ℝ≥0 × W | p.1 ≤ tau p.2} := by
  have heq : {p : ℝ≥0 × W | tau p.2 < p.1} =
      ⋃ q : ℚ, Set.Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {omega | tau omega ≤ Real.toNNReal (q : ℝ)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro hp
      obtain ⟨q, _, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn (tau p.2) p.1).mp hp
      exact ⟨q, hqb, haq.le⟩
    · rintro ⟨q, hq, htq⟩
      exact htq.trans_lt hq
  have hlt : MeasurableSet[V.predictable] {p : ℝ≥0 × W | tau p.2 < p.1} := by
    rw [heq]
    apply MeasurableSet.iUnion
    intro q
    apply measurableSet_predictable_Ioi_prod
    simpa only [WithTop.coe_le_coe] using htau (Real.toNNReal (q : ℝ))
  simpa only [Set.compl_ofPred, not_lt] using hlt.compl

/-- Stop a predictable coefficient on the stochastic interval through tau. -/
def stoppedPredictableCoefficient
    {W : Type*} (theta : ℝ≥0 → W → ℝ) (tau : W → ℝ≥0) : ℝ≥0 → W → ℝ :=
  fun t omega ↦ if t ≤ tau omega then theta t omega else 0

/-- Stochastic interval restriction preserves predictability. -/
theorem IsStronglyPredictable.stoppedPredictableCoefficient
    {W : Type*} [MeasurableSpace W] {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {theta : ℝ≥0 → W → ℝ} (htheta : IsStronglyPredictable V theta)
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0))) :
    IsStronglyPredictable V (stoppedPredictableCoefficient theta tau) := by
  exact htheta.indicator (measurableSet_predictable_le_stoppingTime htau)

/-- Restricting a totalized integral to a stopped interval is exact even
when the original function is not integrable. -/
theorem integral_Ioc_stopped_indicator
    (f : ℝ≥0 → ℝ) (U a : ℝ≥0) :
    (∫ s in Set.Ioc (0 : ℝ≥0) U, (if s ≤ a then f s else 0)
        ∂nonnegativeLebesgueMeasure) =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min U a), f s ∂nonnegativeLebesgueMeasure := by
  have heq : Set.Iic a ∩ Set.Ioc (0 : ℝ≥0) U = Set.Ioc 0 (min U a) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
    tauto
  change (∫ s in Set.Ioc (0 : ℝ≥0) U, (Set.Iic a).indicator f s
    ∂nonnegativeLebesgueMeasure) = _
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, heq]

/-- Stopping the coefficient stops its literal integrated drift. -/
theorem girsanovIntegratedDrift_stoppedPredictableCoefficient
    {W : Type*} (theta : ℝ≥0 → W → ℝ) (tau : W → ℝ≥0) (T t : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift (stoppedPredictableCoefficient theta tau) T t omega =
      girsanovIntegratedDrift theta T (min t (tau omega)) omega := by
  unfold girsanovIntegratedDrift stoppedPredictableCoefficient
  rw [integral_Ioc_stopped_indicator]
  rw [min_right_comm]

/-- Stopping the coefficient stops the prescribed square-integral bracket
pointwise, with no new pathwise integrability assumption. -/
theorem bracket_stoppedPredictableCoefficient
    {W : Type*} {theta bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) (tau : W → ℝ≥0) (t : ℝ≥0) (omega : W) :
    bracket (min t (tau omega)) omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T),
        (stoppedPredictableCoefficient theta tau s omega) ^ 2 ∂nonnegativeLebesgueMeasure := by
  rw [hbracketTheta]
  have heq : (fun s ↦ (stoppedPredictableCoefficient theta tau s omega) ^ 2) =
      fun s ↦ if s ≤ tau omega then (theta s omega) ^ 2 else 0 := by
    funext s
    simp only [stoppedPredictableCoefficient]
    split_ifs <;> norm_num
  rw [heq, integral_Ioc_stopped_indicator, min_right_comm]

/-- Stopping the Girsanov integrator transports its cross variation to the
stopped continuous drift representative under the literal input hypotheses. -/
theorem GirsanovDensityData.crossVariation_stop_regularized
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hBmart : Martingale B V P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0))) :
    HasCrossVariationProcessInProbability (fun t omega ↦ M (min t (tau omega)) omega)
      B (fun t omega ↦ -regularizedGirsanovIntegratedDrift bracket theta T
        (min t (tau omega)) omega) P := by
  let C := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
  let D := fun t omega ↦ -regularizedGirsanovIntegratedDrift bracket theta T t omega
  have hAle : ∀ t omega, bracket t omega ≤ bracket T omega :=
    h.bracket_le_terminal_of_integratedSquare hbracketTheta
  have hMtrue : Martingale M V P := h.martingale_of_bracket_le hAle
  have hM4 : ∀ t, MemLp (M t) 4 P := h.memLp_four_martingale_of_bracket_le hAle
  have hB4 : ∀ t, MemLp (B t) 4 P := fun t ↦
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp ENNReal.ofNat_ne_top
  have hC : StronglyAdapted V C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift htheta T).neg
  have hCzero : C 0 = 0 := by
    funext omega
    simp only [C, girsanovIntegratedDrift, zero_min, Set.Ioc_self, setIntegral_empty, neg_zero,
      Pi.zero_apply]
  have hbrT : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2 ∂nonnegativeLebesgueMeasure := by
    simpa only [min_self] using hbracketTheta T
  have hDcont : ∀ omega, Continuous fun t ↦ D t omega := fun omega ↦
    (continuous_regularizedGirsanovIntegratedDrift htheta hbrT omega).neg
  have hDmeas : ∀ t, StronglyMeasurable (D t) := fun t ↦
    (stronglyMeasurable_regularizedGirsanovIntegratedDrift h.adapted_bracket htheta t).neg
  have hCD : ∀ t, C t =ᵐ[P] D t := fun t ↦
    (h.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t).symm.neg
  exact HasCrossVariationProcessInProbability.stop_left_of_memLp_four
    (C := C) (D := D) hcross hMtrue hBmart hB hC hCzero hM4 hB4
    h.continuous_martingale_path hDcont hDmeas hCD htau

end StochasticCalculus
