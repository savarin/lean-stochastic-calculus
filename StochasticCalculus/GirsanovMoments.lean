/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.Girsanov

/-!
# Moment consequences of the Novikov contract

The half-bracket exponential moment bounds both signs of the stopped real
martingale. This supplies every polynomial moment and removes the need to
approximate the real integrator by unrelated local martingales on the finite
Girsanov horizon.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- Negation preserves the Novikov density data and its bracket. -/
theorem GirsanovDensityData.neg_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    GirsanovDensityData P V (fun t omega ↦ -M t omega) bracket T := by
  refine
    { novikov := h.novikov
      localQuadraticVariation := ?_
      continuous_martingale_path := fun omega ↦ (h.continuous_martingale_path omega).neg
      adapted_martingale := h.adapted_martingale.neg
      adapted_bracket := h.adapted_bracket
      continuous_monotone_bracket := h.continuous_monotone_bracket
      martingale_zero := fun omega ↦ by simp only [h.martingale_zero omega, neg_zero]
      bracket_zero := h.bracket_zero }
  simpa only [neg_one_mul, neg_one_sq, one_mul] using
    h.localQuadraticVariation.const_mul (-1)

/-- Novikov bounds the absolute half-exponential moment of the real
integrator at every stopping time bounded by the terminal horizon. -/
theorem GirsanovDensityData.integrable_stoppedValue_exp_abs_half
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime V tau)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Integrable (fun omega ↦ Real.exp (|stoppedValue M tau omega| / 2)) P ∧
      (∫ omega, Real.exp (|stoppedValue M tau omega| / 2) ∂P) ≤
        2 * Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P) := by
  have hp := h.novikov.integrable_stoppedValue_exp_half h.localQuadraticVariation
    h.continuous_martingale_path h.adapted_martingale h.adapted_bracket
    h.continuous_monotone_bracket h.martingale_zero h.bracket_zero htau hbound
  have hm := h.neg_martingale.novikov.integrable_stoppedValue_exp_half
    h.neg_martingale.localQuadraticVariation h.neg_martingale.continuous_martingale_path
    h.neg_martingale.adapted_martingale h.adapted_bracket
    h.continuous_monotone_bracket h.neg_martingale.martingale_zero h.bracket_zero htau hbound
  change Integrable (fun omega ↦ Real.exp (-stoppedValue M tau omega / 2)) P ∧
    (∫ omega, Real.exp (-stoppedValue M tau omega / 2) ∂P) ≤
      Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P) at hm
  have hmeas : AEStronglyMeasurable (stoppedValue M tau) P :=
    ((stronglyMeasurable_stoppedValue_of_le
      (h.adapted_martingale.isStronglyProgressive_of_continuous
        h.continuous_martingale_path) htau hbound).mono (V.le T)).aestronglyMeasurable
  have habs : AEStronglyMeasurable
      (fun omega ↦ Real.exp (|stoppedValue M tau omega| / 2)) P := by
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul, mul_comm] using
      Real.continuous_exp.comp_aestronglyMeasurable
        (hmeas.norm.const_mul (1 / 2 : ℝ))
  have hdom (omega : W) : Real.exp (|stoppedValue M tau omega| / 2) ≤
      Real.exp (stoppedValue M tau omega / 2) +
        Real.exp (-stoppedValue M tau omega / 2) := by
    by_cases hx : 0 ≤ stoppedValue M tau omega
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hsum : Integrable (fun omega ↦ Real.exp (stoppedValue M tau omega / 2) +
      Real.exp (-stoppedValue M tau omega / 2)) P := hp.1.add hm.1
  have hi : Integrable (fun omega ↦ Real.exp (|stoppedValue M tau omega| / 2)) P := by
    apply hsum.mono' habs
    filter_upwards with omega
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hdom omega
  refine ⟨hi, ?_⟩
  have hle := integral_mono hi hsum hdom
  rw [integral_add hp.1 hm.1] at hle
  linarith [hp.2, hm.2]

/-- A half-exponential controls every absolute polynomial moment, with an
explicit factorial constant. -/
theorem norm_pow_le_factorial_mul_exp_abs_half (x : ℝ) (n : ℕ) :
    ‖x‖ ^ n ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (|x| / 2) := by
  have h := Real.pow_div_factorial_le_exp (|x| / 2)
    (div_nonneg (abs_nonneg x) (by norm_num)) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpow : (|x| / 2) ^ n ≤ Real.exp (|x| / 2) * n.factorial :=
    (div_le_iff₀ hf).mp h
  calc
    ‖x‖ ^ n = (2 : ℝ) ^ n * (|x| / 2) ^ n := by
      rw [← mul_pow, Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ n * (Real.exp (|x| / 2) * n.factorial) :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) n)
    _ = _ := by ring

/-- Every polynomial moment of every bounded stopped value of the real
integrator has one bound depending only on the Novikov moment. -/
theorem GirsanovDensityData.integrable_stoppedValue_norm_pow
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime V tau)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) (n : ℕ) :
    Integrable (fun omega ↦ ‖stoppedValue M tau omega‖ ^ n) P ∧
      (∫ omega, ‖stoppedValue M tau omega‖ ^ n ∂P) ≤
        ((2 : ℝ) ^ n * n.factorial) *
          (2 * Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P)) := by
  have he := h.integrable_stoppedValue_exp_abs_half htau hbound
  have hmeas : AEStronglyMeasurable (stoppedValue M tau) P :=
    ((stronglyMeasurable_stoppedValue_of_le
      (h.adapted_martingale.isStronglyProgressive_of_continuous
        h.continuous_martingale_path) htau hbound).mono (V.le T)).aestronglyMeasurable
  let C : ℝ := (2 : ℝ) ^ n * n.factorial
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmajor := he.1.const_mul C
  have hi : Integrable (fun omega ↦ ‖stoppedValue M tau omega‖ ^ n) P := by
    apply hmajor.mono' (hmeas.norm.pow n)
    filter_upwards with omega
    change ‖‖stoppedValue M tau omega‖ ^ n‖ ≤ C * Real.exp (|stoppedValue M tau omega| / 2)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg (stoppedValue M tau omega)) n)]
    exact norm_pow_le_factorial_mul_exp_abs_half (stoppedValue M tau omega) n
  refine ⟨hi, ?_⟩
  have hle := integral_mono hi hmajor (fun omega ↦
    norm_pow_le_factorial_mul_exp_abs_half (stoppedValue M tau omega) n)
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left he.2 hC)

/-- The real integrator has uniformly integrable values over any family of
stopping times bounded by the Novikov horizon. -/
theorem GirsanovDensityData.uniformIntegrable_stoppedValue_martingale
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (tau : I → W → WithTop ℝ≥0) (htau : ∀ i, IsStoppingTime V (tau i))
    (hbound : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0)) :
    UniformIntegrable (fun i ↦ stoppedValue M (tau i)) 1 P := by
  have hmeas (i : I) : AEStronglyMeasurable (stoppedValue M (tau i)) P :=
    ((stronglyMeasurable_stoppedValue_of_le
      (h.adapted_martingale.isStronglyProgressive_of_continuous
        h.continuous_martingale_path) (htau i) (hbound i)).mono
          (V.le T)).aestronglyMeasurable
  have hnorm : UniformIntegrable
      (fun i omega ↦ ‖stoppedValue M (tau i) omega‖) 1 P := by
    refine uniformIntegrable_one_of_uniform_integral_rpow (2 : ℝ) (by norm_num)
      (fun i ↦ (hmeas i).norm) (fun _ _ ↦ norm_nonneg _) ?_
      (((2 : ℝ) ^ 2 * (2 : ℕ).factorial) *
        (2 * Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P))) ?_
    · intro i
      simpa only [Real.rpow_two] using
        (h.integrable_stoppedValue_norm_pow (htau i) (hbound i) 2).1
    · intro i
      simpa only [Real.rpow_two] using
        (h.integrable_stoppedValue_norm_pow (htau i) (hbound i) 2).2
  exact UniformIntegrable.mono_norm hnorm hmeas
    (fun _ _ ↦ by simp only [norm_norm, le_refl])

/-- Novikov makes the original real integrator a true martingale through
the terminal horizon, as well as making its stochastic exponential one. -/
theorem GirsanovDensityData.martingale_stopAt_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    Martingale (fun t ↦ M (min t T)) V P := by
  let hlocal := h.localQuadraticVariation.isLocalMartingale
  apply hlocal.martingale_stopAt_of_uniformIntegrable_stoppedValue
    h.adapted_martingale T
  intro t ht
  apply h.uniformIntegrable_stoppedValue_martingale
    (fun n omega ↦ min (hlocal.localSeq n omega) (t : WithTop ℝ≥0))
  · intro n
    exact (hlocal.isLocalizingSequence_localSeq.isStoppingTime n).min_const t
  · intro n omega
    exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr ht)

/-- Every bounded stopped value of the real integrator is square integrable. -/
theorem GirsanovDensityData.memLp_two_stoppedValue_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime V tau)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    MemLp (stoppedValue M tau) 2 P := by
  have hmeas : AEStronglyMeasurable (stoppedValue M tau) P :=
    ((stronglyMeasurable_stoppedValue_of_le
      (h.adapted_martingale.isStronglyProgressive_of_continuous
        h.continuous_martingale_path) htau hbound).mono (V.le T)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using
    (h.integrable_stoppedValue_norm_pow htau hbound 2).1

end StochasticCalculus
