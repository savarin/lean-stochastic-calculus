/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.GirsanovMoments
import StochasticCalculus.MartingaleFourthMoment

/-!
# Vanishing of a continuous local martingale on zero-bracket paths

Positive local exponential bounds force the square moment restricted to a
zero-bracket event to vanish. Continuity makes the conclusion simultaneous.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Exponential domination of a square, in a symmetric form. -/
theorem sq_le_two_mul_exp_add_exp_neg (x : ℝ) :
    x ^ 2 ≤ 2 * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 2
  norm_num only [Nat.factorial, Nat.mul_one, Nat.cast_ofNat, sq_abs] at h
  have hexp : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hx]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  linarith

/-- Every real scaling of the local stochastic exponential is integrable
with expectation at most one; no scaled Novikov hypothesis is needed. -/
theorem GirsanovDensityData.integrable_scaled_exponential_and_integral_le_one
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) (c : ℝ) (t : ℝ≥0) :
    Integrable (doleansDadeExponential (fun s omega ↦ c * M s omega)
      (fun s omega ↦ c ^ 2 * bracket s omega) t) P ∧
    (∫ omega, doleansDadeExponential (fun s omega ↦ c * M s omega)
      (fun s omega ↦ c ^ 2 * bracket s omega) t omega ∂P) ≤ 1 := by
  have hlocal :=
    isContinuousLocalMartingale_doleansDadeExponential_const_mul_of_localQuadraticVariation
      h.localQuadraticVariation h.continuous_martingale_path h.adapted_bracket
    h.continuous_monotone_bracket h.martingale_zero h.bracket_zero c
  apply integrable_doleansDadeExponential_and_integral_le_one hlocal.1
  · exact stronglyAdapted_doleansDadeExponential
      (fun s ↦ stronglyMeasurable_const.mul (h.adapted_martingale s))
      (fun s ↦ stronglyMeasurable_const.mul (h.adapted_bracket s))
  · intro omega
    rw [h.martingale_zero, mul_zero]
  · intro omega
    rw [h.bracket_zero, mul_zero]

/-- A square-integrable value of the continuous local martingale vanishes
almost everywhere on the event where its bracket is zero. -/
theorem GirsanovDensityData.martingale_eq_zero_of_bracket_eq_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) (t : ℝ≥0)
    (hM2 : MemLp (M t) 2 P) :
    ∀ᵐ omega ∂P, bracket t omega = 0 → M t omega = 0 := by
  let A := {omega | bracket t omega = 0}
  have hA : MeasurableSet A :=
    ((h.adapted_bracket t).mono (V.le t)).measurable (measurableSet_singleton 0)
  let F := A.indicator (fun omega ↦ M t omega ^ 2)
  have hFint : Integrable F P := hM2.integrable_sq.indicator hA
  have hFnonneg : ∀ omega, 0 ≤ F omega := fun omega ↦
    Set.indicator_nonneg (fun omega _ ↦ sq_nonneg (M t omega)) omega
  have hbound (c : ℝ) : c ^ 2 * (∫ omega, F omega ∂P) ≤ 4 := by
    let E := fun c ↦ doleansDadeExponential (fun s omega ↦ c * M s omega)
      (fun s omega ↦ c ^ 2 * bracket s omega) t
    have hp := h.integrable_scaled_exponential_and_integral_le_one c t
    have hn := h.integrable_scaled_exponential_and_integral_le_one (-c) t
    have hsum : Integrable (fun omega ↦ E c omega + E (-c) omega) P := hp.1.add hn.1
    have hmajor : Integrable (fun omega ↦ 2 * (E c omega + E (-c) omega)) P :=
      hsum.const_mul 2
    have hpoint (omega : W) : c ^ 2 * F omega ≤ 2 * (E c omega + E (-c) omega) := by
      by_cases homega : omega ∈ A
      · have hzero : bracket t omega = 0 := homega
        dsimp only [F, E]
        rw [Set.indicator_of_mem homega]
        simp only [doleansDadeExponential, doleansDadeLog, hzero, mul_zero, sub_zero,
          neg_mul]
        have hs := sq_le_two_mul_exp_add_exp_neg (c * M t omega)
        nlinarith
      · rw [show F omega = 0 from Set.indicator_of_notMem homega _, mul_zero]
        exact mul_nonneg (by norm_num) (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    have hi := integral_mono (hFint.const_mul (c ^ 2)) hmajor hpoint
    rw [integral_const_mul, integral_const_mul, integral_add hp.1 hn.1] at hi
    change c ^ 2 * (∫ omega, F omega ∂P) ≤
      2 * ((∫ omega, E c omega ∂P) + ∫ omega, E (-c) omega ∂P) at hi
    linarith [hp.2, hn.2]
  have hI : (∫ omega, F omega ∂P) = 0 := by
    have hnonneg : 0 ≤ ∫ omega, F omega ∂P := integral_nonneg hFnonneg
    apply le_antisymm _ hnonneg
    by_contra hnot
    have hpos : 0 < ∫ omega, F omega ∂P := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := exists_nat_gt (4 / ∫ omega, F omega ∂P)
    have hc : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hlarge : 4 < ((n + 1 : ℕ) : ℝ) * (∫ omega, F omega ∂P) := by
      apply (div_lt_iff₀ hpos).mp
      exact hn.trans (by norm_num)
    have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hle := mul_le_mul_of_nonneg_right hsq hnonneg
    linarith [hbound ((n + 1 : ℕ) : ℝ)]
  have hzero := (integral_eq_zero_iff_of_nonneg hFnonneg hFint).mp hI
  filter_upwards [hzero] with omega homega
  intro hbracket
  have hmem : omega ∈ A := hbracket
  change F omega = 0 at homega
  rw [show F omega = M t omega ^ 2 from Set.indicator_of_mem hmem _] at homega
  exact sq_eq_zero_iff.mp homega

/-- If all bracket values are bounded by the terminal one, the martingale
vanishes simultaneously at every time on its zero terminal-bracket event. -/
theorem GirsanovDensityData.martingale_all_eq_zero_of_terminal_bracket_eq_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hbracket : ∀ t omega, bracket t omega ≤ bracket T omega)
    (hM2 : ∀ t, MemLp (M t) 2 P) :
    ∀ᵐ omega ∂P, bracket T omega = 0 → ∀ t, M t omega = 0 := by
  have hfixed (t : ℝ≥0) : ∀ᵐ omega ∂P, bracket T omega = 0 → M t omega = 0 := by
    filter_upwards [h.martingale_eq_zero_of_bracket_eq_zero_ae t (hM2 t)] with omega homega
    intro hzero
    apply homega
    have hnonneg : 0 ≤ bracket t omega := by
      rw [← h.bracket_zero omega]
      exact (h.continuous_monotone_bracket omega).2 bot_le
    exact le_antisymm (hzero ▸ hbracket t omega) hnonneg
  filter_upwards [ae_all_iff.mpr (fun n : ℕ ↦ hfixed (TopologicalSpace.denseSeq ℝ≥0 n))]
    with omega homega
  intro hzero
  have heq : (fun t ↦ M t omega) = fun _ ↦ (0 : ℝ) := by
    apply Continuous.ext_on (TopologicalSpace.denseRange_denseSeq ℝ≥0)
      (h.continuous_martingale_path omega) continuous_const
    rw [Set.eqOn_range]
    funext n
    exact homega n hzero
  exact congrFun heq

end StochasticCalculus
