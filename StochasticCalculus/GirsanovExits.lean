/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovLocalization
import StochasticCalculus.ZeroBracket

/-!
# Bounded exits for the predictable Girsanov closure
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The bounded continuous exit as a finite nonnegative time. -/
noncomputable def girsanovExitTime
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) : ℝ≥0 :=
  (continuousExitTime M T R omega).untopA

/-- The finite exit represents the original WithTop stopping time exactly. -/
theorem coe_girsanovExitTime
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    (girsanovExitTime M T R omega : WithTop ℝ≥0) = continuousExitTime M T R omega := by
  rw [girsanovExitTime, WithTop.untopA_eq_untop (continuousExitTime_ne_top M T R omega),
    WithTop.coe_untop]

theorem girsanovExitTime_le
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    girsanovExitTime M T R omega ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [coe_girsanovExitTime]
  exact continuousExitTime_le M T R omega

theorem isStoppingTime_girsanovExitTime
    {W : Type*} [MeasurableSpace W] {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    [V.IsRightContinuous] {M : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (T R : ℝ≥0) :
    IsStoppingTime V (fun omega ↦ (girsanovExitTime M T R omega : WithTop ℝ≥0)) := by
  simpa only [coe_girsanovExitTime] using
    isStoppingTime_continuousExitTime_of_stronglyAdapted hM T R

/-- The indicated localization and ordinary stopping conventions agree
for a process starting at zero. -/
theorem localizingStoppedProcess_coe_nnreal_of_zero
    {W : Type*} {M : ℝ≥0 → W → ℝ} (hMzero : ∀ omega, M 0 omega = 0)
    (tau : W → ℝ≥0) :
    localizingStoppedProcess M (fun omega ↦ (tau omega : WithTop ℝ≥0)) =
      fun t omega ↦ M (min t (tau omega)) omega := by
  funext t omega
  unfold localizingStoppedProcess
  rw [stoppedProcess_coe_nnreal]
  dsimp only
  by_cases hpos : 0 < tau omega
  · rw [Set.indicator_of_mem]
    change (0 : WithTop ℝ≥0) < (tau omega : WithTop ℝ≥0)
    exact_mod_cast hpos
  · have hzero : tau omega = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    have hM0 : M 0 = 0 := funext hMzero
    simp only [hzero, min_zero, hM0, Pi.zero_apply]
    exact Set.indicator_apply_eq_zero.mpr (fun _ ↦ rfl)

/-- A continuous normalized process stopped at its radius exit has a
pathwise deterministic bound. -/
theorem norm_stop_girsanovExitTime_le
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega)
    (hMzero : ∀ omega, M 0 omega = 0) (T R t : ℝ≥0) (omega : W) :
    ‖M (min t (girsanovExitTime M T R omega)) omega‖ ≤ R := by
  have hfun : (fun omega ↦ (girsanovExitTime M T R omega : WithTop ℝ≥0)) =
      continuousExitTime M T R := funext (coe_girsanovExitTime M T R)
  have heq := localizingStoppedProcess_coe_nnreal_of_zero hMzero (girsanovExitTime M T R)
  rw [hfun] at heq
  rw [← show localizingStoppedProcess M (continuousExitTime M T R) t omega =
      M (min t (girsanovExitTime M T R omega)) omega from congrFun (congrFun heq t) omega]
  exact norm_localizingStoppedProcess_continuousExitTime_le hMcont T R t omega

/-- Increasing-radius exits are eventually the full horizon on every
continuous path. -/
theorem eventually_girsanovExitTime_eq_terminal
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega) (T : ℝ≥0) (omega : W) :
    ∀ᶠ n : ℕ in atTop, girsanovExitTime M T (n + 1) omega = T := by
  have hAbs := (hMcont omega).abs
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hAbs.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  filter_upwards [eventually_ge_atTop N] with n hn
  have heq : continuousExitTime M T (n + 1) omega = T := by
    apply continuousExitTime_eq_terminal_of_norm_lt
    intro t ht
    have hCt : |M t omega| ≤ C := hC ⟨t, ⟨bot_le, ht⟩, rfl⟩
    calc
      |M t omega| ≤ C := hCt
      _ ≤ (N : ℝ) := hN
      _ < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
      _ = ((n + 1 : ℝ≥0) : ℝ) := by norm_num
  simp only [girsanovExitTime, heq]
  rfl

/-- The continuous and literal drifts agree at the continuous martingale
exit. On zero-bracket paths the exit is the deterministic terminal time. -/
theorem GirsanovDensityData.regularizedDrift_at_exit_ae_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) (hB : IsPreBrownianReal B P)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    {R : ℝ≥0} (hR : 0 < R) (t : ℝ≥0) :
    (fun omega ↦ regularizedGirsanovIntegratedDrift bracket theta T
      (min t (girsanovExitTime M T R omega)) omega) =ᵐ[P]
    girsanovIntegratedDrift (stoppedPredictableCoefficient theta (girsanovExitTime M T R)) T t := by
  have hAle := h.bracket_le_terminal_of_integratedSquare hbracketTheta
  have hMzero := h.martingale_all_eq_zero_of_terminal_bracket_eq_zero_ae hAle
    (fun s ↦ (h.memLp_four_martingale_of_bracket_le hAle s).mono_exponent (by norm_num))
  filter_upwards [hMzero, h.regularizedGirsanovIntegratedDrift_ae_eq hcross hB (min t T)]
    with omega hzero hfixed
  rw [girsanovIntegratedDrift_stoppedPredictableCoefficient]
  by_cases hA : bracket T omega = 0
  · have hpath := hzero hA
    have hexit : continuousExitTime M T R omega = T := by
      apply continuousExitTime_eq_terminal_of_norm_lt
      intro s _
      rw [hpath s, abs_zero]
      exact_mod_cast hR
    have heq : girsanovExitTime M T R omega = T := by
      simp only [girsanovExitTime, hexit]
      rfl
    simpa only [heq] using hfixed
  · simp only [regularizedGirsanovIntegratedDrift, hA, if_false]

/-- The literal stopped coefficient is the cross bracket after a positive
radius exit of the Girsanov integrator. -/
theorem GirsanovDensityData.crossVariation_girsanovExitTime
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
    {R : ℝ≥0} (hR : 0 < R) :
    HasCrossVariationProcessInProbability
      (fun t omega ↦ M (min t (girsanovExitTime M T R omega)) omega) B
      (fun t omega ↦ -girsanovIntegratedDrift
        (stoppedPredictableCoefficient theta (girsanovExitTime M T R)) T t omega) P := by
  have hstop := h.crossVariation_stop_regularized hB hBmart htheta hbracketTheta hcross
    (isStoppingTime_girsanovExitTime h.adapted_martingale T R)
  intro t
  exact (hstop t).congr_right
    (h.regularizedDrift_at_exit_ae_eq hB hbracketTheta hcross hR t).neg

/-- The complex Fourier exponential for the coefficient and integrator
stopped at a bounded continuous radius exit. -/
noncomputable def girsanovExitComplexExponential
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (c : ℝ)
    (t : ℝ≥0) (omega : W) : ℂ :=
  complexDoleansDadeExponential
    (complexMartingaleCombination
      (fun s omega ↦ M (min s (girsanovExitTime M T R omega)) omega) B c)
    (complexMartingaleCombinationBracket
      (fun s omega ↦ bracket (min s (girsanovExitTime M T R omega)) omega)
      (fun s omega ↦ -girsanovIntegratedDrift
        (stoppedPredictableCoefficient theta (girsanovExitTime M T R)) T s omega) c)
    (min t T) omega

/-- Every positive-radius exit gives a genuine complex exponential
martingale by the bounded-density Girsanov theorem. -/
theorem GirsanovDensityData.martingale_girsanovExitComplexExponential
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
    {R : ℝ≥0} (hR : 0 < R) (c : ℝ) :
    Martingale (girsanovExitComplexExponential M bracket B theta T R c) V P := by
  let tau := girsanovExitTime M T R
  have htau := isStoppingTime_girsanovExitTime h.adapted_martingale T R
  have hbound := girsanovExitTime_le M T R
  have hdata := h.stop htau hbound
  have htheta' := IsStronglyPredictable.stoppedPredictableCoefficient htheta htau
  have hcross' := h.crossVariation_girsanovExitTime hB hBmart htheta hbracketTheta hcross hR
  let cap : ℝ≥0 := ⟨Real.exp (R : ℝ), (Real.exp_pos _).le⟩
  have hcap : ∀ s, s ≤ T → ∀ omega,
      doleansDadeExponential (fun u omega ↦ M (min u (tau omega)) omega)
        (fun u omega ↦ bracket (min u (tau omega)) omega) s omega ≤ cap := by
    intro s _ omega
    have hnorm := norm_stop_girsanovExitTime_le h.continuous_martingale_path
      h.martingale_zero T R s omega
    have hMle : M (min s (tau omega)) omega ≤ R :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
    have hAnonneg : 0 ≤ bracket (min s (tau omega)) omega := by
      rw [← h.bracket_zero omega]
      exact (h.continuous_monotone_bracket omega).2 bot_le
    change Real.exp (M (min s (tau omega)) omega -
      (1 / 2 : ℝ) * bracket (min s (tau omega)) omega) ≤ Real.exp (R : ℝ)
    apply Real.exp_le_exp.mpr
    linarith
  exact hdata.martingale_stopAt_complexDoleans_of_density_le hB
    (fun t ↦ (hBmart.stronglyAdapted t).mono (V.le t)) hBmart htheta'
    (bracket_stoppedPredictableCoefficient hbracketTheta tau) hcross' cap hcap c

/-- Its norm is the original Novikov density evaluated at a bounded
stopping time, times the deterministic Fourier normalization. -/
theorem norm_girsanovExitComplexExponential
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (c : ℝ)
    (t : ℝ≥0) (omega : W) :
    ‖girsanovExitComplexExponential M bracket B theta T R c t omega‖ =
      doleansDadeExponential M bracket (min (min t T) (girsanovExitTime M T R omega)) omega *
        Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) := by
  unfold girsanovExitComplexExponential
  rw [norm_complexDoleansDadeExponential_combination]
  rfl

end StochasticCalculus
