/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.GirsanovExits

/-!
# Predictable Girsanov theorem

Novikov uniform integrability removes the bounded exits from the complex
Fourier martingales. The characteristic-function endpoint identifies the
shifted process under the exact terminal-density measure.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Exit Fourier exponentials are uniformly integrable at every fixed
time, since their norms are bounded stopped Novikov densities. -/
theorem GirsanovDensityData.uniformIntegrable_girsanovExitComplexExponential
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
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P) (c : ℝ) (t : ℝ≥0) :
    UniformIntegrable (fun n : ℕ ↦
      girsanovExitComplexExponential M bracket B theta T (n + 1) c t) 1 P := by
  let tau : ℕ → W → WithTop ℝ≥0 := fun n omega ↦
    (min (min t T) (girsanovExitTime M T (n + 1) omega) : ℝ≥0)
  have htau (n : ℕ) : IsStoppingTime V (tau n) := by
    simpa only [tau, WithTop.coe_min] using (isStoppingTime_const V (min t T)).min
      (isStoppingTime_girsanovExitTime h.adapted_martingale T (n + 1))
  have hbound (n : ℕ) (omega : W) : tau n omega ≤ (T : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr ((min_le_left _ _).trans (min_le_right t T))
  have hUI := h.novikov.uniformIntegrable_stoppedValue_doleansDade
    h.localQuadraticVariation h.continuous_martingale_path h.adapted_martingale
    h.adapted_bracket h.continuous_monotone_bracket h.martingale_zero h.bracket_zero
    tau htau hbound
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2))
  have hmultiple := StochasticCalculus.UniformIntegrable.nsmul_banach hUI (by norm_num) N
  apply StochasticCalculus.UniformIntegrable.mono_norm_banach hmultiple
  · intro n
    exact ((h.martingale_girsanovExitComplexExponential hB hBmart htheta hbracketTheta
      hcross (by positivity : (0 : ℝ≥0) < n + 1) c).integrable t).aestronglyMeasurable
  · intro n omega
    rw [norm_girsanovExitComplexExponential]
    change doleansDadeExponential M bracket
        (min (min t T) (girsanovExitTime M T (n + 1) omega)) omega *
        Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
      ‖N • doleansDadeExponential M bracket
        (min (min t T) (girsanovExitTime M T (n + 1) omega)) omega‖
    have hZpos := doleansDadeExponential_pos M bracket
      (min (min t T) (girsanovExitTime M T (n + 1) omega)) omega
    calc
      _ ≤ doleansDadeExponential M bracket
          (min (min t T) (girsanovExitTime M T (n + 1) omega)) omega * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hZpos.le
      _ = _ := by
        rw [nsmul_eq_mul, norm_mul, norm_natCast, Real.norm_eq_abs, abs_of_pos hZpos]
        ring

/-- On each continuous integrator path, the exited Fourier exponential is
eventually exactly the original one at every fixed observation time. -/
theorem eventually_girsanovExitComplexExponential_eq
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega)
    (bracket B theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (c : ℝ) (t : ℝ≥0) (omega : W) :
    ∀ᶠ n : ℕ in atTop,
      girsanovExitComplexExponential M bracket B theta T (n + 1) c t omega =
        complexDoleansDadeExponential (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket
            (fun u omega ↦ -girsanovIntegratedDrift theta T u omega) c) (min t T) omega := by
  filter_upwards [eventually_girsanovExitTime_eq_terminal hMcont T omega] with n hn
  simp only [girsanovExitComplexExponential, complexDoleansDadeExponential,
    complexMartingaleCombination, complexMartingaleCombinationBracket,
    girsanovIntegratedDrift_stoppedPredictableCoefficient, hn, min_assoc, min_self]

/-- Novikov closes the full complex Fourier martingale without a density
bound or any supplementary Euler approximation hypothesis. -/
theorem GirsanovDensityData.martingale_stopAt_complexDoleans_predictable
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
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P) (c : ℝ) :
    Martingale (fun t ↦ complexDoleansDadeExponential (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket
        (fun u omega ↦ -girsanovIntegratedDrift theta T u omega) c) (min t T)) V P := by
  let C := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
  let E := complexDoleansDadeExponential (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let X := fun n : ℕ ↦ girsanovExitComplexExponential M bracket B theta T (n + 1) c
  have hX (n : ℕ) : Martingale (X n) V P :=
    h.martingale_girsanovExitComplexExponential hB hBmart htheta hbracketTheta hcross
      (by positivity : (0 : ℝ≥0) < n + 1) c
  have hC : StronglyAdapted V C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift htheta T).neg
  have hE : StronglyAdapted V E := stronglyAdapted_complexDoleansDadeExponential
    (stronglyAdapted_complexMartingaleCombination h.adapted_martingale hBmart.stronglyAdapted c)
    (stronglyAdapted_complexMartingaleCombinationBracket h.adapted_bracket hC c)
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable_banach hX
    (fun t ↦ (hE (min t T)).mono (V.mono (min_le_left t T)))
    (h.uniformIntegrable_girsanovExitComplexExponential hB hBmart htheta hbracketTheta hcross c)
  intro t
  apply tendstoInMeasure_of_tendsto_ae
    (fun n ↦ ((hX n).integrable t).aestronglyMeasurable)
  filter_upwards with omega
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_girsanovExitComplexExponential_eq h.continuous_martingale_path
    bracket B theta T c t omega] with n hn
  exact hn.symm

/-- Predictable Girsanov for the raw natural filtration and the exact
terminal-density measure. No continuity assumption on the Brownian version
or extra integrability assumption is added to the input contract. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_predictable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T) (girsanovMeasure P M bracket T) := by
  apply h.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
    hsm hB htheta
  intro c
  exact h.rightCont.martingale_stopAt_complexDoleans_predictable hB
    (martingale_brownian_rightCont_natural hB hsm)
    (StochasticCalculus.IsStronglyPredictable.mono_filtration htheta
      (Filtration.natural B hsm).le_rightCont) hbracketTheta hcross c

end StochasticCalculus
