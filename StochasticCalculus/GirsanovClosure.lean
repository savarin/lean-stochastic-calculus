/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.Girsanov

/-!
# Common-grid closure for the Girsanov exponential

This module transports the stochastic Taylor residual to rational observation
times on one common grid, and develops the remaining martingale closure.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- A cell functional that vanishes on degenerate cells has the same stopped
sum on a common refinement as its terminal sum on the shorter rational
horizon. This identity does not require continuity of any process. -/
theorem uniformStoppedCellSum_common_refinement
    {E : Type*} [AddCommMonoid E]
    (F : ℝ≥0 → ℝ≥0 → E) (hF : ∀ a, F a a = 0)
    (T : ℝ≥0) {k j N : ℕ} (hk : 0 < k) (hj : 0 < j)
    (hN : 0 < N) (hjk : j ≤ k) :
    (∑ i ∈ Finset.range (k * N),
      F (min (T * (j : ℝ≥0) / (k : ℝ≥0))
          (uniformPartitionTime T (k * N) (i + 1)))
        (min (T * (j : ℝ≥0) / (k : ℝ≥0))
          (uniformPartitionTime T (k * N) i))) =
      ∑ i ∈ Finset.range (j * N),
        F (min (T * (j : ℝ≥0) / (k : ℝ≥0))
            (uniformPartitionTime (T * (j : ℝ≥0) / (k : ℝ≥0))
              (j * N) (i + 1)))
          (min (T * (j : ℝ≥0) / (k : ℝ≥0))
            (uniformPartitionTime (T * (j : ℝ≥0) / (k : ℝ≥0))
              (j * N) i)) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let f : ℕ → E := fun i ↦
    F (min a (uniformPartitionTime T (k * N) (i + 1)))
      (min a (uniformPartitionTime T (k * N) i))
  have htime : uniformPartitionTime T (k * N) (j * N) = a := by
    rw [uniformPartitionTime_common_refinement_covariation T hk hj hN]
    have hn0 : ((j * N : ℕ) : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hj hN)
    exact mul_div_cancel_right₀ a hn0
  have htail : ∑ i ∈ Finset.Ico (j * N) (k * N), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : a ≤ uniformPartitionTime T (k * N) i := by
      rw [← htime]
      exact monotone_uniformPartitionTime_general T (k * N)
        (Finset.mem_Ico.mp hi).1
    have hi1 : a ≤ uniformPartitionTime T (k * N) (i + 1) :=
      hi0.trans (monotone_uniformPartitionTime_general T (k * N) (Nat.le_succ i))
    simp only [f, min_eq_left hi0, min_eq_left hi1, hF]
  change (∑ i ∈ Finset.range (k * N), f i) = _
  rw [← Finset.sum_range_add_sum_Ico f (Nat.mul_le_mul_right N hjk),
    htail, add_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only [f, a]
  rw [uniformPartitionTime_common_refinement_covariation T hk hj hN (i + 1),
    uniformPartitionTime_common_refinement_covariation T hk hj hN i]

/-- The complete weighted complex bracket residual transports exactly to
every positive rational grid prefix. There is no crossing cell at an aligned
observation time. -/
theorem complexDoleansWeightedBracketResidualApprox_common_refinement
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (hjk : j ≤ k) (omega : W) :
    complexDoleansWeightedBracketResidualApprox X Q T (k * N)
        (T * (j : ℝ≥0) / (k : ℝ≥0)) omega =
      complexDoleansWeightedBracketResidualApprox X Q
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N)
        (T * (j : ℝ≥0) / (k : ℝ≥0)) omega := by
  apply uniformStoppedCellSum_common_refinement
    (fun b a ↦ complexDoleansDadeExponential X Q a omega *
      ((X b omega - X a omega) ^ 2 - (Q b omega - Q a omega)))
    (fun a ↦ by simp) T hk hj hN hjk

/-- Completed fine-grid cross variation integrated against fixed coarse
weights, minus the same weights integrated against the proposed bracket.
Both grid parameters count subdivisions minus one. -/
def complexCoarseCrossResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X Y A : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (k n : ℕ) (omega : W) : ℂ :=
  (∑ j ∈ Finset.range (k + 1),
    H (uniformPartitionTime T (k + 1) j) omega *
      (quadraticCovariationBeforeStopApprox X Y T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) (j + 1)) omega -
        quadraticCovariationBeforeStopApprox X Y T ((k + 1) * (n + 1))
          (uniformPartitionTime T (k + 1) j) omega : ℂ)) -
    ∑ j ∈ Finset.range (k + 1),
      H (uniformPartitionTime T (k + 1) j) omega *
        (A (uniformPartitionTime T (k + 1) (j + 1)) omega -
          A (uniformPartitionTime T (k + 1) j) omega : ℂ)

/-- Fixed coarse weights require only the input's ordinary deterministic-
time cross-variation contract. -/
theorem HasCrossVariationProcessInProbability.complexCoarseCrossResidualApprox_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {H : ℝ≥0 → W → ℂ} {X Y A : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y A P)
    (hX : ∀ t, AEStronglyMeasurable (X t) P)
    (hY : ∀ t, AEStronglyMeasurable (Y t) P)
    (hH : ∀ t, AEStronglyMeasurable (H t) P) (T : ℝ≥0) (k : ℕ) :
    TendstoInMeasure P (fun n ↦ complexCoarseCrossResidualApprox H X Y A T k n)
      atTop (fun _ ↦ 0) := by
  have hc := h.fullComplexStepWeight_beforeStop_common_refinement hX hY T
    (Nat.zero_lt_succ k)
      (fun j omega ↦ H (uniformPartitionTime T (k + 1) j) omega)
      (fun _ _ ↦ hH _)
  rw [tendstoInMeasure_iff_norm] at hc ⊢
  simpa only [complexCoarseCrossResidualApprox, sub_zero] using hc

/-- The coarse error whose three real components combine into the complex
Girsanov bracket. -/
def complexGirsanovCoarseBracketResidualApprox
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (k n : ℕ) (omega : W) : ℂ :=
  let H := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  complexCoarseCrossResidualApprox H M M bracket T k n omega -
    (c ^ 2 : ℂ) * complexCoarseCrossResidualApprox H B B
      (fun t _omega ↦ (t : ℝ)) T k n omega +
    (((2 * c : ℝ) : ℂ) * Complex.I) *
      complexCoarseCrossResidualApprox H M B C T k n omega

/-- Every section of the algebraic complex exponential is measurable when
its four real input processes have measurable sections. -/
theorem stronglyMeasurable_complexDoleansCombination
    {W : Type*} [MeasurableSpace W]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hM : ∀ t, StronglyMeasurable (M t))
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hB : ∀ t, StronglyMeasurable (B t))
    (hC : ∀ t, StronglyMeasurable (C t)) (c : ℝ) (t : ℝ≥0) :
    StronglyMeasurable (complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t) := by
  have hcontinuous := stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    hM hbracket hC c t
  have hfourier : StronglyMeasurable (fun omega ↦
      Complex.exp (((c * B t omega : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp_stronglyMeasurable
      ((Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hB t).const_mul c)).mul_const Complex.I)
  convert hcontinuous.mul hfourier using 1
  exact funext fun omega ↦
    complexDoleansDadeExponential_combination_factor_continuous_brownian
      M bracket B C c t omega

/-- All three fixed-coarse bracket limits combine before any diagonal is
chosen. This permits two different horizons to share a later selection. -/
theorem GirsanovDensityData.complexGirsanovCoarseBracketResidualApprox_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hC : ∀ t, StronglyMeasurable (C t))
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (c : ℝ) (U : ℝ≥0) (k : ℕ) :
    TendstoInMeasure P
      (fun n ↦ complexGirsanovCoarseBracketResidualApprox M bracket B C c U k n)
      atTop (fun _ ↦ 0) := by
  let H := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  have hMmeas : ∀ t, StronglyMeasurable (M t) := fun t ↦
    (hdata.adapted_martingale t).mono (V.le t)
  have hH : ∀ t, AEStronglyMeasurable (H t) P := fun t ↦
    (stronglyMeasurable_complexDoleansCombination hMmeas
      (fun u ↦ (hdata.adapted_bracket u).mono (V.le u)) hsm hC c t).aestronglyMeasurable
  have hMM := hdata.localQuadraticVariation.toProcess.toCrossVariationSelf
    |>.complexCoarseCrossResidualApprox_tendsto
      (fun t ↦ (hMmeas t).aestronglyMeasurable)
      (fun t ↦ (hMmeas t).aestronglyMeasurable) hH U k
  have hQB : HasQuadraticVariationProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) P := fun t ↦
    quadraticVariation_preBrownianReal_inProbability hB t
  have hBB := hQB.toCrossVariationSelf.complexCoarseCrossResidualApprox_tendsto
    (fun t ↦ (hsm t).aestronglyMeasurable)
    (fun t ↦ (hsm t).aestronglyMeasurable) hH U k
  have hMB := hcross.complexCoarseCrossResidualApprox_tendsto
    (fun t ↦ (hMmeas t).aestronglyMeasurable)
    (fun t ↦ (hsm t).aestronglyMeasurable) hH U k
  have hsum := TendstoInMeasure.add_normed_noMeas
    (TendstoInMeasure.sub_normed_noMeas hMM
      (TendstoInMeasure.const_mul_complex_noMeas hBB (c ^ 2 : ℂ)))
      (TendstoInMeasure.const_mul_complex_noMeas hMB
        (((2 * c : ℝ) : ℂ) * Complex.I))
  rw [tendstoInMeasure_iff_norm] at hsum ⊢
  simpa only [complexGirsanovCoarseBracketResidualApprox, H,
    mul_zero, sub_zero, zero_add] using hsum

/-- Freezing the complex weight identifies a fine weighted cross residual
with its coarse residual, for any selected inner counts. The latter can
therefore be synchronized independently across several horizons. -/
theorem GirsanovDensityData.complexWeightedCrossResidual_sub_coarse_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y A : ℝ≥0 → W → ℝ} {T : ℝ≥0}
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
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega)} < eta)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox A T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    let H := complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
    TendstoInMeasure P (fun r omega ↦
      complexWeightedCrossResidualApprox H X Y A T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T omega -
        complexCoarseCrossResidualApprox H X Y A T
          ((r + 1) ^ 5 - 1) (n ((r + 1) ^ 5 - 1)) omega)
      atTop (fun _ ↦ 0) := by
  have hfreeze := hdata.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    hB hsm hCmeas hCcont c hT n hqtight
  have hfv := hdata.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
    hB hsm hCmeas hCcont c hT n htvtight
  have hdiff := TendstoInMeasure.sub_normed_noMeas hfreeze hfv
  have hdiff' := hdiff.congr_right
    (Filter.Eventually.of_forall fun _omega ↦ sub_zero (0 : ℂ))
  apply hdiff'.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦ by
    have hK : (r + 1) ^ 5 - 1 + 1 = (r + 1) ^ 5 := by
      apply Nat.sub_add_cancel
      have hp : 0 < (r + 1) ^ 5 := by positivity
      omega
    dsimp only
    rw [complexWeightedCrossResidualApprox_terminal]
    simp only [complexCoarseCrossResidualApprox, hK]
    ring

/-- The complete complex bracket residual differs from its coarse three-
component residual by a quantity tending to zero on every polynomial
common-refinement diagonal. No covariation diagonal is chosen here. -/
theorem GirsanovDensityData.complexWeightedBracketResidual_sub_coarse_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (htvC : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox C T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    TendstoInMeasure P (fun r omega ↦
      complexDoleansWeightedBracketResidualApprox
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c) T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) T omega -
        complexGirsanovCoarseBracketResidualApprox M bracket B C c T
          ((r + 1) ^ 5 - 1) (n ((r + 1) ^ 5 - 1)) omega)
      atTop (fun _ ↦ 0) := by
  let H := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let N : ℕ → ℕ := fun r ↦ ((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)
  have hN : ∀ r, 0 < N r := fun r ↦ by dsimp only [N]; positivity
  have hQB : HasQuadraticVariationProcessInProbability B
      (fun t _omega ↦ (t : ℝ)) P := fun t ↦
    quadraticVariation_preBrownianReal_inProbability hB t
  have hMM := hdata.complexWeightedCrossResidual_sub_coarse_tendsto
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
    (hdata.eventually_tight_totalVariationApprox_bracket N hN)
  have hBB := hdata.complexWeightedCrossResidual_sub_coarse_tendsto
    hB hsm hCmeas hCcont c hT n (by
      exact hQB.polynomialBlocks_eventually_tight_sqrt_mul hQB T
        ((integrable_const (T : ℝ)).add (integrable_const (T : ℝ)))
        (Filter.Eventually.of_forall fun _ ↦ add_nonneg T.coe_nonneg T.coe_nonneg)
        (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity))
    (eventually_tight_totalVariationApprox_time (P := P) T N hN)
  have hMB := hdata.complexWeightedCrossResidual_sub_coarse_tendsto
    hB hsm hCmeas hCcont c hT n
    (hdata.polynomialBlocks_eventually_tight_sqrt_martingale_preBrownian
      hB (fun r ↦ n ((r + 1) ^ 5 - 1) + 1) (fun _ ↦ by positivity)) htvC
  have hsum := TendstoInMeasure.add_normed_noMeas
    (TendstoInMeasure.sub_normed_noMeas hMM
      (TendstoInMeasure.const_mul_complex_noMeas hBB (c ^ 2 : ℂ)))
      (TendstoInMeasure.const_mul_complex_noMeas hMB
        (((2 * c : ℝ) : ℂ) * Complex.I))
  have hsum' : TendstoInMeasure P
      (fun r omega ↦
        (complexWeightedCrossResidualApprox H M M bracket T (N r) T omega -
          complexCoarseCrossResidualApprox H M M bracket T
            ((r + 1) ^ 5 - 1) (n ((r + 1) ^ 5 - 1)) omega) -
        (c ^ 2 : ℂ) *
          (complexWeightedCrossResidualApprox H B B (fun t _omega ↦ (t : ℝ))
            T (N r) T omega - complexCoarseCrossResidualApprox H B B
              (fun t _omega ↦ (t : ℝ)) T
              ((r + 1) ^ 5 - 1) (n ((r + 1) ^ 5 - 1)) omega) +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          (complexWeightedCrossResidualApprox H M B C T (N r) T omega -
            complexCoarseCrossResidualApprox H M B C T
              ((r + 1) ^ 5 - 1) (n ((r + 1) ^ 5 - 1)) omega))
      atTop (fun _ ↦ 0) := by
    simpa only [H, N, mul_zero, sub_zero, zero_add] using hsum
  apply hsum'.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦ by
    dsimp only
    rw [complexDoleansWeightedBracketResidualApprox_combination,
      complexWeightedQuadraticResidualApprox_eq_cross_self,
      complexWeightedQuadraticResidualApprox_eq_cross_self]
    dsimp only [complexGirsanovCoarseBracketResidualApprox, H, N]
    ring

/-- Multiplying positive subdivision counts preserves cofinality. -/
theorem tendsto_nat_mul_succ_sub_one {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ d * (n + 1) - 1) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun n hbn ↦ hbn.trans ?_⟩
  exact Nat.le_sub_one_of_lt ((Nat.lt_succ_self n).trans_le
    (Nat.le_mul_of_pos_left (n + 1) hd))

/-- The polynomial coarse index is cofinal. -/
theorem tendsto_girsanov_polynomialIndex :
    Tendsto (fun r : ℕ ↦ (r + 1) ^ 5 - 1) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun n hbn ↦ hbn.trans ?_⟩
  exact Nat.le_sub_one_of_lt ((Nat.lt_succ_self n).trans_le
    (Nat.le_pow (by norm_num)))

set_option maxHeartbeats 2000000 in
-- The two expanded horizon sums and the common-divisibility identities are elaborated together.
/-- At a positive rational subdivision and the terminal horizon, the full
weighted complex bracket residuals vanish along one common cofinal grid.
The joint diagonal is chosen before the two different divisibility factors
are applied. -/
theorem GirsanovDensityData.exists_rational_pair_complexWeightedBracketResidual
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hCvar : ∀ S, S ≤ T → ∀ N : ℕ → ℕ, (∀ r, 0 < N r) →
      ∀ eta : ℝ, 0 < eta → ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox C S (N r) omega} < eta)
    (c : ℝ) (hUT : U ≤ T) (hU : 0 < U)
    {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U (q r + 1) (U * (j : ℝ≥0) / (k : ℝ≥0))) atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U (q r + 1) U) atTop (fun _ ↦ 0) := by
  let a : ℝ≥0 := U * (j : ℝ≥0) / (k : ℝ≥0)
  have haU : a ≤ U := (uniformPartitionTime_mem_Icc_of_le U hk hjk).2
  have haT : a ≤ T := haU.trans hUT
  have ha : 0 < a := by dsimp only [a]; positivity
  let F : ℕ → ℕ → W → ℂ × ℂ := fun l n omega ↦
    (complexGirsanovCoarseBracketResidualApprox M bracket B C c a l
        (j * (n + 1) - 1) omega,
      complexGirsanovCoarseBracketResidualApprox M bracket B C c U l
        (k * (n + 1) - 1) omega)
  have hF : ∀ l, TendstoInMeasure P (F l) atTop (fun _ ↦ (0 : ℂ × ℂ)) := by
    intro l
    exact TendstoInMeasure.prodMk_noMeas
      ((hdata.complexGirsanovCoarseBracketResidualApprox_tendsto
        hB hsm hCmeas hcross c a l).comp (tendsto_nat_mul_succ_sub_one hj))
      ((hdata.complexGirsanovCoarseBracketResidualApprox_tendsto
        hB hsm hCmeas hcross c U l).comp (tendsto_nat_mul_succ_sub_one hk))
  obtain ⟨n, _hn, hd⟩ := TendstoInMeasure.exists_strictMono_diagonal_sub_normed hF
  let p : ℕ → ℕ := fun r ↦ (r + 1) ^ 5 - 1
  let na : ℕ → ℕ := fun l ↦ j * (n l + 1) - 1
  let nu : ℕ → ℕ := fun l ↦ k * (n l + 1) - 1
  have hna (l : ℕ) : na l + 1 = j * (n l + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hj (Nat.zero_lt_succ _))
  have hnu (l : ℕ) : nu l + 1 = k * (n l + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hk (Nat.zero_lt_succ _))
  have hda : TendstoInMeasure P (fun r ↦
      complexGirsanovCoarseBracketResidualApprox M bracket B C c a (p r) (na (p r)))
      atTop (fun _ ↦ 0) := by
    have h := (TendstoInMeasure.fst_noMeas hd).comp tendsto_girsanov_polynomialIndex
    rw [tendstoInMeasure_iff_norm] at h ⊢
    simpa only [F, Prod.fst_sub, Prod.fst_zero, sub_zero,
      Function.comp_apply, p, na] using h
  have hdu : TendstoInMeasure P (fun r ↦
      complexGirsanovCoarseBracketResidualApprox M bracket B C c U (p r) (nu (p r)))
      atTop (fun _ ↦ 0) := by
    have h := (TendstoInMeasure.snd_noMeas hd).comp tendsto_girsanov_polynomialIndex
    rw [tendstoInMeasure_iff_norm] at h ⊢
    simpa only [F, Prod.snd_sub, Prod.snd_zero, sub_zero,
      Function.comp_apply, p, nu] using h
  have hfa := (hdata.mono_time haT).complexWeightedBracketResidual_sub_coarse_tendsto
    hB hsm hCmeas hCcont c ha na
      (hCvar a haT _ (fun _ ↦ by positivity))
  have hfu := (hdata.mono_time hUT).complexWeightedBracketResidual_sub_coarse_tendsto
    hB hsm hCmeas hCcont c hU nu
      (hCvar U hUT _ (fun _ ↦ by positivity))
  have hra : TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      a (((r + 1) ^ 5) * (na (p r) + 1)) a) atTop (fun _ ↦ 0) := by
    have h := TendstoInMeasure.add_normed_noMeas hfa hda
    simpa only [p, sub_add_cancel, zero_add] using h
  have hru : TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      U (((r + 1) ^ 5) * (nu (p r) + 1)) U) atTop (fun _ ↦ 0) := by
    have h := TendstoInMeasure.add_normed_noMeas hfu hdu
    simpa only [p, sub_add_cancel, zero_add] using h
  let q : ℕ → ℕ := fun r ↦ ((r + 1) ^ 5) * (k * (n (p r) + 1)) - 1
  have hqadd (r : ℕ) : q r + 1 = ((r + 1) ^ 5) * (k * (n (p r) + 1)) := by
    apply Nat.sub_add_cancel
    have hpos : 0 < ((r + 1) ^ 5) * (k * (n (p r) + 1)) := by positivity
    exact hpos
  have hq : Tendsto q atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun r hbr ↦ hbr.trans ?_⟩
    apply Nat.le_sub_one_of_lt
    exact (Nat.lt_succ_self r).trans_le
      ((Nat.le_pow (by norm_num)).trans
        (Nat.le_mul_of_pos_right _ (Nat.mul_pos hk (Nat.zero_lt_succ _))))
  refine ⟨q, hq, ?_, ?_⟩
  · apply hra.congr_left
    intro r
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [hqadd, hna, Nat.mul_left_comm ((r + 1) ^ 5) j,
        Nat.mul_left_comm ((r + 1) ^ 5) k]
      exact (complexDoleansWeightedBracketResidualApprox_common_refinement
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) U hk hj
        (by positivity) hjk omega).symm
  · apply hru.congr_left
    intro r
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [hqadd, hnu]

/-- A deterministic finite stopped-cell sum respects almost-everywhere
replacement of its cell functional on the grid horizon. -/
theorem uniformStoppedCellSum_congr_ae
    {W E : Type*} [MeasurableSpace W] [AddCommMonoid E] {P : Measure W}
    (F G : ℝ≥0 → ℝ≥0 → W → E) (U : ℝ≥0)
    (hFG : ∀ b, b ≤ U → ∀ a, a ≤ U → F b a =ᵐ[P] G b a)
    (n : ℕ) (t : ℝ≥0) :
    (fun omega ↦ ∑ i ∈ Finset.range n,
      F (min t (uniformPartitionTime U n (i + 1)))
        (min t (uniformPartitionTime U n i)) omega) =ᵐ[P]
      (fun omega ↦ ∑ i ∈ Finset.range n,
        G (min t (uniformPartitionTime U n (i + 1)))
          (min t (uniformPartitionTime U n i)) omega) := by
  have hcell (i : Fin n) :
      F (min t (uniformPartitionTime U n (i.val + 1)))
          (min t (uniformPartitionTime U n i.val)) =ᵐ[P]
        G (min t (uniformPartitionTime U n (i.val + 1)))
          (min t (uniformPartitionTime U n i.val)) := by
    have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
    exact hFG _ ((min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn i.isLt).2) _
      ((min_le_right _ _).trans
        (uniformPartitionTime_mem_Icc_of_le U hn i.isLt.le).2)
  filter_upwards [ae_all_iff.mpr hcell] with omega homega
  exact Finset.sum_congr rfl fun i hi ↦ homega ⟨i, Finset.mem_range.mp hi⟩

/-- The weighted complex bracket residual is insensitive to deterministic-
time almost-everywhere modifications of its bracket on the grid horizon. -/
theorem complexDoleansWeightedBracketResidualApprox_congr_bracket_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (X Q Q' : ℝ≥0 → W → ℂ) (U : ℝ≥0)
    (hQ : ∀ s, s ≤ U → Q s =ᵐ[P] Q' s) (n : ℕ) (t : ℝ≥0) :
    complexDoleansWeightedBracketResidualApprox X Q U n t =ᵐ[P]
      complexDoleansWeightedBracketResidualApprox X Q' U n t := by
  apply uniformStoppedCellSum_congr_ae
    (fun b a omega ↦ complexDoleansDadeExponential X Q a omega *
      ((X b omega - X a omega) ^ 2 - (Q b omega - Q a omega)))
    (fun b a omega ↦ complexDoleansDadeExponential X Q' a omega *
      ((X b omega - X a omega) ^ 2 - (Q' b omega - Q' a omega))) U ?_ n t
  intro b hb a ha
  filter_upwards [hQ b hb, hQ a ha] with omega hb' ha'
  simp only [complexDoleansDadeExponential, hb', ha']

/-- The higher-order residual has the same deterministic-time version
invariance. No random-time substitution is involved. -/
theorem complexDoleansHigherOrderResidualApprox_congr_bracket_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (X Q Q' : ℝ≥0 → W → ℂ) (U : ℝ≥0)
    (hQ : ∀ s, s ≤ U → Q s =ᵐ[P] Q' s) (n : ℕ) (t : ℝ≥0) :
    complexDoleansHigherOrderResidualApprox X Q U n t =ᵐ[P]
      complexDoleansHigherOrderResidualApprox X Q' U n t := by
  apply uniformStoppedCellSum_congr_ae
    (fun b a omega ↦ complexDoleansDadeExponential X Q a omega *
      complexDoleansSecondOrderResidual (X b omega - X a omega)
        (Q b omega - Q a omega))
    (fun b a omega ↦ complexDoleansDadeExponential X Q' a omega *
      complexDoleansSecondOrderResidual (X b omega - X a omega)
        (Q' b omega - Q' a omega)) U ?_ n t
  intro b hb a ha
  filter_upwards [hQ b hb, hQ a ha] with omega hb' ha'
  simp only [complexDoleansDadeExponential, hb', ha']

/-- Regularizing the drift at an earlier horizon gives the same version at
every time before that horizon. The zero-bracket event is handled using the
input cross-variation identity. -/
theorem GirsanovDensityData.regularizedGirsanovIntegratedDrift_mono_time_ae_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U t : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P) (hUT : U ≤ T) (htU : t ≤ U) :
    regularizedGirsanovIntegratedDrift bracket theta U t =ᵐ[P]
      regularizedGirsanovIntegratedDrift bracket theta T t := by
  filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae hcross hB t,
    hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t]
    with omega hzero hreg
  rw [hreg]
  unfold regularizedGirsanovIntegratedDrift
  by_cases hUzero : bracket U omega = 0
  · rw [ite_eq_left hUzero]
    have hnonneg : 0 ≤ bracket t omega := by
      rw [← hdata.bracket_zero omega]
      exact (hdata.continuous_monotone_bracket omega).2 bot_le
    have hle : bracket t omega ≤ bracket U omega :=
      (hdata.continuous_monotone_bracket omega).2 htU
    have htz : bracket t omega = 0 := by rw [hUzero] at hle; exact le_antisymm hle hnonneg
    have hdrift := hzero htz
    linarith
  · rw [ite_eq_right hUzero]
    unfold girsanovIntegratedDrift
    rw [min_eq_left htU, min_eq_left (htU.trans hUT)]

/-- Full Girsanov weighted-bracket cancellation at both rational observation
times follows from the original predictable-drift hypotheses. -/
theorem GirsanovDensityData.exists_rational_pair_girsanovWeightedBracketResidual
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
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
    (c : ℝ) (hUT : U ≤ T) (hU : 0 < U)
    {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    let C : ℝ≥0 → W → ℝ := fun t omega ↦
      -regularizedGirsanovIntegratedDrift bracket theta T t omega
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U (q r + 1) (U * (j : ℝ≥0) / (k : ℝ≥0))) atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U (q r + 1) U) atTop (fun _ ↦ 0) := by
  apply hdata.exists_rational_pair_complexWeightedBracketResidual hB hsm
    (fun t ↦ (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta t).neg)
    (fun omega ↦ (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg)
    (hdata.hasCrossVariationProcessInProbability_neg_regularizedDrift hcross hB)
    ?_ c hUT hU hk hj hjk
  intro S hST N hN
  exact eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_of_le
    (P := P) htheta hbracketTerminal hST N hN

/-- Both parts of the exact stochastic Taylor identity respect the same
deterministic-time bracket modifications. -/
theorem complexDoleansEulerResidualApprox_congr_bracket_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (X Q Q' : ℝ≥0 → W → ℂ) (U : ℝ≥0)
    (hQ : ∀ s, s ≤ U → Q s =ᵐ[P] Q' s) (n : ℕ) (t : ℝ≥0) :
    complexDoleansEulerResidualApprox X Q U n t =ᵐ[P]
      complexDoleansEulerResidualApprox X Q' U n t := by
  by_cases hn : n = 0
  · subst n
    exact Filter.EventuallyEq.rfl
  have hnadd : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  filter_upwards
    [complexDoleansWeightedBracketResidualApprox_congr_bracket_ae X Q Q' U hQ n t,
      complexDoleansHigherOrderResidualApprox_congr_bracket_ae X Q Q' U hQ n t]
    with omega hW hH
  have hQsplit := complexDoleansEulerResidualApprox_eq_secondOrder X Q U (n - 1) t omega
  have hQsplit' := complexDoleansEulerResidualApprox_eq_secondOrder X Q' U (n - 1) t omega
  rw [hnadd] at hQsplit hQsplit'
  rw [hQsplit, hQsplit', hW, hH]

/-- The all-time higher-order estimate may use an earlier grid horizon
while retaining the drift representative from the original Novikov horizon. -/
theorem GirsanovDensityData.girsanovComplexDoleansHigherOrderCondition_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketU : ∀ omega, bracket U omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) U, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (hUT : U ≤ T) :
    GirsanovComplexDoleansHigherOrderCondition P M bracket B
      (fun t omega ↦ -regularizedGirsanovIntegratedDrift bracket theta T t omega) U := by
  have hbase := girsanovComplexDoleansHigherOrderCondition_of_bound
    ((hdata.mono_time hUT).girsanovComplexDoleansHigherOrderBoundCondition
      hB hsm htheta hbracketU)
  intro c t
  apply (hbase c t).congr_left
  intro n
  apply complexDoleansHigherOrderResidualApprox_congr_bracket_ae
  intro s hs
  filter_upwards
    [hdata.regularizedGirsanovIntegratedDrift_mono_time_ae_eq hcross hB hUT hs]
    with omega homega
  simp only [complexMartingaleCombinationBracket, homega]

/-- Vanishing bracket and higher-order terms close the exact Euler
residual along any cofinal grid already selected by the bracket proof. -/
theorem complexDoleansEulerResidualApprox_tendsto_of_secondOrder
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Q : ℝ≥0 → W → ℂ} {U t : ℝ≥0} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hW : TendstoInMeasure P (fun r ↦
      complexDoleansWeightedBracketResidualApprox X Q U (q r + 1) t)
      atTop (fun _ ↦ 0))
    (hH : TendstoInMeasure P (fun n ↦
      complexDoleansHigherOrderResidualApprox X Q U (n + 1) t)
      atTop (fun _ ↦ 0)) :
    TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox X Q U (q r + 1) t)
      atTop (fun _ ↦ 0) := by
  have hsum := TendstoInMeasure.add_normed_noMeas
    (TendstoInMeasure.const_mul_complex_noMeas hW (1 / 2 : ℂ)) (hH.comp hq)
  have hsum' : TendstoInMeasure P (fun r omega ↦
      (1 / 2 : ℂ) * complexDoleansWeightedBracketResidualApprox X Q U (q r + 1) t omega +
        complexDoleansHigherOrderResidualApprox X Q U (q r + 1) t omega)
      atTop (fun _ ↦ 0) := by
    simpa only [Function.comp_apply, mul_zero, zero_add] using hsum
  apply hsum'.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦
    (complexDoleansEulerResidualApprox_eq_secondOrder X Q U (q r) t omega).symm

/-- The exact Euler residual pins its limit without any integrability or
sample-path continuity premise. -/
theorem complexDoleansEulerProcess_tendsto_of_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Q : ℝ≥0 → W → ℂ} {U t : ℝ≥0} {q : ℕ → ℕ}
    (hres : TendstoInMeasure P
      (fun r ↦ complexDoleansEulerResidualApprox X Q U (q r + 1) t)
      atTop (fun _ ↦ 0)) :
    TendstoInMeasure P (fun r ↦ complexDoleansEulerProcess X Q U (q r + 1) t)
      atTop (complexDoleansDadeExponential X Q (min t U)) := by
  have hnorm (r : ℕ) (omega : W) :
      ‖complexDoleansEulerProcess X Q U (q r + 1) t omega -
          complexDoleansDadeExponential X Q (min t U) omega‖ =
        ‖complexDoleansEulerResidualApprox X Q U (q r + 1) t omega‖ := by
    rw [norm_sub_rev,
      complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual]
  rw [tendstoInMeasure_iff_norm] at hres ⊢
  intro epsilon hepsilon
  simpa only [hnorm, sub_zero] using hres epsilon hepsilon

/-- The Challenge's full bracket identity supplies complete complex Euler
residual convergence at both rational observation times on one grid. The
bracket in this conclusion uses the literal input drift. -/
theorem GirsanovDensityData.exists_rational_pair_girsanovComplexEulerResidual
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hUT : U ≤ T) (hU : 0 < U)
    {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    let Q := complexMartingaleCombinationBracket bracket
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) c
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c) Q
        U (q r + 1) (U * (j : ℝ≥0) / (k : ℝ≥0))) atTop (fun _ ↦ 0) ∧
      TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c) Q U (q r + 1) U)
        atTop (fun _ ↦ 0) := by
  let Qreg := complexMartingaleCombinationBracket bracket
    (fun t omega ↦ -regularizedGirsanovIntegratedDrift bracket theta T t omega) c
  let Qraw := complexMartingaleCombinationBracket bracket
    (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) c
  have hbrT : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure := by simpa only [min_self] using hbracketTheta T
  have hbrU : ∀ omega, bracket U omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) U, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure := by
    simpa only [min_eq_left hUT] using hbracketTheta U
  obtain ⟨q, hq, hWa, hWU⟩ := hdata.exists_rational_pair_girsanovWeightedBracketResidual
    hB hsm htheta hbrT hcross c hUT hU hk hj hjk
  have hHO := hdata.girsanovComplexDoleansHigherOrderCondition_of_le
    hB hsm htheta hbrU hcross hUT
  have hQ : ∀ s, s ≤ U → Qreg s =ᵐ[P] Qraw s := by
    intro s _hs
    filter_upwards [hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB s]
      with omega homega
    simp only [Qreg, Qraw, complexMartingaleCombinationBracket, homega]
  have close (t : ℝ≥0)
      (hW : TendstoInMeasure P (fun r ↦ complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c) Qreg U (q r + 1) t)
        atTop (fun _ ↦ 0)) :
      TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox
        (complexMartingaleCombination M B c) Qraw U (q r + 1) t)
        atTop (fun _ ↦ 0) := by
    have hres := complexDoleansEulerResidualApprox_tendsto_of_secondOrder hq hW (hHO c t)
    apply hres.congr_left
    intro r
    exact complexDoleansEulerResidualApprox_congr_bracket_ae
      (complexMartingaleCombination M B c) Qreg Qraw U hQ (q r + 1) t
  exact ⟨q, hq, close _ hWa, close _ hWU⟩

/-- The self-integrator two-real-process Euler sum has exactly the limit
pinned by its canonical complex residual. -/
theorem complexGirsanovEulerProcess_self_tendsto_of_residual
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {c : ℝ} {U t : ℝ≥0} {q : ℕ → ℕ}
    (hres : TendstoInMeasure P (fun r ↦ complexDoleansEulerResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) U (q r + 1) t)
      atTop (fun _ ↦ 0)) :
    TendstoInMeasure P (fun r ↦ complexGirsanovEulerProcess
      M M bracket B C c U (q r + 1) t) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) (min t U)) := by
  have h := complexDoleansEulerProcess_tendsto_of_residual hres
  apply h.congr_left
  intro r
  exact Filter.Eventually.of_forall fun omega ↦
    (congrFun (congrFun
      (complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
        M bracket B C c U (q r + 1)) t) omega).symm

/-- The exact uncapped Girsanov Euler sums converge in probability at both
rational observation times of a single cofinal grid. All hypotheses are
provided by the Challenge; no martingale-limit premise is assumed. -/
theorem GirsanovDensityData.exists_rational_pair_girsanovComplexEulerSelf
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) (hUT : U ≤ T) (hU : 0 < U)
    {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    let C : ℝ≥0 → W → ℝ := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
    let E := complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      TendstoInMeasure P (fun r ↦ complexGirsanovEulerProcess
        M M bracket B C c U (q r + 1) (U * (j : ℝ≥0) / (k : ℝ≥0)))
        atTop (E (U * (j : ℝ≥0) / (k : ℝ≥0))) ∧
      TendstoInMeasure P (fun r ↦ complexGirsanovEulerProcess
        M M bracket B C c U (q r + 1) U) atTop (E U) := by
  obtain ⟨q, hq, hsa, hsU⟩ := hdata.exists_rational_pair_girsanovComplexEulerResidual
    hB hsm htheta hbracketTheta hcross c hUT hU hk hj hjk
  have haU : U * (j : ℝ≥0) / (k : ℝ≥0) ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U hk hjk).2
  refine ⟨q, hq, ?_, ?_⟩
  · simpa only [min_eq_left haU] using
      complexGirsanovEulerProcess_self_tendsto_of_residual hsa
  · simpa only [min_self] using
      complexGirsanovEulerProcess_self_tendsto_of_residual hsU

end StochasticCalculus
