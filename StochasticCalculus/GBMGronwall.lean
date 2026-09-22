/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GeometricBrownianMotion

/-! # Integral Grönwall for localized moment profiles -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace StochasticCalculus

/-- A nonnegative integrable function controlled by its own time integral
vanishes pointwise. Continuity of the function is unnecessary: its integral
is the continuous function to which the ordinary Grönwall lemma applies. -/
theorem eq_zero_of_nonneg_le_mul_setIntegral
    {u : ℝ → ℝ} {T K : ℝ} (hu : IntegrableOn u (Icc 0 T))
    (hnonneg : ∀ s, 0 ≤ u s)
    (hbound : ∀ s ∈ Icc 0 T, u s ≤ K * ∫ r in Icc 0 s, u r) :
    ∀ s ∈ Icc 0 T, u s = 0 := by
  classical
  let v : ℝ → ℝ := (Icc 0 T).indicator u
  have hv : Integrable v := (integrable_indicator_iff measurableSet_Icc).2 hu
  let F : ℝ → ℝ := fun s ↦ ∫ r in (0 : ℝ)..s, v r
  have hF : Continuous F := hv.continuous_primitive 0
  have hFeq (s : ℝ) (hs : s ∈ Icc 0 T) : F s = ∫ r in Icc 0 s, u r := by
    rw [show F s = ∫ r in (0 : ℝ)..s, v r by rfl,
      intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact Set.indicator_of_mem (show r ∈ Icc 0 T from ⟨hr.1, hr.2.trans hs.2⟩) u
  have hFnonneg (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ F s := by
    rw [hFeq s hs]
    exact integral_nonneg fun r ↦ hnonneg r
  have hFzero : ∀ s ∈ Icc 0 T, F s = 0 := by
    apply eq_zero_of_abs_le_mul_integral_abs (K := K) hF
    intro s hs
    rw [abs_of_nonneg (hFnonneg s hs)]
    have hineq : F s ≤ K * ∫ r in Icc 0 s, F r := by
      rw [hFeq s hs, ← integral_const_mul]
      apply setIntegral_mono_on
        (hu.mono_set (Icc_subset_Icc_right hs.2))
        ((hF.const_mul K).continuousOn.integrableOn_Icc) measurableSet_Icc
      intro r hr
      have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hs.2⟩
      rw [hFeq r hrT]
      exact hbound r hrT
    have habs : (∫ r in (0 : ℝ)..s, |F r|) = ∫ r in Icc 0 s, F r := by
      rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      exact abs_of_nonneg (hFnonneg r ⟨hr.1, hr.2.trans hs.2⟩)
    rwa [habs]
  intro s hs
  have hh := hbound s hs
  rw [← hFeq s hs, hFzero s hs, mul_zero] at hh
  exact le_antisymm hh (hnonneg s)

end StochasticCalculus
