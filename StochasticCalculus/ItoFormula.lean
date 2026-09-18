/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.QuadraticVariationDensity
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Itô's formula for Brownian motion (L2.1)

`f(B_t) = f(0) + ∫₀ᵗ f'(B_s) dB_s + ½∫₀ᵗ f''(B_s) ds`. Route: Taylor
expand `f(B_{t_{i+1}}) - f(B_{t_i})`, use L1.2 for the second-order term.
See task-spec.md § L2.1.

Routing warning: build this from the partition-sum argument directly —
Mathlib has no "stochastic Taylor" lemma to shortcut through.
-/

open MeasureTheory Set
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {P : Measure W} {B : ℝ≥0 → W → ℝ}

namespace StochasticCalculus

/-- The remainder after subtracting the explicit second-order Taylor polynomial. -/
noncomputable def itoTaylorRemainder (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  f x - (f x₀ + deriv f x₀ * (x - x₀) +
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x - x₀) ^ 2)

/-- The deterministic second-order Taylor remainder used in the partition proof is
little-o of the squared increment. -/
private theorem itoTaylor_isLittleO {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x₀ : ℝ) :
    itoTaylorRemainder f x₀ =o[𝓝 x₀] fun x ↦ (x - x₀) ^ 2 := by
  change (fun x ↦ f x - (f x₀ + deriv f x₀ * (x - x₀) +
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x - x₀) ^ 2)) =o[𝓝 x₀]
      fun x ↦ (x - x₀) ^ 2
  have hTaylor := taylor_isLittleO_univ (f := f) (x₀ := x₀) (n := 2) hf
  convert hTaylor using 1 with x
  all_goals try rfl
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, CharP.cast_eq_zero,
    zero_add, Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, pow_one, one_mul,
    iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul,
    Nat.factorial_one, Nat.reduceAdd, one_div]
  funext y
  ring

/-- The second iterated derivative is the ordinary second derivative. -/
private lemma iteratedDeriv_two (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
    show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]

/-- The remainder after subtracting the first-order Taylor polynomial. -/
private noncomputable def itoFirstTaylorRemainder
    (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  f x - (f x₀ + deriv f x₀ * (x - x₀))

/-- On a compact interval, the first-order Taylor remainder of a `C¹`
function is uniformly small compared with the increment. -/
private theorem uniform_itoFirstTaylorRemainder_bound_on_Icc
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, |x - x₀| < δ →
        |itoFirstTaylorRemainder f x₀ x| ≤ ε * |x - x₀| := by
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have huc : UniformContinuousOn (deriv f) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hfirst.continuousOn
  intro ε hε
  rcases Metric.uniformContinuousOn_iff.mp huc ε hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hxx₀
  rcases eq_or_ne x₀ x with rfl | hne
  · simp only [itoFirstTaylorRemainder, sub_self, mul_zero, add_zero, abs_zero,
      le_refl]
  obtain ⟨y, hy, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 0) hne
      (hf.contDiffOn (s := uIcc x₀ x))
  have hyab : y ∈ Icc a b := by
    rcases hx₀ with ⟨hax₀, hx₀b⟩
    rcases hx with ⟨hax, hxb⟩
    grind [uIoo, uIcc]
  have hydist : dist y x₀ < δ := by
    calc
      dist y x₀ = dist x₀ y := dist_comm _ _
      _ ≤ dist x₀ x := Real.dist_left_le_of_mem_uIcc (uIoo_subset_uIcc_self hy)
      _ = |x - x₀| := by rw [Real.dist_eq, abs_sub_comm]
      _ < δ := hxx₀
  have hmod' := hmod y hyab x₀ hx₀ hydist
  rw [Real.dist_eq] at hmod'
  have hTaylor' : f x - f x₀ = deriv f y * (x - x₀) := by
    rw [taylor_within_zero_eval] at hTaylor
    norm_num [show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]] at hTaylor ⊢
    exact hTaylor
  rw [itoFirstTaylorRemainder, show
    f x - (f x₀ + deriv f x₀ * (x - x₀)) =
      (f x - f x₀) - deriv f x₀ * (x - x₀) by ring, hTaylor']
  rw [show deriv f y * (x - x₀) - deriv f x₀ * (x - x₀) =
    (deriv f y - deriv f x₀) * (x - x₀) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hmod'.le (abs_nonneg _)

/-- On a fixed compact interval, the second-order Taylor remainder is uniformly
small compared with the squared increment. -/
private theorem uniform_itoTaylorRemainder_bound_on_Icc
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, |x - x₀| < δ →
        |itoTaylorRemainder f x₀ x| ≤ ε * (x - x₀) ^ 2 := by
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have huc : UniformContinuousOn (deriv (deriv f)) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hsecond.continuousOn
  intro ε hε
  rcases Metric.uniformContinuousOn_iff.mp huc (2 * ε) (mul_pos (by norm_num) hε) with
    ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hxx₀
  rcases eq_or_ne x₀ x with rfl | hne
  · simp only [itoTaylorRemainder, sub_self, mul_zero, add_zero, pow_succ,
      abs_zero, le_refl]
  obtain ⟨y, hy, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne
      (hf.contDiffOn (s := uIcc x₀ x))
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc hne
  have hx₀u : x₀ ∈ uIcc x₀ x := left_mem_uIcc
  have hfirst : iteratedDerivWithin 1 f (uIcc x₀ x) x₀ = deriv f x₀ := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
      (hf.contDiffAt.of_le (by norm_num)) hx₀u]
    rw [show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
  have hyab : y ∈ Icc a b := by
    rcases hx₀ with ⟨hax₀, hx₀b⟩
    rcases hx with ⟨hax, hxb⟩
    grind [uIoo, uIcc]
  have hydist : dist y x₀ < δ := by
    calc
      dist y x₀ = dist x₀ y := dist_comm _ _
      _ ≤ dist x₀ x := Real.dist_left_le_of_mem_uIcc (uIoo_subset_uIcc_self hy)
      _ = |x - x₀| := by rw [Real.dist_eq, abs_sub_comm]
      _ < δ := hxx₀
  have hmod' := hmod y hyab x₀ hx₀ hydist
  rw [Real.dist_eq] at hmod'
  have hTaylor' :
      f x - (f x₀ + deriv f x₀ * (x - x₀)) =
        deriv (deriv f) y * (x - x₀) ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, hfirst] at hTaylor
    rw [iteratedDeriv_two] at hTaylor
    norm_num at hTaylor ⊢
    simpa [smul_eq_mul, mul_comm] using hTaylor
  rw [itoTaylorRemainder, show
    f x - (f x₀ + deriv f x₀ * (x - x₀) +
      (1 / 2) * deriv (deriv f) x₀ * (x - x₀) ^ 2) =
      (f x - (f x₀ + deriv f x₀ * (x - x₀))) -
        (1 / 2) * deriv (deriv f) x₀ * (x - x₀) ^ 2 by ring,
    hTaylor']
  calc
    |deriv (deriv f) y * (x - x₀) ^ 2 / 2 -
        (1 / 2) * deriv (deriv f) x₀ * (x - x₀) ^ 2| =
        (1 / 2) * |deriv (deriv f) y - deriv (deriv f) x₀| *
          (x - x₀) ^ 2 := by
      rw [show deriv (deriv f) y * (x - x₀) ^ 2 / 2 -
          (1 / 2) * deriv (deriv f) x₀ * (x - x₀) ^ 2 =
          (1 / 2) * (deriv (deriv f) y - deriv (deriv f) x₀) *
            (x - x₀) ^ 2 by ring]
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (sq_nonneg (x - x₀))]
    _ ≤ (1 / 2) * (2 * ε) * (x - x₀) ^ 2 := by
      gcongr
    _ = ε * (x - x₀) ^ 2 := by ring

/-- Abstract endpoint for the Taylor-remainder step: termwise little-o
coefficients times an eventually bounded quadratic sum have vanishing total
remainder. -/
private theorem tendsto_sum_zero_of_remainder_bound
    {N : ℕ → ℕ} {r Δ : ℕ → ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      ∑ i ∈ Finset.range (N n), (Δ n i) ^ 2 ≤ C)
    (hremainder : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.range (N n),
        |r n i| ≤ ε * (Δ n i) ^ 2) :
    Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range (N n), r n i)
      Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  rcases (Filter.eventually_atTop.1 hquadratic) with ⟨nq, hnq⟩
  rcases (Filter.eventually_atTop.1 (hremainder δ hδ)) with ⟨nr, hnr⟩
  refine ⟨max nq nr, fun n hn ↦ ?_⟩
  have hq := hnq n (le_trans (le_max_left _ _) hn)
  have hr := hnr n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero]
  calc
    |∑ i ∈ Finset.range (N n), r n i| ≤
        ∑ i ∈ Finset.range (N n), |r n i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (N n), δ * (Δ n i) ^ 2 := by
      exact Finset.sum_le_sum fun i hi ↦ hr i hi
    _ = δ * ∑ i ∈ Finset.range (N n), (Δ n i) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hq hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [ne_of_gt hC]
    _ < ε := by linarith

/-- Every partition point with index at most the denominator lies in `[0, t]`. -/
private lemma uniformPartitionTime_mem_Icc
    (t : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformPartitionTime t n i ∈ Icc 0 t := by
  constructor
  · exact bot_le
  · unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    calc
      t * (i : ℝ≥0) / (n : ℝ≥0) ≤ t * (n : ℝ≥0) / (n : ℝ≥0) := by
        gcongr
      _ = t := mul_div_cancel_right₀ t hn0

/-- Adjacent uniform partition points are exactly one mesh width apart. -/
private lemma dist_uniformPartitionTime_succ
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    dist (uniformPartitionTime t n (i + 1)) (uniformPartitionTime t n i) =
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  have hle : uniformPartitionTime t n i ≤ uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  rw [NNReal.dist_eq, abs_of_nonneg]
  · simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_natCast]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
    norm_num [Nat.cast_add, Nat.cast_one]
  · exact sub_nonneg.mpr (by exact_mod_cast hle)

/-- A continuous path has uniformly vanishing increments along the project's
uniform partitions. -/
private theorem continuous_uniformPartition_increments
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |g (uniformPartitionTime t (n + 1) (i + 1)) -
          g (uniformPartitionTime t (n + 1) i)| < δ := by
  have huc : UniformContinuousOn g (Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  have hdivNN : Filter.Tendsto
      (fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun n : ℕ ↦ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (𝓝 0) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0))
      Filter.atTop (𝓝 (0 : ℝ))
    simpa only [NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv η hη
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro i hi
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi' : i ≤ n + 1 := le_trans (Nat.le_add_right i 1) hipos
  have hx := uniformPartitionTime_mem_Icc t hnpos hi'
  have hy := uniformPartitionTime_mem_Icc t hnpos hipos
  have hmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < η := by
    have := hN n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] using this
  have hdist :
      dist (uniformPartitionTime t (n + 1) (i + 1))
        (uniformPartitionTime t (n + 1) i) < η := by
    rw [dist_uniformPartitionTime_succ t hnpos i]
    exact hmesh
  have hout := hmod _ hy _ hx hdist
  simpa only [Real.dist_eq] using hout

/-- The left-endpoint sums of the derivative of a `C¹` function along the
uniform partitions converge to its endpoint increment. -/
theorem tendsto_uniformPartition_deriv_mul_increment
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        deriv F (uniformPartitionTime t (n + 1) i : ℝ) *
          ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ)))
      Filter.atTop (nhds (F (t : ℝ) - F 0)) := by
  let C : ℝ := (t : ℝ) + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hremainder : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        itoFirstTaylorRemainder F
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ))
      Filter.atTop (nhds 0) := by
    refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
    let η := ε / (2 * C)
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hC)
    obtain ⟨δ, hδ, hbound⟩ :=
      uniform_itoFirstTaylorRemainder_bound_on_Icc hF 0 (t : ℝ) η hη
    have hdivNN : Filter.Tendsto
        (fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2
        (tendsto_const_div_atTop_nhds_zero_nat t)
    have hdiv : Filter.Tendsto
        (fun n : ℕ ↦ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
        Filter.atTop (𝓝 0) := by
      change Filter.Tendsto
        (NNReal.toReal ∘ fun n : ℕ ↦ t / ((n + 1 : ℕ) : ℝ≥0))
        Filter.atTop (𝓝 (0 : ℝ))
      simpa only [NNReal.coe_zero] using
        (NNReal.continuous_coe.tendsto 0).comp hdivNN
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv δ hδ
    refine ⟨N, fun n hn ↦ ?_⟩
    have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
    have hmesh :
        ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < δ := by
      have := hN n hn
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (NNReal.coe_nonneg _)] using this
    have hsumabs :
        (∑ i ∈ Finset.range (n + 1),
          |(uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ)|) = (t : ℝ) := by
      have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
        rw [uniformPartitionTime]
        exact mul_div_cancel_right₀ t (by exact_mod_cast Nat.succ_ne_zero n)
      have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
        simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      calc
        _ = ∑ i ∈ Finset.range (n + 1),
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_of_nonneg]
          exact sub_nonneg.mpr (by
            exact_mod_cast (show uniformPartitionTime t (n + 1) i ≤
              uniformPartitionTime t (n + 1) (i + 1) by
              unfold uniformPartitionTime
              gcongr
              omega))
        _ = (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) 0 : ℝ) := by
          exact Finset.sum_range_sub
            (fun i ↦ (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1)
        _ = (t : ℝ) := by
          rw [htop, hzero]
          simp only [NNReal.coe_zero, sub_zero]
    rw [Real.dist_eq, sub_zero]
    calc
      |∑ i ∈ Finset.range (n + 1),
          itoFirstTaylorRemainder F
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)| ≤
          ∑ i ∈ Finset.range (n + 1),
            |itoFirstTaylorRemainder F
              (uniformPartitionTime t (n + 1) i : ℝ)
              (uniformPartitionTime t (n + 1) (i + 1) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), η *
          |(uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
        have hi' : i ≤ n + 1 := le_trans (Nat.le_add_right i 1) hipos
        apply hbound
        · exact_mod_cast uniformPartitionTime_mem_Icc t hnpos hi'
        · exact_mod_cast uniformPartitionTime_mem_Icc t hnpos hipos
        · rw [← Real.dist_eq, Real.dist_eq, ← NNReal.dist_eq,
            dist_uniformPartitionTime_succ t hnpos i]
          exact hmesh
      _ = η * (t : ℝ) := by rw [← Finset.mul_sum, hsumabs]
      _ ≤ η * C := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        dsimp only [C]
        linarith
      _ = ε / 2 := by
        dsimp only [η]
        field_simp [ne_of_gt hC]
      _ < ε := by linarith
  have hdecomp (n : ℕ) :
      F (t : ℝ) - F 0 =
        (∑ i ∈ Finset.range (n + 1),
          deriv F (uniformPartitionTime t (n + 1) i : ℝ) *
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) +
        ∑ i ∈ Finset.range (n + 1),
          itoFirstTaylorRemainder F
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
    have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
      rw [uniformPartitionTime]
      exact mul_div_cancel_right₀ t (by exact_mod_cast Nat.succ_ne_zero n)
    have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
    rw [← show (∑ i ∈ Finset.range (n + 1),
        (F (uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
          F (uniformPartitionTime t (n + 1) i : ℝ))) =
        F (t : ℝ) - F 0 by
      calc
        _ = F (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
            F (uniformPartitionTime t (n + 1) 0 : ℝ) := by
          exact Finset.sum_range_sub
            (fun i ↦ F (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1)
        _ = F (t : ℝ) - F 0 := by rw [htop, hzero]; rfl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    unfold itoFirstTaylorRemainder
    ring
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1),
        deriv F (uniformPartitionTime t (n + 1) i : ℝ) *
          ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ))) =
        (F (t : ℝ) - F 0) -
          ∑ i ∈ Finset.range (n + 1),
            itoFirstTaylorRemainder F
              (uniformPartitionTime t (n + 1) i : ℝ)
              (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
    linarith [hdecomp n]
  convert tendsto_const_nhds.sub hremainder using 1
  · funext n
    exact hsum n
  · simp only [sub_zero]

/-- Uniform left-endpoint Riemann sums of a continuous function converge to
its integral on `[0, t]`. -/
theorem tendsto_uniformPartition_leftRiemann
    (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        g (uniformPartitionTime t (n + 1) i : ℝ) *
          ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ)))
      Filter.atTop (nhds (∫ s in Icc (0 : ℝ) (t : ℝ), g s)) := by
  let F : ℝ → ℝ := fun u ↦ ∫ s : ℝ in (0 : ℝ)..u, g s
  have hderiv (x : ℝ) : deriv F x = g x := by
    dsimp only [F]
    exact hg.deriv_integral g 0 x
  have hdiff : Differentiable ℝ F := by
    intro x
    exact (hg.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  have hF : ContDiff ℝ 1 F := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hdiff, ?_⟩
    convert hg using 1
    funext x
    exact hderiv x
  have h := tendsto_uniformPartition_deriv_mul_increment hF t
  convert h using 1
  · funext n
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hderiv]
  · dsimp only [F]
    rw [intervalIntegral.integral_same, sub_zero,
      intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
      ← integral_Icc_eq_integral_Ioc]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Along a continuous path, the left-endpoint time sums of the second
derivative converge to the deterministic integral appearing in Itô's
formula. -/
private theorem tendsto_uniformPartition_secondDeriv_timeSum
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) (hcontinuous : Continuous (fun s ↦ B s omega)) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        deriv (deriv f) (B (uniformPartitionTime t (n + 1) i) omega) *
          ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ)))
      Filter.atTop
        (nhds (∫ s in Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega))) := by
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have hg : Continuous
      (fun s : ℝ ↦ deriv (deriv f) (B s.toNNReal omega)) :=
    hsecond.comp (hcontinuous.comp continuous_real_toNNReal)
  simpa only [Real.toNNReal_coe] using
    tendsto_uniformPartition_leftRiemann
      (fun s : ℝ ↦ deriv (deriv f) (B s.toNNReal omega)) hg t

/-- A continuous real-valued path on a finite time interval has its range in
a compact real interval. -/
private theorem continuous_nnreal_range_subset_Icc
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ∃ a b : ℝ, ∀ s ∈ Icc (0 : ℝ≥0) t, g s ∈ Icc a b := by
  let K : Set ℝ := g '' Icc (0 : ℝ≥0) t
  have hK : IsCompact K := isCompact_Icc.image hg
  refine ⟨sInf K, sSup K, ?_⟩
  intro s hs
  have hgs : g s ∈ K := ⟨s, hs, rfl⟩
  exact ⟨csInf_le hK.bddBelow hgs, le_csSup hK.bddAbove hgs⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Function increments telescope along the uniform partition fixed by L1.2. -/
private theorem sum_uniformPartition_increments
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    ∑ i ∈ Finset.range (n + 1),
      (f (B (uniformPartitionTime t (n + 1) (i + 1)) ω) -
        f (B (uniformPartitionTime t (n + 1) i) ω)) =
      f (B t ω) - f (B 0 ω) := by
  have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  calc
    _ = f (B (uniformPartitionTime t (n + 1) (n + 1)) ω) -
        f (B (uniformPartitionTime t (n + 1) 0) ω) := by
      exact Finset.sum_range_sub
        (fun i => f (B (uniformPartitionTime t (n + 1) i) ω)) (n + 1)
    _ = f (B t ω) - f (B 0 ω) := by rw [htop, hzero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Exact second-order Taylor decomposition of the telescoping partition sum. -/
private theorem uniformPartition_taylor_decomposition
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    f (B t ω) - f (B 0 ω) =
      (∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) ω) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω -
            B (uniformPartitionTime t (n + 1) i) ω)) +
      (∑ i ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) * deriv (deriv f) (B (uniformPartitionTime t (n + 1) i) ω) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω -
            B (uniformPartitionTime t (n + 1) i) ω) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω) := by
  rw [← sum_uniformPartition_increments f B t n ω]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold itoTaylorRemainder
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The second-order Taylor sum splits exactly into a centered weighted
quadratic term and the left-endpoint time sum. -/
private theorem uniformPartition_secondOrder_decomposition
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range (n + 1),
      (1 / 2 : ℝ) * deriv (deriv f)
        (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega) ^ 2) =
      (1 / 2 : ℝ) * (∑ i ∈ Finset.range (n + 1),
        deriv (deriv f) (B (uniformPartitionTime t (n + 1) i) omega) *
          ((B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega) ^ 2 -
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ)))) +
      (1 / 2 : ℝ) * (∑ i ∈ Finset.range (n + 1),
        deriv (deriv f) (B (uniformPartitionTime t (n + 1) i) omega) *
          ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (n + 1) i : ℝ))) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

section CenteredWeightedQuadraticVariation

variable {Omega I E : Type*} [MeasurableSpace Omega]

private noncomputable def partitionIncrement
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) (omega : W) : ℝ :=
  B (uniformPartitionTime t n (i + 1)) omega -
    B (uniformPartitionTime t n i) omega

private noncomputable def incrementPrefix
    (Δ : ℕ → W → ℝ) (i : ℕ) (omega : W) : ℝ :=
  ∑ k : ↥(Finset.range i), Δ k omega

private noncomputable def centeredWeightedPartitionIncrement
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ)
    (g : ℝ → ℝ) (i : ℕ) (omega : W) : ℝ :=
  g (incrementPrefix (partitionIncrement B t n) i omega) *
    (partitionIncrement B t n i omega ^ 2 -
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ))

private noncomputable def centeredWeightedQuadraticVariationApprox
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ)
    (g : ℝ → ℝ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    g (B (uniformPartitionTime t n i) omega) *
      (partitionIncrement B t n i omega ^ 2 -
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)))

private lemma uniformPartitionTime_succ_nndist_for_weightedSum
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    nndist ((uniformPartitionTime t n (i + 1) : ℝ))
      ((uniformPartitionTime t n i : ℝ)) = t / (n : ℝ≥0) := by
  have hle : uniformPartitionTime t n i ≤ uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  rw [show nndist ((uniformPartitionTime t n (i + 1) : ℝ))
      ((uniformPartitionTime t n i : ℝ)) =
      uniformPartitionTime t n (i + 1) - uniformPartitionTime t n i by
        apply NNReal.eq
        rw [← dist_nndist, Real.dist_eq, abs_of_nonneg, NNReal.coe_sub hle]
        exact sub_nonneg.mpr (by exact_mod_cast hle)]
  apply NNReal.eq
  rw [NNReal.coe_sub hle]
  simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnR]
  norm_num [Nat.cast_add, Nat.cast_one]

private lemma uniformPartitionTime_succ_real_sub_for_weightedSum
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (uniformPartitionTime t n (i + 1) : ℝ) -
      (uniformPartitionTime t n i : ℝ) =
        ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnR]
  norm_num [Nat.cast_add, Nat.cast_one]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
private lemma incrementPrefix_partitionIncrement_eq
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) (omega : W) :
    incrementPrefix (partitionIncrement B t n) i omega =
      B (uniformPartitionTime t n i) omega -
        B (uniformPartitionTime t n 0) omega := by
  unfold incrementPrefix partitionIncrement
  calc
    (∑ k : ↥(Finset.range i),
      (B (uniformPartitionTime t n (k + 1)) omega -
        B (uniformPartitionTime t n k) omega)) =
        ∑ k ∈ Finset.range i,
          (B (uniformPartitionTime t n (k + 1)) omega -
            B (uniformPartitionTime t n k) omega) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach (Finset.range i)
        (fun k ↦ B (uniformPartitionTime t n (k + 1)) omega -
          B (uniformPartitionTime t n k) omega)
    _ = B (uniformPartitionTime t n i) omega -
        B (uniformPartitionTime t n 0) omega :=
      Finset.sum_range_sub (fun k ↦ B (uniformPartitionTime t n k) omega) i

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem centeredWeightedQuadraticVariationApprox_ae_eq_prefix
    (hB : IsBrownianMotion B P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (g : ℝ → ℝ) :
    centeredWeightedQuadraticVariationApprox B t n g =ᵐ[P]
      fun omega ↦ ∑ i ∈ Finset.range n,
        centeredWeightedPartitionIncrement B t n g i omega := by
  let hpre := hB.toIsPreBrownianReal
  filter_upwards [hpre.eval_zero_ae_eq_zero] with omega hzero
  unfold centeredWeightedQuadraticVariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  unfold centeredWeightedPartitionIncrement
  rw [incrementPrefix_partitionIncrement_eq]
  have htimeZero : uniformPartitionTime t n 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  rw [htimeZero, hzero, sub_zero,
    uniformPartitionTime_succ_real_sub_for_weightedSum t hn i]

/-- Pythagoras for a finite family of pairwise orthogonal vectors in a real
inner-product space. -/
private theorem norm_finsetSum_sq_of_pairwise_inner_eq_zero
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset I) (Z : I → E)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → @inner ℝ E _ (Z i) (Z j) = 0) :
    ‖∑ i ∈ s, Z i‖ ^ 2 = ∑ i ∈ s, ‖Z i‖ ^ 2 := by
  classical
  calc
    ‖∑ i ∈ s, Z i‖ ^ 2 =
        @inner ℝ E _ (∑ i ∈ s, Z i) (∑ j ∈ s, Z j) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i ∈ s, ∑ j ∈ s, @inner ℝ E _ (Z i) (Z j) := by
      simp only [sum_inner, inner_sum]
      exact Finset.sum_comm
    _ = ∑ i ∈ s, ‖Z i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · exact real_inner_self_eq_norm_sq (Z i)
      · intro j hj hji
        exact horth i hi j hj hji.symm
      · exact fun hni ↦ (hni hi).elim

/-- For a square-integrable real function, the second moment is the square
of the real-valued `L²` seminorm. -/
private theorem integral_sq_eq_eLpNorm_toReal_sq
    {P : Measure Omega} {f : Omega → ℝ} (hf : MemLp f 2 P) :
    (∫ omega, f omega ^ 2 ∂P) = (eLpNorm f 2 P).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hnonneg : 0 ≤ ∫ omega, f omega ^ 2 ∂P := by
    exact integral_nonneg (fun omega ↦ sq_nonneg (f omega))
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt hnonneg]

/-- The squared `L²` norm of a finite pairwise-orthogonal family is the sum
of the individual squared norms. -/
private theorem eLpNorm_finsetSum_toReal_sq
    {P : Measure Omega} (s : Finset I) (Y : I → Omega → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ omega, Y i omega * Y j omega ∂P = 0) :
    (eLpNorm (fun omega ↦ ∑ i ∈ s, Y i omega) 2 P).toReal ^ 2 =
      ∑ i ∈ s, (eLpNorm (Y i) 2 P).toReal ^ 2 := by
  classical
  let Z : I → Lp ℝ 2 P := fun i ↦ (hY i).toLp (Y i)
  have hZorth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      @inner ℝ (Lp ℝ 2 P) _ (Z i) (Z j) = 0 := by
    intro i hi j hj hij
    rw [L2.inner_def]
    have hcoe_i := (hY i).coeFn_toLp
    have hcoe_j := (hY j).coeFn_toLp
    calc
      (∫ omega, @inner ℝ ℝ _ (Z i omega) (Z j omega) ∂P) =
          ∫ omega, Y i omega * Y j omega ∂P := by
        apply integral_congr_ae
        filter_upwards [hcoe_i, hcoe_j] with omega hi' hj'
        dsimp only [Z]
        rw [hi', hj']
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = 0 := horth i hi j hj hij
  have hsumMem : MemLp (fun omega ↦ ∑ i ∈ s, Y i omega) 2 P :=
    memLp_finsetSum s (fun i _hi ↦ hY i)
  have htoLp : hsumMem.toLp (fun omega ↦ ∑ i ∈ s, Y i omega) =
      ∑ i ∈ s, Z i := by
    apply Lp.ext
    have hcoe_each : ∀ᵐ omega ∂P, ∀ i ∈ s, Z i omega = Y i omega := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact (hY i).coeFn_toLp
    filter_upwards [hsumMem.coeFn_toLp, Lp.coeFn_fun_finsetSum s Z,
      hcoe_each] with omega hsum hfin heach
    rw [hsum, hfin]
    exact Finset.sum_congr rfl fun i hi ↦ (heach i hi).symm
  calc
    (eLpNorm (fun omega ↦ ∑ i ∈ s, Y i omega) 2 P).toReal ^ 2 =
        ‖hsumMem.toLp (fun omega ↦ ∑ i ∈ s, Y i omega)‖ ^ 2 := by
      rw [Lp.norm_toLp]
    _ = ‖∑ i ∈ s, Z i‖ ^ 2 := by rw [htoLp]
    _ = ∑ i ∈ s, ‖Z i‖ ^ 2 :=
      norm_finsetSum_sq_of_pairwise_inner_eq_zero s Z hZorth
    _ = ∑ i ∈ s, (eLpNorm (Y i) 2 P).toReal ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Lp.norm_toLp]

/-- An earlier-prefix weight times the next centered independent increment
has mean zero. -/
private theorem integral_prefixWeightedIncrement_eq_zero
    {P : Measure Omega} (Δ : ℕ → Omega → ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) (hInd : iIndepFun Δ P)
    (hΔmeas : ∀ k, AEMeasurable (Δ k) P)
    (hmean : ∀ k, (∫ omega, Δ k omega ∂P) = 0) (i : ℕ) :
    (∫ omega, g (incrementPrefix Δ i omega) * Δ i omega ∂P) = 0 := by
  have hindPrefix : IndepFun
      (fun omega ↦ ∑ k ∈ Finset.range i, Δ k omega) (Δ i) P := by
    have hraw := hInd.indepFun_sum_range_succ₀ hΔmeas i
    convert hraw using 1
    funext omega
    simp only [Finset.sum_apply]
  have hind : IndepFun
      (fun omega ↦ g (incrementPrefix Δ i omega)) (Δ i) P := by
    have hcomp := hindPrefix.comp hg measurable_id
    convert hcomp using 1
    · funext omega
      simp only [Function.comp_apply, incrementPrefix,
        Finset.univ_eq_attach]
      exact congrArg g
        (Finset.sum_attach (Finset.range i) (fun k ↦ Δ k omega))
    · funext omega
      rfl
  have hprefix : AEStronglyMeasurable
      (fun omega ↦ g (incrementPrefix Δ i omega)) P := by
    have hs := Finset.aestronglyMeasurable_sum
      (Finset.univ : Finset ↥(Finset.range i))
      (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
    have hp : AEStronglyMeasurable
        (fun omega ↦ incrementPrefix Δ i omega) P := by
      convert hs using 1
      funext omega
      simp only [Finset.sum_apply, incrementPrefix]
    exact (hg.comp_aemeasurable hp.aemeasurable).aestronglyMeasurable
  calc
    (∫ omega, g (incrementPrefix Δ i omega) * Δ i omega ∂P) =
        (∫ omega, g (incrementPrefix Δ i omega) ∂P) *
          (∫ omega, Δ i omega ∂P) :=
      hind.integral_fun_mul_eq_mul_integral hprefix
        (hΔmeas i).aestronglyMeasurable
    _ = 0 := by rw [hmean i, mul_zero]

/-- Earlier-prefix weights times centered increments are pairwise
`L²`-orthogonal. -/
private theorem integral_prefixWeightedIncrement_mul_eq_zero_of_lt
    {P : Measure Omega} (Δ : ℕ → Omega → ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) (hInd : iIndepFun Δ P)
    (hΔmeas : ∀ k, AEMeasurable (Δ k) P)
    (hmean : ∀ k, (∫ omega, Δ k omega ∂P) = 0)
    {i j : ℕ} (hij : i < j) :
    (∫ omega,
      (g (incrementPrefix Δ i omega) * Δ i omega) *
        (g (incrementPrefix Δ j omega) * Δ j omega) ∂P) = 0 := by
  classical
  let lift : ↥(Finset.range i) → ↥(Finset.range j) := fun k ↦
    ⟨k, Finset.mem_range.mpr
      (lt_trans (Finset.mem_range.mp k.property) hij)⟩
  let ii : ↥(Finset.range j) := ⟨i, Finset.mem_range.mpr hij⟩
  let jj : ↥({j} : Finset ℕ) := ⟨j, by
    simp only [Finset.mem_singleton]⟩
  let φ : (↥(Finset.range j) → ℝ) → ℝ := fun x ↦
    g (∑ k : ↥(Finset.range i), x (lift k)) * x ii *
      g (∑ k : ↥(Finset.range j), x k)
  let ψ : (↥({j} : Finset ℕ) → ℝ) → ℝ := fun x ↦ x jj
  have hpast : IndepFun
      (fun omega (k : ↥(Finset.range j)) ↦ Δ k omega)
      (fun omega (k : ↥({j} : Finset ℕ)) ↦ Δ k omega) P :=
    iIndepFun.indepFun_finset₀ (Finset.range j) {j} (by
      simp only [Finset.disjoint_singleton_right, Finset.mem_range]
      omega) hInd hΔmeas
  have hφ : Measurable φ := by
    dsimp only [φ]
    fun_prop
  have hψ : Measurable ψ := by
    dsimp only [ψ]
    fun_prop
  have hindComp := hpast.comp hφ hψ
  have hind : IndepFun
      (fun omega ↦
        g (∑ k : ↥(Finset.range i), Δ k omega) * Δ i omega *
          g (∑ k : ↥(Finset.range j), Δ k omega))
      (fun omega ↦ Δ j omega) P := by
    convert hindComp using 1 <;>
      funext omega <;>
      simp only [Function.comp_apply, φ, ψ, lift, ii, jj]
  have hleft : AEStronglyMeasurable
      (fun omega ↦
        g (∑ k : ↥(Finset.range i), Δ k omega) * Δ i omega *
          g (∑ k : ↥(Finset.range j), Δ k omega)) P := by
    have hsum_i : AEStronglyMeasurable
        (fun omega ↦ ∑ k : ↥(Finset.range i), Δ k omega) P := by
      have hs := Finset.aestronglyMeasurable_sum
        (Finset.univ : Finset ↥(Finset.range i))
        (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
      convert hs using 1
      funext omega
      simp only [Finset.sum_apply]
    have hsum_j : AEStronglyMeasurable
        (fun omega ↦ ∑ k : ↥(Finset.range j), Δ k omega) P := by
      have hs := Finset.aestronglyMeasurable_sum
        (Finset.univ : Finset ↥(Finset.range j))
        (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
      convert hs using 1
      funext omega
      simp only [Finset.sum_apply]
    exact (((hg.comp_aemeasurable hsum_i.aemeasurable).aestronglyMeasurable.mul
      (hΔmeas i).aestronglyMeasurable).mul
      (hg.comp_aemeasurable hsum_j.aemeasurable).aestronglyMeasurable)
  have hright : AEStronglyMeasurable (Δ j) P :=
    (hΔmeas j).aestronglyMeasurable
  calc
    (∫ omega,
      (g (incrementPrefix Δ i omega) * Δ i omega) *
        (g (incrementPrefix Δ j omega) * Δ j omega) ∂P) =
        (∫ omega,
          (g (∑ k : ↥(Finset.range i), Δ k omega) * Δ i omega *
            g (∑ k : ↥(Finset.range j), Δ k omega)) *
              Δ j omega ∂P) := by
      apply integral_congr_ae
      filter_upwards with omega
      simp only [incrementPrefix]
      ring
    _ = (∫ omega,
          g (∑ k : ↥(Finset.range i), Δ k omega) * Δ i omega *
            g (∑ k : ↥(Finset.range j), Δ k omega) ∂P) *
        (∫ omega, Δ j omega ∂P) :=
      hind.integral_fun_mul_eq_mul_integral hleft hright
    _ = 0 := by rw [hmean j, mul_zero]

/-- Earlier-prefix weights times centered squares are pairwise orthogonal. -/
private theorem integral_prefixWeightedCentered_mul_eq_zero_of_lt
    {P : Measure Omega} (Δ : ℕ → Omega → ℝ) (v : ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) (hInd : iIndepFun Δ P)
    (hΔmeas : ∀ k, AEMeasurable (Δ k) P)
    (hmean : ∀ k, (∫ omega, Δ k omega ^ 2 - v ∂P) = 0)
    {i j : ℕ} (hij : i < j) :
    (∫ omega,
      (g (∑ k : ↥(Finset.range i), Δ k omega) *
          (Δ i omega ^ 2 - v)) *
        (g (∑ k : ↥(Finset.range j), Δ k omega) *
          (Δ j omega ^ 2 - v)) ∂P) = 0 := by
  classical
  let lift : ↥(Finset.range i) → ↥(Finset.range j) := fun k ↦
    ⟨k, Finset.mem_range.mpr
      (lt_trans (Finset.mem_range.mp k.property) hij)⟩
  let ii : ↥(Finset.range j) := ⟨i, Finset.mem_range.mpr hij⟩
  let jj : ↥({j} : Finset ℕ) := ⟨j, by
    simp only [Finset.mem_singleton]⟩
  let φ : (↥(Finset.range j) → ℝ) → ℝ := fun x ↦
    g (∑ k : ↥(Finset.range i), x (lift k)) *
      (x ii ^ 2 - v) * g (∑ k : ↥(Finset.range j), x k)
  let ψ : (↥({j} : Finset ℕ) → ℝ) → ℝ := fun x ↦ x jj ^ 2 - v
  have hpast : IndepFun
      (fun omega (k : ↥(Finset.range j)) ↦ Δ k omega)
      (fun omega (k : ↥({j} : Finset ℕ)) ↦ Δ k omega) P :=
    iIndepFun.indepFun_finset₀ (Finset.range j) {j} (by
      simp only [Finset.disjoint_singleton_right, Finset.mem_range]
      omega) hInd hΔmeas
  have hφ : Measurable φ := by
    dsimp only [φ]
    fun_prop
  have hψ : Measurable ψ := by
    dsimp only [ψ]
    fun_prop
  have hindComp := hpast.comp hφ hψ
  have hind : IndepFun
      (fun omega ↦
        g (∑ k : ↥(Finset.range i), Δ k omega) *
          (Δ i omega ^ 2 - v) *
          g (∑ k : ↥(Finset.range j), Δ k omega))
      (fun omega ↦ Δ j omega ^ 2 - v) P := by
    convert hindComp using 1 <;>
      funext omega <;>
      simp only [Function.comp_apply, φ, ψ, lift, ii, jj]
  have hleft : AEStronglyMeasurable
      (fun omega ↦
        g (∑ k : ↥(Finset.range i), Δ k omega) *
          (Δ i omega ^ 2 - v) *
          g (∑ k : ↥(Finset.range j), Δ k omega)) P := by
    have hsum_i : AEStronglyMeasurable
        (fun omega ↦ ∑ k : ↥(Finset.range i), Δ k omega) P := by
      have hs := Finset.aestronglyMeasurable_sum
        (Finset.univ : Finset ↥(Finset.range i))
        (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
      convert hs using 1
      funext omega
      simp only [Finset.sum_apply]
    have hsum_j : AEStronglyMeasurable
        (fun omega ↦ ∑ k : ↥(Finset.range j), Δ k omega) P := by
      have hs := Finset.aestronglyMeasurable_sum
        (Finset.univ : Finset ↥(Finset.range j))
        (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
      convert hs using 1
      funext omega
      simp only [Finset.sum_apply]
    exact (((hg.comp_aemeasurable hsum_i.aemeasurable).aestronglyMeasurable.mul
      (((hΔmeas i).pow_const 2).sub aemeasurable_const).aestronglyMeasurable).mul
      (hg.comp_aemeasurable hsum_j.aemeasurable).aestronglyMeasurable)
  have hright : AEStronglyMeasurable
      (fun omega ↦ Δ j omega ^ 2 - v) P :=
    (((hΔmeas j).pow_const 2).sub aemeasurable_const).aestronglyMeasurable
  calc
    (∫ omega,
      (g (∑ k : ↥(Finset.range i), Δ k omega) *
          (Δ i omega ^ 2 - v)) *
        (g (∑ k : ↥(Finset.range j), Δ k omega) *
          (Δ j omega ^ 2 - v)) ∂P) =
        (∫ omega,
          (g (∑ k : ↥(Finset.range i), Δ k omega) *
              (Δ i omega ^ 2 - v) *
              g (∑ k : ↥(Finset.range j), Δ k omega)) *
            (Δ j omega ^ 2 - v) ∂P) := by
      apply integral_congr_ae
      filter_upwards with omega
      ring
    _ = (∫ omega,
          g (∑ k : ↥(Finset.range i), Δ k omega) *
              (Δ i omega ^ 2 - v) *
              g (∑ k : ↥(Finset.range j), Δ k omega) ∂P) *
        (∫ omega, Δ j omega ^ 2 - v ∂P) :=
      hind.integral_fun_mul_eq_mul_integral hleft hright
    _ = 0 := by rw [hmean j, mul_zero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- An adapted bounded weight preserves the `O(1/n)` centered-QV estimate. -/
private theorem eLpNorm_centeredWeightedPartitionSum_toReal_sq_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K)
    (hgK : ∀ x, |g x| ≤ K) :
    MemLp (fun omega ↦ ∑ i ∈ Finset.range n,
      centeredWeightedPartitionIncrement B t n g i omega) 2 P ∧
      (eLpNorm (fun omega ↦ ∑ i ∈ Finset.range n,
        centeredWeightedPartitionIncrement B t n g i omega) 2 P).toReal ^ 2 ≤
        (n : ℝ) *
          (K ^ 2 * (2 * (((t / (n : ℝ≥0) : ℝ≥0) : ℝ) ^ 2))) := by
  classical
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let d : ℝ≥0 := t / (n : ℝ≥0)
  let Δ : ℕ → W → ℝ := partitionIncrement B t n
  let C : ℕ → W → ℝ := fun i omega ↦ Δ i omega ^ 2 - (d : ℝ)
  let Y : ℕ → W → ℝ := fun i omega ↦
    g (incrementPrefix Δ i omega) * C i omega
  have hLaw (i : ℕ) : HasLaw (Δ i) (gaussianReal 0 d) P := by
    dsimp only [Δ, partitionIncrement, d]
    change HasLaw
      (B (uniformPartitionTime t n (i + 1)) -
        B (uniformPartitionTime t n i))
      (gaussianReal 0 (t / (n : ℝ≥0))) P
    have hraw := hpre.hasLaw_sub (uniformPartitionTime t n (i + 1))
      (uniformPartitionTime t n i)
    convert hraw using 1
    exact congrArg (gaussianReal 0)
      (uniformPartitionTime_succ_nndist_for_weightedSum t hn i).symm
  have hΔmeas (i : ℕ) : AEMeasurable (Δ i) P := by
    dsimp only [Δ, partitionIncrement]
    exact (hpre.aemeasurable (uniformPartitionTime t n (i + 1))).sub
      (hpre.aemeasurable (uniformPartitionTime t n i))
  have hIndΔ : iIndepFun Δ P := by
    have hmono : Monotone (uniformPartitionTime t n) := by
      intro i j hij
      unfold uniformPartitionTime
      gcongr
    change iIndepFun (fun i omega ↦
      B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega) P
    exact hpre.hasIndepIncrements.nat hmono
  have hCmem (i : ℕ) : MemLp (C i) 2 P := by
    simpa only [C] using centeredSquare_memLp_of_hasLaw d (hLaw i)
  have hCmean (i : ℕ) : (∫ omega, C i omega ∂P) = 0 := by
    simpa only [C] using integral_centeredSquare_of_hasLaw d (hLaw i)
  have hCvar (i : ℕ) : Var[C i; P] = 2 * (d : ℝ) ^ 2 := by
    simpa only [C] using variance_centeredSquare_of_hasLaw d (hLaw i)
  have hPrefixStrong (i : ℕ) : AEStronglyMeasurable
      (fun omega ↦ incrementPrefix Δ i omega) P := by
    unfold incrementPrefix
    have hs := Finset.aestronglyMeasurable_sum
      (Finset.univ : Finset ↥(Finset.range i))
      (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply]
  have hCstrong (i : ℕ) : AEStronglyMeasurable (C i) P := by
    dsimp only [C]
    exact (((hΔmeas i).pow_const 2).sub aemeasurable_const).aestronglyMeasurable
  have hYstrong (i : ℕ) : AEStronglyMeasurable (Y i) P := by
    dsimp only [Y]
    exact (hg.comp_aemeasurable (hPrefixStrong i).aemeasurable).aestronglyMeasurable.mul
      (hCstrong i)
  have hYbound (i : ℕ) : ∀ᵐ omega ∂P,
      ‖Y i omega‖ ≤ K * ‖C i omega‖ := by
    filter_upwards with omega
    dsimp only [Y]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hgK (incrementPrefix Δ i omega))
      (norm_nonneg _)
  have hYmem (i : ℕ) : MemLp (Y i) 2 P :=
    (hCmem i).of_le_mul (hYstrong i) (hYbound i)
  have horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i ≠ j →
      (∫ omega, Y i omega * Y j omega ∂P) = 0 := by
    intro i _hi j _hj hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · simpa only [Y, C, incrementPrefix] using
        integral_prefixWeightedCentered_mul_eq_zero_of_lt
          Δ (d : ℝ) g hg hIndΔ hΔmeas hCmean hij'
    · calc
        (∫ omega, Y i omega * Y j omega ∂P) =
            ∫ omega, Y j omega * Y i omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = 0 := by
          simpa only [Y, C, incrementPrefix] using
            integral_prefixWeightedCentered_mul_eq_zero_of_lt
              Δ (d : ℝ) g hg hIndΔ hΔmeas hCmean hji'
  have hCIntegralSq (i : ℕ) :
      (∫ omega, (C i omega) ^ 2 ∂P) = 2 * (d : ℝ) ^ 2 := by
    have hv := variance_eq_sub (hCmem i)
    rw [hCvar i, hCmean i] at hv
    norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hv
    exact hv.symm
  have hCnorm (i : ℕ) : eLpNorm (C i) 2 P =
      ENNReal.ofReal ((2 * (d : ℝ) ^ 2) ^ (2 : ℝ)⁻¹) := by
    rw [(hCmem i).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      hCIntegralSq]
  have hCnormSq (i : ℕ) :
      (eLpNorm (C i) 2 P).toReal ^ 2 = 2 * (d : ℝ) ^ 2 := by
    rw [hCnorm i]
    have hnonneg : 0 ≤ 2 * (d : ℝ) ^ 2 := by positivity
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hnonneg
  have hYnormSq (i : ℕ) :
      (eLpNorm (Y i) 2 P).toReal ^ 2 ≤
        K ^ 2 * (2 * (d : ℝ) ^ 2) := by
    have hnormENN := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hYbound i) 2
    have hright_ne : ENNReal.ofReal K * eLpNorm (C i) 2 P ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hCmem i).eLpNorm_lt_top.ne
    have hnormReal : (eLpNorm (Y i) 2 P).toReal ≤
        K * (eLpNorm (C i) 2 P).toReal := by
      have htoReal := (ENNReal.toReal_le_toReal
        (hYmem i).eLpNorm_lt_top.ne hright_ne).2 hnormENN
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using htoReal
    calc
      (eLpNorm (Y i) 2 P).toReal ^ 2 ≤
          (K * (eLpNorm (C i) 2 P).toReal) ^ 2 :=
        (sq_le_sq₀ ENNReal.toReal_nonneg
          (mul_nonneg hK ENNReal.toReal_nonneg)).2 hnormReal
      _ = K ^ 2 * (eLpNorm (C i) 2 P).toReal ^ 2 := by ring
      _ = K ^ 2 * (2 * (d : ℝ) ^ 2) := by rw [hCnormSq i]
  have hsumEq := eLpNorm_finsetSum_toReal_sq
    (Finset.range n) Y hYmem horth
  constructor
  · change MemLp (fun omega ↦ ∑ i ∈ Finset.range n, Y i omega) 2 P
    exact memLp_finsetSum (Finset.range n) (fun i _hi ↦ hYmem i)
  · change (eLpNorm (fun omega ↦ ∑ i ∈ Finset.range n, Y i omega) 2 P).toReal ^ 2 ≤
      (n : ℝ) * (K ^ 2 * (2 * (d : ℝ) ^ 2))
    calc
      (eLpNorm (fun omega ↦ ∑ i ∈ Finset.range n, Y i omega) 2 P).toReal ^ 2 =
          ∑ i ∈ Finset.range n, (eLpNorm (Y i) 2 P).toReal ^ 2 := hsumEq
      _ ≤ ∑ i ∈ Finset.range n, K ^ 2 * (2 * (d : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hYnormSq i
      _ = (n : ℝ) * (K ^ 2 * (2 * (d : ℝ) ^ 2)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The same estimate for weights evaluated at the actual Brownian left
endpoints. -/
private theorem eLpNorm_centeredWeightedQuadraticVariationApprox_toReal_sq_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K)
    (hgK : ∀ x, |g x| ≤ K) :
    MemLp (centeredWeightedQuadraticVariationApprox B t n g) 2 P ∧
      (eLpNorm (centeredWeightedQuadraticVariationApprox B t n g) 2 P).toReal ^ 2 ≤
        (n : ℝ) *
          (K ^ 2 * (2 * (((t / (n : ℝ≥0) : ℝ≥0) : ℝ) ^ 2))) := by
  have hprefix := eLpNorm_centeredWeightedPartitionSum_toReal_sq_le
    hB t hn g hg K hK hgK
  have hae := centeredWeightedQuadraticVariationApprox_ae_eq_prefix
    hB t hn g
  constructor
  · exact (memLp_congr_ae hae).2 hprefix.1
  · rw [eLpNorm_congr_ae hae]
    exact hprefix.2

private lemma tendsto_sqrt_const_div_add_one_for_weightedSum (C : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ Real.sqrt (C / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
  have hdivNat : Filter.Tendsto
      (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat C)
  have hdiv : Filter.Tendsto
      (fun n : ℕ ↦ C / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdivNat
  change Filter.Tendsto
    (Real.sqrt ∘ fun n : ℕ ↦ C / ((n : ℝ) + 1))
    Filter.atTop (nhds 0)
  simpa only [Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hdiv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Globally bounded adapted continuous weights make the centered weighted
Brownian quadratic-variation sums converge to zero in `L²`. -/
private theorem tendsto_eLpNorm_centeredWeightedQuadraticVariationApprox
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K)
    (hgK : ∀ x, |g x| ≤ K) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        (centeredWeightedQuadraticVariationApprox B t (n + 1) g) 2 P)
      Filter.atTop (nhds 0) := by
  let C : ℝ := 2 * K ^ 2 * (t : ℝ) ^ 2
  have hestimate (n : ℕ) :=
    eLpNorm_centeredWeightedQuadraticVariationApprox_toReal_sq_le
      hB t (Nat.zero_lt_succ n) g hg K hK hgK
  have hfinite : ∀ n : ℕ,
      eLpNorm (centeredWeightedQuadraticVariationApprox B t (n + 1) g) 2 P ≠ ∞ :=
    fun n ↦ (hestimate n).1.eLpNorm_lt_top.ne
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).1
  apply squeeze_zero
    (g := fun n : ℕ ↦ Real.sqrt (C / ((n : ℝ) + 1)))
  · intro n
    exact ENNReal.toReal_nonneg
  · intro n
    apply Real.le_sqrt_of_sq_le
    calc
      (eLpNorm
          (centeredWeightedQuadraticVariationApprox B t (n + 1) g)
          2 P).toReal ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) *
            (K ^ 2 *
              (2 * (((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ^ 2))) :=
        (hestimate n).2
      _ = C / ((n : ℝ) + 1) := by
        dsimp only [C]
        simp only [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_add,
          Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
        have hnR : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hnR]
  · exact tendsto_sqrt_const_div_add_one_for_weightedSum C

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The bounded weighted centered-QV sums therefore converge to zero in
probability. -/
private theorem centeredWeightedQuadraticVariationApprox_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K)
    (hgK : ∀ x, |g x| ≤ K) :
    TendstoInMeasure P
      (fun n ↦ centeredWeightedQuadraticVariationApprox B t (n + 1) g)
      Filter.atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  · intro n
    exact (eLpNorm_centeredWeightedQuadraticVariationApprox_toReal_sq_le
      hB t (Nat.zero_lt_succ n) g hg K hK hgK).1.aestronglyMeasurable
  · exact aestronglyMeasurable_const
  · have hfun :
        (fun n ↦ eLpNorm
          (centeredWeightedQuadraticVariationApprox B t (n + 1) g -
            fun _ ↦ 0) 2 P) =
        (fun n ↦ eLpNorm
          (centeredWeightedQuadraticVariationApprox B t (n + 1) g) 2 P) := by
        funext n
        apply eLpNorm_congr_ae
        filter_upwards with omega
        simp only [Pi.sub_apply, sub_zero]
    rw [hfun]
    exact tendsto_eLpNorm_centeredWeightedQuadraticVariationApprox
      hB t g hg K hK hgK

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem aestronglyMeasurable_centeredWeightedQuadraticVariationApprox
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (n : ℕ)
    (g : ℝ → ℝ) (hg : Measurable g) :
    AEStronglyMeasurable
      (centeredWeightedQuadraticVariationApprox B t n g) P := by
  unfold centeredWeightedQuadraticVariationApprox
  have hpre := hB.toIsPreBrownianReal
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega ↦
        g (B (uniformPartitionTime t n i) omega) *
          ((B (uniformPartitionTime t n (i + 1)) omega -
              B (uniformPartitionTime t n i) omega) ^ 2 -
            ((uniformPartitionTime t n (i + 1) : ℝ) -
              (uniformPartitionTime t n i : ℝ)))) P :=
    Finset.aestronglyMeasurable_sum (Finset.range n)
      (fun i _hi ↦ by
      have hweight := hg.comp_aemeasurable
        (hpre.aemeasurable (uniformPartitionTime t n i))
      have hΔ :=
        (hpre.aemeasurable (uniformPartitionTime t n (i + 1))).sub
          (hpre.aemeasurable (uniformPartitionTime t n i))
      have hcenter : AEMeasurable (fun omega ↦
          (B (uniformPartitionTime t n (i + 1)) omega -
              B (uniformPartitionTime t n i) omega) ^ 2 -
            ((uniformPartitionTime t n (i + 1) : ℝ) -
              (uniformPartitionTime t n i : ℝ))) P :=
        (hΔ.pow_const 2).sub aemeasurable_const
      exact hweight.aestronglyMeasurable.mul hcenter.aestronglyMeasurable)
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, partitionIncrement]

private def boundedOutputCutoff (g : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  max (-((k : ℝ) + 1)) (min (g x) ((k : ℝ) + 1))

private lemma measurable_boundedOutputCutoff
    (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) :
    Measurable (boundedOutputCutoff g k) := by
  unfold boundedOutputCutoff
  fun_prop

private lemma abs_boundedOutputCutoff_le
    (g : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    |boundedOutputCutoff g k x| ≤ (k : ℝ) + 1 := by
  rw [abs_le]
  constructor
  · unfold boundedOutputCutoff
    exact le_max_left _ _
  · unfold boundedOutputCutoff
    exact max_le (by
      have hk : 0 ≤ (k : ℝ) + 1 := by positivity
      linarith) (min_le_right _ _)

private lemma boundedOutputCutoff_eq
    (g : ℝ → ℝ) (k : ℕ) (x : ℝ)
    (hlow : -((k : ℝ) + 1) ≤ g x)
    (hupp : g x ≤ (k : ℝ) + 1) :
    boundedOutputCutoff g k x = g x := by
  unfold boundedOutputCutoff
  rw [min_eq_left hupp, max_eq_right hlow]

private def quarticSubsequence (k : ℕ) : ℕ := (k + 1) ^ 4

private lemma strictMono_quarticSubsequence : StrictMono quarticSubsequence := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold quarticSubsequence
  apply Nat.pow_lt_pow_left
  · omega
  · norm_num

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem tendsto_eLpNorm_boundedOutputCutoff_subsequence
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g)
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    Filter.Tendsto
      (fun k ↦ eLpNorm
        (centeredWeightedQuadraticVariationApprox B t
          (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k)) 2 P)
      Filter.atTop (nhds 0) := by
  let C : ℝ := 2 * (t : ℝ) ^ 2
  have hestimate (k : ℕ) :=
    eLpNorm_centeredWeightedQuadraticVariationApprox_toReal_sq_le
      hB t (Nat.zero_lt_succ (ns (quarticSubsequence k)))
      (boundedOutputCutoff g k) (measurable_boundedOutputCutoff g hg k)
      ((k : ℝ) + 1) (by positivity) (abs_boundedOutputCutoff_le g k)
  have hfinite : ∀ k : ℕ,
      eLpNorm
        (centeredWeightedQuadraticVariationApprox B t
          (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k)) 2 P ≠ ∞ :=
    fun k ↦ (hestimate k).1.eLpNorm_lt_top.ne
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).1
  apply squeeze_zero
    (g := fun k : ℕ ↦ Real.sqrt C / ((k : ℝ) + 1))
  · intro k
    exact ENNReal.toReal_nonneg
  · intro k
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hdenpos : 0 < ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) := by
      positivity
    have hqle : quarticSubsequence k ≤ ns (quarticSubsequence k) :=
      hns.le_apply
    have hdenNat : quarticSubsequence k ≤ ns (quarticSubsequence k) + 1 :=
      hqle.trans (Nat.le_succ _)
    have hdenReal : ((k : ℝ) + 1) ^ 4 ≤
        ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) := by
      have hcast : ((quarticSubsequence k : ℕ) : ℝ) ≤
          ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdenNat
      simpa only [quarticSubsequence, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one] using hcast
    have hsqBound :
        (eLpNorm
          (centeredWeightedQuadraticVariationApprox B t
            (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k))
          2 P).toReal ^ 2 ≤ C / (((k : ℝ) + 1) ^ 2) := by
      calc
        (eLpNorm
            (centeredWeightedQuadraticVariationApprox B t
              (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k))
            2 P).toReal ^ 2 ≤
            ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) *
              (((k : ℝ) + 1) ^ 2 *
                (2 * (((t /
                  ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ^ 2))) :=
          (hestimate k).2
        _ = (C * ((k : ℝ) + 1) ^ 2) /
            ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) := by
          dsimp only [C]
          simp only [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_add,
            Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
          have hdenne : ((ns (quarticSubsequence k) : ℝ) + 1) ≠ 0 := by
            positivity
          field_simp [hdenne]
        _ ≤ C / (((k : ℝ) + 1) ^ 2) := by
          apply (div_le_div_iff₀ hdenpos (sq_pos_of_pos hkpos)).2
          calc
            C * ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2 =
                C * ((k : ℝ) + 1) ^ 4 := by ring
            _ ≤ C * ((ns (quarticSubsequence k) + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hdenReal (by
                dsimp only [C]
                positivity)
    apply le_of_sq_le_sq
    · calc
        (eLpNorm
            (centeredWeightedQuadraticVariationApprox B t
              (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k))
            2 P).toReal ^ 2 ≤ C / (((k : ℝ) + 1) ^ 2) := hsqBound
        _ = (Real.sqrt C / ((k : ℝ) + 1)) ^ 2 := by
          rw [div_pow, Real.sq_sqrt]
          dsimp only [C]
          positivity
    · exact div_nonneg (Real.sqrt_nonneg C) hkpos.le
  · have hdivNat : Filter.Tendsto
        (fun k : ℕ ↦ Real.sqrt C / ((k + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2
        (tendsto_const_div_atTop_nhds_zero_nat (Real.sqrt C))
    simpa only [Nat.cast_add, Nat.cast_one] using hdivNat

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Continuous adapted weights need not be globally bounded: growing bounded
cutoffs and Brownian path continuity localize the preceding `L²` estimate. -/
private theorem continuous_centeredWeightedQuadraticVariationApprox_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    TendstoInMeasure P
      (fun n ↦ centeredWeightedQuadraticVariationApprox B t (n + 1) g)
      Filter.atTop (fun _ ↦ 0) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (centeredWeightedQuadraticVariationApprox B t (n + 1) g) P :=
    fun n ↦ aestronglyMeasurable_centeredWeightedQuadraticVariationApprox
      hB t (n + 1) g hg.measurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  have hcutProb : TendstoInMeasure P
      (fun k ↦ centeredWeightedQuadraticVariationApprox B t
        (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k))
      Filter.atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    · intro k
      exact aestronglyMeasurable_centeredWeightedQuadraticVariationApprox
        hB t (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k)
          (measurable_boundedOutputCutoff g hg.measurable k)
    · exact aestronglyMeasurable_const
    · have hfun :
          (fun k ↦ eLpNorm
            (centeredWeightedQuadraticVariationApprox B t
                (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k) -
              fun _ ↦ 0) 2 P) =
          (fun k ↦ eLpNorm
            (centeredWeightedQuadraticVariationApprox B t
              (ns (quarticSubsequence k) + 1) (boundedOutputCutoff g k)) 2 P) := by
          funext k
          apply eLpNorm_congr_ae
          filter_upwards with omega
          simp only [Pi.sub_apply, sub_zero]
      rw [hfun]
      exact tendsto_eLpNorm_boundedOutputCutoff_subsequence
        hB t g hg.measurable ns hns
  obtain ⟨r, hr, hcutAE⟩ := hcutProb.exists_seq_tendsto_ae
  refine ⟨fun k ↦ quarticSubsequence (r k),
    strictMono_quarticSubsequence.comp hr, ?_⟩
  filter_upwards [hB.cont, hcutAE] with omega hcontinuous hcut
  have hpathContinuous : Continuous (fun s ↦ g (B s omega)) :=
    hg.comp hcontinuous
  obtain ⟨a, b, hrange⟩ :=
    continuous_nnreal_range_subset_Icc (fun s ↦ g (B s omega))
      hpathContinuous t
  obtain ⟨N, hN⟩ := exists_nat_gt (max |a| |b|)
  have heq : ∀ᶠ k in Filter.atTop,
      centeredWeightedQuadraticVariationApprox B t
          (ns (quarticSubsequence (r k)) + 1) (boundedOutputCutoff g (r k)) omega =
        centeredWeightedQuadraticVariationApprox B t
          (ns (quarticSubsequence (r k)) + 1) g omega := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    unfold centeredWeightedQuadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hpartPos : 0 < ns (quarticSubsequence (r k)) + 1 :=
      Nat.zero_lt_succ _
    have htime : uniformPartitionTime t
        (ns (quarticSubsequence (r k)) + 1) i ∈ Set.Icc 0 t :=
      uniformPartitionTime_mem_Icc_of_le t hpartPos
        (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hx := hrange _ htime
    have hkr : k ≤ r k := hr.le_apply
    have hNR : (N : ℝ) ≤ (r k : ℝ) := by
      exact_mod_cast le_trans hk hkr
    have hlow : -((r k : ℝ) + 1) ≤
        g (B (uniformPartitionTime t
          (ns (quarticSubsequence (r k)) + 1) i) omega) := by
      have haMax : |a| ≤ max |a| |b| := le_max_left _ _
      have haNeg : -|a| ≤ a := neg_abs_le a
      have hxa := hx.1
      linarith
    have hupp :
        g (B (uniformPartitionTime t
          (ns (quarticSubsequence (r k)) + 1) i) omega) ≤
          (r k : ℝ) + 1 := by
      have hbMax : |b| ≤ max |a| |b| := le_max_right _ _
      have hbAbs : b ≤ |b| := le_abs_self b
      have hxb := hx.2
      linarith
    rw [boundedOutputCutoff_eq g (r k) _ hlow hupp]
  exact hcut.congr' heq

private noncomputable def secondOrderTaylorApprox
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / 2 : ℝ) * deriv (deriv f)
      (B (uniformPartitionTime t n i) omega) *
      partitionIncrement B t n i omega ^ 2

private noncomputable def secondDerivativeTimeIntegral
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    deriv (deriv f) (B s.toNNReal omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The entire second-order Taylor sum converges in probability to the
second-derivative time integral. -/
private theorem secondOrderTaylorApprox_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ secondOrderTaylorApprox f B t (n + 1))
      Filter.atTop (secondDerivativeTimeIntegral f B t) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (secondOrderTaylorApprox f B t (n + 1)) P := by
    intro n
    unfold secondOrderTaylorApprox
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (n + 1), fun omega ↦
          (1 / 2 : ℝ) * deriv (deriv f)
            (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega) ^ 2) P :=
      Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
        (fun i _hi ↦ by
        have hweight := hsecond.measurable.comp_aemeasurable
          (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
        have hΔ :=
          (hpre.aemeasurable (uniformPartitionTime t (n + 1) (i + 1))).sub
            (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
        exact (aestronglyMeasurable_const.mul hweight.aestronglyMeasurable).mul
          (hΔ.pow_const 2).aestronglyMeasurable)
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, partitionIncrement]
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  have hcenter := continuous_centeredWeightedQuadraticVariationApprox_tendstoInMeasure
    hB t (deriv (deriv f)) hsecond
  obtain ⟨ms, hms, hcenterAE⟩ :=
    (hcenter.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hB.cont, hcenterAE] with omega hcontinuous hcenter'
  have htime := (tendsto_uniformPartition_secondDeriv_timeSum
    hf B t omega hcontinuous).comp
      (hns.tendsto_atTop.comp hms.tendsto_atTop)
  have hcenter'' : Filter.Tendsto
      (fun k ↦ centeredWeightedQuadraticVariationApprox B t
        (ns (ms k) + 1) (deriv (deriv f)) omega)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using hcenter'
  have htime' : Filter.Tendsto
      (fun k ↦ ∑ i ∈ Finset.range (ns (ms k) + 1),
        deriv (deriv f) (B (uniformPartitionTime t (ns (ms k) + 1) i) omega) *
          ((uniformPartitionTime t (ns (ms k) + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (ns (ms k) + 1) i : ℝ)))
      Filter.atTop
        (nhds (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega))) := by
    change Filter.Tendsto
      (fun k ↦ ∑ i ∈ Finset.range (ns (ms k) + 1),
        deriv (deriv f) (B (uniformPartitionTime t (ns (ms k) + 1) i) omega) *
          ((uniformPartitionTime t (ns (ms k) + 1) (i + 1) : ℝ) -
            (uniformPartitionTime t (ns (ms k) + 1) i : ℝ)))
      Filter.atTop
        (nhds (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega))) at htime
    exact htime
  have hsum := (hcenter''.const_mul (1 / 2 : ℝ)).add
    (htime'.const_mul (1 / 2 : ℝ))
  convert hsum using 1
  · funext k
    unfold secondOrderTaylorApprox centeredWeightedQuadraticVariationApprox
    simpa only [partitionIncrement] using
      uniformPartition_secondOrder_decomposition f B t (ns (ms k)) omega
  · unfold secondDerivativeTimeIntegral
    simp only [mul_zero, zero_add]

private noncomputable def firstOrderTaylorApprox
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    deriv f (B (uniformPartitionTime t n i) omega) *
      partitionIncrement B t n i omega

private noncomputable def taylorRemainderApprox
    (f : ℝ → ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoTaylorRemainder f (B (uniformPartitionTime t n i) omega)
      (B (uniformPartitionTime t n (i + 1)) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem aestronglyMeasurable_firstOrderTaylorApprox
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (firstOrderTaylorApprox f B t n) P := by
  have hpre := hB.toIsPreBrownianReal
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  unfold firstOrderTaylorApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega ↦
        deriv f (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega)) P :=
    Finset.aestronglyMeasurable_sum (Finset.range n)
      (fun i _hi ↦ by
        have hweight := hfirst.measurable.comp_aemeasurable
          (hpre.aemeasurable (uniformPartitionTime t n i))
        have hΔ :=
          (hpre.aemeasurable (uniformPartitionTime t n (i + 1))).sub
            (hpre.aemeasurable (uniformPartitionTime t n i))
        exact hweight.aestronglyMeasurable.mul hΔ.aestronglyMeasurable)
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, partitionIncrement]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem aestronglyMeasurable_secondOrderTaylorApprox
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (secondOrderTaylorApprox f B t n) P := by
  have hpre := hB.toIsPreBrownianReal
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  unfold secondOrderTaylorApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega ↦
        (1 / 2 : ℝ) * deriv (deriv f)
          (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega) ^ 2) P :=
    Finset.aestronglyMeasurable_sum (Finset.range n)
      (fun i _hi ↦ by
        have hweight := hsecond.measurable.comp_aemeasurable
          (hpre.aemeasurable (uniformPartitionTime t n i))
        have hΔ :=
          (hpre.aemeasurable (uniformPartitionTime t n (i + 1))).sub
            (hpre.aemeasurable (uniformPartitionTime t n i))
        exact (aestronglyMeasurable_const.mul hweight.aestronglyMeasurable).mul
          (hΔ.pow_const 2).aestronglyMeasurable)
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, partitionIncrement]


end CenteredWeightedQuadraticVariation

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The uniform Taylor estimate and an eventually bounded quadratic sum make
the remainder sum vanish along any path with uniformly small partition
increments. -/
private theorem tendsto_uniformPartition_taylorRemainder
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (ω : W) (C : ℝ) (hC : 0 < C)
    (hcontinuous : Continuous (fun s ↦ B s ω))
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox B t (n + 1) ω ≤ C) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω))
      Filter.atTop (nhds 0) := by
  obtain ⟨a, b, hrange⟩ :=
    continuous_nnreal_range_subset_Icc (fun s ↦ B s ω) hcontinuous t
  apply tendsto_sum_zero_of_remainder_bound
    (N := fun n ↦ n + 1)
    (r := fun n i ↦
      itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
        (B (uniformPartitionTime t (n + 1) (i + 1)) ω))
    (Δ := fun n i ↦ B (uniformPartitionTime t (n + 1) (i + 1)) ω -
      B (uniformPartitionTime t (n + 1) i) ω)
    hC
  · simpa only [quadraticVariationApprox] using hquadratic
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      uniform_itoTaylorRemainder_bound_on_Icc hf a b ε hε
    filter_upwards [continuous_uniformPartition_increments
      (fun s ↦ B s ω) hcontinuous t δ hδ] with n hn
    intro i hi
    have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
    have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    have hi' : i ≤ n + 1 := le_trans (Nat.le_add_right i 1) hipos
    exact hbound _ (hrange _ (uniformPartitionTime_mem_Icc t hnpos hi')) _
      (hrange _ (uniformPartitionTime_mem_Icc t hnpos hipos)) (hn i hi)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Pathwise convergence of the quadratic sums supplies the boundedness input
for the continuous-path Taylor remainder theorem. -/
private theorem tendsto_uniformPartition_taylorRemainder_of_quadraticVariation
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (ω : W) (q : ℝ)
    (hcontinuous : Continuous (fun s ↦ B s ω))
    (hquadratic : Filter.Tendsto
      (fun n ↦ quadraticVariationApprox B t (n + 1) ω)
      Filter.atTop (nhds q)) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω))
      Filter.atTop (nhds 0) := by
  let C := |q| + 1
  apply tendsto_uniformPartition_taylorRemainder hf B t ω C (by
    dsimp only [C]
    positivity) hcontinuous
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hquadratic 1 zero_lt_one
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hdist := hN n hn
  rw [Real.dist_eq] at hdist
  dsimp only [C]
  have hupper := (abs_lt.mp hdist).2
  linarith [le_abs_self q]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The continuous-path remainder argument is stable under any partition
subsequence tending to infinity. -/
theorem tendsto_subseq_uniformPartition_taylorRemainder_of_quadraticVariation
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (ω : W) (q : ℝ) (ns : ℕ → ℕ)
    (hns : Filter.Tendsto ns Filter.atTop Filter.atTop)
    (hcontinuous : Continuous (fun s ↦ B s ω))
    (hquadratic : Filter.Tendsto
      (fun n ↦ quadraticVariationApprox B t (ns n + 1) ω)
      Filter.atTop (nhds q)) :
    Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (ns n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (ns n + 1) i) ω)
          (B (uniformPartitionTime t (ns n + 1) (i + 1)) ω))
      Filter.atTop (nhds 0) := by
  let C := |q| + 1
  obtain ⟨a, b, hrange⟩ :=
    continuous_nnreal_range_subset_Icc (fun s ↦ B s ω) hcontinuous t
  apply tendsto_sum_zero_of_remainder_bound
    (N := fun n ↦ ns n + 1)
    (r := fun n i ↦
      itoTaylorRemainder f (B (uniformPartitionTime t (ns n + 1) i) ω)
        (B (uniformPartitionTime t (ns n + 1) (i + 1)) ω))
    (Δ := fun n i ↦ B (uniformPartitionTime t (ns n + 1) (i + 1)) ω -
      B (uniformPartitionTime t (ns n + 1) i) ω)
    (C := C) (by
      dsimp only [C]
      positivity)
  · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hquadratic 1 zero_lt_one
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hdist := hN n hn
    rw [Real.dist_eq] at hdist
    dsimp only [C]
    have hupper := (abs_lt.mp hdist).2
    simpa only [quadraticVariationApprox] using
      (show quadraticVariationApprox B t (ns n + 1) ω ≤ |q| + 1 by
        linarith [le_abs_self q])
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      uniform_itoTaylorRemainder_bound_on_Icc hf a b ε hε
    filter_upwards [hns.eventually
      (continuous_uniformPartition_increments
        (fun s ↦ B s ω) hcontinuous t δ hδ)] with n hn
    intro i hi
    have hnpos : 0 < ns n + 1 := Nat.zero_lt_succ (ns n)
    have hipos : i + 1 ≤ ns n + 1 := Finset.mem_range.mp hi
    have hi' : i ≤ ns n + 1 := le_trans (Nat.le_add_right i 1) hipos
    exact hbound _ (hrange _ (uniformPartitionTime_mem_Icc t hnpos hi')) _
      (hrange _ (uniformPartitionTime_mem_Icc t hnpos hipos)) (hn i hi)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian quadratic variation has an almost-surely convergent subsequence
along which the Taylor remainder sum vanishes. -/
private theorem exists_subseq_tendsto_taylorRemainder_ae
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun n ↦ ∑ i ∈ Finset.range (ns n + 1),
          itoTaylorRemainder f (B (uniformPartitionTime t (ns n + 1) i) ω)
            (B (uniformPartitionTime t (ns n + 1) (i + 1)) ω))
        Filter.atTop (nhds 0) := by
  have hprob := quadraticVariation_brownianMotion_inProbability hB t
  unfold HasQuadraticVariationInProbabilityAt at hprob
  obtain ⟨ns, hns, hqv⟩ := hprob.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hB.cont, hqv] with ω hcontinuous hquadratic
  apply tendsto_subseq_uniformPartition_taylorRemainder_of_quadraticVariation
    hf B t ω (t : ℝ) ns hns.tendsto_atTop hcontinuous
  simpa only using hquadratic

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The exact Taylor remainder sums along the uniform partitions vanish in
probability. -/
private theorem taylorRemainder_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ω ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω))
      Filter.atTop (fun _ ↦ 0) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have hremainder :
      Continuous (fun p : ℝ × ℝ ↦ itoTaylorRemainder f p.1 p.2) := by
    unfold itoTaylorRemainder
    fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω)) P := by
    intro n
    have hs := Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
      (fun i _hi ↦ (hremainder.measurable.comp_aemeasurable
        ((hB.toIsPreBrownianReal.aemeasurable
          (uniformPartitionTime t (n + 1) i)).prodMk
        (hB.toIsPreBrownianReal.aemeasurable
          (uniformPartitionTime t (n + 1) (i + 1))))).aestronglyMeasurable)
    have hfun :
        (fun ω ↦ ∑ i ∈ Finset.range (n + 1),
          itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
            (B (uniformPartitionTime t (n + 1) (i + 1)) ω)) =
        ∑ i ∈ Finset.range (n + 1), fun ω ↦
          itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) ω)
            (B (uniformPartitionTime t (n + 1) (i + 1)) ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hfun]
    exact hs
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  have hprob := quadraticVariation_brownianMotion_inProbability hB t
  unfold HasQuadraticVariationInProbabilityAt at hprob
  obtain ⟨ms, hms, hquadratic⟩ :=
    (hprob.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hB.cont, hquadratic] with ω hcontinuous hquadratic'
  apply tendsto_subseq_uniformPartition_taylorRemainder_of_quadraticVariation
    hf B t ω (t : ℝ) (fun k ↦ ns (ms k))
    (hns.tendsto_atTop.comp hms.tendsto_atTop) hcontinuous
  simpa only [Function.comp_apply] using hquadratic'

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem aestronglyMeasurable_taylorRemainderApprox
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (taylorRemainderApprox f B t n) P := by
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← iteratedDeriv_two f]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have hremainder :
      Continuous (fun p : ℝ × ℝ ↦ itoTaylorRemainder f p.1 p.2) := by
    unfold itoTaylorRemainder
    fun_prop
  unfold taylorRemainderApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi ↦ (hremainder.measurable.comp_aemeasurable
      ((hB.toIsPreBrownianReal.aemeasurable
        (uniformPartitionTime t n i)).prodMk
      (hB.toIsPreBrownianReal.aemeasurable
        (uniformPartitionTime t n (i + 1))))).aestronglyMeasurable)
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Function.comp_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem firstOrderTaylorApprox_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ firstOrderTaylorApprox f B t (n + 1)) Filter.atTop
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let D : W → ℝ := secondDerivativeTimeIntegral f B t
  let F : W → ℝ := fun omega ↦ f (B t omega) - f (B 0 omega)
  have hsecond : TendstoInMeasure P
      (fun n ↦ secondOrderTaylorApprox f B t (n + 1))
      Filter.atTop D := by
    simpa only [D] using secondOrderTaylorApprox_tendstoInMeasure hB hf t
  have hremainder : TendstoInMeasure P
      (fun n ↦ taylorRemainderApprox f B t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
    change TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) omega)
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega))
      Filter.atTop (fun _ ↦ 0)
    exact taylorRemainder_tendstoInMeasure hB hf t
  have hsecondMeas : ∀ n, AEStronglyMeasurable
      (secondOrderTaylorApprox f B t (n + 1)) P :=
    fun n ↦ aestronglyMeasurable_secondOrderTaylorApprox hB hf t (n + 1)
  have hremainderMeas : ∀ n, AEStronglyMeasurable
      (taylorRemainderApprox f B t (n + 1)) P :=
    fun n ↦ aestronglyMeasurable_taylorRemainderApprox hB hf t (n + 1)
  have hfcontinuous : Continuous f := hf.continuous
  have hFMeas : AEStronglyMeasurable F P := by
    dsimp only [F]
    exact ((hfcontinuous.measurable.comp_aemeasurable
      (hpre.aemeasurable t)).sub
      (hfcontinuous.measurable.comp_aemeasurable
        (hpre.aemeasurable 0))).aestronglyMeasurable
  have hF : TendstoInMeasure P (fun _ : ℕ ↦ F) Filter.atTop F :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ hFMeas) (by
      filter_upwards with omega
      exact tendsto_const_nhds)
  have hFSecond := hF.sub_real hsecond (fun _ ↦ hFMeas) hsecondMeas
  have hraw := hFSecond.sub_real hremainder
    (fun n ↦ hFMeas.sub (hsecondMeas n)) hremainderMeas
  have hraw' : TendstoInMeasure P
      (fun n omega ↦ (F omega -
        secondOrderTaylorApprox f B t (n + 1) omega) -
          taylorRemainderApprox f B t (n + 1) omega)
      Filter.atTop (fun omega ↦ F omega - D omega) := by
    apply hraw.congr_right
    filter_upwards with omega
    simp only [sub_zero]
  have hfirst : TendstoInMeasure P
      (fun n ↦ firstOrderTaylorApprox f B t (n + 1))
      Filter.atTop (fun omega ↦ F omega - D omega) := by
    apply hraw'.congr_left
    intro n
    filter_upwards with omega
    dsimp only [F]
    unfold firstOrderTaylorApprox secondOrderTaylorApprox
      taylorRemainderApprox partitionIncrement
    have hdecomp := uniformPartition_taylor_decomposition f B t n omega
    rw [hdecomp]
    ring
  apply hfirst.congr_right
  filter_upwards [hpre.eval_zero_ae_eq_zero] with omega hzero
  dsimp only [F, D, secondDerivativeTimeIntegral]
  rw [hzero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The left-endpoint first-order Taylor sums along Brownian uniform
partitions converge in probability to the residual determined by the
terminal value and the second-order time integral. -/
theorem firstOrderTaylorSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) := by
  convert firstOrderTaylorApprox_tendstoInMeasure hB hf t using 1
  funext n omega
  unfold firstOrderTaylorApprox partitionIncrement
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with any `C¹` state weight converge to the
Itô residual written using the weight's zero-based interval-integral primitive. -/
theorem brownian_contDiff_one_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, g y
  have hcont : Continuous g := hg.continuous
  have hdiff : Differentiable ℝ f := by
    dsimp only [f]
    exact intervalIntegral.differentiable_integral_of_continuous hcont
  have hderiv : deriv f = g := by
    funext x
    dsimp only [f]
    exact Continuous.deriv_integral g hcont 0 x
  have hf : ContDiff ℝ 2 f := by
    change ContDiff ℝ (1 + 1) f
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h
      norm_num at h
    · rw [hderiv]
      exact hg
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv] at h
  simpa only [f, intervalIntegral.integral_same, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A candidate is the convergence-in-probability limit of the Brownian
left sums for a `C¹` state weight exactly when it agrees almost everywhere
with the weight's explicit interval-integral residual. -/
theorem brownian_contDiff_one_leftSum_tendstoInMeasure_iff_ae_eq
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) (I : W → ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop I ↔
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) =ᵐ[P] I := by
  have hlimit := brownian_contDiff_one_leftSum_tendstoInMeasure hB hg t
  constructor
  · intro hI
    exact tendstoInMeasure_ae_unique hlimit hI
  · intro hI
    exact hlimit.congr_right hI

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Every uniform-partition Brownian left sum with a globally bounded
measurable state weight is square-integrable. -/
theorem memLp_two_bounded_brownian_leftSum
    (hB : IsBrownianMotion B P) (g : ℝ → ℝ) (hg : Measurable g)
    (Kg : ℝ≥0) (hg_bound : ∀ x, |g x| ≤ (Kg : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    MemLp
      (fun omega => ∑ i ∈ Finset.range n,
        g (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega)) 2 P := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hpre := hB.toIsPreBrownianReal
  apply memLp_finsetSum (Finset.range n)
  intro i _hi
  have hweight := hg.comp_aemeasurable
    (hpre.aemeasurable (uniformPartitionTime t n i))
  have hdeltaMeas :=
    (hpre.aemeasurable (uniformPartitionTime t n (i + 1))).sub
      (hpre.aemeasurable (uniformPartitionTime t n i))
  have htermMeas : AEStronglyMeasurable
      (fun omega =>
        g (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega)) P :=
    hweight.aestronglyMeasurable.mul hdeltaMeas.aestronglyMeasurable
  have hdeltaMem : MemLp
      (B (uniformPartitionTime t n (i + 1)) -
        B (uniformPartitionTime t n i)) 2 P :=
    (hpre.isGaussianProcess.hasGaussianLaw_eval
      (uniformPartitionTime t n (i + 1))).memLp_two.sub
      (hpre.isGaussianProcess.hasGaussianLaw_eval
        (uniformPartitionTime t n i)).memLp_two
  apply (hdeltaMem.const_mul (Kg : ℝ)).mono htermMeas
  filter_upwards with omega
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg Kg),
    Pi.sub_apply]
  exact mul_le_mul_of_nonneg_right
    (hg_bound (B (uniformPartitionTime t n i) omega)) (abs_nonneg _)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- On Brownian probability space, every uniform-partition left sum with a
globally bounded measurable state weight belongs to `Lᵖ` below `L²`. -/
theorem memLp_bounded_brownian_leftSum_of_exponent_le_two
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) (g : ℝ → ℝ) (hg : Measurable g)
    (Kg : ℝ≥0) (hg_bound : ∀ x, |g x| ≤ (Kg : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    MemLp
      (fun omega => ∑ i ∈ Finset.range n,
        g (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega)) p P := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact (memLp_two_bounded_brownian_leftSum
    hB g hg Kg hg_bound t n).mono_exponent hp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, every uniform-partition first-order Taylor
sum belongs to `Lᵖ` for every exponent at most two. -/
theorem memLp_firstOrderTaylorSum_of_exponent_le_two_of_deriv_bound
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    MemLp
      (fun omega => ∑ i ∈ Finset.range n,
        deriv f (B (uniformPartitionTime t n i) omega) *
          (B (uniformPartitionTime t n (i + 1)) omega -
            B (uniformPartitionTime t n i) omega)) p P := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact memLp_bounded_brownian_leftSum_of_exponent_le_two
    hp hB (deriv f) hderiv.continuous.measurable K hderivK t n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Discrete Itô isometry bound: the squared `L²` norm of every bounded
adapted Brownian left sum is at most `K² t`, uniformly in the partition size. -/
theorem eLpNorm_bounded_brownian_leftSum_toReal_sq_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ≥0)
    (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    (eLpNorm
      (fun omega => ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) 2 P).toReal ^ 2 ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  classical
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let d : ℝ≥0 := t / ((n + 1 : ℕ) : ℝ≥0)
  let Δ : ℕ → W → ℝ := partitionIncrement B t (n + 1)
  let Y : ℕ → W → ℝ := fun i omega ↦
    g (incrementPrefix Δ i omega) * Δ i omega
  have hLaw (i : ℕ) : HasLaw (Δ i) (gaussianReal 0 d) P := by
    dsimp only [Δ, partitionIncrement, d]
    change HasLaw
      (B (uniformPartitionTime t (n + 1) (i + 1)) -
        B (uniformPartitionTime t (n + 1) i))
      (gaussianReal 0 (t / ((n + 1 : ℕ) : ℝ≥0))) P
    have hraw := hpre.hasLaw_sub (uniformPartitionTime t (n + 1) (i + 1))
      (uniformPartitionTime t (n + 1) i)
    convert hraw using 1
    exact congrArg (gaussianReal 0)
      (uniformPartitionTime_succ_nndist_for_weightedSum
        t (Nat.zero_lt_succ n) i).symm
  have hΔmeas (i : ℕ) : AEMeasurable (Δ i) P := by
    dsimp only [Δ, partitionIncrement]
    exact (hpre.aemeasurable (uniformPartitionTime t (n + 1) (i + 1))).sub
      (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
  have hIndΔ : iIndepFun Δ P := by
    have hmono : Monotone (uniformPartitionTime t (n + 1)) := by
      intro i j hij
      unfold uniformPartitionTime
      gcongr
    change iIndepFun (fun i omega ↦
      B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega) P
    exact hpre.hasIndepIncrements.nat hmono
  have hΔmem (i : ℕ) : MemLp (Δ i) 2 P :=
    (hLaw i).hasGaussianLaw.memLp_two
  have hΔmean (i : ℕ) : (∫ omega, Δ i omega ∂P) = 0 := by
    simpa only [integral_id_gaussianReal] using (hLaw i).integral_eq
  have hPrefixStrong (i : ℕ) : AEStronglyMeasurable
      (fun omega ↦ incrementPrefix Δ i omega) P := by
    unfold incrementPrefix
    have hs := Finset.aestronglyMeasurable_sum
      (Finset.univ : Finset ↥(Finset.range i))
      (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply]
  have hYstrong (i : ℕ) : AEStronglyMeasurable (Y i) P := by
    dsimp only [Y]
    exact (hg.comp_aemeasurable
      (hPrefixStrong i).aemeasurable).aestronglyMeasurable.mul
      (hΔmeas i).aestronglyMeasurable
  have hYbound (i : ℕ) : ∀ᵐ omega ∂P,
      ‖Y i omega‖ ≤ (K : ℝ) * ‖Δ i omega‖ := by
    filter_upwards with omega
    dsimp only [Y]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using
        hgK (incrementPrefix Δ i omega)) (norm_nonneg _)
  have hYmem (i : ℕ) : MemLp (Y i) 2 P :=
    (hΔmem i).of_le_mul (hYstrong i) (hYbound i)
  have horth : ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (n + 1), i ≠ j →
      (∫ omega, Y i omega * Y j omega ∂P) = 0 := by
    intro i _hi j _hj hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · simpa only [Y] using
        integral_prefixWeightedIncrement_mul_eq_zero_of_lt
          Δ g hg hIndΔ hΔmeas hΔmean hij'
    · calc
        (∫ omega, Y i omega * Y j omega ∂P) =
            ∫ omega, Y j omega * Y i omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = 0 := by
          simpa only [Y] using
            integral_prefixWeightedIncrement_mul_eq_zero_of_lt
              Δ g hg hIndΔ hΔmeas hΔmean hji'
  have hΔIntegralSq (i : ℕ) :
      (∫ omega, (Δ i omega) ^ 2 ∂P) = (d : ℝ) := by
    have hvar : Var[Δ i; P] = (d : ℝ) := by
      rw [(hLaw i).variance_eq, variance_id_gaussianReal]
    have hv := variance_eq_sub (hΔmem i)
    rw [hvar, hΔmean i] at hv
    norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hv
    exact hv.symm
  have hΔnorm (i : ℕ) : eLpNorm (Δ i) 2 P =
      ENNReal.ofReal (((d : ℝ)) ^ (2 : ℝ)⁻¹) := by
    rw [(hΔmem i).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, hΔIntegralSq]
  have hΔnormSq (i : ℕ) :
      (eLpNorm (Δ i) 2 P).toReal ^ 2 = (d : ℝ) := by
    rw [hΔnorm i]
    have hdnonneg : 0 ≤ (d : ℝ) := NNReal.coe_nonneg d
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hdnonneg _)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hdnonneg
  have hYnormSq (i : ℕ) :
      (eLpNorm (Y i) 2 P).toReal ^ 2 ≤ (K : ℝ) ^ 2 * (d : ℝ) := by
    have hnormENN := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hYbound i) 2
    have hright_ne : ENNReal.ofReal (K : ℝ) * eLpNorm (Δ i) 2 P ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΔmem i).eLpNorm_lt_top.ne
    have hnormReal : (eLpNorm (Y i) 2 P).toReal ≤
        (K : ℝ) * (eLpNorm (Δ i) 2 P).toReal := by
      have htoReal := (ENNReal.toReal_le_toReal
        (hYmem i).eLpNorm_lt_top.ne hright_ne).2 hnormENN
      simpa only [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (NNReal.coe_nonneg K)] using htoReal
    calc
      (eLpNorm (Y i) 2 P).toReal ^ 2 ≤
          ((K : ℝ) * (eLpNorm (Δ i) 2 P).toReal) ^ 2 :=
        (sq_le_sq₀ ENNReal.toReal_nonneg
          (mul_nonneg (NNReal.coe_nonneg K) ENNReal.toReal_nonneg)).2 hnormReal
      _ = (K : ℝ) ^ 2 * (eLpNorm (Δ i) 2 P).toReal ^ 2 := by ring
      _ = (K : ℝ) ^ 2 * (d : ℝ) := by rw [hΔnormSq i]
  have hsumEq := eLpNorm_finsetSum_toReal_sq
    (Finset.range (n + 1)) Y hYmem horth
  have hprefixBound :
      (eLpNorm (fun omega ↦ ∑ i ∈ Finset.range (n + 1), Y i omega)
        2 P).toReal ^ 2 ≤ (K : ℝ) ^ 2 * (t : ℝ) := by
    calc
      (eLpNorm (fun omega ↦ ∑ i ∈ Finset.range (n + 1), Y i omega)
          2 P).toReal ^ 2 =
          ∑ i ∈ Finset.range (n + 1),
            (eLpNorm (Y i) 2 P).toReal ^ 2 := hsumEq
      _ ≤ ∑ i ∈ Finset.range (n + 1), (K : ℝ) ^ 2 * (d : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hYnormSq i
      _ = ((n + 1 : ℕ) : ℝ) * ((K : ℝ) ^ 2 * (d : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (K : ℝ) ^ 2 * (t : ℝ) := by
        dsimp only [d]
        simp only [NNReal.coe_div, NNReal.coe_natCast]
        have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hnR]
  have hsourcePrefix :
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) =ᵐ[P]
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1), Y i omega) := by
    filter_upwards [hpre.eval_zero_ae_eq_zero] with omega hzero
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [Y, Δ, partitionIncrement]
    rw [incrementPrefix_partitionIncrement_eq]
    have htimeZero : uniformPartitionTime t (n + 1) 0 = 0 := by
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
    rw [htimeZero, hzero, sub_zero]
  rw [eLpNorm_congr_ae hsourcePrefix]
  exact hprefixBound

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The `L²` norm of a Brownian left sum with a bounded measurable state
weight is at most `K * sqrt t`, uniformly in the positive partition size. -/
theorem eLpNorm_bounded_brownian_leftSum_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    eLpNorm
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hmem := memLp_two_bounded_brownian_leftSum
    hB g hg K hgK t (n + 1)
  have hsq := eLpNorm_bounded_brownian_leftSum_toReal_sq_le
    hB t g hg K hgK n
  have hCnonneg : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  apply (ENNReal.toReal_le_toReal hmem.eLpNorm_lt_top.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hCnonneg]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).mp
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
  exact hsq

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The uniform `L²` bound for bounded-state Brownian left sums also bounds
their `Lᵖ` norm at every exponent below two. -/
theorem eLpNorm_bounded_brownian_leftSum_le_of_exponent_le_two
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    eLpNorm
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) p P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact (eLpNorm_le_eLpNorm_of_exponent_le hp
    (memLp_two_bounded_brownian_leftSum
      hB g hg K hgK t (n + 1)).1).trans
    (eLpNorm_bounded_brownian_leftSum_le hB t g hg K hgK n)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, every first-order Taylor sum has `Lᵖ` norm
at most `K * sqrt t` for each exponent at most two. -/
theorem eLpNorm_firstOrderTaylorSum_le_of_exponent_le_two_of_deriv_bound
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    eLpNorm
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) p P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact eLpNorm_bounded_brownian_leftSum_le_of_exponent_le_two
    hp hB t (deriv f) hderiv.continuous.measurable K hderivK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The expected absolute value of a bounded-state Brownian left sum is at
most `K * sqrt t`, uniformly in the positive partition size. -/
theorem integral_norm_bounded_brownian_leftSum_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    (∫ omega, ‖∑ i ∈ Finset.range (n + 1),
      g (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)‖ ∂P) ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  have hmem : MemLp S 1 P := by
    simpa only [S] using memLp_bounded_brownian_leftSum_of_exponent_le_two
      (by norm_num) hB g hg K hgK t (n + 1)
  have hbound : eLpNorm S 1 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
    simpa only [S] using
      eLpNorm_bounded_brownian_leftSum_le_of_exponent_le_two
        (by norm_num) hB t g hg K hgK n
  have hC : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm S 1 P).toReal ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [ENNReal.toReal_ofReal hC] using htoReal
  calc
    (∫ omega, ‖S omega‖ ∂P) = (eLpNorm S 1 P).toReal := by
      simpa only [eLpNorm_one_eq_lintegral_enorm] using
        integral_norm_eq_lintegral_enorm hmem.1
    _ ≤ (K : ℝ) * Real.sqrt (t : ℝ) := hreal

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, the expected absolute value of every
first-order Taylor sum is at most `K * sqrt t`. -/
theorem integral_norm_firstOrderTaylorSum_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    (∫ omega, ‖∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)‖ ∂P) ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact integral_norm_bounded_brownian_leftSum_le
    hB t (deriv f) hderiv.continuous.measurable K hderivK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A Brownian left sum with a bounded measurable state weight has expectation
zero. This is the discrete centeredness property behind the stochastic term. -/
theorem integral_bounded_brownian_leftSum_eq_zero
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    (∫ omega, ∑ i ∈ Finset.range (n + 1),
      g (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega) ∂P) = 0 := by
  classical
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let d : ℝ≥0 := t / ((n + 1 : ℕ) : ℝ≥0)
  let Δ : ℕ → W → ℝ := partitionIncrement B t (n + 1)
  let Y : ℕ → W → ℝ := fun i omega ↦
    g (incrementPrefix Δ i omega) * Δ i omega
  have hLaw (i : ℕ) : HasLaw (Δ i) (gaussianReal 0 d) P := by
    dsimp only [Δ, partitionIncrement, d]
    change HasLaw
      (B (uniformPartitionTime t (n + 1) (i + 1)) -
        B (uniformPartitionTime t (n + 1) i))
      (gaussianReal 0 (t / ((n + 1 : ℕ) : ℝ≥0))) P
    have hraw := hpre.hasLaw_sub (uniformPartitionTime t (n + 1) (i + 1))
      (uniformPartitionTime t (n + 1) i)
    convert hraw using 1
    exact congrArg (gaussianReal 0)
      (uniformPartitionTime_succ_nndist_for_weightedSum
        t (Nat.zero_lt_succ n) i).symm
  have hΔmeas (i : ℕ) : AEMeasurable (Δ i) P := by
    dsimp only [Δ, partitionIncrement]
    exact (hpre.aemeasurable (uniformPartitionTime t (n + 1) (i + 1))).sub
      (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
  have hIndΔ : iIndepFun Δ P := by
    have hmono : Monotone (uniformPartitionTime t (n + 1)) := by
      intro i j hij
      unfold uniformPartitionTime
      gcongr
    change iIndepFun (fun i omega ↦
      B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega) P
    exact hpre.hasIndepIncrements.nat hmono
  have hΔmem (i : ℕ) : MemLp (Δ i) 2 P :=
    (hLaw i).hasGaussianLaw.memLp_two
  have hΔmean (i : ℕ) : (∫ omega, Δ i omega ∂P) = 0 := by
    simpa only [integral_id_gaussianReal] using (hLaw i).integral_eq
  have hPrefixStrong (i : ℕ) : AEStronglyMeasurable
      (fun omega ↦ incrementPrefix Δ i omega) P := by
    unfold incrementPrefix
    have hs := Finset.aestronglyMeasurable_sum
      (Finset.univ : Finset ↥(Finset.range i))
      (fun k _hk ↦ (hΔmeas k).aestronglyMeasurable)
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply]
  have hYstrong (i : ℕ) : AEStronglyMeasurable (Y i) P := by
    dsimp only [Y]
    exact (hg.comp_aemeasurable
      (hPrefixStrong i).aemeasurable).aestronglyMeasurable.mul
      (hΔmeas i).aestronglyMeasurable
  have hYbound (i : ℕ) : ∀ᵐ omega ∂P,
      ‖Y i omega‖ ≤ (K : ℝ) * ‖Δ i omega‖ := by
    filter_upwards with omega
    dsimp only [Y]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using
        hgK (incrementPrefix Δ i omega)) (norm_nonneg _)
  have hYmem (i : ℕ) : MemLp (Y i) 2 P :=
    (hΔmem i).of_le_mul (hYstrong i) (hYbound i)
  have hYmean (i : ℕ) : (∫ omega, Y i omega ∂P) = 0 := by
    simpa only [Y] using integral_prefixWeightedIncrement_eq_zero
      Δ g hg hIndΔ hΔmeas hΔmean i
  have hprefixMean :
      (∫ omega, ∑ i ∈ Finset.range (n + 1), Y i omega ∂P) = 0 := by
    rw [integral_finsetSum (Finset.range (n + 1))
      (fun i _hi ↦ (hYmem i).integrable (by norm_num))]
    simp only [hYmean, Finset.sum_const_zero]
  have hsourcePrefix :
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) =ᵐ[P]
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1), Y i omega) := by
    filter_upwards [hpre.eval_zero_ae_eq_zero] with omega hzero
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [Y, Δ, partitionIncrement]
    rw [incrementPrefix_partitionIncrement_eq]
    have htimeZero : uniformPartitionTime t (n + 1) 0 = 0 := by
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
    rw [htimeZero, hzero, sub_zero]
  rw [integral_congr_ae hsourcePrefix]
  exact hprefixMean

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The second moment of a Brownian left sum with a bounded measurable state
weight is at most `K² * t`, uniformly in the positive partition size. -/
theorem integral_sq_bounded_brownian_leftSum_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    (∫ omega, (∑ i ∈ Finset.range (n + 1),
      g (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)) ^ 2 ∂P) ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  have hmem : MemLp S 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg K hgK t (n + 1)
  rw [show (∫ omega, S omega ^ 2 ∂P) =
      (eLpNorm S 2 P).toReal ^ 2 from
    integral_sq_eq_eLpNorm_toReal_sq hmem]
  simpa only [S] using eLpNorm_bounded_brownian_leftSum_toReal_sq_le
    hB t g hg K hgK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Every bounded-derivative first-order Taylor sum is centered. -/
theorem integral_firstOrderTaylorSum_eq_zero_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    (∫ omega, ∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega) ∂P) = 0 := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact integral_bounded_brownian_leftSum_eq_zero
    hB t (deriv f) hderiv.continuous.measurable K hderivK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The second moment of every bounded-derivative first-order Taylor sum is
at most `K² * t`. -/
theorem integral_sq_firstOrderTaylorSum_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    (∫ omega, (∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)) ^ 2 ∂P) ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact integral_sq_bounded_brownian_leftSum_le
    hB t (deriv f) hderiv.continuous.measurable K hderivK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The variance of a bounded-state Brownian left sum is at most `K² * t`,
uniformly in the positive partition size. -/
theorem variance_bounded_brownian_leftSum_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ) :
    Var[fun omega ↦ ∑ i ∈ Finset.range (n + 1),
      g (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega); P] ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  have hmem : MemLp S 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg K hgK t (n + 1)
  have hmean : (∫ omega, S omega ∂P) = 0 := by
    simpa only [S] using
      integral_bounded_brownian_leftSum_eq_zero hB t g hg K hgK n
  have hvar := variance_eq_sub hmem
  rw [hmean] at hvar
  norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hvar
  rw [show Var[S; P] = (∫ omega, S omega ^ 2 ∂P) from hvar]
  simpa only [S] using integral_sq_bounded_brownian_leftSum_le
    hB t g hg K hgK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The variance of every bounded-derivative first-order Taylor sum is at
most `K² * t`. -/
theorem variance_firstOrderTaylorSum_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) :
    Var[fun omega ↦ ∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega); P] ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact variance_bounded_brownian_leftSum_le
    hB t (deriv f) hderiv.continuous.measurable K hderivK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for a bounded-state Brownian left sum. -/
theorem measure_bounded_brownian_leftSum_ge_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (n : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |∑ i ∈ Finset.range (n + 1),
      g (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)|} ≤
      ENNReal.ofReal (((K : ℝ) ^ 2 * (t : ℝ)) / epsilon ^ 2) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  have hmem : MemLp S 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg K hgK t (n + 1)
  have hmean : (∫ omega, S omega ∂P) = 0 := by
    simpa only [S] using
      integral_bounded_brownian_leftSum_eq_zero hB t g hg K hgK n
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  rw [hmean] at hcheb
  simp only [sub_zero, S] at hcheb
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact variance_bounded_brownian_leftSum_le hB t g hg K hgK n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for a bounded-derivative first-order Taylor sum. -/
theorem measure_firstOrderTaylorSum_ge_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ))
    (t : ℝ≥0) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)|} ≤
      ENNReal.ofReal (((K : ℝ) ^ 2 * (t : ℝ)) / epsilon ^ 2) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact measure_bounded_brownian_leftSum_ge_le
    hB t (deriv f) hderiv.continuous.measurable K hderivK n hepsilon

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A uniformly `L²`-bounded family of measurable real functions is uniformly
integrable at every lower exponent with a positive reciprocal gap from `2`. -/
theorem unifIntegrable_of_eLpNorm_two_bounded
    {I : Type*} {f : I → W → ℝ} {p : ℝ≥0∞}
    (hp : p ≤ 2)
    (hgap : 0 < 1 / ENNReal.toReal p - 1 / ENNReal.toReal 2)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) 2 P ≤ (C : ℝ≥0∞)) :
    UnifIntegrable f p P := by
  let a : ℝ := 1 / ENNReal.toReal p - 1 / ENNReal.toReal 2
  intro ε hε
  let x : ℝ := ε / ((C : ℝ) + 1)
  let δ : ℝ := x ^ a⁻¹
  have hdenom : 0 < (C : ℝ) + 1 := by positivity
  have hx : 0 < x := div_pos hε hdenom
  have ha : 0 < a := hgap
  have hδ : 0 < δ := Real.rpow_pos_of_pos hx _
  refine ⟨δ, hδ, fun i s hs hPs ↦ ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  calc
    eLpNorm (f i) p (P.restrict s) ≤
        eLpNorm (f i) 2 (P.restrict s) *
          (P.restrict s) Set.univ ^ a := by
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hf i).restrict
    _ ≤ (C : ℝ≥0∞) * (P s) ^ a := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_of_nonneg_right
        ((eLpNorm_mono_measure (f i) Measure.restrict_le_self).trans (hC i))
        (by positivity)
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal δ) ^ a := by
      gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_rpow_of_pos hδ,
        show δ ^ a = x by
          dsimp only [δ]
          exact Real.rpow_inv_rpow hx.le ha.ne']
      dsimp only [x]
      rw [← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg C),
        ENNReal.ofReal_le_ofReal_iff hε.le]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hdenom).2
        (by nlinarith only [hε, NNReal.coe_nonneg C])

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A uniformly `L²`-bounded family of measurable real functions is uniformly
integrable at every strictly positive exponent below `2`. -/
theorem unifIntegrable_of_eLpNorm_two_bounded_of_lt_two
    {I : Type*} {f : I → W → ℝ} {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp2 : p < 2)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) 2 P ≤ (C : ℝ≥0∞)) :
    UnifIntegrable f p P := by
  have hpTop : p ≠ ∞ := (hp2.trans (by finiteness)).ne
  have hreal : ENNReal.toReal p < ENNReal.toReal 2 :=
    (ENNReal.toReal_lt_toReal hpTop (by norm_num)).2 hp2
  have hgap : 0 < 1 / ENNReal.toReal p - 1 / ENNReal.toReal 2 := by
    norm_num only [ENNReal.toReal_ofNat] at hreal ⊢
    exact sub_pos.2
      (one_div_lt_one_div_of_lt (ENNReal.toReal_pos hp0.ne' hpTop) hreal)
  exact unifIntegrable_of_eLpNorm_two_bounded hp2.le hgap hf C hC

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A uniformly `L²`-bounded family of real functions is uniformly
integrable in `L¹`. -/
theorem unifIntegrable_one_of_eLpNorm_two_bounded
    {I : Type*} {f : I → W → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) 2 P ≤ (C : ℝ≥0∞)) :
    UnifIntegrable f 1 P := by
  exact unifIntegrable_of_eLpNorm_two_bounded
    (by norm_num) (by norm_num) hf C hC

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Uniform-partition Brownian left sums with a bounded measurable state
weight are uniformly integrable at every strictly positive exponent below
`2`. -/
theorem unifIntegrable_bounded_brownian_leftSum_of_lt_two
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) :
    UnifIntegrable
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) p P := by
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let C : ℝ≥0 :=
    ⟨(K : ℝ) * Real.sqrt (t : ℝ),
      mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)⟩
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg K hgK t (n + 1)
  have hSbound (n : ℕ) : eLpNorm (S n) 2 P ≤ (C : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (S n) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ))
    simpa only [S] using
      eLpNorm_bounded_brownian_leftSum_le_of_exponent_le_two
        (by norm_num) hB t g hg K hgK n
  simpa only [S] using unifIntegrable_of_eLpNorm_two_bounded_of_lt_two
    hp0 hp2 (fun n ↦ (hSmem n).1) C hSbound

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Uniform-partition Brownian left sums with a bounded measurable state
weight are uniformly integrable in `L¹`. -/
theorem unifIntegrable_bounded_brownian_leftSum
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) :
    UnifIntegrable
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) 1 P := by
  exact unifIntegrable_bounded_brownian_leftSum_of_lt_two
    (by norm_num) (by norm_num) hB t g hg K hgK

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- First-order Taylor sums with a globally bounded derivative are uniformly
integrable in `Lᵖ` for every `0 < p < 2`. -/
theorem unifIntegrable_firstOrderTaylorSum_of_deriv_bound_of_lt_two
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    UnifIntegrable
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) p P := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact unifIntegrable_bounded_brownian_leftSum_of_lt_two
    hp0 hp2 hB t (deriv f) hderiv.continuous.measurable K hderivK

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- First-order Taylor sums with a globally bounded derivative are uniformly
integrable in `L¹`. -/
theorem unifIntegrable_firstOrderTaylorSum_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    UnifIntegrable
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega)) 1 P := by
  exact unifIntegrable_firstOrderTaylorSum_of_deriv_bound_of_lt_two
    (by norm_num) (by norm_num) hB hf K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Uniform-partition Brownian left sums for a bounded `C¹` state weight
converge strongly in `Lᵖ` to their explicit antiderivative residual for
`1 ≤ p < 2`. -/
theorem brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            g (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ (∫ x in (0 : ℝ)..B t omega, g x) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv g (B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  let C : ℝ≥0 :=
    ⟨(K : ℝ) * Real.sqrt (t : ℝ),
      mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)⟩
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg.continuous.measurable K hgK t (n + 1)
  have hSbound (n : ℕ) : eLpNorm (S n) 2 P ≤ (C : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (S n) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ))
    simpa only [S] using
      eLpNorm_bounded_brownian_leftSum_le_of_exponent_le_two
        (by norm_num) hB t g hg.continuous.measurable K hgK n
  have hUI : UnifIntegrable S p P := by
    simpa only [S] using unifIntegrable_bounded_brownian_leftSum_of_lt_two
      (zero_lt_one.trans_le hp1) hp2 hB t g hg.continuous.measurable K hgK
  have hlimit : TendstoInMeasure P S Filter.atTop residual := by
    simpa only [S, residual] using
      brownian_contDiff_one_leftSum_tendstoInMeasure hB hg t
  have hresmem : MemLp residual p P := by
    have hresbound : eLpNorm residual 2 P ≤ (C : ℝ≥0∞) := by
      exact eLpNorm_le_of_tendstoInMeasure
        (C := (C : ℝ≥0∞)) (p := 2)
        (Filter.Eventually.of_forall hSbound) hlimit
        (fun n ↦ (hSmem n).1)
    have hresmem2 : MemLp residual 2 P :=
      ⟨hlimit.aestronglyMeasurable (fun n ↦ (hSmem n).1),
        hresbound.trans_lt ENNReal.coe_lt_top⟩
    exact hresmem2.mono_exponent hp2.le
  have hpTop : p ≠ ∞ := (hp2.trans (by finiteness)).ne
  have hvitali := tendsto_Lp_finite_of_tendstoInMeasure
    (p := p) hp1 hpTop
    (fun n ↦ (hSmem n).1) hresmem hUI hlimit
  simpa only [S, residual] using hvitali

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Uniform-partition Brownian left sums for a bounded `C¹` state weight
converge strongly in `L¹` to their explicit antiderivative residual. -/
theorem brownian_contDiff_one_leftSum_tendsto_eLpNorm_one
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            g (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ (∫ x in (0 : ℝ)..B t omega, g x) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv g (B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
    (by norm_num) (by norm_num) hB hg K hgK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, its uniform-partition first-order Taylor
sums converge strongly in `Lᵖ` to the Itô-formula residual for
`1 ≤ p < 2`. -/
theorem firstOrderTaylorSum_tendsto_eLpNorm_of_lt_two_of_deriv_bound
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ f (B t omega) - f 0 -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv (deriv f) (B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
      hp1 hp2 hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, its uniform-partition first-order Taylor
sums converge strongly in `L¹` to the Itô-formula residual. -/
theorem firstOrderTaylorSum_tendsto_eLpNorm_one_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ f (B t omega) - f 0 -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv (deriv f) (B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact firstOrderTaylorSum_tendsto_eLpNorm_of_lt_two_of_deriv_bound
    (by norm_num) (by norm_num) hB hf K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a bounded `C¹` state weight, a measurable candidate is the strong
`Lᵖ` limit of the Brownian left sums exactly when it agrees almost everywhere
with the explicit antiderivative residual, for `1 ≤ p < 2`. -/
theorem brownian_contDiff_one_leftSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0)
    (I : W → ℝ) (hI : AEStronglyMeasurable I P) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            g (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) - I) p P)
      Filter.atTop (nhds 0) ↔
      (fun omega ↦
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) =ᵐ[P] I := by
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg.continuous.measurable K hgK t (n + 1)
  have hstrongR : Filter.Tendsto
      (fun n ↦ eLpNorm (S n - residual) p P)
      Filter.atTop (nhds 0) := by
    simpa only [S, residual] using
      brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
        hp1 hp2 hB hg K hgK t
  change Filter.Tendsto (fun n ↦ eLpNorm (S n - I) p P)
      Filter.atTop (nhds 0) ↔ residual =ᵐ[P] I
  constructor
  · intro hstrongI
    have hprob : TendstoInMeasure P S Filter.atTop I := by
      exact tendstoInMeasure_of_tendsto_eLpNorm
        (p := p) (zero_lt_one.trans_le hp1).ne'
        (fun n ↦ (hSmem n).1) hI hstrongI
    exact (brownian_contDiff_one_leftSum_tendstoInMeasure_iff_ae_eq
      hB hg t I).mp (by simpa only [S] using hprob)
  · intro hRI
    have heq : (fun n ↦ eLpNorm (S n - I) p P) =
        (fun n ↦ eLpNorm (S n - residual) p P) := by
      funext n
      exact (eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hRI)).symm
    rw [heq]
    exact hstrongR

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a bounded `C¹` state weight, a measurable candidate is the strong
`L¹` limit of the Brownian left sums exactly when it agrees almost everywhere
with the explicit antiderivative residual. -/
theorem brownian_contDiff_one_leftSum_tendsto_eLpNorm_one_iff_ae_eq
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0)
    (I : W → ℝ) (hI : AEStronglyMeasurable I P) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            g (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) - I) 1 P)
      Filter.atTop (nhds 0) ↔
      (fun omega ↦
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) =ᵐ[P] I := by
  exact brownian_contDiff_one_leftSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two
    (by norm_num) (by norm_num) hB hg K hgK t I hI

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For `C²` functions with globally bounded first derivative, a measurable
candidate is the strong `Lᵖ` limit of the first-order Taylor sums exactly when
it agrees almost everywhere with the explicit Itô-formula residual, for
`1 ≤ p < 2`. -/
theorem firstOrderTaylorSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two_of_deriv_bound
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    (I : W → ℝ) (hI : AEStronglyMeasurable I P) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) - I) p P)
      Filter.atTop (nhds 0) ↔
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) =ᵐ[P] I := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    brownian_contDiff_one_leftSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two
      hp1 hp2 hB hderiv K hderivK t I hI

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For `C²` functions with globally bounded first derivative, a measurable
candidate is the strong `L¹` limit of the first-order Taylor sums exactly when
it agrees almost everywhere with the explicit Itô-formula residual. -/
theorem firstOrderTaylorSum_tendsto_eLpNorm_one_iff_ae_eq_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    (I : W → ℝ) (hI : AEStronglyMeasurable I P) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦
          ∑ i ∈ Finset.range (n + 1),
            deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega)) - I) 1 P)
      Filter.atTop (nhds 0) ↔
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) =ᵐ[P] I := by
  exact firstOrderTaylorSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two_of_deriv_bound
    (by norm_num) (by norm_num) hB hf K hderivK t I hI

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Any `Lᵖ` carrier sequence representing the bounded Brownian left sums
converges to a candidate carrier exactly when that carrier represents the
explicit residual almost everywhere, for `1 ≤ p < 2`. -/
theorem Lp_brownian_contDiff_one_leftSum_tendsto_iff_ae_eq_of_lt_two
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0)
    (S : ℕ → Lp ℝ p P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ p P) :
    Filter.Tendsto S Filter.atTop (nhds I) ↔
      (fun omega ↦
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) =ᵐ[P] (↑I : W → ℝ) := by
  let rawS : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hnormEq :
      (fun n ↦ eLpNorm ((↑(S n) : W → ℝ) - (↑I : W → ℝ)) p P) =
        (fun n ↦ eLpNorm (rawS n - (↑I : W → ℝ)) p P) := by
    funext n
    exact eLpNorm_congr_ae ((hS n).sub Filter.EventuallyEq.rfl)
  change Filter.Tendsto S Filter.atTop (nhds I) ↔
    residual =ᵐ[P] (↑I : W → ℝ)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' S I, hnormEq]
  simpa only [rawS, residual] using
    brownian_contDiff_one_leftSum_tendsto_eLpNorm_iff_ae_eq_of_lt_two
      Fact.out hp2 hB hg K hgK t (↑I : W → ℝ) (Lp.aestronglyMeasurable I)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Any `L¹` carrier sequence representing the bounded Brownian left sums
converges to a candidate carrier exactly when that carrier represents the
explicit residual almost everywhere. -/
theorem Lp_one_brownian_contDiff_one_leftSum_tendsto_iff_ae_eq
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0)
    (S : ℕ → Lp ℝ 1 P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ 1 P) :
    Filter.Tendsto S Filter.atTop (nhds I) ↔
      (fun omega ↦
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) =ᵐ[P] (↑I : W → ℝ) := by
  exact Lp_brownian_contDiff_one_leftSum_tendsto_iff_ae_eq_of_lt_two
    (by norm_num) hB hg K hgK t S hS I

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Any `Lᵖ` carrier sequence representing bounded-derivative `C²`
first-order Taylor sums converges to a candidate exactly when the candidate
represents the explicit Itô-formula residual almost everywhere, for
`1 ≤ p < 2`. -/
theorem Lp_firstOrderTaylorSum_tendsto_iff_ae_eq_of_lt_two_of_deriv_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    (S : ℕ → Lp ℝ p P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ p P) :
    Filter.Tendsto S Filter.atTop (nhds I) ↔
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) =ᵐ[P] (↑I : W → ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    Lp_brownian_contDiff_one_leftSum_tendsto_iff_ae_eq_of_lt_two
      hp2 hB hderiv K hderivK t S hS I

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Any `L¹` carrier sequence representing bounded-derivative `C²`
first-order Taylor sums converges to a candidate exactly when the candidate
represents the explicit Itô-formula residual almost everywhere. -/
theorem Lp_one_firstOrderTaylorSum_tendsto_iff_ae_eq_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    (S : ℕ → Lp ℝ 1 P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ 1 P) :
    Filter.Tendsto S Filter.atTop (nhds I) ↔
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) =ᵐ[P] (↑I : W → ℝ) := by
  exact Lp_firstOrderTaylorSum_tendsto_iff_ae_eq_of_lt_two_of_deriv_bound
    (by norm_num) hB hf K hderivK t S hS I

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A globally bounded `C¹` state weight has an explicit Brownian residual
whose `L²` norm is at most `K * sqrt t`. -/
theorem eLpNorm_brownian_contDiff_one_residual_le
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    eLpNorm
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  have hlimit : TendstoInMeasure P S Filter.atTop
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) := by
    simpa only [S] using brownian_contDiff_one_leftSum_tendstoInMeasure hB hg t
  have hmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg.continuous.measurable K hgK t (n + 1)
  apply eLpNorm_le_of_tendstoInMeasure
    (C := ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)))
    (p := 2) ?_ hlimit (fun n ↦ (hmem n).1)
  filter_upwards with n
  have hsq := eLpNorm_bounded_brownian_leftSum_toReal_sq_le
    hB t g hg.continuous.measurable K hgK n
  have hCnonneg : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm (S n) 2 P).toReal ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
    have hCsq : ((K : ℝ) * Real.sqrt (t : ℝ)) ^ 2 =
        (K : ℝ) ^ 2 * (t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
    apply (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).mp
    rw [hCsq]
    simpa only [S] using hsq
  exact (ENNReal.toReal_le_toReal (hmem n).eLpNorm_lt_top.ne
    ENNReal.ofReal_ne_top).mp (by
      simpa only [ENNReal.toReal_ofReal hCnonneg] using hreal)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit residual for a `C¹` Brownian state weight is an almost
everywhere strongly measurable random variable. -/
theorem aestronglyMeasurable_brownian_contDiff_one_residual
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) :
    AEStronglyMeasurable
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) P := by
  have hlimit := brownian_contDiff_one_leftSum_tendstoInMeasure hB hg t
  apply hlimit.aestronglyMeasurable
  intro n
  have hpre := hB.toIsPreBrownianReal
  have hsum := Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
    (fun i _hi => by
      have hweight := hg.continuous.measurable.comp_aemeasurable
        (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
      have hdelta :=
        (hpre.aemeasurable (uniformPartitionTime t (n + 1) (i + 1))).sub
          (hpre.aemeasurable (uniformPartitionTime t (n + 1) i))
      exact hweight.aestronglyMeasurable.mul hdelta.aestronglyMeasurable)
  convert hsum using 1
  funext omega
  simp only [Finset.sum_apply, Function.comp_apply, Pi.mul_apply, Pi.sub_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit residual selected by bounded `C¹` Brownian left sums has
expectation zero. -/
theorem integral_brownian_contDiff_one_residual_eq_zero
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega, (
      (∫ x in (0 : ℝ)..B t omega, g x) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv g (B s.toNNReal omega)) ∂P) = 0 := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg.continuous.measurable K hgK t (n + 1)
  have hL1 : Filter.Tendsto
      (fun n ↦ eLpNorm (S n - residual) 1 P)
      Filter.atTop (nhds 0) := by
    simpa only [S, residual] using
      brownian_contDiff_one_leftSum_tendsto_eLpNorm_one hB hg K hgK t
  have hintegral := tendsto_integral_of_L1' residual
    (by simpa only [residual] using
      aestronglyMeasurable_brownian_contDiff_one_residual hB hg t)
    (Filter.Eventually.of_forall
      (fun n ↦ (hSmem n).integrable (by norm_num))) hL1
  have hzero : Filter.Tendsto (fun n ↦ ∫ omega, S n omega ∂P)
      Filter.atTop (nhds 0) := by
    convert tendsto_const_nhds using 1
    funext n
    simpa only [S] using integral_bounded_brownian_leftSum_eq_zero
      hB t g hg.continuous.measurable K hgK n
  have hreszero : (∫ omega, residual omega ∂P) = 0 :=
    tendsto_nhds_unique hintegral hzero
  simpa only [residual] using hreszero

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A globally bounded `C¹` Brownian state weight has a square-integrable
explicit residual; no separate bound on its derivative is required. -/
theorem memLp_two_brownian_contDiff_one_residual_of_bound
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    MemLp
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) 2 P := by
  refine ⟨aestronglyMeasurable_brownian_contDiff_one_residual hB hg t, ?_⟩
  exact lt_of_le_of_lt
    (eLpNorm_brownian_contDiff_one_residual_le hB hg K hgK t)
    ENNReal.ofReal_lt_top

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- On Brownian probability space, the explicit residual of a globally
bounded `C¹` state weight belongs to every `Lᵖ` space below `L²`. -/
theorem memLp_brownian_contDiff_one_residual_of_exponent_le_two
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    MemLp
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) p P := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact (memLp_two_brownian_contDiff_one_residual_of_bound
    hB hg K hgK t).mono_exponent hp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The `K * sqrt t` bound for a bounded-`C¹` Brownian residual controls its
`Lᵖ` norm at every exponent at most two. -/
theorem eLpNorm_brownian_contDiff_one_residual_le_of_exponent_le_two
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    eLpNorm
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) p P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact (eLpNorm_le_eLpNorm_of_exponent_le hp
    (memLp_two_brownian_contDiff_one_residual_of_bound
      hB hg K hgK t).1).trans
    (eLpNorm_brownian_contDiff_one_residual_le hB hg K hgK t)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a sequence and a candidate limit with a.e. strongly measurable
representatives, convergence of their `L¹` seminorm error implies convergence
of their expected pointwise norm error. -/
theorem tendsto_integral_norm_sub_of_tendsto_eLpNorm_one
    {S : ℕ → W → ℝ} {R : W → ℝ}
    (hS : ∀ n, AEStronglyMeasurable (S n) P)
    (hR : AEStronglyMeasurable R P)
    (h : Filter.Tendsto (fun n ↦ eLpNorm (S n - R) 1 P)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ∫ omega, ‖S n omega - R omega‖ ∂P)
      Filter.atTop (nhds 0) := by
  have hreal : Filter.Tendsto
      (fun n ↦ (eLpNorm (S n - R) 1 P).toReal)
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (ENNReal.toReal ∘ fun n ↦ eLpNorm (S n - R) 1 P)
      Filter.atTop (nhds (ENNReal.toReal 0))
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have heq (n : ℕ) :
      (∫ omega, ‖S n omega - R omega‖ ∂P) =
        (eLpNorm (S n - R) 1 P).toReal := by
    simpa only [Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm] using
      integral_norm_eq_lintegral_enorm ((hS n).sub hR)
  simpa only [heq] using hreal

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a globally bounded `C¹` Brownian state weight, the expected absolute
error between the left sums and their explicit residual tends to zero. -/
theorem brownian_contDiff_one_leftSum_tendsto_integral_norm
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          g (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        ((∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  let S : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let R : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        (by norm_num) hB g hg.continuous.measurable K hgK t (n + 1)
  have hRmem : MemLp R 2 P := by
    simpa only [R] using
      memLp_two_brownian_contDiff_one_residual_of_bound hB hg K hgK t
  have hstrong : Filter.Tendsto
      (fun n ↦ eLpNorm (S n - R) 1 P) Filter.atTop (nhds 0) := by
    simpa only [S, R] using
      brownian_contDiff_one_leftSum_tendsto_eLpNorm_one hB hg K hgK t
  simpa only [S, R] using
    tendsto_integral_norm_sub_of_tendsto_eLpNorm_one
      (fun n ↦ (hSmem n).1) hRmem.1 hstrong

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, the expected absolute error between its
first-order Taylor sums and the explicit Itô residual tends to zero. -/
theorem firstOrderTaylorSum_tendsto_integral_norm_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        (f (B t omega) - f 0 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    brownian_contDiff_one_leftSum_tendsto_integral_norm
      hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The expected absolute value of the explicit residual selected by a
bounded `C¹` Brownian state weight is at most `K * sqrt t`. -/
theorem integral_norm_brownian_contDiff_one_residual_le
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega, ‖
      (∫ x in (0 : ℝ)..B t omega, g x) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv g (B s.toNNReal omega)‖ ∂P) ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let R : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hmem : MemLp R 1 P := by
    simpa only [R] using
      memLp_brownian_contDiff_one_residual_of_exponent_le_two
        (by norm_num) hB hg K hgK t
  have hbound : eLpNorm R 1 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
    simpa only [R] using
      eLpNorm_brownian_contDiff_one_residual_le_of_exponent_le_two
        (by norm_num) hB hg K hgK t
  have hC : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm R 1 P).toReal ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [ENNReal.toReal_ofReal hC] using htoReal
  calc
    (∫ omega, ‖R omega‖ ∂P) = (eLpNorm R 1 P).toReal := by
      simpa only [eLpNorm_one_eq_lintegral_enorm] using
        integral_norm_eq_lintegral_enorm hmem.1
    _ ≤ (K : ℝ) * Real.sqrt (t : ℝ) := hreal

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is bounded by `K`, the expected absolute value of the explicit
first-order Taylor residual is at most `K * sqrt t`. -/
theorem integral_norm_firstOrderTaylor_residual_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega, ‖f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega)‖ ∂P) ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    integral_norm_brownian_contDiff_one_residual_le
      hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The centered residual selected by a bounded `C¹` Brownian state weight
has variance at most `K² * t`. -/
theorem variance_brownian_contDiff_one_residual_le
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Var[fun omega ↦
      (∫ x in (0 : ℝ)..B t omega, g x) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv g (B s.toNNReal omega); P] ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hmem : MemLp residual 2 P := by
    simpa only [residual] using
      memLp_two_brownian_contDiff_one_residual_of_bound hB hg K hgK t
  have hmean : (∫ omega, residual omega ∂P) = 0 := by
    simpa only [residual] using
      integral_brownian_contDiff_one_residual_eq_zero hB hg K hgK t
  have hvar := variance_eq_sub hmem
  rw [hmean] at hvar
  norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hvar
  rw [show Var[residual; P] = (∫ omega, residual omega ^ 2 ∂P) from hvar]
  rw [integral_sq_eq_eLpNorm_toReal_sq hmem]
  have hbound := eLpNorm_brownian_contDiff_one_residual_le hB hg K hgK t
  have hCnonneg : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm residual 2 P).toReal ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [residual, ENNReal.toReal_ofReal hCnonneg] using htoReal
  calc
    (eLpNorm residual 2 P).toReal ^ 2 ≤
        ((K : ℝ) * Real.sqrt (t : ℝ)) ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).2 hreal
    _ = (K : ℝ) ^ 2 * (t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit residual selected by a bounded `C¹` Brownian state weight
has second moment at most `K² * t`. -/
theorem integral_sq_brownian_contDiff_one_residual_le
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega,
      ((∫ x in (0 : ℝ)..B t omega, g x) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv g (B s.toNNReal omega)) ^ 2 ∂P) ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let R : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hmem : MemLp R 2 P := by
    simpa only [R] using
      memLp_two_brownian_contDiff_one_residual_of_bound hB hg K hgK t
  have hmean : (∫ omega, R omega ∂P) = 0 := by
    simpa only [R] using
      integral_brownian_contDiff_one_residual_eq_zero hB hg K hgK t
  have hvarEq := variance_eq_sub hmem
  rw [hmean] at hvarEq
  norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hvarEq
  calc
    (∫ omega, R omega ^ 2 ∂P) = Var[R; P] := hvarEq.symm
    _ ≤ (K : ℝ) ^ 2 * (t : ℝ) :=
      variance_brownian_contDiff_one_residual_le hB hg K hgK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the explicit residual selected by a bounded
`C¹` Brownian state weight. -/
theorem measure_brownian_contDiff_one_residual_ge_le
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |(∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)|} ≤
      ENNReal.ofReal (((K : ℝ) ^ 2 * (t : ℝ)) / epsilon ^ 2) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let R : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hmem : MemLp R 2 P := by
    simpa only [R] using
      memLp_two_brownian_contDiff_one_residual_of_bound hB hg K hgK t
  have hmean : (∫ omega, R omega ∂P) = 0 := by
    simpa only [R] using
      integral_brownian_contDiff_one_residual_eq_zero hB hg K hgK t
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  rw [hmean] at hcheb
  simp only [sub_zero] at hcheb
  simp only [R] at hcheb
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact variance_brownian_contDiff_one_residual_le hB hg K hgK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, the explicit first-order Taylor residual is
square-integrable. -/
theorem memLp_two_firstOrderTaylor_residual_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    MemLp
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) 2 P := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    memLp_two_brownian_contDiff_one_residual_of_bound
      hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, the explicit first-order Taylor residual
belongs to every `Lᵖ` space with exponent at most two. -/
theorem memLp_firstOrderTaylor_residual_of_exponent_le_two_of_deriv_bound
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    MemLp
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) p P := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    memLp_brownian_contDiff_one_residual_of_exponent_le_two
      hp hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is bounded by `K`, the `L²` norm of the explicit first-order
Taylor residual is at most `K * sqrt t`. -/
theorem eLpNorm_firstOrderTaylor_residual_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    eLpNorm
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    eLpNorm_brownian_contDiff_one_residual_le hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is bounded by `K`, the explicit first-order Taylor residual has
`Lᵖ` norm at most `K * sqrt t` for every exponent at most two. -/
theorem eLpNorm_firstOrderTaylor_residual_le_of_exponent_le_two_of_deriv_bound
    {p : ℝ≥0∞} (hp : p ≤ 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    eLpNorm
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) p P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    eLpNorm_brownian_contDiff_one_residual_le_of_exponent_le_two
      hp hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is globally bounded, the explicit first-order Taylor residual is
centered. -/
theorem integral_firstOrderTaylor_residual_eq_zero_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega, (f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega)) ∂P) = 0 := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    integral_brownian_contDiff_one_residual_eq_zero
      hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is bounded by `K`, the variance of the explicit first-order
Taylor residual is at most `K² * t`. -/
theorem variance_firstOrderTaylor_residual_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    Var[fun omega ↦ f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega); P] ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    variance_brownian_contDiff_one_residual_le hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `f'` is bounded by `K`, the second moment of the explicit first-order
Taylor residual is at most `K² * t`. -/
theorem integral_sq_firstOrderTaylor_residual_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    (∫ omega, (f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega)) ^ 2 ∂P) ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    integral_sq_brownian_contDiff_one_residual_le
      hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the explicit first-order Taylor residual of a
`C²` function with globally bounded first derivative. -/
theorem measure_firstOrderTaylor_residual_ge_le_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega)|} ≤
      ENNReal.ofReal (((K : ℝ) ^ 2 * (t : ℝ)) / epsilon ^ 2) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    measure_brownian_contDiff_one_residual_ge_le
      hB hderiv K hderivK t hepsilon

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A bounded `C¹` state weight determines an `L²` random variable represented
almost everywhere by its explicit Brownian residual, with norm at most
`K * sqrt t`. -/
theorem exists_Lp_brownian_contDiff_one_residual_of_bound
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ R : Lp ℝ 2 P,
      ‖R‖ ≤ (K : ℝ) * Real.sqrt (t : ℝ) ∧
      ∀ᵐ omega ∂P,
        R omega =
          (∫ x in (0 : ℝ)..B t omega, g x) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv g (B s.toNNReal omega) := by
  let residual : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hmem : MemLp residual 2 P := by
    simpa only [residual] using
      memLp_two_brownian_contDiff_one_residual_of_bound hB hg K hgK t
  refine ⟨hmem.toLp residual, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    have hbound := eLpNorm_brownian_contDiff_one_residual_le hB hg K hgK t
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [residual,
      ENNReal.toReal_ofReal
        (mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _))] using hreal
  · filter_upwards [hmem.coeFn_toLp] with omega homega
    exact homega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a `C²` function with bounded first derivative, the stochastic term in
the Brownian Itô formula can be chosen as a centered `L²` random variable of
norm at most `K * sqrt t`. -/
theorem exists_centered_Lp_two_ito_formula_brownianMotion_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ I : Lp ℝ 2 P,
      ‖I‖ ≤ (K : ℝ) * Real.sqrt (t : ℝ) ∧
      (∫ omega, I omega ∂P) = 0 ∧
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  rcases exists_Lp_brownian_contDiff_one_residual_of_bound
      hB hderiv K hderivK t with ⟨I, hInorm, hI⟩
  have hmean :
      (∫ omega, ((∫ x in (0 : ℝ)..B t omega, deriv f x) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) ∂P) = 0 :=
    integral_brownian_contDiff_one_residual_eq_zero
      hB hderiv K hderivK t
  refine ⟨I, hInorm, (integral_congr_ae hI).trans hmean, ?_⟩
  filter_upwards [hI] with omega homega
  rw [hFTC] at homega
  linarith only [homega]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Bounded `C¹` Brownian left sums and their explicit residual admit
`Lᵖ` representatives whose carriers converge in the Banach-space topology,
for `1 ≤ p < 2`. -/
theorem exists_Lp_brownian_contDiff_one_leftSum_limit_of_lt_two
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ p P) (R : Lp ℝ p P),
      Filter.Tendsto S Filter.atTop (nhds R) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          g (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        R omega =
          (∫ x in (0 : ℝ)..B t omega, g x) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv g (B s.toNNReal omega) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let rawS : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
    g (B (uniformPartitionTime t (n + 1) i) omega) *
      (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
        B (uniformPartitionTime t (n + 1) i) omega)
  let rawR : W → ℝ := fun omega ↦
    (∫ x in (0 : ℝ)..B t omega, g x) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv g (B s.toNNReal omega)
  have hSmemP (n : ℕ) : MemLp (rawS n) p P := by
    simpa only [rawS] using
      memLp_bounded_brownian_leftSum_of_exponent_le_two
        hp2.le hB g hg.continuous.measurable K hgK t (n + 1)
  have hRmemP : MemLp rawR p P := by
    simpa only [rawR] using
      memLp_brownian_contDiff_one_residual_of_exponent_le_two
        hp2.le hB hg K hgK t
  let S : ℕ → Lp ℝ p P := fun n ↦ (hSmemP n).toLp (rawS n)
  let R : Lp ℝ p P := hRmemP.toLp rawR
  refine ⟨S, R, ?_, ?_, ?_⟩
  · have hnorm : Filter.Tendsto
        (fun n ↦ eLpNorm (rawS n - rawR) p P)
        Filter.atTop (nhds 0) := by
      simpa only [rawS, rawR] using
        brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
          Fact.out hp2 hB hg K hgK t
    simpa only [S, R] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' rawS hSmemP rawR hRmemP).2 hnorm
  · intro n
    filter_upwards [(hSmemP n).coeFn_toLp] with omega homega
    exact homega
  · filter_upwards [hRmemP.coeFn_toLp] with omega homega
    exact homega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Bounded `C¹` Brownian left sums and their explicit residual admit
`L¹` representatives whose carriers converge in the Banach-space topology. -/
theorem exists_Lp_one_brownian_contDiff_one_leftSum_limit
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (K : ℝ≥0) (hgK : ∀ x, |g x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ 1 P) (R : Lp ℝ 1 P),
      Filter.Tendsto S Filter.atTop (nhds R) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          g (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        R omega =
          (∫ x in (0 : ℝ)..B t omega, g x) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv g (B s.toNNReal omega) := by
  exact exists_Lp_brownian_contDiff_one_leftSum_limit_of_lt_two
    (by norm_num) hB hg K hgK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Bounded-derivative `C²` first-order Taylor sums and the explicit
Itô-formula residual admit `Lᵖ` representatives whose carriers converge,
for `1 ≤ p < 2`. -/
theorem exists_Lp_firstOrderTaylorSum_limit_of_lt_two_of_deriv_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ p P) (I : Lp ℝ p P),
      Filter.Tendsto S Filter.atTop (nhds I) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        I omega = f (B t omega) - f 0 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hFTC (z : ℝ) : (∫ x in (0 : ℝ)..z, deriv f x) = f z - f 0 := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable (by norm_num) |>.differentiableAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable 0 z)
  simpa only [hFTC] using
    exists_Lp_brownian_contDiff_one_leftSum_limit_of_lt_two
      hp2 hB hderiv K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Bounded-derivative `C²` first-order Taylor sums and the explicit
Itô-formula residual admit `L¹` representatives whose carriers converge. -/
theorem exists_Lp_one_firstOrderTaylorSum_limit_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ 1 P) (I : Lp ℝ 1 P),
      Filter.Tendsto S Filter.atTop (nhds I) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        I omega = f (B t omega) - f 0 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  exact exists_Lp_firstOrderTaylorSum_limit_of_lt_two_of_deriv_bound
    (by norm_num) hB hf K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a `C²` function with bounded first derivative, there are `Lᵖ`
carriers for the first-order Taylor sums and their limit such that the carriers
converge and the limit satisfies the Brownian Itô formula almost everywhere,
for `1 ≤ p < 2`. -/
theorem exists_Lp_ito_formula_brownianMotion_of_lt_two_of_deriv_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : p < 2)
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ p P) (I : Lp ℝ p P),
      Filter.Tendsto S Filter.atTop (nhds I) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  rcases exists_Lp_firstOrderTaylorSum_limit_of_lt_two_of_deriv_bound
      hp2 hB hf K hderivK t with ⟨S, I, hlimit, hS, hI⟩
  refine ⟨S, I, hlimit, hS, ?_⟩
  filter_upwards [hI] with omega homega
  linarith only [homega]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a `C²` function with bounded first derivative, there are `L¹`
carriers for the first-order Taylor sums and their limit such that the carriers
converge and the limit satisfies the Brownian Itô formula almost everywhere. -/
theorem exists_Lp_one_ito_formula_brownianMotion_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0) :
    ∃ (S : ℕ → Lp ℝ 1 P) (I : Lp ℝ 1 P),
      Filter.Tendsto S Filter.atTop (nhds I) ∧
      (∀ n, ∀ᵐ omega ∂P,
        S n omega = ∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) ∧
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  exact exists_Lp_ito_formula_brownianMotion_of_lt_two_of_deriv_bound
    (by norm_num) hB hf K hderivK t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If a `C¹` Brownian state weight and its derivative are globally bounded,
then its explicit residual is square-integrable. -/
theorem memLp_two_brownian_contDiff_one_residual
    (hB : IsBrownianMotion B P) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (Kg Kdg : ℝ≥0)
    (hg_bound : ∀ x, |g x| ≤ (Kg : ℝ))
    (hderiv_bound : ∀ x, |deriv g x| ≤ (Kdg : ℝ))
    (t : ℝ≥0) :
    MemLp
      (fun omega =>
        (∫ x in (0 : ℝ)..B t omega, g x) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv g (B s.toNNReal omega)) 2 P := by
  have _hderiv_bound_at_zero := hderiv_bound 0
  exact memLp_two_brownian_contDiff_one_residual_of_bound
    hB hg Kg hg_bound t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The Brownian left-endpoint sums for the identity integrand converge in
probability to the explicit value `(B_t² - t) / 2`. This is the concrete
partition-side form of `∫₀ᵗ B_s dB_s`. -/
theorem brownian_identity_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        B (uniformPartitionTime t (n + 1) i) omega *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega ↦ (B t omega ^ 2 - (t : ℝ)) / 2) := by
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2 / 2) := by
    fun_prop
  have hderiv : deriv (fun x : ℝ => x ^ 2 / 2) = fun x => x := by
    funext x
    have hx := ((hasDerivAt_pow 2 x).div_const 2).deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hx
    rw [hx]
    ring
  have hderivId : deriv (fun x : ℝ => x) = fun _ => 1 := by
    funext x
    exact hasDerivAt_id x |>.deriv
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hderivId] at h
  have hint : (∫ _s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ)) = (t : ℝ) := by
    rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_nonneg t))]
    simp only [sub_zero, smul_eq_mul, mul_one]
  apply h.congr_right
  filter_upwards with omega
  rw [hint]
  norm_num
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- More generally, Brownian left-endpoint sums for every affine state
integrand have their explicit Itô limit. -/
theorem brownian_affine_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (c0 c1 : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        (c0 + c1 * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega ↦
        c0 * B t omega + c1 * (B t omega ^ 2 - (t : ℝ)) / 2) := by
  have hf : ContDiff ℝ 2 (fun x : ℝ => c0 * x + c1 * x ^ 2 / 2) := by
    fun_prop
  have hderiv : deriv (fun x : ℝ => c0 * x + c1 * x ^ 2 / 2) =
      fun x => c0 + c1 * x := by
    funext x
    have hx : HasDerivAt (fun y : ℝ => c0 * y + c1 * y ^ 2 / 2)
        (c0 + c1 * x) x := by
      have hraw := ((hasDerivAt_id x).const_mul c0).add
        (((hasDerivAt_pow 2 x).const_mul c1).div_const 2)
      have hfun : ((fun y : ℝ => c0 * id y) +
          fun y : ℝ => c1 * y ^ 2 / 2) =
          (fun y : ℝ => c0 * y + c1 * y ^ 2 / 2) := by
        funext y
        rfl
      rw [hfun] at hraw
      norm_num only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one] at hraw
      have hcoef : c0 + c1 * (2 * x) / 2 = c0 + c1 * x := by
        ring
      rw [hcoef] at hraw
      exact hraw
    exact hx.deriv
  have hderivAffine : deriv (fun x : ℝ => c0 + c1 * x) = fun _ => c1 := by
    funext x
    have hx : HasDerivAt (fun y : ℝ => c0 + c1 * y) c1 x := by
      have hraw := (hasDerivAt_const (x := x) (c := c0)).add
        (hasDerivAt_const_mul (x := x) c1)
      have hfun : ((fun _ : ℝ => c0) + fun y : ℝ => c1 * y) =
          (fun y : ℝ => c0 + c1 * y) := by
        funext y
        rfl
      rw [hfun, zero_add] at hraw
      exact hraw
    exact hx.deriv
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hderivAffine] at h
  have hint : (∫ _s in Set.Icc (0 : ℝ) (t : ℝ), c1) = c1 * (t : ℝ) := by
    rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_nonneg t))]
    simp only [sub_zero, smul_eq_mul]
    ring
  apply h.congr_right
  filter_upwards with omega
  rw [hint]
  norm_num
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with quadratic state weight have the cubic
Itô limit, independently of the opaque stochastic-integral bridge. -/
theorem brownian_quadratic_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        B (uniformPartitionTime t (n + 1) i) omega ^ 2 *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => B t omega ^ 3 / 3 -
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ), B s.toNNReal omega) := by
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 3 / 3) := by
    fun_prop
  have hderiv : deriv (fun x : ℝ => x ^ 3 / 3) = fun x => x ^ 2 := by
    funext x
    have hx := ((hasDerivAt_pow 3 x).div_const 3).deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSubDiff] at hx
    rw [hx]
    ring
  have hderivSq : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    funext x
    have hx := (hasDerivAt_pow 2 x).deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at hx
    exact hx
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hderivSq] at h
  apply h.congr_right
  filter_upwards with omega
  rw [integral_const_mul]
  norm_num
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with state weight `B^(n+1)` have the
polynomial Itô limit for every natural `n`. -/
theorem brownian_polynomial_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (n : ℕ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        B (uniformPartitionTime t (k + 1) i) omega ^ (n + 1) *
          (B (uniformPartitionTime t (k + 1) (i + 1)) omega -
            B (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop (fun omega =>
        B t omega ^ (n + 2) / (n + 2 : ℕ) -
          ((n + 1 : ℕ) : ℝ) / 2 *
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), B s.toNNReal omega ^ n) := by
  let f : ℝ → ℝ := fun x => x ^ (n + 2) / (n + 2 : ℕ)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hden : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hderiv : deriv f = fun x => x ^ (n + 1) := by
    funext x
    have hx := ((hasDerivAt_pow (n + 2) x).div_const (n + 2 : ℕ)).deriv
    dsimp only [f]
    rw [show n + 2 - 1 = n + 1 by omega] at hx
    rw [hx]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp [hden]
  have hderivPow : deriv (fun x : ℝ => x ^ (n + 1)) =
      fun x => ((n + 1 : ℕ) : ℝ) * x ^ n := by
    funext x
    have hx := (hasDerivAt_pow (n + 1) x).deriv
    rw [show n + 1 - 1 = n by omega] at hx
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hderivPow] at h
  apply h.congr_right
  filter_upwards with omega
  rw [integral_const_mul]
  dsimp only [f]
  have hpow : 0 ^ (n + 2) = (0 : ℝ) := by
    rw [zero_pow]
    omega
  rw [hpow]
  field_simp [hden]
  ring

/-- The coefficientwise polynomial antiderivative with zero constant term. -/
noncomputable def polynomialAntiderivative (p : Polynomial ℝ) : Polynomial ℝ :=
  p.sum fun n a =>
    Polynomial.monomial (n + 1) (a / ((n + 1 : ℕ) : ℝ))

/-- Differentiating `polynomialAntiderivative p` recovers `p`. -/
theorem derivative_polynomialAntiderivative (p : Polynomial ℝ) :
    (polynomialAntiderivative p).derivative = p := by
  classical
  rw [polynomialAntiderivative, Polynomial.sum_def]
  simp only [map_sum]
  conv_rhs => rw [← p.sum_monomial_eq]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Polynomial.derivative_monomial, Nat.add_sub_cancel]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hn]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with an arbitrary polynomial state weight
have the Itô limit obtained from the zero-constant polynomial antiderivative. -/
theorem brownian_polynomialEval_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (p : Polynomial ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        p.eval (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        (polynomialAntiderivative p).eval (B t omega) -
          (polynomialAntiderivative p).eval 0 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            p.derivative.eval (B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => (polynomialAntiderivative p).eval x
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    induction polynomialAntiderivative p using Polynomial.induction_on' with
    | add q r hq hr => simpa using hq.add hr
    | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow n)
  have hderiv : deriv f = fun x => p.eval x := by
    funext x
    dsimp only [f]
    rw [Polynomial.deriv, derivative_polynomialAntiderivative]
  have hsecond : deriv (fun x : ℝ => p.eval x) =
      fun x => p.derivative.eval x := by
    funext x
    exact p.deriv
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  simpa only [f] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with exponential state weight have the
canonical exponential Itô limit, independently of the opaque
stochastic-integral bridge. -/
theorem brownian_exp_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.exp (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => Real.exp (B t omega) - 1 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          Real.exp (B s.toNNReal omega)) := by
  have hg : ContDiff ℝ 1 Real.exp := by
    fun_prop
  have h := brownian_contDiff_one_leftSum_tendstoInMeasure hB hg t
  rw [Real.deriv_exp] at h
  apply h.congr_right
  filter_upwards with omega
  rw [intervalIntegral.integral_deriv_eq_sub' Real.exp Real.deriv_exp]
  · simp only [Real.exp_zero]
  · exact fun _x _hx => Real.differentiableAt_exp
  · exact Real.continuous_exp.continuousOn

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums weighted by the derivative of
`exp (lambda * x)` have their exact Itô limit for every real scale `lambda`. -/
theorem brownian_scaledExpDerivative_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        (lambda * Real.exp
          (lambda * B (uniformPartitionTime t (n + 1) i) omega)) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.exp (lambda * B t omega) - 1 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda ^ 2 * Real.exp (lambda * B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => Real.exp (lambda * x)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f =
      fun x => lambda * Real.exp (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).exp
    dsimp only [f]
    rw [hx.deriv]
    ring
  have hsecond : deriv (fun x : ℝ =>
      lambda * Real.exp (lambda * x)) =
      fun x => lambda ^ 2 * Real.exp (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).exp
    have hscaled := hx.const_mul lambda
    rw [hscaled.deriv]
    ring
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  simpa only [f, mul_zero, Real.exp_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `exp (lambda B)` have their exact exponential Taylor-residual limit,
independently of the opaque stochastic-integral bridge. -/
theorem brownian_scaledExp_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) (hlambda : lambda ≠ 0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.exp (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.exp (lambda * B t omega) / lambda - 1 / lambda -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.exp (lambda * B s.toNNReal omega)) := by
  have hall :=
    brownian_scaledExpDerivative_leftSum_tendstoInMeasure hB t lambda
  have hscaled := hall.const_mul_real_noMeas (1 / lambda)
  apply hscaled.congr
  · intro n
    filter_upwards with omega
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hlambda]
  · filter_upwards with omega
    have hint :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda ^ 2 * Real.exp (lambda * B s.toNNReal omega)) =
        lambda * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.exp (lambda * B s.toNNReal omega) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [hint]
    field_simp [hlambda]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with cosine state weight have the canonical
trigonometric Itô limit, independently of the opaque stochastic-integral
bridge. -/
theorem brownian_cos_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.cos (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => Real.sin (B t omega) +
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          Real.sin (B s.toNNReal omega)) := by
  have hf : ContDiff ℝ 2 Real.sin := by
    fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x => -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderivSin, hderivCos] at h
  apply h.congr_right
  filter_upwards with omega
  rw [integral_neg]
  simp only [Real.sin_zero, sub_zero]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with cosine state weight converge strongly in
`Lᵖ` to their canonical trigonometric Itô residual for `1 ≤ p < 2`. -/
theorem brownian_cos_leftSum_tendsto_eLpNorm_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.cos (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ Real.sin (B t omega) +
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Real.sin (B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  have hf : ContDiff ℝ 2 Real.sin := by fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x ↦ -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have h := firstOrderTaylorSum_tendsto_eLpNorm_of_lt_two_of_deriv_bound
    hp1 hp2 hB hf 1 (fun x ↦ by
      rw [hderivSin]
      exact Real.abs_cos_le_one x) t
  rw [hderivSin, hderivCos] at h
  simpa only [Real.sin_zero, sub_zero, integral_neg, mul_neg,
    sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with cosine state weight converge strongly in
`L¹` to their canonical trigonometric Itô residual. -/
theorem brownian_cos_leftSum_tendsto_eLpNorm_one
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.cos (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ Real.sin (B t omega) +
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Real.sin (B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact brownian_cos_leftSum_tendsto_eLpNorm_of_lt_two
    (by norm_num) (by norm_num) hB t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The expected absolute error between cosine-weighted Brownian left sums
and their canonical trigonometric Itô residual tends to zero. -/
theorem brownian_cos_leftSum_tendsto_integral_norm
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          Real.cos (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        (Real.sin (B t omega) +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            Real.sin (B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  have hf : ContDiff ℝ 2 Real.sin := by fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x ↦ -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have h := firstOrderTaylorSum_tendsto_integral_norm_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderivSin]
      exact Real.abs_cos_le_one x) t
  rw [hderivSin, hderivCos] at h
  simpa only [Real.sin_zero, sub_zero, integral_neg, mul_neg,
    sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit stochastic term for the sine Itô formula, obtained from
cosine-weighted Brownian left sums, has mean zero. -/
theorem integral_brownian_cos_residual_eq_zero
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    (∫ omega, (Real.sin (B t omega) +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.sin (B s.toNNReal omega)) ∂P) = 0 := by
  have hg : ContDiff ℝ 1 Real.cos := by fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x ↦ -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have hfSin : ContDiff ℝ 1 Real.sin := by fun_prop
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, Real.cos x) = Real.sin z := by
    rw [← hderivSin, intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ Real.differentiable_sin.differentiableAt)
      (hfSin.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [Real.sin_zero, sub_zero]
  have h := integral_brownian_contDiff_one_residual_eq_zero
    hB hg 1 (fun x ↦ Real.abs_cos_le_one x) t
  rw [hderivCos] at h
  simpa only [hprimitive, integral_neg, mul_neg, sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit stochastic term for the sine Itô formula has variance at
most `t`. -/
theorem variance_brownian_cos_residual_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Var[fun omega ↦ Real.sin (B t omega) +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.sin (B s.toNNReal omega); P] ≤ (t : ℝ) := by
  have hg : ContDiff ℝ 1 Real.cos := by fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x ↦ -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have hfSin : ContDiff ℝ 1 Real.sin := by fun_prop
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, Real.cos x) = Real.sin z := by
    rw [← hderivSin, intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ Real.differentiable_sin.differentiableAt)
      (hfSin.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [Real.sin_zero, sub_zero]
  have h := variance_brownian_contDiff_one_residual_le
    hB hg 1 (fun x ↦ Real.abs_cos_le_one x) t
  rw [hderivCos] at h
  simpa only [hprimitive, integral_neg, mul_neg, sub_neg_eq_add,
    NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the canonical residual selected by
cosine-weighted Brownian left sums. -/
theorem measure_brownian_cos_residual_ge_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |Real.sin (B t omega) +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.sin (B s.toNNReal omega)|} ≤
      ENNReal.ofReal ((t : ℝ) / epsilon ^ 2) := by
  have hf : ContDiff ℝ 2 Real.sin := by fun_prop
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hderivCos : deriv Real.cos = fun x ↦ -Real.sin x := by
    funext x
    exact Real.hasDerivAt_cos x |>.deriv
  have h := measure_firstOrderTaylor_residual_ge_le_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderivSin]
      exact Real.abs_cos_le_one x) t hepsilon
  rw [hderivSin, hderivCos] at h
  simpa only [Real.sin_zero, sub_zero, integral_neg, mul_neg,
    sub_neg_eq_add, NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums weighted by the derivative of
`sin (lambda * x)` have their exact Itô limit for every real scale `lambda`. -/
theorem brownian_scaledSinDerivative_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        (lambda * Real.cos
          (lambda * B (uniformPartitionTime t (n + 1) i) omega)) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.sin (lambda * B t omega) +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda ^ 2 * Real.sin (lambda * B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => Real.sin (lambda * x)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f =
      fun x => lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    dsimp only [f]
    rw [hx.deriv]
    ring
  have hsecond : deriv (fun x : ℝ =>
      lambda * Real.cos (lambda * x)) =
      fun x => -(lambda ^ 2 * Real.sin (lambda * x)) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    have hscaled := hx.const_mul lambda
    rw [hscaled.deriv]
    ring
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  apply h.congr_right
  filter_upwards with omega
  rw [integral_neg]
  simp only [f, mul_zero, Real.sin_zero, sub_zero]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `cos (lambda B)` have their exact trigonometric residual limit. -/
theorem brownian_scaledCos_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.cos (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.sin (lambda * B t omega) / lambda +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.sin (lambda * B s.toNNReal omega)) := by
  have hall :=
    brownian_scaledSinDerivative_leftSum_tendstoInMeasure hB t lambda
  have hscaled := hall.const_mul_real_noMeas (1 / lambda)
  apply hscaled.congr
  · intro n
    filter_upwards with omega
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hlambda]
  · filter_upwards with omega
    have hint :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda ^ 2 * Real.sin (lambda * B s.toNNReal omega)) =
        lambda * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [hint]
    field_simp [hlambda]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `cos (lambda B)` converge strongly in `Lᵖ` to their exact residual
for `1 ≤ p < 2`. -/
theorem brownian_scaledCos_leftSum_tendsto_eLpNorm_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.cos (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ Real.sin (lambda * B t omega) / lambda +
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              lambda * Real.sin (lambda * B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℝ := fun x ↦ Real.cos (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_cos_le_one _
  have hderiv : deriv g = fun x ↦ -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) = Real.sin (lambda * z) / lambda := by
    let F : ℝ → ℝ := fun x ↦ Real.sin (lambda * x) / lambda
    have hF : ContDiff ℝ 1 F := by
      dsimp only [F]
      fun_prop
    have hFderiv : deriv F = g := by
      funext x
      have hx := (hasDerivAt_const_mul (x := x) lambda).sin
      have hx' := hx.div_const lambda
      dsimp only [F, g]
      rw [hx'.deriv]
      field_simp [hlambda]
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [F, mul_zero, Real.sin_zero, zero_div, sub_zero]
  have h := brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
    hp1 hp2 hB hg 1 hgK t
  rw [hderiv] at h
  have hint (omega : W) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        -lambda * Real.sin (lambda * B s.toNNReal omega)) =
        -(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with s
    ring
  simpa only [g, hprimitive, hint, mul_neg, sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `cos (lambda B)` converge strongly in `L¹` to their exact residual. -/
theorem brownian_scaledCos_leftSum_tendsto_eLpNorm_one
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.cos (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ Real.sin (lambda * B t omega) / lambda +
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              lambda * Real.sin (lambda * B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact brownian_scaledCos_leftSum_tendsto_eLpNorm_of_lt_two
    (by norm_num) (by norm_num) hB t lambda hlambda

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the expected absolute error between
`cos (lambda * B)`-weighted Brownian left sums and their explicit residual
tends to zero. -/
theorem brownian_scaledCos_leftSum_tendsto_integral_norm
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          Real.cos (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        (Real.sin (lambda * B t omega) / lambda +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.sin (lambda * B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℝ := fun x ↦ Real.cos (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_cos_le_one _
  have hderiv : deriv g = fun x ↦ -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) = Real.sin (lambda * z) / lambda := by
    let F : ℝ → ℝ := fun x ↦ Real.sin (lambda * x) / lambda
    have hF : ContDiff ℝ 1 F := by
      dsimp only [F]
      fun_prop
    have hFderiv : deriv F = g := by
      funext x
      have hx := (hasDerivAt_const_mul (x := x) lambda).sin
      have hx' := hx.div_const lambda
      dsimp only [F, g]
      rw [hx'.deriv]
      field_simp [hlambda]
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [F, mul_zero, Real.sin_zero, zero_div, sub_zero]
  have h := brownian_contDiff_one_leftSum_tendsto_integral_norm
    hB hg 1 hgK t
  rw [hderiv] at h
  have hint (omega : W) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        -lambda * Real.sin (lambda * B s.toNNReal omega)) =
        -(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with s
    ring
  simpa only [g, hprimitive, hint, mul_neg, sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the explicit residual selected by
`cos (lambda * B)`-weighted Brownian left sums has mean zero. -/
theorem integral_brownian_scaledCos_residual_eq_zero
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    (∫ omega, (Real.sin (lambda * B t omega) / lambda +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        lambda * Real.sin (lambda * B s.toNNReal omega)) ∂P) = 0 := by
  let g : ℝ → ℝ := fun x ↦ Real.cos (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_cos_le_one _
  have hderiv : deriv g = fun x ↦ -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) = Real.sin (lambda * z) / lambda := by
    let F : ℝ → ℝ := fun x ↦ Real.sin (lambda * x) / lambda
    have hF : ContDiff ℝ 1 F := by
      dsimp only [F]
      fun_prop
    have hFderiv : deriv F = g := by
      funext x
      have hx := (hasDerivAt_const_mul (x := x) lambda).sin
      have hx' := hx.div_const lambda
      dsimp only [F, g]
      rw [hx'.deriv]
      field_simp [hlambda]
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [F, mul_zero, Real.sin_zero, zero_div, sub_zero]
  have h := integral_brownian_contDiff_one_residual_eq_zero
    hB hg 1 hgK t
  rw [hderiv] at h
  have hint (omega : W) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        -lambda * Real.sin (lambda * B s.toNNReal omega)) =
        -(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with s
    ring
  simpa only [g, hprimitive, hint, mul_neg, sub_neg_eq_add] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the explicit residual selected by
`cos (lambda * B)`-weighted Brownian left sums has variance at most `t`. -/
theorem variance_brownian_scaledCos_residual_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Var[fun omega ↦ Real.sin (lambda * B t omega) / lambda +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        lambda * Real.sin (lambda * B s.toNNReal omega); P] ≤
      (t : ℝ) := by
  let g : ℝ → ℝ := fun x ↦ Real.cos (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_cos_le_one _
  have hderiv : deriv g = fun x ↦ -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) = Real.sin (lambda * z) / lambda := by
    let F : ℝ → ℝ := fun x ↦ Real.sin (lambda * x) / lambda
    have hF : ContDiff ℝ 1 F := by
      dsimp only [F]
      fun_prop
    have hFderiv : deriv F = g := by
      funext x
      have hx := (hasDerivAt_const_mul (x := x) lambda).sin
      have hx' := hx.div_const lambda
      dsimp only [F, g]
      rw [hx'.deriv]
      field_simp [hlambda]
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [F, mul_zero, Real.sin_zero, zero_div, sub_zero]
  have h := variance_brownian_contDiff_one_residual_le
    hB hg 1 hgK t
  rw [hderiv] at h
  have hint (omega : W) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        -lambda * Real.sin (lambda * B s.toNNReal omega)) =
        -(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with s
    ring
  simpa only [g, hprimitive, hint, mul_neg, sub_neg_eq_add,
    NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the residual selected by
`cos (lambda * B)`-weighted Brownian left sums. -/
theorem measure_brownian_scaledCos_residual_ge_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |Real.sin (lambda * B t omega) / lambda +
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        lambda * Real.sin (lambda * B s.toNNReal omega)|} ≤
      ENNReal.ofReal ((t : ℝ) / epsilon ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ Real.sin (lambda * x) / lambda
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = fun x ↦ Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    have hx' := hx.div_const lambda
    dsimp only [f]
    rw [hx'.deriv]
    field_simp [hlambda]
  have hsecond : deriv (fun x : ℝ ↦ Real.cos (lambda * x)) =
      fun x ↦ -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    rw [hx.deriv]
    ring
  have h := measure_firstOrderTaylor_residual_ge_le_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderiv]
      exact Real.abs_cos_le_one _) t hepsilon
  rw [hderiv, hsecond] at h
  have hint (omega : W) :
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        -lambda * Real.sin (lambda * B s.toNNReal omega)) =
        -(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sin (lambda * B s.toNNReal omega)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with s
    ring
  simpa only [f, mul_zero, Real.sin_zero, zero_div, sub_zero, hint,
    mul_neg, sub_neg_eq_add, NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with sine state weight have the canonical
trigonometric Itô limit, independently of the opaque stochastic-integral
bridge. -/
theorem brownian_sin_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.sin (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => 1 - Real.cos (B t omega) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          Real.cos (B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => 1 - Real.cos x
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ => 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hderivSin] at h
  simpa only [f, Real.cos_zero, sub_self, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit stochastic term for the cosine Itô formula, obtained from
sine-weighted Brownian left sums, has mean zero. -/
theorem integral_brownian_sin_residual_eq_zero
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    (∫ omega, (1 - Real.cos (B t omega) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.cos (B s.toNNReal omega)) ∂P) = 0 := by
  let f : ℝ → ℝ := fun x ↦ 1 - Real.cos x
  have hf : ContDiff ℝ 1 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ ↦ 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, Real.sin x) = 1 - Real.cos z := by
    rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable_one.differentiableAt)
      (hf.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [f, Real.cos_zero, sub_self, sub_zero]
  have hg : ContDiff ℝ 1 Real.sin := by fun_prop
  have h := integral_brownian_contDiff_one_residual_eq_zero
    hB hg 1 (fun x ↦ Real.abs_sin_le_one x) t
  rw [hderivSin] at h
  simpa only [hprimitive] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The explicit stochastic term for the cosine Itô formula has variance at
most `t`. -/
theorem variance_brownian_sin_residual_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Var[fun omega ↦ 1 - Real.cos (B t omega) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.cos (B s.toNNReal omega); P] ≤ (t : ℝ) := by
  let f : ℝ → ℝ := fun x ↦ 1 - Real.cos x
  have hf : ContDiff ℝ 1 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ ↦ 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, Real.sin x) = 1 - Real.cos z := by
    rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hf.differentiable_one.differentiableAt)
      (hf.continuous_deriv_one.intervalIntegrable 0 z)]
    simp only [f, Real.cos_zero, sub_self, sub_zero]
  have hg : ContDiff ℝ 1 Real.sin := by fun_prop
  have h := variance_brownian_contDiff_one_residual_le
    hB hg 1 (fun x ↦ Real.abs_sin_le_one x) t
  rw [hderivSin] at h
  simpa only [hprimitive, NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the canonical residual selected by
sine-weighted Brownian left sums. -/
theorem measure_brownian_sin_residual_ge_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |1 - Real.cos (B t omega) -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        Real.cos (B s.toNNReal omega)|} ≤
      ENNReal.ofReal ((t : ℝ) / epsilon ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ 1 - Real.cos x
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ ↦ 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have h := measure_firstOrderTaylor_residual_ge_le_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderiv]
      exact Real.abs_sin_le_one x) t hepsilon
  rw [hderiv, hderivSin] at h
  simpa only [f, Real.cos_zero, sub_self, sub_zero, NNReal.coe_one,
    one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with sine state weight converge strongly in
`Lᵖ` to their canonical trigonometric Itô residual for `1 ≤ p < 2`. -/
theorem brownian_sin_leftSum_tendsto_eLpNorm_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.sin (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ 1 - Real.cos (B t omega) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Real.cos (B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x ↦ 1 - Real.cos x
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ ↦ 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have h := firstOrderTaylorSum_tendsto_eLpNorm_of_lt_two_of_deriv_bound
    hp1 hp2 hB hf 1 (fun x ↦ by
      rw [hderiv]
      exact Real.abs_sin_le_one x) t
  rw [hderiv, hderivSin] at h
  simpa only [f, Real.cos_zero, sub_self, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with sine state weight converge strongly in
`L¹` to their canonical trigonometric Itô residual. -/
theorem brownian_sin_leftSum_tendsto_eLpNorm_one
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.sin (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ 1 - Real.cos (B t omega) -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Real.cos (B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact brownian_sin_leftSum_tendsto_eLpNorm_of_lt_two
    (by norm_num) (by norm_num) hB t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The expected absolute error between sine-weighted Brownian left sums
and their canonical trigonometric Itô residual tends to zero. -/
theorem brownian_sin_leftSum_tendsto_integral_norm
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          Real.sin (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        (1 - Real.cos (B t omega) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            Real.cos (B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x ↦ 1 - Real.cos x
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = Real.sin := by
    funext x
    have hx := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_cos x)
    change deriv ((fun _ : ℝ ↦ 1) - Real.cos) x = Real.sin x
    rw [hx.deriv]
    ring
  have hderivSin : deriv Real.sin = Real.cos := by
    funext x
    exact Real.hasDerivAt_sin x |>.deriv
  have h := firstOrderTaylorSum_tendsto_integral_norm_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderiv]
      exact Real.abs_sin_le_one x) t
  rw [hderiv, hderivSin] at h
  simpa only [f, Real.cos_zero, sub_self, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums weighted by the derivative of
`cos (lambda * x)` have their exact Itô limit for every real scale `lambda`. -/
theorem brownian_scaledCosDerivative_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        ((-lambda) * Real.sin
          (lambda * B (uniformPartitionTime t (n + 1) i) omega)) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.cos (lambda * B t omega) - 1 +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda ^ 2 * Real.cos (lambda * B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => Real.cos (lambda * x)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f =
      fun x => -lambda * Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    dsimp only [f]
    rw [hx.deriv]
    ring
  have hsecond : deriv (fun x : ℝ =>
      -lambda * Real.sin (lambda * x)) =
      fun x => -(lambda ^ 2 * Real.cos (lambda * x)) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    have hscaled := hx.const_mul (-lambda)
    rw [hscaled.deriv]
    ring
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  apply h.congr_right
  filter_upwards with omega
  rw [integral_neg]
  simp only [f, mul_zero, Real.cos_zero]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `sin (lambda B)` have their exact trigonometric residual limit. -/
theorem brownian_scaledSin_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.sin (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        1 / lambda - Real.cos (lambda * B t omega) / lambda -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.cos (lambda * B s.toNNReal omega)) := by
  have hall :=
    brownian_scaledCosDerivative_leftSum_tendstoInMeasure hB t lambda
  have hscaled := hall.const_mul_real_noMeas (-1 / lambda)
  apply hscaled.congr
  · intro n
    filter_upwards with omega
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hlambda]
  · filter_upwards with omega
    have hint :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda ^ 2 * Real.cos (lambda * B s.toNNReal omega)) =
        lambda * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.cos (lambda * B s.toNNReal omega) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [hint]
    field_simp [hlambda]
    ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `sin (lambda B)` converge strongly in `Lᵖ` to their exact residual
for `1 ≤ p < 2`. -/
theorem brownian_scaledSin_leftSum_tendsto_eLpNorm_of_lt_two
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.sin (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ 1 / lambda - Real.cos (lambda * B t omega) / lambda -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              lambda * Real.cos (lambda * B s.toNNReal omega)) p P)
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℝ := fun x ↦ Real.sin (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_sin_le_one _
  have hderiv : deriv g = fun x ↦ lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) =
        1 / lambda - Real.cos (lambda * z) / lambda := by
    let H : ℝ → ℝ := (fun _ ↦ 1) - fun x ↦ Real.cos (lambda * x)
    let F : ℝ → ℝ := fun x ↦ H x / lambda
    have hH : ContDiff ℝ 1 H := by
      change ContDiff ℝ 1 (fun x ↦ 1 - Real.cos (lambda * x))
      fun_prop
    have hF : ContDiff ℝ 1 F := by
      change ContDiff ℝ 1 (fun x ↦ H x / lambda)
      exact hH.div_const lambda
    have hFderiv : deriv F = g := by
      funext x
      have hx : HasDerivAt H
          (0 - -Real.sin (lambda * x) * lambda) x := by
        exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
          ((hasDerivAt_const_mul (x := x) lambda).cos)
      have hx' := hx.div_const lambda
      change deriv (fun y ↦ H y / lambda) x = g x
      rw [hx'.deriv]
      dsimp only [g]
      field_simp [hlambda]
      ring
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    change (1 - Real.cos (lambda * z)) / lambda -
      (1 - Real.cos (lambda * 0)) / lambda =
        1 / lambda - Real.cos (lambda * z) / lambda
    rw [mul_zero, Real.cos_zero]
    field_simp [hlambda]
    ring
  have h := brownian_contDiff_one_leftSum_tendsto_eLpNorm_of_lt_two
    hp1 hp2 hB hg 1 hgK t
  rw [hderiv] at h
  simpa only [g, hprimitive] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `sin (lambda B)` converge strongly in `L¹` to their exact residual. -/
theorem brownian_scaledSin_leftSum_tendsto_eLpNorm_one
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        ((fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          Real.sin (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
          fun omega ↦ 1 / lambda - Real.cos (lambda * B t omega) / lambda -
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              lambda * Real.cos (lambda * B s.toNNReal omega)) 1 P)
      Filter.atTop (nhds 0) := by
  exact brownian_scaledSin_leftSum_tendsto_eLpNorm_of_lt_two
    (by norm_num) (by norm_num) hB t lambda hlambda

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the expected absolute error between
`sin (lambda * B)`-weighted Brownian left sums and their explicit residual
tends to zero. -/
theorem brownian_scaledSin_leftSum_tendsto_integral_norm
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, ‖
        (∑ i ∈ Finset.range (n + 1),
          Real.sin (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega)) -
        (1 / lambda - Real.cos (lambda * B t omega) / lambda -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.cos (lambda * B s.toNNReal omega))‖ ∂P)
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℝ := fun x ↦ Real.sin (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_sin_le_one _
  have hderiv : deriv g = fun x ↦ lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) =
        1 / lambda - Real.cos (lambda * z) / lambda := by
    let H : ℝ → ℝ := (fun _ ↦ 1) - fun x ↦ Real.cos (lambda * x)
    let F : ℝ → ℝ := fun x ↦ H x / lambda
    have hH : ContDiff ℝ 1 H := by
      change ContDiff ℝ 1 (fun x ↦ 1 - Real.cos (lambda * x))
      fun_prop
    have hF : ContDiff ℝ 1 F := by
      change ContDiff ℝ 1 (fun x ↦ H x / lambda)
      exact hH.div_const lambda
    have hFderiv : deriv F = g := by
      funext x
      have hx : HasDerivAt H
          (0 - -Real.sin (lambda * x) * lambda) x := by
        exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
          ((hasDerivAt_const_mul (x := x) lambda).cos)
      have hx' := hx.div_const lambda
      change deriv (fun y ↦ H y / lambda) x = g x
      rw [hx'.deriv]
      dsimp only [g]
      field_simp [hlambda]
      ring
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    change (1 - Real.cos (lambda * z)) / lambda -
      (1 - Real.cos (lambda * 0)) / lambda =
        1 / lambda - Real.cos (lambda * z) / lambda
    rw [mul_zero, Real.cos_zero]
    field_simp [hlambda]
    ring
  have h := brownian_contDiff_one_leftSum_tendsto_integral_norm
    hB hg 1 hgK t
  rw [hderiv] at h
  simpa only [g, hprimitive] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the explicit residual selected by
`sin (lambda * B)`-weighted Brownian left sums has mean zero. -/
theorem integral_brownian_scaledSin_residual_eq_zero
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    (∫ omega, (1 / lambda - Real.cos (lambda * B t omega) / lambda -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        lambda * Real.cos (lambda * B s.toNNReal omega)) ∂P) = 0 := by
  let g : ℝ → ℝ := fun x ↦ Real.sin (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_sin_le_one _
  have hderiv : deriv g = fun x ↦ lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) =
        1 / lambda - Real.cos (lambda * z) / lambda := by
    let H : ℝ → ℝ := (fun _ ↦ 1) - fun x ↦ Real.cos (lambda * x)
    let F : ℝ → ℝ := fun x ↦ H x / lambda
    have hH : ContDiff ℝ 1 H := by
      change ContDiff ℝ 1 (fun x ↦ 1 - Real.cos (lambda * x))
      fun_prop
    have hF : ContDiff ℝ 1 F := by
      change ContDiff ℝ 1 (fun x ↦ H x / lambda)
      exact hH.div_const lambda
    have hFderiv : deriv F = g := by
      funext x
      have hx : HasDerivAt H
          (0 - -Real.sin (lambda * x) * lambda) x := by
        exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
          ((hasDerivAt_const_mul (x := x) lambda).cos)
      have hx' := hx.div_const lambda
      change deriv (fun y ↦ H y / lambda) x = g x
      rw [hx'.deriv]
      dsimp only [g]
      field_simp [hlambda]
      ring
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    change (1 - Real.cos (lambda * z)) / lambda -
      (1 - Real.cos (lambda * 0)) / lambda =
        1 / lambda - Real.cos (lambda * z) / lambda
    rw [mul_zero, Real.cos_zero]
    field_simp [hlambda]
    ring
  have h := integral_brownian_contDiff_one_residual_eq_zero
    hB hg 1 hgK t
  rw [hderiv] at h
  simpa only [g, hprimitive] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale, the explicit residual selected by
`sin (lambda * B)`-weighted Brownian left sums has variance at most `t`. -/
theorem variance_brownian_scaledSin_residual_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    Var[fun omega ↦
      1 / lambda - Real.cos (lambda * B t omega) / lambda -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.cos (lambda * B s.toNNReal omega); P] ≤
      (t : ℝ) := by
  let g : ℝ → ℝ := fun x ↦ Real.sin (lambda * x)
  have hg : ContDiff ℝ 1 g := by
    dsimp only [g]
    fun_prop
  have hgK (x : ℝ) : |g x| ≤ (1 : ℝ) := by
    dsimp only [g]
    exact Real.abs_sin_le_one _
  have hderiv : deriv g = fun x ↦ lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    dsimp only [g]
    rw [hx.deriv]
    ring
  have hprimitive (z : ℝ) :
      (∫ x in (0 : ℝ)..z, g x) =
        1 / lambda - Real.cos (lambda * z) / lambda := by
    let H : ℝ → ℝ := (fun _ ↦ 1) - fun x ↦ Real.cos (lambda * x)
    let F : ℝ → ℝ := fun x ↦ H x / lambda
    have hH : ContDiff ℝ 1 H := by
      change ContDiff ℝ 1 (fun x ↦ 1 - Real.cos (lambda * x))
      fun_prop
    have hF : ContDiff ℝ 1 F := by
      change ContDiff ℝ 1 (fun x ↦ H x / lambda)
      exact hH.div_const lambda
    have hFderiv : deriv F = g := by
      funext x
      have hx : HasDerivAt H
          (0 - -Real.sin (lambda * x) * lambda) x := by
        exact (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
          ((hasDerivAt_const_mul (x := x) lambda).cos)
      have hx' := hx.div_const lambda
      change deriv (fun y ↦ H y / lambda) x = g x
      rw [hx'.deriv]
      dsimp only [g]
      field_simp [hlambda]
      ring
    rw [← hFderiv]
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun _ _ ↦ hF.differentiable_one.differentiableAt)
      (hF.continuous_deriv_one.intervalIntegrable 0 z)]
    change (1 - Real.cos (lambda * z)) / lambda -
      (1 - Real.cos (lambda * 0)) / lambda =
        1 / lambda - Real.cos (lambda * z) / lambda
    rw [mul_zero, Real.cos_zero]
    field_simp [hlambda]
    ring
  have h := variance_brownian_contDiff_one_residual_le
    hB hg 1 hgK t
  rw [hderiv] at h
  simpa only [g, hprimitive, NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Chebyshev's inequality for the residual selected by
`sin (lambda * B)`-weighted Brownian left sums. -/
theorem measure_brownian_scaledSin_residual_ge_le
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P {omega | epsilon ≤ |1 / lambda - Real.cos (lambda * B t omega) / lambda -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        lambda * Real.cos (lambda * B s.toNNReal omega)|} ≤
      ENNReal.ofReal ((t : ℝ) / epsilon ^ 2) := by
  let f : ℝ → ℝ := fun x ↦ 1 / lambda - Real.cos (lambda * x) / lambda
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f = fun x ↦ Real.sin (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cos
    have hx' := hx.div_const lambda
    have hconst := hasDerivAt_const (x := x) (c := 1 / lambda)
    have hsub := hconst.sub hx'
    change deriv ((fun _ : ℝ ↦ 1 / lambda) -
      fun y ↦ Real.cos (lambda * y) / lambda) x =
        Real.sin (lambda * x)
    rw [hsub.deriv]
    field_simp [hlambda]
    ring
  have hsecond : deriv (fun x : ℝ ↦ Real.sin (lambda * x)) =
      fun x ↦ lambda * Real.cos (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sin
    rw [hx.deriv]
    ring
  have h := measure_firstOrderTaylor_residual_ge_le_of_deriv_bound
    hB hf 1 (fun x ↦ by
      rw [hderiv]
      exact Real.abs_sin_le_one _) t hepsilon
  rw [hderiv, hsecond] at h
  simpa only [f, mul_zero, Real.cos_zero, sub_self, sub_zero,
    NNReal.coe_one, one_pow, one_mul] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with hyperbolic-cosine state weight have the
canonical hyperbolic Itô limit, independently of the opaque
stochastic-integral bridge. -/
theorem brownian_cosh_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.cosh (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => Real.sinh (B t omega) -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          Real.sinh (B s.toNNReal omega)) := by
  have hf : ContDiff ℝ 2 Real.sinh := Real.contDiff_sinh
  have hderivSinh : deriv Real.sinh = Real.cosh := Real.deriv_sinh
  have hderivCosh : deriv Real.cosh = Real.sinh := Real.deriv_cosh
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderivSinh, hderivCosh] at h
  simpa only [Real.sinh_zero, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums weighted by the derivative of
`sinh (lambda * x)` have their exact Itô limit for every real scale `lambda`. -/
theorem brownian_scaledSinhDerivative_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        (lambda * Real.cosh
          (lambda * B (uniformPartitionTime t (n + 1) i) omega)) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.sinh (lambda * B t omega) -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda ^ 2 * Real.sinh (lambda * B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => Real.sinh (lambda * x)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f =
      fun x => lambda * Real.cosh (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sinh
    dsimp only [f]
    rw [hx.deriv]
    ring
  have hsecond : deriv (fun x : ℝ =>
      lambda * Real.cosh (lambda * x)) =
      fun x => lambda ^ 2 * Real.sinh (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cosh
    have hscaled := hx.const_mul lambda
    rw [hscaled.deriv]
    ring
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  simpa only [f, mul_zero, Real.sinh_zero, sub_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `cosh (lambda B)` have their exact hyperbolic residual limit. -/
theorem brownian_scaledCosh_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.cosh (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.sinh (lambda * B t omega) / lambda -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.sinh (lambda * B s.toNNReal omega)) := by
  have hall :=
    brownian_scaledSinhDerivative_leftSum_tendstoInMeasure hB t lambda
  have hscaled := hall.const_mul_real_noMeas (1 / lambda)
  apply hscaled.congr
  · intro n
    filter_upwards with omega
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hlambda]
  · filter_upwards with omega
    have hint :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda ^ 2 * Real.sinh (lambda * B s.toNNReal omega)) =
        lambda * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.sinh (lambda * B s.toNNReal omega) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [hint]
    field_simp [hlambda]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums with hyperbolic-sine state weight have the
canonical hyperbolic Itô limit, independently of the opaque
stochastic-integral bridge. -/
theorem brownian_sinh_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.sinh (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega => Real.cosh (B t omega) - 1 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          Real.cosh (B s.toNNReal omega)) := by
  have hf : ContDiff ℝ 2 Real.cosh := Real.contDiff_cosh
  have hderivCosh : deriv Real.cosh = Real.sinh := Real.deriv_cosh
  have hderivSinh : deriv Real.sinh = Real.cosh := Real.deriv_sinh
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderivCosh, hderivSinh] at h
  simpa only [Real.cosh_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian left-endpoint sums weighted by the derivative of
`cosh (lambda * x)` have their exact Itô limit for every real scale `lambda`. -/
theorem brownian_scaledCoshDerivative_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        (lambda * Real.sinh
          (lambda * B (uniformPartitionTime t (n + 1) i) omega)) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.cosh (lambda * B t omega) - 1 -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda ^ 2 * Real.cosh (lambda * B s.toNNReal omega)) := by
  let f : ℝ → ℝ := fun x => Real.cosh (lambda * x)
  have hf : ContDiff ℝ 2 f := by
    dsimp only [f]
    fun_prop
  have hderiv : deriv f =
      fun x => lambda * Real.sinh (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).cosh
    dsimp only [f]
    rw [hx.deriv]
    ring
  have hsecond : deriv (fun x : ℝ =>
      lambda * Real.sinh (lambda * x)) =
      fun x => lambda ^ 2 * Real.cosh (lambda * x) := by
    funext x
    have hx := (hasDerivAt_const_mul (x := x) lambda).sinh
    have hscaled := hx.const_mul lambda
    rw [hscaled.deriv]
    ring
  have h := firstOrderTaylorSum_tendstoInMeasure hB hf t
  rw [hderiv, hsecond] at h
  simpa only [f, mul_zero, Real.cosh_zero] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every nonzero scale `lambda`, Brownian left-endpoint sums with state
weight `sinh (lambda B)` have their exact hyperbolic residual limit. -/
theorem brownian_scaledSinh_leftSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0) (lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range (n + 1),
        Real.sinh (lambda * B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop (fun omega =>
        Real.cosh (lambda * B t omega) / lambda - 1 / lambda -
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            lambda * Real.cosh (lambda * B s.toNNReal omega)) := by
  have hall :=
    brownian_scaledCoshDerivative_leftSum_tendstoInMeasure hB t lambda
  have hscaled := hall.const_mul_real_noMeas (1 / lambda)
  apply hscaled.congr
  · intro n
    filter_upwards with omega
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hlambda]
  · filter_upwards with omega
    have hint :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda ^ 2 * Real.cosh (lambda * B s.toNNReal omega)) =
        lambda * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          lambda * Real.cosh (lambda * B s.toNNReal omega) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [hint]
    field_simp [hlambda]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A globally bounded measurable adapted weight makes the centered weighted
Brownian squared-increment sums converge to zero in `L²`. -/
theorem boundedWeightedBrownianQuadraticVariation_tendsto_eLpNorm
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (K : ℝ) (hK : 0 ≤ K)
    (hgK : ∀ x, |g x| ≤ K) :
    Filter.Tendsto
      (fun n ↦ eLpNorm
        (fun omega ↦ ∑ i ∈ Finset.range (n + 1),
          g (B (uniformPartitionTime t (n + 1) i) omega) *
            ((B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega) ^ 2 -
              ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime t (n + 1) i : ℝ)))) 2 P)
      Filter.atTop (nhds 0) := by
  convert tendsto_eLpNorm_centeredWeightedQuadraticVariationApprox
    hB t g hg K hK hgK using 1
  funext n
  congr 1

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For every continuous adapted weight, the centered weighted Brownian
squared-increment sums converge to zero in probability. -/
theorem centeredWeightedBrownianQuadraticVariation_tendstoInMeasure
    (hB : IsBrownianMotion B P) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        g (B (uniformPartitionTime t (n + 1) i) omega) *
          ((B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega) ^ 2 -
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))))
      Filter.atTop (fun _ ↦ 0) := by
  convert continuous_centeredWeightedQuadraticVariationApprox_tendstoInMeasure
    hB t g hg using 1
  funext n omega
  unfold centeredWeightedQuadraticVariationApprox partitionIncrement
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The quadratic Taylor sums along Brownian uniform partitions converge in
probability to half the second-derivative time integral. -/
theorem secondOrderTaylorSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        (1 / 2 : ℝ) * deriv (deriv f)
          (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega) ^ 2)
      Filter.atTop
      (fun omega ↦ (1 / 2 : ℝ) *
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) := by
  convert secondOrderTaylorApprox_tendstoInMeasure hB hf t using 1
  · funext n omega
    unfold secondOrderTaylorApprox partitionIncrement
    rfl
  · funext omega
    unfold secondDerivativeTimeIntegral
    rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The fully expanded second-order Taylor remainder sums along Brownian
uniform partitions converge to zero in probability. -/
theorem taylorRemainderSum_tendstoInMeasure
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        (f (B (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          (f (B (uniformPartitionTime t (n + 1) i) omega) +
            deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega) +
            (1 / 2 : ℝ) * deriv (deriv f)
              (B (uniformPartitionTime t (n + 1) i) omega) *
              (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
                B (uniformPartitionTime t (n + 1) i) omega) ^ 2)))
      Filter.atTop (fun _ ↦ 0) := by
  simpa only [itoTaylorRemainder] using
    taylorRemainder_tendstoInMeasure hB hf t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A function is a convergence-in-probability limit of the Brownian
first-order Taylor sums exactly when it agrees almost everywhere with the
explicit residual furnished by the Taylor decomposition. -/
theorem firstOrderTaylorSum_tendstoInMeasure_iff_ae_eq
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop I ↔
      (fun omega ↦ f (B t omega) - f 0 -
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega)) =ᵐ[P] I := by
  have hlimit := firstOrderTaylorSum_tendstoInMeasure hB hf t
  constructor
  · intro hI
    exact tendstoInMeasure_ae_unique hlimit hI
  · intro hI
    exact hlimit.congr_right hI

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Convergence in probability of the Brownian first-order Taylor sums to
`I` is equivalent to the corresponding almost-everywhere Itô identity. -/
theorem ito_formula_brownianMotion_ae_iff_firstOrder_limit
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop I ↔
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  constructor
  · intro hfirst
    have hresidual :=
      (firstOrderTaylorSum_tendstoInMeasure_iff_ae_eq hB hf t I).mp hfirst
    filter_upwards [hresidual] with omega homega
    linarith only [homega]
  · intro hformula
    apply (firstOrderTaylorSum_tendstoInMeasure_iff_ae_eq hB hf t I).mpr
    filter_upwards [hformula] with omega homega
    linarith only [homega]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `L¹` carriers representing the Brownian first-order Taylor sums
converge, then their carrier limit is a valid stochastic term in the
almost-everywhere Itô formula. -/
theorem ito_formula_brownianMotion_ae_of_Lp_one_firstOrder_limit
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (S : ℕ → Lp ℝ 1 P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ 1 P) (hfirst : Filter.Tendsto S Filter.atTop (nhds I)) :
    ∀ᵐ omega ∂P,
      f (B t omega) = f 0 + I omega +
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega) := by
  let rawS : ℕ → W → ℝ := fun n omega ↦
    ∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)
  have hrawMeas (n : ℕ) : AEStronglyMeasurable (rawS n) P :=
    (Lp.aestronglyMeasurable (S n)).congr (hS n)
  have hnorm : Filter.Tendsto
      (fun n ↦ eLpNorm (rawS n - (↑I : W → ℝ)) 1 P)
      Filter.atTop (nhds 0) := by
    have hcarrier :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' S I).mp hfirst
    apply hcarrier.congr'
    filter_upwards with n
    exact eLpNorm_congr_ae ((hS n).sub Filter.EventuallyEq.rfl)
  have hprob : TendstoInMeasure P rawS Filter.atTop (↑I : W → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
      hrawMeas (Lp.aestronglyMeasurable I) hnorm
  apply (ito_formula_brownianMotion_ae_iff_firstOrder_limit
    hB hf t (↑I : W → ℝ)).mp
  simpa only [rawS] using hprob

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If `L²` carriers representing the Brownian first-order Taylor sums
converge, then their carrier limit is a valid stochastic term in the
almost-everywhere Itô formula. -/
theorem ito_formula_brownianMotion_ae_of_Lp_two_firstOrder_limit
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (S : ℕ → Lp ℝ 2 P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ 2 P) (hfirst : Filter.Tendsto S Filter.atTop (nhds I)) :
    ∀ᵐ omega ∂P,
      f (B t omega) = f 0 + I omega +
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega) := by
  let rawS : ℕ → W → ℝ := fun n omega ↦
    ∑ i ∈ Finset.range (n + 1),
      deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
        (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
          B (uniformPartitionTime t (n + 1) i) omega)
  have hrawMeas (n : ℕ) : AEStronglyMeasurable (rawS n) P :=
    (Lp.aestronglyMeasurable (S n)).congr (hS n)
  have hnorm : Filter.Tendsto
      (fun n ↦ eLpNorm (rawS n - (↑I : W → ℝ)) 2 P)
      Filter.atTop (nhds 0) := by
    have hcarrier :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' S I).mp hfirst
    apply hcarrier.congr'
    filter_upwards with n
    exact eLpNorm_congr_ae ((hS n).sub Filter.EventuallyEq.rfl)
  have hprob : TendstoInMeasure P rawS Filter.atTop (↑I : W → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      hrawMeas (Lp.aestronglyMeasurable I) hnorm
  apply (ito_formula_brownianMotion_ae_iff_firstOrder_limit
    hB hf t (↑I : W → ℝ)).mp
  simpa only [rawS] using hprob

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a `C²` function with bounded first derivative, convergence of any
`L¹` carrier sequence representing the first-order Taylor sums is equivalent
to the almost-everywhere Itô formula for its candidate limit. -/
theorem ito_formula_brownianMotion_ae_iff_Lp_one_firstOrder_limit_of_deriv_bound
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (K : ℝ≥0) (hderivK : ∀ x, |deriv f x| ≤ (K : ℝ)) (t : ℝ≥0)
    (S : ℕ → Lp ℝ 1 P)
    (hS : ∀ n, (↑(S n) : W → ℝ) =ᵐ[P] fun omega ↦
      ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
    (I : Lp ℝ 1 P) :
    Filter.Tendsto S Filter.atTop (nhds I) ↔
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  rw [Lp_one_firstOrderTaylorSum_tendsto_iff_ae_eq_of_deriv_bound
    hB hf K hderivK t S hS I]
  constructor
  · intro hresidual
    filter_upwards [hresidual] with omega homega
    linarith only [homega]
  · intro hformula
    filter_upwards [hformula] with omega homega
    linarith only [homega]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem ito_formula_brownianMotion_ae_of_firstOrder_limit_aux
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ)
    (hfirst : TendstoInMeasure P
      (fun n ↦ firstOrderTaylorApprox f B t (n + 1)) Filter.atTop
      I) :
    ∀ᵐ omega ∂P,
      f (B t omega) = f 0 + I omega +
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  let D : W → ℝ := secondDerivativeTimeIntegral f B t
  have hsecond : TendstoInMeasure P
      (fun n ↦ secondOrderTaylorApprox f B t (n + 1)) Filter.atTop D := by
    simpa only [D] using secondOrderTaylorApprox_tendstoInMeasure hB hf t
  have hremainder : TendstoInMeasure P
      (fun n ↦ taylorRemainderApprox f B t (n + 1)) Filter.atTop
      (fun _ ↦ 0) := by
    change TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        itoTaylorRemainder f (B (uniformPartitionTime t (n + 1) i) omega)
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega))
      Filter.atTop (fun _ ↦ 0)
    exact taylorRemainder_tendstoInMeasure hB hf t
  have hfirstMeas : ∀ n, AEStronglyMeasurable
      (firstOrderTaylorApprox f B t (n + 1)) P :=
    fun n ↦ aestronglyMeasurable_firstOrderTaylorApprox hB hf t (n + 1)
  have hsecondMeas : ∀ n, AEStronglyMeasurable
      (secondOrderTaylorApprox f B t (n + 1)) P :=
    fun n ↦ aestronglyMeasurable_secondOrderTaylorApprox hB hf t (n + 1)
  have hremainderMeas : ∀ n, AEStronglyMeasurable
      (taylorRemainderApprox f B t (n + 1)) P :=
    fun n ↦ aestronglyMeasurable_taylorRemainderApprox hB hf t (n + 1)
  have hfirstSecond := hfirst.add_real hsecond hfirstMeas hsecondMeas
  have htotal := hfirstSecond.add_real hremainder
    (fun n ↦ (hfirstMeas n).add (hsecondMeas n)) hremainderMeas
  have htotal' : TendstoInMeasure P
      (fun n omega ↦
        (firstOrderTaylorApprox f B t (n + 1) omega +
          secondOrderTaylorApprox f B t (n + 1) omega) +
          taylorRemainderApprox f B t (n + 1) omega)
      Filter.atTop (fun omega ↦ I omega + D omega) := by
    apply htotal.congr_right
    filter_upwards with omega
    simp only [add_zero]
  have hdecomp : ∀ n : ℕ,
      (fun omega ↦
        (firstOrderTaylorApprox f B t (n + 1) omega +
          secondOrderTaylorApprox f B t (n + 1) omega) +
          taylorRemainderApprox f B t (n + 1) omega) =ᵐ[P]
        (fun omega ↦ f (B t omega) - f (B 0 omega)) := by
    intro n
    filter_upwards with omega
    unfold firstOrderTaylorApprox secondOrderTaylorApprox taylorRemainderApprox
    simpa only [partitionIncrement] using
      (uniformPartition_taylor_decomposition f B t n omega).symm
  have hconstTarget : TendstoInMeasure P
      (fun _ : ℕ ↦ fun omega ↦ f (B t omega) - f (B 0 omega))
      Filter.atTop (fun omega ↦ I omega + D omega) :=
    htotal'.congr_left hdecomp
  have hfcontinuous : Continuous f := hf.continuous
  have hconstMeas : AEStronglyMeasurable
      (fun omega ↦ f (B t omega) - f (B 0 omega)) P :=
    ((hfcontinuous.measurable.comp_aemeasurable
      (hpre.aemeasurable t)).sub
      (hfcontinuous.measurable.comp_aemeasurable
        (hpre.aemeasurable 0))).aestronglyMeasurable
  have hconstSelf : TendstoInMeasure P
      (fun _ : ℕ ↦ fun omega ↦ f (B t omega) - f (B 0 omega))
      Filter.atTop (fun omega ↦ f (B t omega) - f (B 0 omega)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ hconstMeas) (by
      filter_upwards with omega
      exact tendsto_const_nhds)
  have hcore := tendstoInMeasure_ae_unique hconstSelf hconstTarget
  filter_upwards [hcore, hpre.eval_zero_ae_eq_zero] with omega hcore' hzero
  dsimp only [D, secondDerivativeTimeIntegral] at hcore' ⊢
  rw [hzero] at hcore'
  linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If the left-endpoint first-order Taylor sums converge in probability to
`I`, then the Brownian Itô formula with candidate stochastic term `I` holds
almost everywhere. -/
theorem ito_formula_brownianMotion_ae_of_firstOrder_limit
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ)
    (hfirst : TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop I) :
    ∀ᵐ omega ∂P,
      f (B t omega) = f 0 + I omega +
        (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (B s.toNNReal omega) := by
  exact (ito_formula_brownianMotion_ae_iff_firstOrder_limit hB hf t I).mp hfirst

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Every singleton has zero measure under a Brownian law. -/
private lemma brownian_measure_singleton_zero
    (hB : IsBrownianMotion B P) (omega0 : W) : P {omega0} = 0 := by
  have hLaw := hB.toIsPreBrownianReal.hasLaw_eval 1
  have hFiber : P {omega | B 1 omega = B 1 omega0} = 0 := by
    have hp : MeasurableSet {x : ℝ | x = B 1 omega0} := by
      rw [Set.ofPred_eq_eq_singleton]
      exact measurableSet_singleton (B 1 omega0)
    rw [hLaw.measure_eq hp, Set.ofPred_eq_eq_singleton]
    exact (ProbabilityTheory.nullSingletonClass_gaussianReal
      (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)).measure_singleton (B 1 omega0)
  refine measure_mono_null ?_ hFiber
  intro omega homega
  have heq : omega = omega0 := Set.mem_singleton_iff.mp homega
  change B 1 omega = B 1 omega0
  rw [heq]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A Brownian-law hypothesis cannot imply a pointwise identity whose
right-hand side is unchanged when the Brownian process is modified on a null
set. This is the null-modification obstruction to a pointwise Itô formula. -/
theorem no_pointwise_brownian_identity_rule
    (hB : IsBrownianMotion B P) (omega0 : W) (I : ℝ≥0 → W → ℝ)
    (hRule : ∀ {D : ℝ≥0 → W → ℝ}, IsBrownianMotion D P →
      ∀ t omega, D t omega = I t omega) : False := by
  classical
  have homega0 : P {omega0} = 0 := brownian_measure_singleton_zero hB omega0
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    if omega = omega0 then B t omega + 1 else B t omega
  have hne : ∀ᵐ omega ∂P, omega ≠ omega0 := by
    rw [ae_iff]
    have hset : {omega | ¬omega ≠ omega0} = ({omega0} : Set W) := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, not_ne_iff]
    rw [hset]
    exact homega0
  have hBC (t : ℝ≥0) : B t =ᵐ[P] C t := by
    filter_upwards [hne] with omega homega
    simp only [C, homega, ↓reduceIte]
  have hC : IsBrownianMotion C P := {
    toIsPreBrownianReal := hB.toIsPreBrownianReal.congr hBC
    cont := by
      filter_upwards [hB.cont, hne] with omega hcont homega
      simpa only [C, homega, ↓reduceIte] using hcont
  }
  have heq : B 0 omega0 = C 0 omega0 :=
    (hRule hB 0 omega0).trans (hRule hC 0 omega0).symm
  have hne' : B 0 omega0 ≠ C 0 omega0 := by
    simp only [C, ↓reduceIte, ne_eq]
    intro h
    linarith
  exact hne' heq

/-!
The source scaffold ended with a pointwise formula involving an opaque
`itoIntegral`.  That endpoint is intentionally not retained here.  Brownian
motion and stochastic-integral representatives are stable only up to null
sets, and `no_pointwise_brownian_identity_rule` above formalizes the resulting
obstruction.  The public endpoints in this file therefore use almost-everywhere
equality and characterize the stochastic term as the limit in probability of
the Brownian left sums.  A subsequent integration layer identifies that limit
with the natural `L²` Itô integral when the state integrand belongs to its
domain.
-/

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- **Itô's formula for a `C²` function of Brownian motion.**

The stochastic integral is presented by its defining approximation contract:
`I` is a convergence-in-probability limit of the left-endpoint Brownian sums.
This formulation is invariant under changes on null sets and therefore avoids
the impossible pointwise endpoint ruled out by
`no_pointwise_brownian_identity_rule`. -/
theorem ito_formula_brownianMotion
    (hB : IsBrownianMotion B P) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
          deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
            (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
              B (uniformPartitionTime t (n + 1) i) omega))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f (B t omega) = f 0 + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f) (B s.toNNReal omega) := by
  let I : W → ℝ := fun omega ↦
    f (B t omega) - f 0 -
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (B s.toNNReal omega)
  have hlimit : TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range (n + 1),
        deriv f (B (uniformPartitionTime t (n + 1) i) omega) *
          (B (uniformPartitionTime t (n + 1) (i + 1)) omega -
            B (uniformPartitionTime t (n + 1) i) omega))
      Filter.atTop I := by
    simpa only [I] using firstOrderTaylorSum_tendstoInMeasure hB hf t
  refine ⟨I, hlimit, ?_⟩
  filter_upwards with omega
  dsimp only [I]
  ring

end StochasticCalculus
