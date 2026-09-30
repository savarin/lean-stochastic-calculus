/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.QuadraticVariationDensity
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Taylor partition sums along Brownian paths

The pieces of the Itô-formula development that the pricing chain uses: the
Taylor remainder of a twice differentiable function, its uniform bounds on
compact intervals, and the convergence along uniform partitions of the
derivative-weighted increment sums, the left Riemann sums, and the
quadratic-variation-controlled remainder sums.
-/

public section

open MeasureTheory Set
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {P : Measure W} {B : ℝ≥0 → W → ℝ}

namespace StochasticCalculus

/-- The remainder after subtracting the explicit second-order Taylor polynomial. -/
@[expose] noncomputable def itoTaylorRemainder (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  f x - (f x₀ + deriv f x₀ * (x - x₀) +
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x - x₀) ^ 2)

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

section CenteredWeightedQuadraticVariation

variable {Omega I E : Type*} [MeasurableSpace Omega]

end CenteredWeightedQuadraticVariation

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

/-!
Brownian motion and stochastic-integral representatives are stable only up
to null sets.  The endpoints in this file therefore use almost-everywhere
equality and characterize the stochastic term as the limit in probability of
the Brownian left sums.
-/

end StochasticCalculus
