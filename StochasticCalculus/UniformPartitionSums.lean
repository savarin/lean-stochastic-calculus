/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.TendstoInMeasureAlgebra

/-!
# Uniform partition sums

The abbreviation `IsBrownianMotion` for Mathlib's `IsBrownianReal`, the
uniform partition of `[0, t]`, and the quadratic, fourth, cross and total
variation sums along it, with their algebraic identities, measurability,
and the integrated drift of a measurable coefficient.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace

noncomputable section
set_option linter.unusedDecidableInType false

namespace StochasticCalculus

/-- Brownian motion with Mathlib's canonical finite-dimensional laws and
almost-everywhere continuous paths. -/
abbrev IsBrownianMotion {W : Type*} [MeasurableSpace W] (B : ℝ≥0 → W → ℝ) (P : Measure W) :
    Prop :=
  IsBrownianReal B P

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

/-- The `i`-th point in the uniform `n`-step partition of `[0, t]`. -/
noncomputable def uniformPartitionTime (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  t * (i : ℝ≥0) / (n : ℝ≥0)

lemma monotone_uniformPartitionTime (t : ℝ≥0) (n : ℕ) :
    Monotone (uniformPartitionTime t n) := by
  intro i j hij
  unfold uniformPartitionTime
  gcongr

private lemma uniformPartitionTime_succ_sub (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    uniformPartitionTime t n (i + 1) - uniformPartitionTime t n i =
      t / (n : ℝ≥0) := by
  apply NNReal.eq
  rw [NNReal.coe_sub]
  · simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_natCast]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
    norm_num [Nat.cast_add, Nat.cast_one]
  · unfold uniformPartitionTime
    gcongr
    omega

lemma uniformPartitionTime_succ_nndist (t : ℝ≥0) {n : ℕ}
    (hn : 0 < n) (i : ℕ) :
    nndist ((uniformPartitionTime t n (i + 1) : ℝ))
      ((uniformPartitionTime t n i : ℝ)) = t / (n : ℝ≥0) := by
  have hle : uniformPartitionTime t n i ≤ uniformPartitionTime t n (i + 1) :=
    monotone_uniformPartitionTime t n (Nat.le_add_right i 1)
  rw [show nndist ((uniformPartitionTime t n (i + 1) : ℝ))
      ((uniformPartitionTime t n i : ℝ)) =
      uniformPartitionTime t n (i + 1) - uniformPartitionTime t n i by
        apply NNReal.eq
        rw [← dist_nndist, Real.dist_eq, abs_of_nonneg, NNReal.coe_sub hle]
        exact sub_nonneg.mpr (by exact_mod_cast hle)]
  exact uniformPartitionTime_succ_sub t hn i

/-- Every uniform-partition point whose index is at most the denominator
lies in the time interval `[0, t]`. -/
lemma uniformPartitionTime_mem_Icc_of_le
    (t : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformPartitionTime t n i ∈ Set.Icc 0 t := by
  constructor
  · exact bot_le
  · unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    calc
      t * (i : ℝ≥0) / (n : ℝ≥0) ≤ t * (n : ℝ≥0) / (n : ℝ≥0) := by
        gcongr
      _ = t := mul_div_cancel_right₀ t hn0

/-- Adjacent uniform-partition points are exactly one mesh width apart. -/
lemma dist_uniformPartitionTime_succ_eq
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

/-- A path continuous on `[0, t]` has uniformly vanishing increments along
the uniform partitions of that interval. -/
theorem continuousOn_uniformPartition_increments_tendsto
    (g : ℝ≥0 → ℝ) (t : ℝ≥0) (hg : ContinuousOn g (Set.Icc 0 t)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |g (uniformPartitionTime t (n + 1) (i + 1)) -
          g (uniformPartitionTime t (n + 1) i)| < δ := by
  have huc : UniformContinuousOn g (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
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
  have hx := uniformPartitionTime_mem_Icc_of_le t hnpos hi'
  have hy := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  have hmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < η := by
    have := hN n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] using this
  have hdist :
      dist (uniformPartitionTime t (n + 1) (i + 1))
        (uniformPartitionTime t (n + 1) i) < η := by
    rw [dist_uniformPartitionTime_succ_eq t hnpos i]
    exact hmesh
  have hout := hmod _ hy _ hx hdist
  simpa only [Real.dist_eq] using hout

/-- A continuous path has uniformly vanishing increments along the uniform
partitions. -/
theorem continuous_uniformPartition_increments_tendsto
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (t : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |g (uniformPartitionTime t (n + 1) (i + 1)) -
          g (uniformPartitionTime t (n + 1) i)| < δ :=
  continuousOn_uniformPartition_increments_tendsto g t hg.continuousOn

/-- Sum of squared increments along the uniform `n`-step partition of `[0, t]`. -/
noncomputable def quadraticVariationApprox
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (B (uniformPartitionTime t n (i + 1)) ω -
      B (uniformPartitionTime t n i) ω) ^ 2

/-- Sum of fourth powers of increments along the uniform `n`-step partition.

For a pre-Brownian process its expectation is of order `1 / n`.  This is the
path-regularity-free replacement for a maximum-mesh estimate in Taylor
remainder arguments. -/
noncomputable def fourthVariationApprox
    (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (B (uniformPartitionTime t n (i + 1)) ω -
      B (uniformPartitionTime t n i) ω) ^ 4

/-- Sum of products of the increments of two processes along the uniform
`n`-step partition of `[0, t]`. -/
noncomputable def quadraticCovariationApprox
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (X (uniformPartitionTime t n (i + 1)) ω -
      X (uniformPartitionTime t n i) ω) *
    (Y (uniformPartitionTime t n (i + 1)) ω -
      Y (uniformPartitionTime t n i) ω)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Quadratic-covariation approximants are symmetric. -/
theorem quadraticCovariationApprox_comm
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationApprox X Y t n omega =
      quadraticCovariationApprox Y X t n omega := by
  unfold quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Sum of absolute increments along the uniform `n`-step partition. -/
noncomputable def totalVariationApprox
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    |X (uniformPartitionTime t n (i + 1)) ω -
      X (uniformPartitionTime t n i) ω|

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Every squared-increment sum is nonnegative. -/
theorem quadraticVariationApprox_nonneg (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (ω : W) :
    0 ≤ quadraticVariationApprox X t n ω := by
  unfold quadraticVariationApprox
  exact Finset.sum_nonneg fun _ _hi => sq_nonneg _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Every fourth-variation approximant is nonnegative. -/
theorem fourthVariationApprox_nonneg (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (ω : W) :
    0 ≤ fourthVariationApprox X t n ω := by
  unfold fourthVariationApprox
  exact Finset.sum_nonneg fun _ _hi => by positivity

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Scaling a process scales every squared-increment sum by the square of
the scalar. -/
theorem quadraticVariationApprox_const_mul
    (c : ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    quadraticVariationApprox (fun s ω => c * X s ω) t n ω =
      c ^ 2 * quadraticVariationApprox X t n ω := by
  unfold quadraticVariationApprox
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Multiplication by a random variable that is constant in time scales each
squared-increment sum pointwise by the square of that random variable. -/
theorem quadraticVariationApprox_timeConstant_mul
    (c : W → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticVariationApprox (fun s ω => c ω * X s ω) t n omega =
      c omega ^ 2 * quadraticVariationApprox X t n omega := by
  unfold quadraticVariationApprox
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Multiplying two processes by random variables that are constant in time
scales every quadratic-covariation sum pointwise by their product. -/
theorem quadraticCovariationApprox_timeConstant_mul
    (c d : W → ℝ) (X Y : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationApprox
      (fun s ω => c ω * X s ω) (fun s ω => d ω * Y s ω) t n omega =
      (c omega * d omega) * quadraticCovariationApprox X Y t n omega := by
  unfold quadraticCovariationApprox
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Exact polarization of the squared-increment sum of two processes. -/
theorem quadraticVariationApprox_add (X Y : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (ω : W) :
    quadraticVariationApprox (fun s ω => X s ω + Y s ω) t n ω =
      quadraticVariationApprox X t n ω + quadraticVariationApprox Y t n ω +
        2 * quadraticCovariationApprox X Y t n ω := by
  unfold quadraticVariationApprox quadraticCovariationApprox
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Exact expansion of the squared-increment sum of a deterministic linear
combination of two processes. -/
theorem quadraticVariationApprox_linearCombination
    (X Y : ℝ≥0 → W → ℝ) (c d : ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticVariationApprox
      (fun s omega => c * X s omega + d * Y s omega) t n omega =
      c ^ 2 * quadraticVariationApprox X t n omega +
        d ^ 2 * quadraticVariationApprox Y t n omega +
        2 * c * d * quadraticCovariationApprox X Y t n omega := by
  unfold quadraticVariationApprox quadraticCovariationApprox
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Finite-sum Cauchy--Schwarz for the quadratic-covariation approximant. -/
theorem quadraticCovariationApprox_sq_le
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    quadraticCovariationApprox X Y t n ω ^ 2 ≤
      quadraticVariationApprox X t n ω * quadraticVariationApprox Y t n ω := by
  unfold quadraticCovariationApprox quadraticVariationApprox
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A time-constant random summand does not change squared increments. -/
theorem quadraticVariationApprox_add_timeConstant
    (X : ℝ≥0 → W → ℝ) (c : W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    quadraticVariationApprox (fun s ω => c ω + X s ω) t n ω =
      quadraticVariationApprox X t n ω := by
  unfold quadraticVariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Per-time almost-everywhere strong measurability of a process makes every
uniform-partition quadratic-variation sum almost-everywhere strongly
measurable. -/
theorem aestronglyMeasurable_quadraticVariationApprox
    (hX : ∀ s, AEStronglyMeasurable (X s) P) (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (quadraticVariationApprox X t n) P := by
  unfold quadraticVariationApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi => by
      have hd := (hX (uniformPartitionTime t n (i + 1))).sub
        (hX (uniformPartitionTime t n i))
      convert hd.mul hd using 1)
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Per-time almost-everywhere strong measurability makes every uniform
fourth-variation sum almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_fourthVariationApprox
    (hX : ∀ s, AEStronglyMeasurable (X s) P) (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (fourthVariationApprox X t n) P := by
  unfold fourthVariationApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi => (((hX (uniformPartitionTime t n (i + 1))).sub
      (hX (uniformPartitionTime t n i))).pow 4))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.pow_apply, Pi.sub_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Per-time almost-everywhere strong measurability of two processes makes
every uniform-partition quadratic-covariation sum almost-everywhere strongly
measurable. -/
theorem aestronglyMeasurable_quadraticCovariationApprox
    {Y : ℝ≥0 → W → ℝ}
    (hX : ∀ s, AEStronglyMeasurable (X s) P)
    (hY : ∀ s, AEStronglyMeasurable (Y s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (quadraticCovariationApprox X Y t n) P := by
  unfold quadraticCovariationApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi => ((hX (uniformPartitionTime t n (i + 1))).sub
      (hX (uniformPartitionTime t n i))).mul
      ((hY (uniformPartitionTime t n (i + 1))).sub
        (hY (uniformPartitionTime t n i))))
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- If one process has vanishing quadratic-variation sums and another has
convergent quadratic-variation sums, then their covariation sums vanish along
the same index filter. -/
theorem tendsto_quadraticCovariationApprox_zero_of_left_qv_zero
    {ι : Type*} {l : Filter ι} (k : ι → ℕ)
    (A M : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) (q : ℝ)
    (hA : Filter.Tendsto
      (fun n => quadraticVariationApprox A t (k n) ω) l (nhds 0))
    (hM : Filter.Tendsto
      (fun n => quadraticVariationApprox M t (k n) ω) l (nhds q)) :
    Filter.Tendsto
      (fun n => quadraticCovariationApprox A M t (k n) ω) l (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero (g := fun n => Real.sqrt
    (quadraticVariationApprox A t (k n) ω *
      quadraticVariationApprox M t (k n) ω))
  · intro n
    exact abs_nonneg _
  · intro n
    apply Real.le_sqrt_of_sq_le
    simpa only [Function.comp_apply, sq_abs] using
      quadraticCovariationApprox_sq_le A M t (k n) ω
  · have hprod := hA.mul hM
    have hsqrt := hprod.sqrt
    simpa only [zero_mul, Real.sqrt_zero] using hsqrt

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Adding a process with vanishing quadratic variation does not change a
pathwise quadratic-variation limit. -/
theorem tendsto_quadraticVariationApprox_add_of_left_qv_zero
    {ι : Type*} {l : Filter ι} (k : ι → ℕ)
    (A M : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) (q : ℝ)
    (hA : Filter.Tendsto
      (fun n => quadraticVariationApprox A t (k n) ω) l (nhds 0))
    (hM : Filter.Tendsto
      (fun n => quadraticVariationApprox M t (k n) ω) l (nhds q)) :
    Filter.Tendsto
      (fun n => quadraticVariationApprox
        (fun s ω => A s ω + M s ω) t (k n) ω) l (nhds q) := by
  have hcov := tendsto_quadraticCovariationApprox_zero_of_left_qv_zero
    k A M t ω q hA hM
  have hsum := (hA.add hM).add (hcov.const_mul 2)
  convert hsum using 1
  · funext n
    rw [quadraticVariationApprox_add]
  · norm_num

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A path continuous on `[0, t]` with uniformly bounded discrete total
variation has vanishing quadratic variation along the uniform partitions. -/
theorem tendsto_quadraticVariationApprox_zero_of_continuousOn_of_variation_le
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) (C : ℝ) (hC : 0 < C)
    (hcontinuous : ContinuousOn (fun s ↦ X s ω) (Set.Icc 0 t))
    (hvariation : ∀ n, totalVariationApprox X t n ω ≤ C) :
    Filter.Tendsto (fun n ↦ quadraticVariationApprox X t (n + 1) ω)
      Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (continuousOn_uniformPartition_increments_tendsto
      (fun s ↦ X s ω) t hcontinuous δ hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmesh := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quadraticVariationApprox_nonneg X t (n + 1) ω)]
  calc
    quadraticVariationApprox X t (n + 1) ω =
        ∑ i ∈ Finset.range (n + 1),
          |X (uniformPartitionTime t (n + 1) (i + 1)) ω -
            X (uniformPartitionTime t (n + 1) i) ω| *
          |X (uniformPartitionTime t (n + 1) (i + 1)) ω -
            X (uniformPartitionTime t (n + 1) i) ω| := by
      unfold quadraticVariationApprox
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← sq_abs, pow_two]
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
          |X (uniformPartitionTime t (n + 1) (i + 1)) ω -
            X (uniformPartitionTime t (n + 1) i) ω| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hmesh i hi).le (abs_nonneg _)
    _ = δ * totalVariationApprox X t (n + 1) ω := by
      unfold totalVariationApprox
      rw [Finset.mul_sum]
    _ ≤ δ * C := mul_le_mul_of_nonneg_left (hvariation (n + 1)) hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [ne_of_gt hC]
    _ < ε := by linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A continuous path with uniformly bounded discrete total variation has
vanishing quadratic variation along the uniform partitions. -/
theorem tendsto_quadraticVariationApprox_zero_of_continuous_of_variation_le
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) (C : ℝ) (hC : 0 < C)
    (hcontinuous : Continuous (fun s ↦ X s ω))
    (hvariation : ∀ n, totalVariationApprox X t n ω ≤ C) :
    Filter.Tendsto (fun n ↦ quadraticVariationApprox X t (n + 1) ω)
      Filter.atTop (nhds 0) :=
  tendsto_quadraticVariationApprox_zero_of_continuousOn_of_variation_le
    X t ω C hC hcontinuous.continuousOn hvariation

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A continuous nondecreasing real path has vanishing quadratic variation
along the uniform partitions.  Monotonicity makes every discrete total
variation telescope to the endpoint increment. -/
theorem tendsto_quadraticVariationApprox_zero_of_continuous_monotone
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W)
    (hcontinuous : Continuous (fun s ↦ X s ω))
    (hmonotone : Monotone (fun s ↦ X s ω)) :
    Filter.Tendsto (fun n ↦ quadraticVariationApprox X t (n + 1) ω)
      Filter.atTop (nhds 0) := by
  let C := |X t ω - X 0 ω| + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  apply tendsto_quadraticVariationApprox_zero_of_continuous_of_variation_le
    X t ω C hC hcontinuous
  intro n
  cases n with
  | zero =>
      simp only [totalVariationApprox, Finset.range_zero, Finset.sum_empty]
      exact hC.le
  | succ n =>
      have hn : 0 < n + 1 := Nat.zero_lt_succ n
      unfold totalVariationApprox
      calc
        (∑ i ∈ Finset.range (n + 1),
            |X (uniformPartitionTime t (n + 1) (i + 1)) ω -
              X (uniformPartitionTime t (n + 1) i) ω|) =
            ∑ i ∈ Finset.range (n + 1),
              (X (uniformPartitionTime t (n + 1) (i + 1)) ω -
                X (uniformPartitionTime t (n + 1) i) ω) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_of_nonneg]
          exact sub_nonneg.mpr
            (hmonotone (monotone_uniformPartitionTime t (n + 1)
              (Nat.le_succ i)))
        _ = X (uniformPartitionTime t (n + 1) (n + 1)) ω -
              X (uniformPartitionTime t (n + 1) 0) ω := by
          exact Finset.sum_range_sub
            (fun i ↦ X (uniformPartitionTime t (n + 1) i) ω) (n + 1)
        _ = X t ω - X 0 ω := by
          have hn' : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt hn
          have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
            rw [uniformPartitionTime]
            exact mul_div_cancel_right₀ t hn'
          rw [htop]
          simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
        _ ≤ C := by
          dsimp only [C]
          linarith [le_abs_self (X t ω - X 0 ω)]

/-- The indefinite integral of a real function, parametrized by
nonnegative time. -/
noncomputable def nnrealIntegralPrimitive (g : ℝ → ℝ) (x : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (x : ℝ), g s

private lemma nnrealIntegralPrimitive_sub_eq_integral_Ioc
    {g : ℝ → ℝ} {t a b : ℝ≥0}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) (t : ℝ)))
    (hab : a ≤ b) (hbt : b ≤ t) :
    nnrealIntegralPrimitive g b - nnrealIntegralPrimitive g a =
      ∫ s in Set.Ioc (a : ℝ) (b : ℝ), g s := by
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbtR : (b : ℝ) ≤ (t : ℝ) := by exact_mod_cast hbt
  have hIntB : IntegrableOn g (Set.Icc (0 : ℝ) (b : ℝ)) :=
    hg.mono_set (Set.Icc_subset_Icc le_rfl hbtR)
  have hsub : Set.Icc (0 : ℝ) (a : ℝ) ⊆ Set.Icc (0 : ℝ) (b : ℝ) :=
    Set.Icc_subset_Icc le_rfl habR
  have hset : Set.Icc (0 : ℝ) (b : ℝ) \ Set.Icc (0 : ℝ) (a : ℝ) =
      Set.Ioc (a : ℝ) (b : ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hx0, hxb⟩, hxa⟩
      refine ⟨?_, hxb⟩
      exact lt_of_not_ge fun hax => hxa ⟨hx0, hax⟩
    · rintro ⟨hax, hxb⟩
      refine ⟨⟨?_, hxb⟩, ?_⟩
      · exact le_trans (NNReal.coe_nonneg a) hax.le
      · intro hx
        exact (not_lt_of_ge hx.2) hax
  unfold nnrealIntegralPrimitive
  rw [← setIntegral_sdiff measurableSet_Icc hIntB hsub, hset]

private lemma abs_nnrealIntegralPrimitive_sub_le
    {g : ℝ → ℝ} {t a b : ℝ≥0}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) (t : ℝ)))
    (hab : a ≤ b) (hbt : b ≤ t) :
    |nnrealIntegralPrimitive g b - nnrealIntegralPrimitive g a| ≤
      nnrealIntegralPrimitive (fun s => |g s|) b -
        nnrealIntegralPrimitive (fun s => |g s|) a := by
  have hgabs : IntegrableOn (fun s => |g s|) (Set.Icc (0 : ℝ) (t : ℝ)) := by
    change Integrable (fun s => |g s|)
      (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))
    simpa only [Real.norm_eq_abs] using hg.norm
  rw [nnrealIntegralPrimitive_sub_eq_integral_Ioc hg hab hbt,
    nnrealIntegralPrimitive_sub_eq_integral_Ioc hgabs hab hbt]
  exact abs_integral_le_integral_abs

private lemma uniformPartitionTime_top
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    uniformPartitionTime t n n = t := by
  unfold uniformPartitionTime
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  exact mul_div_cancel_right₀ t hn0

/-- An integrable function has a continuous nonnegative-time primitive on
its interval of integrability. -/
theorem continuousOn_nnrealIntegralPrimitive
    {g : ℝ → ℝ} {t : ℝ≥0}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) (t : ℝ))) :
    ContinuousOn (nnrealIntegralPrimitive g) (Set.Icc (0 : ℝ≥0) t) := by
  have hreal : ContinuousOn
      (fun x : ℝ => ∫ s in Set.Icc (0 : ℝ) x, g s)
      (Set.Icc (0 : ℝ) (t : ℝ)) :=
    intervalIntegral.continuousOn_primitive_Icc hg
  exact hreal.comp NNReal.continuous_coe.continuousOn fun x hx => by
    exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The discrete total variation of an integrable primitive is bounded by
the integral of the absolute value of its integrand. -/
theorem totalVariationApprox_nnrealIntegralPrimitive_le
    {g : ℝ → ℝ} {t : ℝ≥0}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) (t : ℝ))) (n : ℕ) :
    totalVariationApprox
        (fun s (_u : Unit) => nnrealIntegralPrimitive g s) t n () ≤
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), |g s| := by
  have hgabs : IntegrableOn (fun s => |g s|) (Set.Icc (0 : ℝ) (t : ℝ)) := by
    change Integrable (fun s => |g s|)
      (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))
    simpa only [Real.norm_eq_abs] using hg.norm
  cases n with
  | zero =>
      unfold totalVariationApprox
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  | succ n =>
      have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
      unfold totalVariationApprox
      calc
        (∑ i ∈ Finset.range (n + 1),
          |nnrealIntegralPrimitive g (uniformPartitionTime t (n + 1) (i + 1)) -
            nnrealIntegralPrimitive g (uniformPartitionTime t (n + 1) i)|) ≤
            ∑ i ∈ Finset.range (n + 1),
              (nnrealIntegralPrimitive (fun s => |g s|)
                  (uniformPartitionTime t (n + 1) (i + 1)) -
                nnrealIntegralPrimitive (fun s => |g s|)
                  (uniformPartitionTime t (n + 1) i)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
          have hi : i ≤ i + 1 := Nat.le_add_right i 1
          have htime : uniformPartitionTime t (n + 1) i ≤
              uniformPartitionTime t (n + 1) (i + 1) := by
            unfold uniformPartitionTime
            gcongr
          exact abs_nnrealIntegralPrimitive_sub_le hg htime
            (uniformPartitionTime_mem_Icc_of_le t hnpos hipos).2
        _ = nnrealIntegralPrimitive (fun s => |g s|)
              (uniformPartitionTime t (n + 1) (n + 1)) -
            nnrealIntegralPrimitive (fun s => |g s|)
              (uniformPartitionTime t (n + 1) 0) := by
          exact Finset.sum_range_sub
            (fun i => nnrealIntegralPrimitive (fun s => |g s|)
              (uniformPartitionTime t (n + 1) i)) (n + 1)
        _ = ∫ s in Set.Icc (0 : ℝ) (t : ℝ), |g s| := by
          rw [uniformPartitionTime_top t hnpos]
          have hzero : nnrealIntegralPrimitive (fun s => |g s|) 0 = 0 := by
            unfold nnrealIntegralPrimitive
            change (∫ s in Set.Icc (0 : ℝ) (0 : ℝ), |g s|) = 0
            rw [integral_Icc_eq_integral_Ioc, Set.Ioc_self,
              Measure.restrict_empty, integral_zero_measure]
          rw [show uniformPartitionTime t (n + 1) 0 = 0 by
            simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div],
            hzero, sub_zero]
          rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The quadratic variation of an integrable primitive vanishes pathwise
along the uniform partitions. -/
theorem tendsto_quadraticVariationApprox_nnrealIntegralPrimitive_zero
    {g : ℝ → ℝ} {t : ℝ≥0}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) (t : ℝ))) :
    Filter.Tendsto
      (fun n => quadraticVariationApprox
        (fun s (_u : Unit) => nnrealIntegralPrimitive g s) t (n + 1) ())
      Filter.atTop (nhds 0) := by
  let C := (∫ s in Set.Icc (0 : ℝ) (t : ℝ), |g s|) + 1
  have hnonneg : 0 ≤ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), |g s| :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  apply tendsto_quadraticVariationApprox_zero_of_continuousOn_of_variation_le
    (X := fun s (_u : Unit) => nnrealIntegralPrimitive g s) t () C
  · dsimp only [C]
    linarith
  · exact continuousOn_nnrealIntegralPrimitive hg
  · intro n
    exact (totalVariationApprox_nnrealIntegralPrimitive_le hg n).trans (by
      dsimp only [C]
      linarith)

/-- The finite-variation drift component of an Itô process. -/
noncomputable def integratedDrift
    (μ : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (t : ℝ), μ s.toNNReal ω

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The drift component has pathwise quadratic variation zero on every
horizon where the drift path is integrable. -/
theorem tendsto_quadraticVariationApprox_integratedDrift_zero
    (μ : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W)
    (hμ : IntegrableOn (fun s : ℝ => μ s.toNNReal ω)
      (Set.Icc (0 : ℝ) (t : ℝ))) :
    Filter.Tendsto
      (fun n => quadraticVariationApprox (integratedDrift μ) t (n + 1) ω)
      Filter.atTop (nhds 0) := by
  have h := tendsto_quadraticVariationApprox_nnrealIntegralPrimitive_zero
    (g := fun s : ℝ => μ s.toNNReal ω) (t := t) hμ
  convert h using 1
  funext n
  unfold quadraticVariationApprox integratedDrift nnrealIntegralPrimitive
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Joint measurability of the drift makes its integral at each fixed time a
strongly measurable random variable. -/
theorem stronglyMeasurable_integratedDrift
    (hμ : Measurable (Function.uncurry μ)) (t : ℝ≥0) :
    StronglyMeasurable (integratedDrift μ t) := by
  let S : Set ℝ := Set.Icc (0 : ℝ) (t : ℝ)
  have hpair : Measurable (fun p : W × ℝ => (p.2.toNNReal, p.1)) :=
    Measurable.prod (measurable_real_toNNReal.comp measurable_snd) measurable_fst
  have hbase : Measurable (fun p : W × ℝ => μ p.2.toNNReal p.1) :=
    hμ.comp hpair
  have hset : MeasurableSet {p : W × ℝ | p.2 ∈ S} :=
    measurableSet_Icc.preimage measurable_snd
  have hind : StronglyMeasurable (fun p : W × ℝ =>
      if p.2 ∈ S then μ p.2.toNNReal p.1 else 0) := by
    exact (hbase.piecewise hset measurable_const).stronglyMeasurable
  have hi := hind.integral_prod_right' (ν := volume)
  change StronglyMeasurable (fun ω => ∫ s in S, μ s.toNNReal ω)
  convert hi using 1
  funext ω
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    by_cases hs : s ∈ S
    · simp only [S, Set.indicator_of_mem hs, if_pos hs]
    · simp only [S, Set.indicator_of_notMem hs, if_neg hs]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Every uniform-partition quadratic-variation sum of the drift component
is strongly measurable. -/
theorem stronglyMeasurable_quadraticVariationApprox_integratedDrift
    (hμ : Measurable (Function.uncurry μ)) (t : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (quadraticVariationApprox (integratedDrift μ) t n) := by
  unfold quadraticVariationApprox
  have hs := Finset.stronglyMeasurable_sum (Finset.range n)
    (fun i _hi => by
      have hd := (stronglyMeasurable_integratedDrift hμ
        (uniformPartitionTime t n (i + 1))).sub
        (stronglyMeasurable_integratedDrift hμ
          (uniformPartitionTime t n i))
      convert hd.mul hd using 1)
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

end StochasticCalculus
