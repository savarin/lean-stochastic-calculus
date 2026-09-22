/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.ItoProcess

/-!
# Quadratic variation (L1.2, L1.3)

L1.2: `⟨B⟩_t = t`. Route: partition mesh → 0, L² convergence of
`Σ(B_{t_{i+1}} - B_{t_i})² → t`. See task-spec.md § L1.2.

L1.3: `⟨X⟩_t = ∫₀ᵗ σ_s² ds` for a general Itô process. Generalizes L1.2
via the Itô integral's isometry — do not re-derive the isometry, cite it
from Prerequisites.lean. See task-spec.md § L1.3.

L1.2 uses literal `L²(P)` convergence of squared-increment sums along
uniform partitions. L1.3 uses convergence in probability: a predictable
`L²` diffusion need not have the fourth moments needed for an `L²` limit
of squared increments.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace

set_option linter.unusedDecidableInType false

section TendstoInMeasureRealAlgebra

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise addition preserves real-valued convergence in measure over an
arbitrary filter, without measurability assumptions on the functions. -/
theorem TendstoInMeasure.add_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u v : ι → Ω → ℝ} {U V : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U)
    (hv : TendstoInMeasure Q v l V) :
    TendstoInMeasure Q (fun i ω => u i ω + v i ω) l
      (fun ω => U ω + V ω) := by
  rw [tendstoInMeasure_iff_dist] at hu hv ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have huHalf := hu (ε / 2) hhalf
  have hvHalf := hv (ε / 2) hhalf
  have hsum : Filter.Tendsto
      (fun i =>
        Q {ω | ε / 2 ≤ dist (u i ω) (U ω)} +
          Q {ω | ε / 2 ≤ dist (v i ω) (V ω)}) l (nhds 0) := by
    simpa only [add_zero] using huHalf.add hvHalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro i
  calc
    Q {ω | ε ≤ dist (u i ω + v i ω) (U ω + V ω)} ≤
        Q ({ω | ε / 2 ≤ dist (u i ω) (U ω)} ∪
          {ω | ε / 2 ≤ dist (v i ω) (V ω)}) := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      change ε ≤ dist (u i ω + v i ω) (U ω + V ω) at hω
      by_contra hUnion
      have huSmall : dist (u i ω) (U ω) < ε / 2 :=
        lt_of_not_ge (fun huBad => hUnion (Or.inl huBad))
      have hvSmall : dist (v i ω) (V ω) < ε / 2 :=
        lt_of_not_ge (fun hvBad => hUnion (Or.inr hvBad))
      have hdist :
          dist (u i ω + v i ω) (U ω + V ω) ≤
            dist (u i ω) (U ω) + dist (v i ω) (V ω) :=
        dist_add_add_le _ _ _ _
      linarith
    _ ≤ Q {ω | ε / 2 ≤ dist (u i ω) (U ω)} +
        Q {ω | ε / 2 ≤ dist (v i ω) (V ω)} := measure_union_le _ _

/-- Deterministic scalar multiplication preserves real-valued convergence in
measure over an arbitrary filter, without measurability assumptions on the
functions. -/
theorem TendstoInMeasure.const_mul_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u : ι → Ω → ℝ} {U : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U) (c : ℝ) :
    TendstoInMeasure Q (fun i ω => c * u i ω) l (fun ω => c * U ω) := by
  rw [tendstoInMeasure_iff_norm] at hu ⊢
  intro ε hε
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, sub_self, norm_zero, Set.ofPred_false, measure_empty,
      not_le.mpr hε] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0))
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    have hscaled := hu (ε / |c|) (div_pos hε hcpos)
    have hfun :
        (fun i => Q {x | ε ≤ ‖c * u i x - c * U x‖}) =
        (fun i => Q {x | ε / |c| ≤ ‖u i x - U x‖}) := by
      funext i
      apply congrArg Q
      ext ω
      simp only [Set.mem_ofPred_eq, ← mul_sub, norm_mul, Real.norm_eq_abs]
      rw [div_le_iff₀ hcpos, mul_comm]
    rw [hfun]
    exact hscaled

/-- Pointwise subtraction preserves real-valued convergence in measure over
an arbitrary filter, without measurability assumptions on the functions. -/
theorem TendstoInMeasure.sub_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u v : ι → Ω → ℝ} {U V : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U)
    (hv : TendstoInMeasure Q v l V) :
    TendstoInMeasure Q (fun i ω => u i ω - v i ω) l
      (fun ω => U ω - V ω) := by
  have hneg := hv.const_mul_real_noMeas (-1)
  have hadd := hu.add_real_noMeas hneg
  apply hadd.congr
  · intro i
    filter_upwards with ω
    ring
  · filter_upwards with ω
    ring

/-- Convergence in measure of real-valued sequences is preserved by
pointwise addition. Mathlib's convergence-in-measure API does not currently
package this algebraic operation. -/
theorem TendstoInMeasure.add_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u v : ℕ → Ω → ℝ} {U V : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (hv : TendstoInMeasure Q v Filter.atTop V)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hvMeas : ∀ n, AEStronglyMeasurable (v n) Q) :
    TendstoInMeasure Q (fun n ω => u n ω + v n ω)
      Filter.atTop (fun ω => U ω + V ω) := by
  have _hsumMeas : ∀ n, AEStronglyMeasurable
      (fun ω => u n ω + v n ω) Q :=
    fun n => (huMeas n).add (hvMeas n)
  exact hu.add_real_noMeas hv

/-- Convergence in measure of real-valued sequences is preserved by
pointwise subtraction. -/
theorem TendstoInMeasure.sub_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u v : ℕ → Ω → ℝ} {U V : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (hv : TendstoInMeasure Q v Filter.atTop V)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hvMeas : ∀ n, AEStronglyMeasurable (v n) Q) :
    TendstoInMeasure Q (fun n ω => u n ω - v n ω)
      Filter.atTop (fun ω => U ω - V ω) := by
  have _hsubMeas : ∀ n, AEStronglyMeasurable
      (fun ω => u n ω - v n ω) Q :=
    fun n => (huMeas n).sub (hvMeas n)
  exact hu.sub_real_noMeas hv

/-- Convergence in measure of real-valued sequences is preserved by
multiplication by a deterministic scalar. -/
theorem TendstoInMeasure.const_mul_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u : ℕ → Ω → ℝ} {U : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q) (c : ℝ) :
    TendstoInMeasure Q (fun n ω => c * u n ω)
      Filter.atTop (fun ω => c * U ω) := by
  have _hmulMeas : ∀ n, AEStronglyMeasurable
      (fun ω => c * u n ω) Q :=
    fun n => aestronglyMeasurable_const.mul (huMeas n)
  exact hu.const_mul_real_noMeas c

/-- Convergence in measure of real-valued sequences is preserved by
pointwise multiplication by a fixed measurable random variable. -/
theorem TendstoInMeasure.mul_fixed_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u : ℕ → Ω → ℝ} {U c : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hcMeas : AEStronglyMeasurable c Q) :
    TendstoInMeasure Q (fun n ω => c ω * u n ω)
      Filter.atTop (fun ω => c ω * U ω) := by
  have hmulMeas : ∀ n, AEStronglyMeasurable
      (fun ω => c ω * u n ω) Q :=
    fun n => hcMeas.mul (huMeas n)
  rw [exists_seq_tendstoInMeasure_atTop_iff hmulMeas]
  intro ns hns
  obtain ⟨ms, hms, huAE⟩ := (hu.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [huAE] with ω hu'
  exact hu'.const_mul (c ω)

end MeasureTheory

end TendstoInMeasureRealAlgebra

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

private lemma monotone_uniformPartitionTime (t : ℝ≥0) (n : ℕ) :
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

private lemma uniformPartitionTime_succ_nndist (t : ℝ≥0) {n : ℕ}
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

/-- `B` has quadratic variation `q` at `t` when its uniform-partition
squared-increment sums converge to `q` in `L²(P)`. -/
def HasQuadraticVariationAt
    (B : ℝ≥0 → W → ℝ) (P : Measure W) (t : ℝ≥0) (q : ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ ↦ eLpNorm (fun ω ↦ quadraticVariationApprox B t (n + 1) ω - q) 2 P)
    Filter.atTop (nhds 0)

/-- Quadratic variation in probability, used when the limiting bracket is random. -/
def HasQuadraticVariationInProbabilityAt
    (X : ℝ≥0 → W → ℝ) (P : Measure W) (t : ℝ≥0) (q : W → ℝ) : Prop :=
  TendstoInMeasure P
    (fun n : ℕ ↦ quadraticVariationApprox X t (n + 1))
    Filter.atTop q

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic variation in probability is preserved by deterministic scalar
multiplication, including when the bracket is random. -/
theorem HasQuadraticVariationInProbabilityAt.const_mul
    [IsFiniteMeasure P] {t : ℝ≥0} {q : W → ℝ}
    (hX : HasQuadraticVariationInProbabilityAt X P t q)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P) (c : ℝ) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega => c * X s omega) P t
      (fun omega => c ^ 2 * q omega) := by
  have hQmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox X t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      hXmeas t (n + 1)
  unfold HasQuadraticVariationInProbabilityAt at hX ⊢
  have hscaled := hX.const_mul_real hQmeas (c ^ 2)
  apply hscaled.congr_left
  intro n
  filter_upwards with omega
  rw [quadraticVariationApprox_const_mul]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A process with almost-everywhere continuous nondecreasing paths has zero
quadratic variation in probability at every fixed time. -/
theorem quadraticVariation_continuous_monotone_inProbability_zero
    [IsFiniteMeasure P]
    (A : ℝ≥0 → W → ℝ)
    (hAmeas : ∀ s, AEStronglyMeasurable (A s) P)
    (hApath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ A s omega) ∧ Monotone (fun s ↦ A s omega))
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt A P t (fun _ ↦ 0) := by
  unfold HasQuadraticVariationInProbabilityAt
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact aestronglyMeasurable_quadraticVariationApprox hAmeas t (n + 1)
  · filter_upwards [hApath] with omega homega
    exact tendsto_quadraticVariationApprox_zero_of_continuous_monotone
      A t omega homega.1 homega.2

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic variation in probability is scaled pointwise by the square of a
measurable random multiplier that is constant in time. -/
theorem HasQuadraticVariationInProbabilityAt.timeConstant_mul
    [IsFiniteMeasure P] {t : ℝ≥0} {q : W → ℝ}
    (hX : HasQuadraticVariationInProbabilityAt X P t q)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (c : W → ℝ) (hcMeas : AEStronglyMeasurable c P) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega => c omega * X s omega) P t
      (fun omega => c omega ^ 2 * q omega) := by
  have hQmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox X t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      hXmeas t (n + 1)
  unfold HasQuadraticVariationInProbabilityAt at hX ⊢
  have hscaled := hX.mul_fixed_real hQmeas (AEStronglyMeasurable.pow hcMeas 2)
  apply hscaled.congr_left
  intro n
  filter_upwards with omega
  simpa only [Pi.pow_apply] using
    (quadraticVariationApprox_timeConstant_mul c X t (n + 1) omega).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Literal `L²` quadratic variation implies quadratic variation in
probability when the process is measurable at each fixed time. -/
theorem HasQuadraticVariationAt.to_inProbability
    {t : ℝ≥0} {q : ℝ} (hX : HasQuadraticVariationAt X P t q)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P) :
    HasQuadraticVariationInProbabilityAt X P t (fun _ => q) := by
  unfold HasQuadraticVariationInProbabilityAt
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  · intro n
    exact aestronglyMeasurable_quadraticVariationApprox hXmeas t (n + 1)
  · exact aestronglyMeasurable_const
  · unfold HasQuadraticVariationAt at hX
    convert hX using 1
    funext n
    congr 1

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Uniform-partition quadratic-variation sums respect almost-everywhere
equality of the underlying process at each fixed time. -/
theorem quadraticVariationApprox_congr_ae
    {Y : ℝ≥0 → W → ℝ} (hXY : ∀ s, X s =ᵐ[P] Y s)
    (t : ℝ≥0) (n : ℕ) :
    quadraticVariationApprox X t n =ᵐ[P] quadraticVariationApprox Y t n := by
  have hnext : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n (i + 1)) ω =
        Y (uniformPartitionTime t n (i + 1)) ω :=
    (Finset.range n).eventually_all.mpr fun i _hi => hXY _
  have hprev : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) ω =
        Y (uniformPartitionTime t n i) ω :=
    (Finset.range n).eventually_all.mpr fun i _hi => hXY _
  filter_upwards [hnext, hprev] with ω hn hp
  unfold quadraticVariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [hn i hi, hp i hi]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic variation in probability is invariant under per-time
almost-everywhere changes of the process and an almost-everywhere change of
the proposed limit. -/
theorem HasQuadraticVariationInProbabilityAt.congr
    {Y : ℝ≥0 → W → ℝ} {t : ℝ≥0} {q r : W → ℝ}
    (hX : HasQuadraticVariationInProbabilityAt X P t q)
    (hXY : ∀ s, X s =ᵐ[P] Y s) (hqr : q =ᵐ[P] r) :
    HasQuadraticVariationInProbabilityAt Y P t r := by
  unfold HasQuadraticVariationInProbabilityAt at hX ⊢
  exact hX.congr
    (fun n => quadraticVariationApprox_congr_ae hXY t (n + 1)) hqr

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If the quadratic variations of `X`, `Y`, and `X + Y` converge in
probability, polarization identifies the convergence-in-probability limit of
their quadratic-covariation sums. -/
theorem tendstoInMeasure_quadraticCovariationApprox
    [IsFiniteMeasure P] {Y : ℝ≥0 → W → ℝ} {t : ℝ≥0}
    {qX qY qXY : W → ℝ}
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (hX : HasQuadraticVariationInProbabilityAt X P t qX)
    (hY : HasQuadraticVariationInProbabilityAt Y P t qY)
    (hXY : HasQuadraticVariationInProbabilityAt
      (fun s ω => X s ω + Y s ω) P t qXY) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Y t (n + 1)) Filter.atTop
      (fun ω => (1 / 2 : ℝ) * (qXY ω - qX ω - qY ω)) := by
  have hQXmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox X t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox hXmeas t (n + 1)
  have hQYmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox Y t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox hYmeas t (n + 1)
  have hQXYmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox (fun s ω => X s ω + Y s ω)
        t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      (fun s => (hXmeas s).add (hYmeas s)) t (n + 1)
  have hsubX := hXY.sub_real hX hQXYmeas hQXmeas
  have hsubXY := hsubX.sub_real hY
    (fun n => (hQXYmeas n).sub (hQXmeas n)) hQYmeas
  have hscaled := hsubXY.const_mul_real
    (fun n => ((hQXYmeas n).sub (hQXmeas n)).sub (hQYmeas n)) (1 / 2 : ℝ)
  apply hscaled.congr
  · intro n
    filter_upwards with ω
    rw [quadraticVariationApprox_add]
    ring
  · exact Filter.EventuallyEq.rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic covariation in probability is scaled pointwise by two measurable
random multipliers that are constant in time. -/
theorem tendstoInMeasure_quadraticCovariationApprox_timeConstant_mul
    [IsFiniteMeasure P] {Y : ℝ≥0 → W → ℝ} {t : ℝ≥0} {q : W → ℝ}
    (hCov : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Y t (n + 1))
      Filter.atTop q)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (c d : W → ℝ) (hcMeas : AEStronglyMeasurable c P)
    (hdMeas : AEStronglyMeasurable d P) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => c omega * X s omega)
        (fun s omega => d omega * Y s omega) t (n + 1))
      Filter.atTop (fun omega => c omega * d omega * q omega) := by
  have hCovMeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X Y t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hYmeas t (n + 1)
  have hscaled := hCov.mul_fixed_real hCovMeas (hcMeas.mul hdMeas)
  apply hscaled.congr_left
  intro n
  filter_upwards with omega
  simpa only [Pi.mul_apply] using
    (quadraticCovariationApprox_timeConstant_mul
      c d X Y t (n + 1) omega).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The quadratic variation of a deterministic linear combination is obtained
from the quadratic variations of both summands and their covariation. -/
theorem HasQuadraticVariationInProbabilityAt.linearCombination
    [IsFiniteMeasure P] {Y : ℝ≥0 → W → ℝ} {t : ℝ≥0}
    {qX qY qXY : W → ℝ}
    (hX : HasQuadraticVariationInProbabilityAt X P t qX)
    (hY : HasQuadraticVariationInProbabilityAt Y P t qY)
    (hCov : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Y t (n + 1))
      Filter.atTop qXY)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (c d : ℝ) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega => c * X s omega + d * Y s omega) P t
      (fun omega => c ^ 2 * qX omega + d ^ 2 * qY omega +
        2 * c * d * qXY omega) := by
  have hQXmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox X t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      hXmeas t (n + 1)
  have hQYmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox Y t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      hYmeas t (n + 1)
  have hCovMeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X Y t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hYmeas t (n + 1)
  unfold HasQuadraticVariationInProbabilityAt at hX hY ⊢
  have hcX := hX.const_mul_real hQXmeas (c ^ 2)
  have hdY := hY.const_mul_real hQYmeas (d ^ 2)
  have hsum := hcX.add_real hdY
    (fun n => aestronglyMeasurable_const.mul (hQXmeas n))
    (fun n => aestronglyMeasurable_const.mul (hQYmeas n))
  have hscaledCov := hCov.const_mul_real hCovMeas (2 * c * d)
  have htotal := hsum.add_real hscaledCov
    (fun n => (aestronglyMeasurable_const.mul (hQXmeas n)).add
      (aestronglyMeasurable_const.mul (hQYmeas n)))
    (fun n => aestronglyMeasurable_const.mul (hCovMeas n))
  apply htotal.congr
  · intro n
    filter_upwards with omega
    rw [quadraticVariationApprox_linearCombination]
  · exact Filter.EventuallyEq.rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic covariation in probability is linear in its first process
argument for deterministic coefficients. -/
theorem tendstoInMeasure_quadraticCovariationApprox_linearCombination_left
    [IsFiniteMeasure P] {Y Z : ℝ≥0 → W → ℝ} {t : ℝ≥0}
    {qXZ qYZ : W → ℝ}
    (hXZ : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Z t (n + 1))
      Filter.atTop qXZ)
    (hYZ : TendstoInMeasure P
      (fun n => quadraticCovariationApprox Y Z t (n + 1))
      Filter.atTop qYZ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (c d : ℝ) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => c * X s omega + d * Y s omega) Z t (n + 1))
      Filter.atTop (fun omega => c * qXZ omega + d * qYZ omega) := by
  have hXZmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X Z t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hZmeas t (n + 1)
  have hYZmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox Y Z t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hYmeas hZmeas t (n + 1)
  have hcXZ := hXZ.const_mul_real hXZmeas c
  have hdYZ := hYZ.const_mul_real hYZmeas d
  have hraw := hcXZ.add_real hdYZ
    (fun n => aestronglyMeasurable_const.mul (hXZmeas n))
    (fun n => aestronglyMeasurable_const.mul (hYZmeas n))
  apply hraw.congr_left
  intro n
  filter_upwards with omega
  unfold quadraticCovariationApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic covariation in probability is linear in its second process
argument for deterministic coefficients. -/
theorem tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
    [IsFiniteMeasure P] {Y Z : ℝ≥0 → W → ℝ} {t : ℝ≥0}
    {qXY qXZ : W → ℝ}
    (hXY : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Y t (n + 1))
      Filter.atTop qXY)
    (hXZ : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Z t (n + 1))
      Filter.atTop qXZ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (c d : ℝ) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox X
        (fun s omega => c * Y s omega + d * Z s omega) t (n + 1))
      Filter.atTop (fun omega => c * qXY omega + d * qXZ omega) := by
  have hXYmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X Y t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hYmeas t (n + 1)
  have hXZmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X Z t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hZmeas t (n + 1)
  have hcXY := hXY.const_mul_real hXYmeas c
  have hdXZ := hXZ.const_mul_real hXZmeas d
  have hraw := hcXY.add_real hdXZ
    (fun n => aestronglyMeasurable_const.mul (hXYmeas n))
    (fun n => aestronglyMeasurable_const.mul (hXZmeas n))
  apply hraw.congr_left
  intro n
  filter_upwards with omega
  unfold quadraticCovariationApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private theorem tendstoInMeasure_quadraticCovariationApprox_zero_right
    [IsFiniteMeasure P] {X : ℝ≥0 → W → ℝ} {t : ℝ≥0} :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox X (fun _ _ => 0) t (n + 1))
      Filter.atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have : quadraticCovariationApprox X (fun _ _ => 0) t (n + 1) =
        (fun _ => 0) := by
      funext omega
      unfold quadraticCovariationApprox
      simp only [sub_self, mul_zero, Finset.sum_const_zero]
    rw [this]
    exact aestronglyMeasurable_const
  · filter_upwards with omega
    have : (fun n => quadraticCovariationApprox X (fun _ _ => 0)
        t (n + 1) omega) = (fun _ => 0) := by
      funext n
      unfold quadraticCovariationApprox
      simp only [sub_self, mul_zero, Finset.sum_const_zero]
    rw [this]
    exact tendsto_const_nhds

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic covariation in probability with a deterministic finite linear
combination is the same finite linear combination of the component limits. -/
theorem tendstoInMeasure_quadraticCovariationApprox_finset_sum
    [IsFiniteMeasure P] {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (X : ℝ≥0 → W → ℝ) (Y : ι → ℝ≥0 → W → ℝ)
    (c : ι → ℝ) (q : ι → W → ℝ) (t : ℝ≥0)
    (hXmeas : ∀ r, AEStronglyMeasurable (X r) P)
    (hYmeas : ∀ i ∈ S, ∀ r, AEStronglyMeasurable (Y i r) P)
    (hCov : ∀ i ∈ S,
      TendstoInMeasure P
        (fun n => quadraticCovariationApprox X (Y i) t (n + 1))
        Filter.atTop (q i)) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox X
        (fun r omega => ∑ i ∈ S, c i * Y i r omega) t (n + 1))
      Filter.atTop (fun omega => ∑ i ∈ S, c i * q i omega) := by
  induction S using Finset.induction_on with
  | empty =>
      have hzero :=
        tendstoInMeasure_quadraticCovariationApprox_zero_right
          (P := P) (X := X) (t := t)
      apply hzero.congr
      · intro n
        filter_upwards with omega
        unfold quadraticCovariationApprox
        simp only [Finset.sum_empty, sub_self, mul_zero, Finset.sum_const_zero]
      · filter_upwards with omega
        rw [Finset.sum_empty]
  | @insert i S hi ih =>
      have hYiMeas : ∀ r, AEStronglyMeasurable (Y i r) P :=
        hYmeas i (Finset.mem_insert_self i S)
      have hSumMeas : ∀ r, AEStronglyMeasurable
          (fun omega => ∑ j ∈ S, c j * Y j r omega) P := by
        intro r
        have hterm : ∀ j ∈ S, AEStronglyMeasurable
            (fun omega => c j * Y j r omega) P := by
          intro j hj
          exact aestronglyMeasurable_const.mul
            (hYmeas j (Finset.mem_insert_of_mem hj) r)
        convert Finset.aestronglyMeasurable_sum S hterm using 1
        funext omega
        rw [Finset.sum_apply]
      have hRest := ih
        (fun j hj r => hYmeas j (Finset.mem_insert_of_mem hj) r)
        (fun j hj => hCov j (Finset.mem_insert_of_mem hj))
      have hCombined :=
        tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
          (hCov i (Finset.mem_insert_self i S)) hRest hXmeas hYiMeas hSumMeas
          (c i) 1
      simpa only [Finset.sum_insert hi, one_mul] using hCombined

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Adding a random variable that is constant in time does not change
quadratic variation in probability. -/
theorem HasQuadraticVariationInProbabilityAt.add_timeConstant
    {Y : ℝ≥0 → W → ℝ} {t : ℝ≥0} {q : W → ℝ}
    (hY : HasQuadraticVariationInProbabilityAt Y P t q) (c : W → ℝ) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => c ω + Y s ω) P t q := by
  unfold HasQuadraticVariationInProbabilityAt at hY ⊢
  exact hY.congr
    (fun n => Filter.Eventually.of_forall fun ω =>
      (quadraticVariationApprox_add_timeConstant Y c t (n + 1) ω).symm)
    Filter.EventuallyEq.rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- In probability, adding a zero-quadratic-variation process preserves the
quadratic variation of the other summand. -/
theorem HasQuadraticVariationInProbabilityAt.add_of_left_zero
    [IsFiniteMeasure P] {A M : ℝ≥0 → W → ℝ} {t : ℝ≥0} {q : W → ℝ}
    (hA : HasQuadraticVariationInProbabilityAt A P t (fun _ => 0))
    (hM : HasQuadraticVariationInProbabilityAt M P t q)
    (haddMeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox (fun s ω => A s ω + M s ω) t (n + 1)) P) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => A s ω + M s ω) P t q := by
  unfold HasQuadraticVariationInProbabilityAt at hA hM ⊢
  rw [exists_seq_tendstoInMeasure_atTop_iff haddMeas]
  intro ns hns
  obtain ⟨nsA, hnsA, hAe⟩ :=
    (hA.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hnsA' : StrictMono (ns ∘ nsA) := hns.comp hnsA
  obtain ⟨nsM, hnsM, hMe⟩ :=
    (hM.comp hnsA'.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨nsA ∘ nsM, hnsA.comp hnsM, ?_⟩
  filter_upwards [hAe, hMe] with ω hAω hMω
  have hAfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox A t (ns (nsA (nsM i)) + 1) ω)
      Filter.atTop (nhds 0) := by
    convert hAω.comp hnsM.tendsto_atTop using 1
    funext i
    rfl
  have hMfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox M t (ns (nsA (nsM i)) + 1) ω)
      Filter.atTop (nhds (q ω)) := by
    simpa only [Function.comp_apply] using hMω
  simpa only [Function.comp_apply] using
    tendsto_quadraticVariationApprox_add_of_left_qv_zero
      (fun i => ns (nsA (nsM i)) + 1) A M t ω (q ω) hAfinal hMfinal

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A convenient measurable-process form of
`HasQuadraticVariationInProbabilityAt.add_of_left_zero`. -/
theorem HasQuadraticVariationInProbabilityAt.add_of_left_zero_of_aestronglyMeasurable
    [IsFiniteMeasure P] {A M : ℝ≥0 → W → ℝ} {t : ℝ≥0} {q : W → ℝ}
    (hA : HasQuadraticVariationInProbabilityAt A P t (fun _ => 0))
    (hM : HasQuadraticVariationInProbabilityAt M P t q)
    (hAmeas : ∀ s, AEStronglyMeasurable (A s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => A s ω + M s ω) P t q := by
  apply hA.add_of_left_zero hM
  intro n
  exact aestronglyMeasurable_quadraticVariationApprox
    (fun s => (hAmeas s).add (hMmeas s)) t (n + 1)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The drift integral has quadratic variation zero in probability on a
finite measure space. -/
theorem quadraticVariation_integratedDrift_inProbability
    [IsFiniteMeasure P]
    (hμmeas : Measurable (Function.uncurry μ)) (t : ℝ≥0)
    (hμint : ∀ ω, IntegrableOn (fun s : ℝ => μ s.toNNReal ω)
      (Set.Icc (0 : ℝ) (t : ℝ))) :
    HasQuadraticVariationInProbabilityAt (integratedDrift μ) P t (fun _ => 0) := by
  unfold HasQuadraticVariationInProbabilityAt
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (stronglyMeasurable_quadraticVariationApprox_integratedDrift
      hμmeas t (n + 1)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω =>
      tendsto_quadraticVariationApprox_integratedDrift_zero μ t ω (hμint ω)

-- Differentiate the centered Gaussian moment-generating function four
-- times to obtain the single-increment fourth moment used below.
private lemma integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  calc
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v =
        iteratedDeriv 4 (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero]
      · rfl
      · simp only [integrableExpSet_fun_id_gaussianReal, interior_univ, Set.mem_univ]
    _ = 3 * (v : ℝ) ^ 2 := by
      rw [mgf_fun_id_gaussianReal]
      let a : ℝ := v
      let f : ℝ → ℝ := fun t ↦ Real.exp (a * t ^ 2 / 2)
      have hf (t : ℝ) : HasDerivAt f (a * t * f t) t := by
        have hpoly := (((hasDerivAt_id t).pow 2).const_mul a).div_const 2
        dsimp only [f]
        convert hpoly.exp using 1
        · funext x
          simp only [id_eq, Pi.pow_apply]
        · simp only [id_eq, Pi.pow_apply]
          ring
      have h1 : deriv f = fun t ↦ a * t * f t := by
        funext t
        exact (hf t).deriv
      have hp1 (t : ℝ) : HasDerivAt (fun x ↦ a * x) a t := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul a
      have hf2 (t : ℝ) :
          HasDerivAt (fun x ↦ a * x * f x) ((a + a ^ 2 * t ^ 2) * f t) t := by
        convert (hp1 t).mul (hf t) using 1
        all_goals first | rfl | ring
      have h2 : deriv (fun t ↦ a * t * f t) = fun t ↦ (a + a ^ 2 * t ^ 2) * f t := by
        funext t
        exact (hf2 t).deriv
      have hp2 : deriv (fun x : ℝ ↦ a + a ^ 2 * x ^ 2) = fun t ↦ 2 * a ^ 2 * t := by
        funext t
        rw [deriv_fun_add (by fun_prop) (by fun_prop)]
        simp only [deriv_const', differentiableAt_const, differentiableAt_fun_id,
          Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul,
          deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
        ring
      have h3 : deriv (fun t ↦ (a + a ^ 2 * t ^ 2) * f t) =
          fun t ↦ (3 * a ^ 2 * t + a ^ 3 * t ^ 3) * f t := by
        funext t
        rw [deriv_fun_mul (by fun_prop) (hf t).differentiableAt,
          congrFun hp2 t, congrFun h1 t]
        ring
      have hp3 : deriv (fun x : ℝ ↦ 3 * a ^ 2 * x + a ^ 3 * x ^ 3) =
          fun t ↦ 3 * a ^ 2 + 3 * a ^ 3 * t ^ 2 := by
        funext t
        have hlinear : deriv (fun x : ℝ ↦ 3 * a ^ 2 * x) t = 3 * a ^ 2 := by
          simpa only [id_eq, mul_one] using
            ((hasDerivAt_id t).const_mul (3 * a ^ 2)).deriv
        have hcubic : deriv (fun x : ℝ ↦ a ^ 3 * x ^ 3) t = 3 * a ^ 3 * t ^ 2 := by
          have hraw := (((hasDerivAt_id t).pow 3).const_mul (a ^ 3)).deriv
          simp only [id_eq, Pi.pow_apply] at hraw
          convert hraw using 1
          norm_num
          ring
        rw [deriv_fun_add (by fun_prop) (by fun_prop), hlinear, hcubic]
      have h4 : deriv (fun t ↦ (3 * a ^ 2 * t + a ^ 3 * t ^ 3) * f t) =
          fun t ↦ (3 * a ^ 2 + 6 * a ^ 3 * t ^ 2 + a ^ 4 * t ^ 4) * f t := by
        funext t
        rw [deriv_fun_mul (by fun_prop) (hf t).differentiableAt,
          congrFun hp3 t, congrFun h1 t]
        ring
      simp only [zero_mul, zero_add]
      change iteratedDeriv 4 f 0 = 3 * a ^ 2
      rw [iteratedDeriv_succ (n := 3), iteratedDeriv_succ (n := 2),
        iteratedDeriv_succ (n := 1), iteratedDeriv_succ (n := 0), iteratedDeriv_zero,
        h1, h2, h3, h4]
      norm_num [f]

/-- A real random variable with a centered Gaussian law has fourth moment
`3 * v ^ 2`. -/
lemma integral_pow_four_of_hasLaw_gaussianReal
    {Omega : Type*} [MeasurableSpace Omega] {Q : Measure Omega}
    {Z : Omega → ℝ} (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    ∫ omega, Z omega ^ 4 ∂Q = 3 * (v : ℝ) ^ 2 := by
  calc
    ∫ omega, Z omega ^ 4 ∂Q =
        ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := by
      simpa only [Function.comp_apply] using
        hZ.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
    _ = 3 * (v : ℝ) ^ 2 := integral_pow_four_gaussianReal v

/-- Fourth powers of real Gaussian random variables are integrable. -/
lemma integrable_pow_four_of_hasLaw_gaussianReal
    {Omega : Type*} [MeasurableSpace Omega] {Q : Measure Omega}
    {Z : Omega → ℝ} (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    Integrable (fun omega => Z omega ^ 4) Q := by
  let _ : IsProbabilityMeasure Q := hZ.isProbabilityMeasure
  have hmem : MemLp Z 4 Q := hZ.hasGaussianLaw.memLp (by norm_num)
  apply hmem.integrable_norm_pow'.congr
  filter_upwards with omega
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The expected fourth variation of a pre-Brownian process on an `n`-step
uniform partition is exactly `3 * t² / n`. -/
theorem integral_fourthVariationApprox_preBrownianReal
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ omega, fourthVariationApprox B t n omega ∂P =
      3 * (t : ℝ) ^ 2 / (n : ℝ) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let d : ℝ≥0 := t / (n : ℝ≥0)
  have hLaw (i : ℕ) : HasLaw
      (B (uniformPartitionTime t n (i + 1)) -
        B (uniformPartitionTime t n i)) (gaussianReal 0 d) P := by
    have hraw := hB.hasLaw_sub (uniformPartitionTime t n (i + 1))
      (uniformPartitionTime t n i)
    convert hraw using 1
    exact congrArg (gaussianReal 0)
      (uniformPartitionTime_succ_nndist t hn i).symm
  have hInt (i : ℕ) : Integrable
      (fun omega => (B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega) ^ 4) P := by
    change Integrable (fun omega =>
      ((B (uniformPartitionTime t n (i + 1)) -
        B (uniformPartitionTime t n i)) omega) ^ 4) P
    exact integrable_pow_four_of_hasLaw_gaussianReal d (hLaw i)
  unfold fourthVariationApprox
  rw [integral_finsetSum (Finset.range n) (fun i _hi => hInt i)]
  calc
    (∑ i ∈ Finset.range n,
        ∫ omega, (B (uniformPartitionTime t n (i + 1)) omega -
          B (uniformPartitionTime t n i) omega) ^ 4 ∂P) =
        ∑ _i ∈ Finset.range n, 3 * (d : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      change (∫ omega,
        ((B (uniformPartitionTime t n (i + 1)) -
          B (uniformPartitionTime t n i)) omega) ^ 4 ∂P) = _
      exact integral_pow_four_of_hasLaw_gaussianReal d (hLaw i)
    _ = 3 * (t : ℝ) ^ 2 / (n : ℝ) := by
      dsimp only [d]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        NNReal.coe_div, NNReal.coe_natCast]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      field_simp [hnR]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The fourth variation of a pre-Brownian process along increasingly fine
uniform partitions vanishes in probability.  Only the Gaussian increment
laws are used; no continuity of the chosen path version is required. -/
theorem fourthVariationApprox_preBrownianReal_tendstoInMeasure_zero
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => fourthVariationApprox B t (n + 1)) Filter.atTop
      (fun _ => 0) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hbound : Filter.Tendsto
      (fun n : ℕ => (3 * (t : ℝ) ^ 2 / ((n : ℝ) + 1)) / epsilon)
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto
        (fun n : ℕ => 3 * (t : ℝ) ^ 2 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat (3 * (t : ℝ) ^ 2))
    simpa only [zero_div] using hbase.div_const epsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hbound) delta hdelta
  refine ⟨N, fun n hn => ?_⟩
  have hInt : Integrable (fourthVariationApprox B t (n + 1)) P := by
    unfold fourthVariationApprox
    apply integrable_finsetSum
    intro i _hi
    change Integrable (fun omega =>
      ((B (uniformPartitionTime t (n + 1) (i + 1)) -
        B (uniformPartitionTime t (n + 1) i)) omega) ^ 4) P
    exact integrable_pow_four_of_hasLaw_gaussianReal _ (hB.hasLaw_sub _ _)
  have hMarkov : epsilon * P.real
      {omega | epsilon ≤ fourthVariationApprox B t (n + 1) omega} ≤
      ∫ omega, fourthVariationApprox B t (n + 1) omega ∂P := by
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall
        (fourthVariationApprox_nonneg B t (n + 1))) hInt epsilon
  have hmeasure : P.real
      {omega | epsilon ≤ fourthVariationApprox B t (n + 1) omega} ≤
      (3 * (t : ℝ) ^ 2 / ((n : ℝ) + 1)) / epsilon := by
    apply (le_div_iff₀ hepsilon).2
    rw [mul_comm]
    calc
      _ ≤ ∫ omega, fourthVariationApprox B t (n + 1) omega ∂P := hMarkov
      _ = 3 * (t : ℝ) ^ 2 / ((n : ℝ) + 1) := by
        convert integral_fourthVariationApprox_preBrownianReal hB t
          (Nat.zero_lt_succ n) using 1
        all_goals norm_num
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (div_nonneg (by positivity) (by positivity))
      hepsilon.le)] at hsmall
  change dist
    (P.real {omega | epsilon ≤
      ‖fourthVariationApprox B t (n + 1) omega - 0‖}) 0 < delta
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hset : {omega | epsilon ≤
      ‖fourthVariationApprox B t (n + 1) omega - 0‖} =
      {omega | epsilon ≤ fourthVariationApprox B t (n + 1) omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (fourthVariationApprox_nonneg B t (n + 1) omega)]
  rw [hset]
  exact hmeasure.trans_lt hsmall

/-- The second moment of a centered real Gaussian is its variance. -/
lemma integral_pow_two_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have hmem : MemLp (fun x : ℝ ↦ x) 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal 2
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_sub hmem] at hvar
  norm_num [integral_id_gaussianReal] at hvar
  exact hvar

/-- A real random variable with centered Gaussian law has second moment
equal to the variance parameter. -/
lemma integral_pow_two_of_hasLaw_gaussianReal
    {Omega : Type*} [MeasurableSpace Omega] {Q : Measure Omega}
    {Z : Omega → ℝ} (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    ∫ omega, Z omega ^ 2 ∂Q = (v : ℝ) := by
  calc
    ∫ omega, Z omega ^ 2 ∂Q =
        ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v := by
      simpa only [Function.comp_apply] using
        hZ.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    _ = (v : ℝ) := integral_pow_two_gaussianReal v

/-- Squares of real random variables with centered Gaussian law are
integrable. -/
lemma integrable_pow_two_of_hasLaw_gaussianReal
    {Omega : Type*} [MeasurableSpace Omega] {Q : Measure Omega}
    {Z : Omega → ℝ} (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    Integrable (fun omega => Z omega ^ 2) Q := by
  let _ : IsProbabilityMeasure Q := hZ.isProbabilityMeasure
  have hmem : MemLp Z 2 Q := hZ.hasGaussianLaw.memLp (by norm_num)
  apply hmem.integrable_norm_pow'.congr
  filter_upwards with omega
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]

private lemma integral_centered_square_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 ∂gaussianReal 0 v =
      2 * (v : ℝ) ^ 2 := by
  have hmem4 : MemLp (fun x : ℝ ↦ x) 4 (gaussianReal 0 v) :=
    memLp_id_gaussianReal 4
  have hmem2 : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 v) := by
    let _ : ENNReal.HolderTriple 4 4 2 := ⟨by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← two_mul,
        ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩
    have hmul : MemLp ((fun x : ℝ ↦ x) * (fun x : ℝ ↦ x)) 2
        (gaussianReal 0 v) := hmem4.mul hmem4
    convert hmul using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    hmem2.integrable (by norm_num)
  have hint4 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) := by
    have hm : MemLp ((fun x : ℝ ↦ x ^ 2) * (fun x : ℝ ↦ x ^ 2)) 1
        (gaussianReal 0 v) := hmem2.mul hmem2
    have hm1 : MemLp (fun x : ℝ ↦ x ^ 4) 1 (gaussianReal 0 v) := by
      convert hm using 1
      funext x
      simp only [Pi.mul_apply]
      ring
    exact memLp_one_iff_integrable.mp hm1
  have hpoly : (fun x : ℝ ↦ (x ^ 2 - (v : ℝ)) ^ 2) =
      fun x ↦ x ^ 4 - (2 * (v : ℝ)) * x ^ 2 + (v : ℝ) ^ 2 := by
    funext x
    ring
  rw [hpoly]
  calc
    (∫ x : ℝ, x ^ 4 - 2 * (v : ℝ) * x ^ 2 + (v : ℝ) ^ 2
        ∂gaussianReal 0 v) =
        (∫ x : ℝ, x ^ 4 - 2 * (v : ℝ) * x ^ 2 ∂gaussianReal 0 v) +
          ∫ _x : ℝ, (v : ℝ) ^ 2 ∂gaussianReal 0 v := by
      exact integral_add (hint4.sub (hint2.const_mul _)) (integrable_const _)
    _ = ((∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) -
          ∫ x : ℝ, 2 * (v : ℝ) * x ^ 2 ∂gaussianReal 0 v) +
          ∫ _x : ℝ, (v : ℝ) ^ 2 ∂gaussianReal 0 v := by
      rw [integral_sub hint4 (hint2.const_mul _)]
    _ = 2 * (v : ℝ) ^ 2 := by
      rw [integral_const_mul, integral_const, integral_pow_four_gaussianReal,
        integral_pow_two_gaussianReal]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      ring

/-- A centered squared Gaussian random variable is square integrable. -/
lemma centeredSquare_memLp_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {Z : Ω → ℝ}
    (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    MemLp (fun ω ↦ Z ω ^ 2 - (v : ℝ)) 2 Q := by
  let _ : IsProbabilityMeasure Q := hZ.isProbabilityMeasure
  have hmem4 : MemLp Z 4 Q := hZ.hasGaussianLaw.memLp (by norm_num)
  have hmem2 : MemLp (fun ω ↦ Z ω ^ 2) 2 Q := by
    let _ : ENNReal.HolderTriple 4 4 2 := ⟨by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← two_mul,
        ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩
    have hmul : MemLp (Z * Z) 2 Q := hmem4.mul hmem4
    convert hmul using 1
    funext ω
    simp only [Pi.mul_apply]
    ring
  convert hmem2.sub (memLp_const (v : ℝ)) using 1
  funext ω
  rfl

/-- The centered square of a centered Gaussian random variable has mean zero. -/
lemma integral_centeredSquare_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {Z : Ω → ℝ}
    (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    (∫ ω, Z ω ^ 2 - (v : ℝ) ∂Q) = 0 := by
  calc
    (∫ ω, Z ω ^ 2 - (v : ℝ) ∂Q) =
        ∫ x : ℝ, x ^ 2 - (v : ℝ) ∂gaussianReal 0 v := by
      simpa only [Function.comp_apply] using
        hZ.integral_comp (f := fun x : ℝ ↦ x ^ 2 - (v : ℝ)) (by fun_prop)
    _ = 0 := by
      have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) := by
        have hm : MemLp (fun x : ℝ ↦ x) 2 (gaussianReal 0 v) :=
          memLp_id_gaussianReal 2
        exact hm.integrable_norm_pow' |>.congr (by
          filter_upwards with x
          simp only [Real.norm_eq_abs, sq_abs])
      rw [integral_sub hint2 (integrable_const _), integral_const,
        integral_pow_two_gaussianReal]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, sub_self]

/-- The centered square of a centered Gaussian with variance `v` has variance
`2 * v ^ 2`. -/
lemma variance_centeredSquare_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Z : Ω → ℝ} (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal 0 v) Q) :
    Var[fun ω ↦ Z ω ^ 2 - (v : ℝ); Q] = 2 * (v : ℝ) ^ 2 := by
  have hmem := centeredSquare_memLp_of_hasLaw v hZ
  have hmean := integral_centeredSquare_of_hasLaw v hZ
  rw [variance_eq_sub hmem, hmean]
  norm_num only [Pi.pow_apply, zero_pow, sub_zero]
  calc
    (∫ x, ((fun ω ↦ Z ω ^ 2 - (v : ℝ)) ^ 2) x ∂Q) =
        ∫ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 ∂gaussianReal 0 v := by
      simpa only [Pi.pow_apply, Function.comp_apply] using
        hZ.integral_comp (f := fun x : ℝ ↦ (x ^ 2 - (v : ℝ)) ^ 2) (by fun_prop)
    _ = 2 * (v : ℝ) ^ 2 := integral_centered_square_sq_gaussianReal v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Exact `L²` norm of the centered squared pre-Brownian increments along any
monotone deterministic finite time grid. This is the non-uniform partition
form of the finite-sum estimate behind Brownian quadratic variation. -/
theorem eLpNorm_preBrownian_centeredSquaredIncrementSum_eq
    (hB : IsPreBrownianReal B P) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) :
    eLpNorm
      (fun ω => ∑ i ∈ Finset.range n,
        ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 -
          (nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ)) : ℝ))) 2 P =
      ENNReal.ofReal
        ((∑ i ∈ Finset.range n,
          2 * (nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ)) : ℝ) ^ 2) ^
            (2 : ℝ)⁻¹) := by
  let hpre := hB
  let _ : IsProbabilityMeasure P := hpre.isGaussianProcess.isProbabilityMeasure
  let d : ℕ → ℝ≥0 := fun i =>
    nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ))
  let Δ : ℕ → W → ℝ := fun i ω =>
    B (τ (i + 1)) ω - B (τ i) ω
  let Y : ℕ → W → ℝ := fun i ω => Δ i ω ^ 2 - (d i : ℝ)
  have hLaw (i : ℕ) : HasLaw (Δ i) (gaussianReal 0 (d i)) P := by
    dsimp only [Δ, d]
    exact hpre.hasLaw_sub (τ (i + 1)) (τ i)
  have hYmem (i : ℕ) : MemLp (Y i) 2 P := by
    simpa only [Y] using centeredSquare_memLp_of_hasLaw (d i) (hLaw i)
  have hYmean (i : ℕ) : (∫ ω, Y i ω ∂P) = 0 := by
    simpa only [Y] using integral_centeredSquare_of_hasLaw (d i) (hLaw i)
  have hYvar (i : ℕ) : Var[Y i; P] = 2 * (d i : ℝ) ^ 2 := by
    simpa only [Y] using variance_centeredSquare_of_hasLaw (d i) (hLaw i)
  have hIndΔ : iIndepFun Δ P := by
    simpa only [Δ] using hpre.hasIndepIncrements.nat hτ
  have hIndY : iIndepFun Y P := by
    have hcomp := hIndΔ.comp
      (fun i (x : ℝ) => x ^ 2 - (d i : ℝ)) (fun _ => by fun_prop)
    simpa only [Y, Function.comp_def] using hcomp
  have hPair : Set.Pairwise (↑(Finset.range n) : Set ℕ)
      (fun i j => Y i ⟂ᵢ[P] Y j) := by
    exact fun i _ j _ hij => hIndY.indepFun hij
  have hVarSum :
      Var[fun ω => ∑ i ∈ Finset.range n, Y i ω; P] =
        ∑ i ∈ Finset.range n, 2 * (d i : ℝ) ^ 2 := by
    rw [show (fun ω => ∑ i ∈ Finset.range n, Y i ω) =
        ∑ i ∈ Finset.range n, Y i by
      funext ω
      simp only [Finset.sum_apply]]
    rw [IndepFun.variance_sum (fun i _ => hYmem i) hPair]
    exact Finset.sum_congr rfl fun i _ => hYvar i
  have hMeanSum : (∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P) = 0 := by
    rw [integral_finsetSum (Finset.range n)
      (fun i _ => (hYmem i).integrable (by norm_num))]
    simp only [hYmean, Finset.sum_const_zero]
  have hMemSum : MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
    memLp_finsetSum (Finset.range n) (fun i _ => hYmem i)
  have hIntegralSq :
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) =
        ∑ i ∈ Finset.range n, 2 * (d i : ℝ) ^ 2 := by
    have hv := variance_eq_sub hMemSum
    rw [hVarSum, hMeanSum] at hv
    norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hv
    exact hv.symm
  have hfun :
      (fun ω => ∑ i ∈ Finset.range n,
        ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 -
          (nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ)) : ℝ))) =
      (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  rw [hfun, hMemSum.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    hIntegralSq]
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian specialization of the pre-Brownian finite-grid estimate. -/
theorem eLpNorm_brownian_centeredSquaredIncrementSum_eq
    (hB : IsBrownianMotion B P) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) :
    eLpNorm
      (fun ω => ∑ i ∈ Finset.range n,
        ((B (τ (i + 1)) ω - B (τ i) ω) ^ 2 -
          (nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ)) : ℝ))) 2 P =
      ENNReal.ofReal
        ((∑ i ∈ Finset.range n,
          2 * (nndist ((τ (i + 1) : ℝ)) ((τ i : ℝ)) : ℝ) ^ 2) ^
            (2 : ℝ)⁻¹) :=
  eLpNorm_preBrownian_centeredSquaredIncrementSum_eq
    hB.toIsPreBrownianReal τ hτ n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A Brownian motion run on a continuous monotone deterministic clock `A`
with `A 0 = 0` has literal `L²` quadratic variation `A t` at time `t`. -/
theorem quadraticVariation_timeChanged_brownian
    (hB : IsBrownianMotion B P) (A : ℝ≥0 → ℝ≥0)
    (hA0 : A 0 = 0) (hAcont : Continuous A) (hAmono : Monotone A)
    (t : ℝ≥0) :
    HasQuadraticVariationAt (fun s omega ↦ B (A s) omega) P t (A t : ℝ) := by
  let τ : ℕ → ℕ → ℝ≥0 := fun n i ↦
    A (uniformPartitionTime t (n + 1) i)
  let S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range (n + 1),
    2 * (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ) ^ 2
  have hgridMono (n : ℕ) : Monotone (τ n) := by
    intro i j hij
    apply hAmono
    unfold uniformPartitionTime
    gcongr
  have hwidth (n i : ℕ) :
      (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ) =
        (τ n (i + 1) : ℝ) - (τ n i : ℝ) := by
    rw [← dist_nndist, Real.dist_eq, abs_of_nonneg]
    exact sub_nonneg.mpr (by
      exact_mod_cast hgridMono n (Nat.le_add_right i 1))
  have hsumWidth (n : ℕ) :
      ∑ i ∈ Finset.range (n + 1),
        (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ) =
          (A t : ℝ) := by
    simp_rw [hwidth n]
    rw [Finset.sum_range_sub (fun i ↦ (τ n i : ℝ)) (n + 1)]
    have hn0 : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
      unfold uniformPartitionTime
      rw [mul_div_cancel_right₀ t hn0]
    have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
    dsimp only [τ]
    rw [htop, hzero, hA0]
    simp only [NNReal.coe_zero, sub_zero]
  have hnorm (n : ℕ) :
      eLpNorm
        (fun omega ↦ quadraticVariationApprox
          (fun s omega ↦ B (A s) omega) t (n + 1) omega - (A t : ℝ))
        2 P = ENNReal.ofReal ((S n) ^ (2 : ℝ)⁻¹) := by
    have hraw := eLpNorm_brownian_centeredSquaredIncrementSum_eq
      hB (τ n) (hgridMono n) (n + 1)
    rw [← hraw]
    congr 1
    funext omega
    unfold quadraticVariationApprox
    rw [Finset.sum_sub_distrib, hsumWidth n]
  have hSnonneg (n : ℕ) : 0 ≤ S n := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro i _hi
    positivity
  have hArealCont : Continuous (fun s ↦ (A s : ℝ)) :=
    NNReal.continuous_coe.comp hAcont
  have hS : Filter.Tendsto S Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let η : ℝ := ε / (2 * (A t : ℝ) + 1)
    have hden : 0 < 2 * (A t : ℝ) + 1 := by positivity
    have hη : 0 < η := div_pos hε hden
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (continuous_uniformPartition_increments_tendsto
        (fun s ↦ (A s : ℝ)) hArealCont t η hη)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hincr := hN n hn
    have hsumBound : S n ≤ 2 * η * (A t : ℝ) := by
      dsimp only [S]
      calc
        ∑ i ∈ Finset.range (n + 1),
            2 * (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ) ^ 2 ≤
            ∑ i ∈ Finset.range (n + 1),
              (2 * η) *
                (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          let d : ℝ :=
            (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ)
          have hd0 : 0 ≤ d := by
            dsimp only [d]
            positivity
          have hdlt : d < η := by
            have hi := hincr i hi
            have hmonoReal :
                0 ≤ (τ n (i + 1) : ℝ) - (τ n i : ℝ) :=
              sub_nonneg.mpr (by
                exact_mod_cast hgridMono n (Nat.le_add_right i 1))
            rw [abs_of_nonneg hmonoReal] at hi
            dsimp only [d]
            rw [hwidth n i]
            simpa only [τ] using hi
          have hprod := mul_nonneg hd0 (sub_nonneg.mpr hdlt.le)
          dsimp only [d] at hd0 hdlt hprod ⊢
          nlinarith only [hprod]
        _ = 2 * η *
            (∑ i ∈ Finset.range (n + 1),
              (nndist ((τ n (i + 1) : ℝ)) ((τ n i : ℝ)) : ℝ)) := by
          rw [Finset.mul_sum]
        _ = 2 * η * (A t : ℝ) := by rw [hsumWidth n]
    have hupper : 2 * η * (A t : ℝ) < ε := by
      have hfrac : 2 * (A t : ℝ) / (2 * (A t : ℝ) + 1) < 1 :=
        (div_lt_one hden).2 (by linarith)
      calc
        2 * η * (A t : ℝ) =
            ε * (2 * (A t : ℝ) / (2 * (A t : ℝ) + 1)) := by
          dsimp only [η]
          field_simp [ne_of_gt hden]
        _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
        _ = ε := mul_one ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hSnonneg n)]
    exact lt_of_le_of_lt hsumBound hupper
  have hsqrt : Filter.Tendsto (fun n ↦ Real.sqrt (S n))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto (Real.sqrt ∘ S) Filter.atTop (nhds 0)
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hS
  unfold HasQuadraticVariationAt
  have heq :
      (fun n : ℕ ↦ eLpNorm
        (fun omega ↦ quadraticVariationApprox
          (fun s omega ↦ B (A s) omega) t (n + 1) omega - (A t : ℝ))
        2 P) =
      (fun n ↦ ENNReal.ofReal (Real.sqrt (S n))) := by
    funext n
    rw [hnorm n]
    simp only [Real.sqrt_eq_rpow, one_div]
  rw [heq]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hsqrt

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The Brownian increment accumulated after a deterministic time `a` has
literal `L²` quadratic variation `t - a` at time `t`. -/
theorem quadraticVariation_brownian_after_time
    (hB : IsBrownianMotion B P) (a t : ℝ≥0) :
    HasQuadraticVariationAt
      (fun s omega ↦ B s omega - B (min s a) omega) P t (t - a : ℝ≥0) := by
  let A : ℝ≥0 → ℝ≥0 := fun s ↦ s - a
  have hA0 : A 0 = 0 := by
    dsimp only [A]
    exact zero_tsub a
  have hAcont : Continuous A := by
    dsimp only [A]
    fun_prop
  have hAmono : Monotone A := by
    intro s u hsu
    exact tsub_le_tsub_right hsu a
  have hraw := quadraticVariation_timeChanged_brownian
    (hB.shift a) A hA0 hAcont hAmono t
  convert hraw using 1
  funext s omega
  dsimp only [A]
  by_cases hsa : s ≤ a
  · rw [min_eq_left hsa, tsub_eq_zero_of_le hsa]
    simp only [add_zero, sub_self]
  · have has : a ≤ s := le_of_not_ge hsa
    rw [min_eq_right has, add_comm a, tsub_add_cancel_of_le has]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The quadratic variation after a deterministic time also converges in
probability. -/
theorem quadraticVariation_brownian_after_time_inProbability
    (hB : IsBrownianMotion B P) (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega ↦ B s omega - B (min s a) omega) P t
      (fun _ ↦ (t - a : ℝ≥0)) := by
  apply (quadraticVariation_brownian_after_time hB a t).to_inProbability
  intro s
  exact (hB.toIsPreBrownianReal.aemeasurable s).aestronglyMeasurable.sub
    (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The Brownian increment accumulated on a deterministic interval `[a, b]`
has literal `L²` quadratic variation `min t b - min t a`. -/
theorem quadraticVariation_brownian_interval
    (hB : IsBrownianMotion B P) {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) :
    HasQuadraticVariationAt
      (fun s omega ↦ B (min s b) omega - B (min s a) omega) P t
      (min t b - min t a : ℝ≥0) := by
  let A : ℝ≥0 → ℝ≥0 := fun s ↦ min (s - a) (b - a)
  have hA0 : A 0 = 0 := by
    dsimp only [A]
    rw [zero_tsub, min_eq_left (show (0 : ℝ≥0) ≤ b - a by exact bot_le)]
  have hAcont : Continuous A := by
    dsimp only [A]
    fun_prop
  have hAmono : Monotone A := by
    intro s u hsu
    exact min_le_min (tsub_le_tsub_right hsu a) le_rfl
  have hraw := quadraticVariation_timeChanged_brownian
    (hB.shift a) A hA0 hAcont hAmono t
  have hprocess :
      (fun s omega ↦ B (a + A s) omega - B a omega) =
      (fun s omega ↦ B (min s b) omega - B (min s a) omega) := by
    funext s omega
    dsimp only [A]
    by_cases hsa : s ≤ a
    · rw [tsub_eq_zero_of_le hsa,
        min_eq_left (show (0 : ℝ≥0) ≤ b - a by exact bot_le), min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
      simp only [add_zero, sub_self]
    · have has : a ≤ s := le_of_not_ge hsa
      rw [min_eq_right has]
      by_cases hsb : s ≤ b
      · rw [min_eq_left (tsub_le_tsub_right hsb a), min_eq_left hsb,
          add_comm a, tsub_add_cancel_of_le has]
      · have hbs : b ≤ s := le_of_not_ge hsb
        rw [min_eq_right (tsub_le_tsub_right hbs a), min_eq_right hbs,
          add_comm a, tsub_add_cancel_of_le hab]
  rw [hprocess] at hraw
  have hAt : A t = min t b - min t a := by
    dsimp only [A]
    by_cases hta : t ≤ a
    · rw [tsub_eq_zero_of_le hta,
        min_eq_left (show (0 : ℝ≥0) ≤ b - a by exact bot_le), min_eq_left hta,
        min_eq_left (hta.trans hab)]
      exact (tsub_self t).symm
    · have hat : a ≤ t := le_of_not_ge hta
      rw [min_eq_right hat]
      by_cases htb : t ≤ b
      · rw [min_eq_left (tsub_le_tsub_right htb a), min_eq_left htb]
      · have hbt : b ≤ t := le_of_not_ge htb
        rw [min_eq_right (tsub_le_tsub_right hbt a), min_eq_right hbt]
  simpa only [hAt] using hraw

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The deterministic-interval Brownian bracket also converges in
probability. -/
theorem quadraticVariation_brownian_interval_inProbability
    (hB : IsBrownianMotion B P) {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega ↦ B (min s b) omega - B (min s a) omega) P t
      (fun _ ↦ (min t b - min t a : ℝ≥0)) := by
  apply (quadraticVariation_brownian_interval hB hab t).to_inProbability
  intro s
  exact (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
    (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A Brownian interval block multiplied by a measurable random variable that
is constant in time has its clipped interval bracket scaled pointwise by the
square of that multiplier. -/
theorem quadraticVariation_timeConstant_mul_brownian_interval_inProbability
    (hB : IsBrownianMotion B P) (c : W → ℝ)
    (hcMeas : AEStronglyMeasurable c P) {a b : ℝ≥0}
    (hab : a ≤ b) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega =>
        c omega * (B (min s b) omega - B (min s a) omega)) P t
      (fun omega => c omega ^ 2 *
        ((min t b - min t a : ℝ≥0) : ℝ)) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact (quadraticVariation_brownian_interval_inProbability hB hab t).timeConstant_mul
    (fun s =>
      (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
        (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable)
    c hcMeas

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian increments accumulated on adjacent deterministic intervals have
zero quadratic covariation in probability. -/
theorem tendstoInMeasure_adjacent_brownian_interval_covariation_zero
    (hB : IsBrownianMotion B P) {a b c : ℝ≥0}
    (hab : a ≤ b) (hbc : b ≤ c) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => B (min s b) omega - B (min s a) omega)
        (fun s omega => B (min s c) omega - B (min s b) omega)
        t (n + 1)) Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let X : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s b) omega - B (min s a) omega
  let Y : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s c) omega - B (min s b) omega
  have hXmeas : ∀ s, AEStronglyMeasurable (X s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s c)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable
  have hX : HasQuadraticVariationInProbabilityAt X P t
      (fun _ => ((min t b - min t a : ℝ≥0) : ℝ)) := by
    simpa only [X] using
      quadraticVariation_brownian_interval_inProbability hB hab t
  have hY : HasQuadraticVariationInProbabilityAt Y P t
      (fun _ => ((min t c - min t b : ℝ≥0) : ℝ)) := by
    simpa only [Y] using
      quadraticVariation_brownian_interval_inProbability hB hbc t
  have hAC := quadraticVariation_brownian_interval_inProbability
    hB (hab.trans hbc) t
  have hXY : HasQuadraticVariationInProbabilityAt
      (fun s omega => X s omega + Y s omega) P t
      (fun _ => ((min t c - min t a : ℝ≥0) : ℝ)) := by
    apply hAC.congr
    · intro s
      filter_upwards with omega
      dsimp only [X, Y]
      ring
    · exact Filter.EventuallyEq.rfl
  have hcov := tendstoInMeasure_quadraticCovariationApprox
    hXmeas hYmeas hX hY hXY
  apply hcov.congr_right
  filter_upwards with omega
  have hminAB : min t a ≤ min t b := min_le_min le_rfl hab
  have hminBC : min t b ≤ min t c := min_le_min le_rfl hbc
  have hminAC : min t a ≤ min t c := hminAB.trans hminBC
  rw [NNReal.coe_sub hminAC, NNReal.coe_sub hminAB, NNReal.coe_sub hminBC]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian increment blocks accumulated on ordered disjoint deterministic
intervals have zero quadratic covariation in probability. -/
theorem tendstoInMeasure_disjoint_brownian_interval_covariation_zero
    (hB : IsBrownianMotion B P) {a b c d : ℝ≥0}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => B (min s b) omega - B (min s a) omega)
        (fun s omega => B (min s d) omega - B (min s c) omega)
        t (n + 1)) Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let X : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s b) omega - B (min s a) omega
  let G : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s c) omega - B (min s b) omega
  let Y : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s d) omega - B (min s c) omega
  let R : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s d) omega - B (min s b) omega
  have hXmeas : ∀ s, AEStronglyMeasurable (X s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hGmeas : ∀ s, AEStronglyMeasurable (G s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s c)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable
  have hRmeas : ∀ s, AEStronglyMeasurable (R s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s d)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable
  have hXR : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X R t (n + 1))
      Filter.atTop (fun _ => 0) := by
    simpa only [X, R] using
      tendstoInMeasure_adjacent_brownian_interval_covariation_zero
        hB hab (hbc.trans hcd) t
  have hXG : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X G t (n + 1))
      Filter.atTop (fun _ => 0) := by
    simpa only [X, G] using
      tendstoInMeasure_adjacent_brownian_interval_covariation_zero
        hB hab hbc t
  have hXRmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X R t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hRmeas t (n + 1)
  have hXGmeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox X G t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hGmeas t (n + 1)
  have hraw := hXR.sub_real hXG hXRmeas hXGmeas
  apply hraw.congr
  · intro n
    filter_upwards with omega
    dsimp only [X, G, Y, R]
    unfold quadraticCovariationApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · filter_upwards with omega
    norm_num

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A deterministic linear combination of two ordered disjoint Brownian
interval blocks has bracket equal to the sum of the two squared-coefficient
block lengths. -/
theorem quadraticVariation_two_disjoint_brownian_blocks
    (hB : IsBrownianMotion B P) {a b c d : ℝ≥0}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (c1 c2 : ℝ) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s omega =>
        c1 * (B (min s b) omega - B (min s a) omega) +
        c2 * (B (min s d) omega - B (min s c) omega)) P t
      (fun _ =>
        c1 ^ 2 * (min t b - min t a : ℝ≥0) +
        c2 ^ 2 * (min t d - min t c : ℝ≥0)) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let X : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s b) omega - B (min s a) omega
  let Y : ℝ≥0 → W → ℝ := fun s omega =>
    B (min s d) omega - B (min s c) omega
  have hXmeas : ∀ s, AEStronglyMeasurable (X s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s d)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s c)).aestronglyMeasurable
  have hX : HasQuadraticVariationInProbabilityAt X P t
      (fun _ => ((min t b - min t a : ℝ≥0) : ℝ)) := by
    simpa only [X] using
      quadraticVariation_brownian_interval_inProbability hB hab t
  have hY : HasQuadraticVariationInProbabilityAt Y P t
      (fun _ => ((min t d - min t c : ℝ≥0) : ℝ)) := by
    simpa only [Y] using
      quadraticVariation_brownian_interval_inProbability hB hcd t
  have hCov : TendstoInMeasure P
      (fun n => quadraticCovariationApprox X Y t (n + 1))
      Filter.atTop (fun _ => 0) := by
    simpa only [X, Y] using
      tendstoInMeasure_disjoint_brownian_interval_covariation_zero
        hB hab hbc hcd t
  simpa only [X, Y, mul_zero, add_zero] using
    hX.linearCombination hY hCov hXmeas hYmeas c1 c2

private noncomputable def stoppedUniformPartitionTime
    (t a : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  min (uniformPartitionTime t n i) a

private lemma monotone_stoppedUniformPartitionTime (t a : ℝ≥0) (n : ℕ) :
    Monotone (stoppedUniformPartitionTime t a n) := by
  intro i j hij
  unfold stoppedUniformPartitionTime uniformPartitionTime
  exact min_le_min (by gcongr) le_rfl

private lemma stoppedUniformPartitionTime_zero (t a : ℝ≥0) (n : ℕ) :
    stoppedUniformPartitionTime t a n 0 = 0 := by
  simp only [stoppedUniformPartitionTime, uniformPartitionTime, Nat.cast_zero,
    mul_zero, zero_div]
  exact min_eq_left bot_le

private lemma stoppedUniformPartitionTime_top
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    stoppedUniformPartitionTime t a n n = min t a := by
  unfold stoppedUniformPartitionTime uniformPartitionTime
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [mul_div_cancel_right₀ t hn0]

private lemma stoppedUniformPartitionWidth_toReal
    (t a : ℝ≥0) (n i : ℕ) :
    (nndist
      ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
      ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) =
      (stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ) := by
  rw [← dist_nndist, Real.dist_eq, abs_of_nonneg]
  exact sub_nonneg.mpr (by
    exact_mod_cast monotone_stoppedUniformPartitionTime t a n
      (Nat.le_add_right i 1))

private lemma sum_stoppedUniformPartitionWidth
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n,
      (nndist
        ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
        ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) =
      (min t a : ℝ≥0) := by
  simp_rw [stoppedUniformPartitionWidth_toReal]
  rw [Finset.sum_range_sub
      (fun i => (stoppedUniformPartitionTime t a n i : ℝ)) n,
    stoppedUniformPartitionTime_top t a hn,
    stoppedUniformPartitionTime_zero]
  simp only [NNReal.coe_zero, sub_zero]

private lemma stoppedUniformPartitionWidth_le_mesh
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (nndist
      ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
      ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ≤
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  rw [stoppedUniformPartitionWidth_toReal]
  have hmono :
      (stoppedUniformPartitionTime t a n i : ℝ) ≤
        (stoppedUniformPartitionTime t a n (i + 1) : ℝ) := by
    exact_mod_cast monotone_stoppedUniformPartitionTime t a n
      (Nat.le_add_right i 1)
  have hmin := abs_min_sub_min_le_max
    (uniformPartitionTime t n (i + 1) : ℝ) (a : ℝ)
    (uniformPartitionTime t n i : ℝ) (a : ℝ)
  have hraw :
      |(stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ)| ≤
      |(uniformPartitionTime t n (i + 1) : ℝ) -
        (uniformPartitionTime t n i : ℝ)| := by
    simpa only [stoppedUniformPartitionTime, NNReal.coe_min, sub_self,
      abs_zero, max_eq_left (abs_nonneg
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)))] using hmin
  rw [← abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    |(stoppedUniformPartitionTime t a n (i + 1) : ℝ) -
        (stoppedUniformPartitionTime t a n i : ℝ)| ≤
        |(uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)| := hraw
    _ = ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
      simpa only [NNReal.dist_eq] using dist_uniformPartitionTime_succ_eq t hn i

private lemma sum_stoppedUniformPartitionWidth_sq_le
    (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n,
      2 * (nndist
        ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
        ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ^ 2 ≤
      2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * (min t a : ℝ≥0) := by
  calc
    ∑ i ∈ Finset.range n,
        2 * (nndist
          ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
          ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.range n,
          2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) *
            (nndist
              ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
              ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hd0 : 0 ≤ (nndist
          ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
          ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) := NNReal.coe_nonneg _
      have hdle := stoppedUniformPartitionWidth_le_mesh t a hn i
      nlinarith only [hd0, hdle]
    _ = 2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) *
        (∑ i ∈ Finset.range n,
          (nndist
            ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
            ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = 2 * ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) * (min t a : ℝ≥0) := by
      rw [sum_stoppedUniformPartitionWidth t a hn]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private lemma eLpNorm_stoppedBrownian_qv_sub_eq
    (hB : IsPreBrownianReal B P) (t a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    eLpNorm
      (fun ω => quadraticVariationApprox
        (fun s ω => B (min s a) ω) t n ω - (min t a : ℝ≥0)) 2 P =
      ENNReal.ofReal
        ((∑ i ∈ Finset.range n,
          2 * (nndist
            ((stoppedUniformPartitionTime t a n (i + 1) : ℝ))
            ((stoppedUniformPartitionTime t a n i : ℝ)) : ℝ) ^ 2) ^
              (2 : ℝ)⁻¹) := by
  have hraw := eLpNorm_preBrownian_centeredSquaredIncrementSum_eq hB
    (stoppedUniformPartitionTime t a n)
    (monotone_stoppedUniformPartitionTime t a n) n
  rw [← hraw]
  congr 1
  funext ω
  unfold quadraticVariationApprox
  rw [Finset.sum_sub_distrib, sum_stoppedUniformPartitionWidth t a hn]
  rfl

private lemma tendsto_rpow_two_inv_const_div_add_one (C : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (C / ((n : ℝ) + 1)) ^ (2 : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
  have hdivNat : Filter.Tendsto (fun n : ℕ => C / (n : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat C
  have hdiv : Filter.Tendsto (fun n : ℕ => C / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Filter.tendsto_add_atTop_iff_nat 1).2 hdivNat
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (C / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto (Real.sqrt ∘ fun n : ℕ => C / ((n : ℝ) + 1))
      Filter.atTop (nhds 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hdiv
  simpa only [Real.sqrt_eq_rpow, one_div] using hsqrt

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Pre-Brownian motion stopped at a deterministic time `a` has quadratic
variation `min t a` at time `t`, with literal `L²` convergence. -/
theorem quadraticVariation_stopped_preBrownianReal
    (hB : IsPreBrownianReal B P) (a t : ℝ≥0) :
    HasQuadraticVariationAt (fun s ω => B (min s a) ω) P t
      (min t a : ℝ≥0) := by
  unfold HasQuadraticVariationAt
  let C : ℝ := 2 * (t : ℝ) * (min t a : ℝ≥0)
  have hfinite : ∀ n : ℕ,
      eLpNorm
        (fun ω => quadraticVariationApprox
          (fun s ω => B (min s a) ω) t (n + 1) ω -
            (min t a : ℝ≥0)) 2 P ≠ ∞ := by
    intro n
    rw [eLpNorm_stoppedBrownian_qv_sub_eq hB t a (Nat.zero_lt_succ n)]
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).1
  apply squeeze_zero
    (g := fun n : ℕ => (C / ((n : ℝ) + 1)) ^ (2 : ℝ)⁻¹)
  · intro n
    exact ENNReal.toReal_nonneg
  · intro n
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (n + 1),
        2 * (nndist
          ((stoppedUniformPartitionTime t a (n + 1) (i + 1) : ℝ))
          ((stoppedUniformPartitionTime t a (n + 1) i : ℝ)) : ℝ) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _hi
      exact mul_nonneg (by norm_num) (sq_nonneg _)
    rw [eLpNorm_stoppedBrownian_qv_sub_eq hB t a (Nat.zero_lt_succ n),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hsum0 _)]
    have hsumle :
        ∑ i ∈ Finset.range (n + 1),
            2 * (nndist
              ((stoppedUniformPartitionTime t a (n + 1) (i + 1) : ℝ))
              ((stoppedUniformPartitionTime t a (n + 1) i : ℝ)) : ℝ) ^ 2 ≤
            C / ((n : ℝ) + 1) := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            2 * (nndist
              ((stoppedUniformPartitionTime t a (n + 1) (i + 1) : ℝ))
              ((stoppedUniformPartitionTime t a (n + 1) i : ℝ)) : ℝ) ^ 2 ≤
            2 * ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) *
              (min t a : ℝ≥0) :=
          sum_stoppedUniformPartitionWidth_sq_le t a (Nat.zero_lt_succ n)
        _ = C / ((n : ℝ) + 1) := by
          dsimp only [C]
          have hden : ((((n + 1 : ℕ) : ℝ≥0) : ℝ)) = (n : ℝ) + 1 := by
            norm_num
          rw [NNReal.coe_div, hden]
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hn]
    exact Real.rpow_le_rpow hsum0 hsumle (by positivity)
  · exact tendsto_rpow_two_inv_const_div_add_one C

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The deterministic stopped pre-Brownian bracket also converges in probability. -/
theorem quadraticVariation_stopped_preBrownianReal_inProbability
    (hB : IsPreBrownianReal B P) (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => B (min s a) ω) P t (fun _ => (min t a : ℝ≥0)) := by
  apply (quadraticVariation_stopped_preBrownianReal hB a t).to_inProbability
  intro s
  exact (hB.aemeasurable (min s a)).aestronglyMeasurable

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Brownian specialization of the stopped bracket convergence in probability. -/
theorem quadraticVariation_stopped_brownian_inProbability
    (hB : IsBrownianMotion B P) (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => B (min s a) ω) P t (fun _ => (min t a : ℝ≥0)) :=
  quadraticVariation_stopped_preBrownianReal_inProbability
    hB.toIsPreBrownianReal a t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
private lemma eLpNorm_quadraticVariationApprox_sub_eq
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    eLpNorm (fun ω ↦ quadraticVariationApprox B t n ω - (t : ℝ)) 2 P =
      ENNReal.ofReal ((2 * (t : ℝ) ^ 2 / (n : ℝ)) ^ (2 : ℝ)⁻¹) := by
  let hpre := hB
  let _ : IsProbabilityMeasure P := hpre.isGaussianProcess.isProbabilityMeasure
  let d : ℝ≥0 := t / (n : ℝ≥0)
  let Δ : ℕ → W → ℝ := fun i ω ↦
    B (uniformPartitionTime t n (i + 1)) ω - B (uniformPartitionTime t n i) ω
  let Y : ℕ → W → ℝ := fun i ω ↦ Δ i ω ^ 2 - (d : ℝ)
  have hLaw (i : ℕ) : HasLaw (Δ i) (gaussianReal 0 d) P := by
    dsimp only [Δ, d]
    change HasLaw
      (B (uniformPartitionTime t n (i + 1)) - B (uniformPartitionTime t n i))
      (gaussianReal 0 (t / (n : ℝ≥0))) P
    have hraw :=
      hpre.hasLaw_sub (uniformPartitionTime t n (i + 1)) (uniformPartitionTime t n i)
    convert hraw using 1
    exact congrArg (gaussianReal 0) (uniformPartitionTime_succ_nndist t hn i).symm
  have hYmem (i : ℕ) : MemLp (Y i) 2 P := by
    simpa only [Y] using centeredSquare_memLp_of_hasLaw d (hLaw i)
  have hYmean (i : ℕ) : (∫ ω, Y i ω ∂P) = 0 := by
    simpa only [Y] using integral_centeredSquare_of_hasLaw d (hLaw i)
  have hYvar (i : ℕ) : Var[Y i; P] = 2 * (d : ℝ) ^ 2 := by
    simpa only [Y] using variance_centeredSquare_of_hasLaw d (hLaw i)
  have hIndΔ : iIndepFun Δ P := by
    simpa only [Δ] using
      hpre.hasIndepIncrements.nat (monotone_uniformPartitionTime t n)
  have hIndY : iIndepFun Y P := by
    have hcomp := hIndΔ.comp (fun (_ : ℕ) (x : ℝ) ↦ x ^ 2 - (d : ℝ))
      (fun _ ↦ by fun_prop)
    simpa only [Y, Function.comp_def] using hcomp
  have hPair : Set.Pairwise (↑(Finset.range n) : Set ℕ)
      (fun i j ↦ Y i ⟂ᵢ[P] Y j) := by
    exact fun i _ j _ hij ↦ hIndY.indepFun hij
  have hVarSum :
      Var[fun ω ↦ ∑ i ∈ Finset.range n, Y i ω; P] =
        (n : ℝ) * (2 * (d : ℝ) ^ 2) := by
    calc
      Var[fun ω ↦ ∑ i ∈ Finset.range n, Y i ω; P] =
          ∑ i ∈ Finset.range n, Var[Y i; P] := by
        rw [show (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) =
            ∑ i ∈ Finset.range n, Y i by
          funext ω
          simp only [Finset.sum_apply]]
        exact IndepFun.variance_sum (fun i _ ↦ hYmem i) hPair
      _ = (n : ℝ) * (2 * (d : ℝ) ^ 2) := by
        simp only [hYvar, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMeanSum : (∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P) = 0 := by
    rw [integral_finsetSum (Finset.range n)
      (fun i _ ↦ (hYmem i).integrable (by norm_num))]
    simp only [hYmean, Finset.sum_const_zero]
  have hMemSum : MemLp (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) 2 P :=
    memLp_finsetSum (Finset.range n) (fun i _ ↦ hYmem i)
  have hIntegralSq :
      (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) =
        (n : ℝ) * (2 * (d : ℝ) ^ 2) := by
    have hv := variance_eq_sub hMemSum
    rw [hVarSum, hMeanSum] at hv
    norm_num only [Pi.pow_apply, zero_pow, sub_zero] at hv
    exact hv.symm
  have hnd : (n : ℝ) * (d : ℝ) = (t : ℝ) := by
    dsimp only [d]
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
  have hSumEq (ω : W) :
      (∑ i ∈ Finset.range n, Y i ω) =
        quadraticVariationApprox B t n ω - (t : ℝ) := by
    dsimp only [Y, Δ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hnd]
    rfl
  have hvariance :
      (n : ℝ) * (2 * (d : ℝ) ^ 2) = 2 * (t : ℝ) ^ 2 / (n : ℝ) := by
    dsimp only [d]
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
  have hfun : (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) =
      (fun ω ↦ quadraticVariationApprox B t n ω - (t : ℝ)) :=
    funext hSumEq
  rw [← hfun, hMemSum.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    hIntegralSq, hvariance]

private lemma tendsto_ofReal_sqrt_const_div_add_one (C : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (Real.sqrt (C / ((n : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
  have hdivNat : Filter.Tendsto (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat C)
  have hdiv : Filter.Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdivNat
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (C / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto (Real.sqrt ∘ fun n : ℕ ↦ C / ((n : ℝ) + 1))
      Filter.atTop (nhds 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hdiv
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hsqrt

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Quadratic variation of Brownian motion: ⟨B⟩_t = t. -/
theorem quadraticVariation_brownianMotion
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    HasQuadraticVariationAt B P t (t : ℝ) := by
  unfold HasQuadraticVariationAt
  have hfun :
      (fun n : ℕ ↦ eLpNorm
        (fun ω ↦ quadraticVariationApprox B t (n + 1) ω - (t : ℝ)) 2 P) =
      (fun n : ℕ ↦ ENNReal.ofReal
        ((2 * (t : ℝ) ^ 2 / ((n : ℝ) + 1)) ^ (2 : ℝ)⁻¹)) := by
    funext n
    rw [eLpNorm_quadraticVariationApprox_sub_eq hB.toIsPreBrownianReal t
      (Nat.zero_lt_succ n)]
    simp only [Nat.cast_succ]
  rw [hfun]
  simpa only [Real.sqrt_eq_rpow, one_div] using
    tendsto_ofReal_sqrt_const_div_add_one (2 * (t : ℝ) ^ 2)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The Brownian quadratic-variation theorem also gives convergence in
probability, matching the carrier used for general Itô processes. -/
theorem quadraticVariation_brownianMotion_inProbability
    (hB : IsBrownianMotion B P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt B P t (fun _ => (t : ℝ)) := by
  unfold HasQuadraticVariationInProbabilityAt
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  · intro n
    unfold quadraticVariationApprox
    have hs := Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
      (fun i _hi => (((hB.toIsPreBrownianReal.aemeasurable
        (uniformPartitionTime t (n + 1) (i + 1))).sub
        (hB.toIsPreBrownianReal.aemeasurable
          (uniformPartitionTime t (n + 1) i))).pow_const 2).aestronglyMeasurable)
    have hfun :
        (fun ω => ∑ i ∈ Finset.range (n + 1),
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω -
            B (uniformPartitionTime t (n + 1) i) ω) ^ 2) =
        ∑ i ∈ Finset.range (n + 1), fun ω =>
          (B (uniformPartitionTime t (n + 1) (i + 1)) ω -
            B (uniformPartitionTime t (n + 1) i) ω) ^ 2 := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hfun]
    exact hs
  · exact aestronglyMeasurable_const
  · have h := quadraticVariation_brownianMotion hB t
    unfold HasQuadraticVariationAt at h
    convert h using 1
    funext n
    congr 1

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The uniform-partition quadratic variation calculation only uses the
finite-dimensional Brownian laws; path continuity is not needed. -/
theorem quadraticVariation_preBrownianReal
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasQuadraticVariationAt B P t (t : ℝ) := by
  unfold HasQuadraticVariationAt
  have hfun :
      (fun n : ℕ ↦ eLpNorm
        (fun omega ↦ quadraticVariationApprox B t (n + 1) omega - (t : ℝ)) 2 P) =
      (fun n : ℕ ↦ ENNReal.ofReal
        ((2 * (t : ℝ) ^ 2 / ((n : ℝ) + 1)) ^ (2 : ℝ)⁻¹)) := by
    funext n
    rw [eLpNorm_quadraticVariationApprox_sub_eq hB t (Nat.zero_lt_succ n)]
    simp only [Nat.cast_succ]
  rw [hfun]
  simpa only [Real.sqrt_eq_rpow, one_div] using
    tendsto_ofReal_sqrt_const_div_add_one (2 * (t : ℝ) ^ 2)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A pre-Brownian process has quadratic variation `t` in probability at
every deterministic time, independently of its choice of path version. -/
theorem quadraticVariation_preBrownianReal_inProbability
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt B P t (fun _ ↦ (t : ℝ)) := by
  apply (quadraticVariation_preBrownianReal hB t).to_inProbability
  exact fun s ↦ (hB.aemeasurable s).aestronglyMeasurable

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The stopped Brownian block and the Brownian increment accumulated after
the stopping time have vanishing quadratic covariation in probability. -/
theorem tendstoInMeasure_stopped_brownian_after_time_covariation_zero
    (hB : IsBrownianMotion B P) (a t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => B (min s a) omega)
        (fun s omega => B s omega - B (min s a) omega) t (n + 1))
      Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let U : ℝ≥0 → W → ℝ := fun s omega => B (min s a) omega
  let V : ℝ≥0 → W → ℝ := fun s omega => B s omega - B (min s a) omega
  have hUmeas : ∀ s, AEStronglyMeasurable (U s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hVmeas : ∀ s, AEStronglyMeasurable (V s) P := fun s =>
    ((hB.toIsPreBrownianReal.aemeasurable s).sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a))).aestronglyMeasurable
  have hU : HasQuadraticVariationInProbabilityAt U P t
      (fun _ => ((min t a : ℝ≥0) : ℝ)) := by
    simpa only [U] using quadraticVariation_stopped_brownian_inProbability hB a t
  have hV : HasQuadraticVariationInProbabilityAt V P t
      (fun _ => ((t - a : ℝ≥0) : ℝ)) := by
    simpa only [V] using quadraticVariation_brownian_after_time_inProbability hB a t
  have hUV : HasQuadraticVariationInProbabilityAt
      (fun s omega => U s omega + V s omega) P t (fun _ => (t : ℝ)) := by
    apply (quadraticVariation_brownianMotion_inProbability hB t).congr
    · intro s
      filter_upwards with omega
      dsimp only [U, V]
      ring
    · exact Filter.EventuallyEq.rfl
  have hcov := tendstoInMeasure_quadraticCovariationApprox
    hUmeas hVmeas hU hV hUV
  apply hcov.congr_right
  filter_upwards with omega
  by_cases hta : t ≤ a
  · rw [min_eq_left hta, tsub_eq_zero_of_le hta]
    norm_num
  · have hat : a ≤ t := le_of_not_ge hta
    rw [min_eq_right hat, NNReal.coe_sub hat]
    ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The stopped Brownian block has covariation `min t a` with the full
Brownian path. -/
theorem tendstoInMeasure_stopped_brownian_brownian_covariation
    (hB : IsBrownianMotion B P) (a t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s omega => B (min s a) omega) B t (n + 1))
      Filter.atTop (fun _ => ((min t a : ℝ≥0) : ℝ)) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let U : ℝ≥0 → W → ℝ := fun s omega => B (min s a) omega
  let V : ℝ≥0 → W → ℝ := fun s omega => B s omega - B (min s a) omega
  have hUmeas : ∀ s, AEStronglyMeasurable (U s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hVmeas : ∀ s, AEStronglyMeasurable (V s) P := fun s =>
    ((hB.toIsPreBrownianReal.aemeasurable s).sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a))).aestronglyMeasurable
  have hU : HasQuadraticVariationInProbabilityAt U P t
      (fun _ => ((min t a : ℝ≥0) : ℝ)) := by
    simpa only [U] using quadraticVariation_stopped_brownian_inProbability hB a t
  have hCov : TendstoInMeasure P
      (fun n => quadraticCovariationApprox U V t (n + 1))
      Filter.atTop (fun _ => 0) := by
    simpa only [U, V] using
      tendstoInMeasure_stopped_brownian_after_time_covariation_zero hB a t
  have hQUmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationApprox U t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticVariationApprox
      hUmeas t (n + 1)
  have hCovMeas : ∀ n, AEStronglyMeasurable
      (quadraticCovariationApprox U V t (n + 1)) P :=
    fun n => aestronglyMeasurable_quadraticCovariationApprox
      hUmeas hVmeas t (n + 1)
  unfold HasQuadraticVariationInProbabilityAt at hU
  have hsum := hU.add_real hCov hQUmeas hCovMeas
  apply hsum.congr
  · intro n
    filter_upwards with omega
    dsimp only [U, V]
    unfold quadraticVariationApprox quadraticCovariationApprox
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · filter_upwards with omega
    norm_num

/-- The second moment of an increment of the chosen representative of the
natural Itô integral process is the squared `RandomL2` norm of that increment.
This representative-level form is used to integrate quadratic-variation
approximants. -/
theorem integral_sq_naturalItoProcessRepresentative_sub
    [SecondCountableTopology W] [IsGaussian P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (s t : ℝ≥0) :
    ∫ ω, (naturalItoProcessRepresentative hB hsm rfl U t ω -
        naturalItoProcessRepresentative hB hsm rfl U s ω) ^ 2 ∂P =
      ‖naturalItoProcess hB hsm rfl U t -
        naturalItoProcess hB hsm rfl U s‖ ^ 2 := by
  let It := naturalItoProcess hB hsm rfl U t
  let Is := naturalItoProcess hB hsm rfl U s
  calc
    ∫ ω, (naturalItoProcessRepresentative hB hsm rfl U t ω -
        naturalItoProcessRepresentative hB hsm rfl U s ω) ^ 2 ∂P =
        ∫ ω, ⟪((It - Is : RandomL2 P) : W → ℝ) ω,
          ((It - Is : RandomL2 P) : W → ℝ) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub It Is,
        naturalItoProcess_ae_eq_representative hB hsm rfl U t,
        naturalItoProcess_ae_eq_representative hB hsm rfl U s]
        with ω hsub ht hs
      change ((It : W → ℝ) ω) =
        naturalItoProcessRepresentative hB hsm rfl U t ω at ht
      change ((Is : W → ℝ) ω) =
        naturalItoProcessRepresentative hB hsm rfl U s ω at hs
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [ht, hs]
      simp [pow_two]
    _ = inner ℝ (It - Is) (It - Is) := (L2.inner_def _ _).symm
    _ = ‖It - Is‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- Orthogonality of Itô-integral increments turns the squared norm of an
increment into a telescoping difference. -/
theorem norm_sq_naturalItoProcess_sub
    [SecondCountableTopology W] [IsGaussian P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ‖naturalItoProcess hB hsm rfl U t -
        naturalItoProcess hB hsm rfl U s‖ ^ 2 =
      ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 -
        ‖naturalItoProcess hB hsm rfl U s‖ ^ 2 := by
  have ho := inner_naturalItoProcess_sub_naturalItoProcess
    hB hsm rfl hst U U
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  rw [norm_sub_sq_real]
  linarith

/-- The squared increments of the chosen representative of a natural Itô
integral process are integrable. -/
theorem integrable_sq_naturalItoProcessRepresentative_sub
    [SecondCountableTopology W] [IsGaussian P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (s t : ℝ≥0) :
    Integrable (fun ω =>
      (naturalItoProcessRepresentative hB hsm rfl U t ω -
        naturalItoProcessRepresentative hB hsm rfl U s ω) ^ 2) P := by
  let It := naturalItoProcess hB hsm rfl U t
  let Is := naturalItoProcess hB hsm rfl U s
  have hbase : Integrable (fun ω =>
      (((It - Is : RandomL2 P) : W → ℝ) ω) ^ 2) P :=
    (Lp.memLp (It - Is)).integrable_sq
  apply hbase.congr
  filter_upwards [Lp.coeFn_sub It Is,
    naturalItoProcess_ae_eq_representative hB hsm rfl U t,
    naturalItoProcess_ae_eq_representative hB hsm rfl U s]
    with ω hsub ht hs
  change ((It : W → ℝ) ω) =
    naturalItoProcessRepresentative hB hsm rfl U t ω at ht
  change ((Is : W → ℝ) ω) =
    naturalItoProcessRepresentative hB hsm rfl U s ω at hs
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [ht, hs]

/-- Every finite quadratic-variation approximant of a natural Itô integral
has expectation equal to the terminal second moment.  In particular, the
identity is uniform in the partition size, which is the key estimate in the
`PredictableProcessL2` density argument. -/
theorem integral_quadraticVariationApprox_naturalItoProcessRepresentative
    [SecondCountableTopology W] [IsGaussian P]
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, quadraticVariationApprox
        (naturalItoProcessRepresentative hB hsm rfl U) t n ω ∂P =
      ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 := by
  unfold quadraticVariationApprox
  rw [integral_finsetSum]
  · calc
      (∑ i ∈ Finset.range n,
          ∫ ω,
            (naturalItoProcessRepresentative hB hsm rfl U
                (uniformPartitionTime t n (i + 1)) ω -
              naturalItoProcessRepresentative hB hsm rfl U
                (uniformPartitionTime t n i) ω) ^ 2 ∂P) =
          ∑ i ∈ Finset.range n,
            ‖naturalItoProcess hB hsm rfl U
                (uniformPartitionTime t n (i + 1)) -
              naturalItoProcess hB hsm rfl U
                (uniformPartitionTime t n i)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact integral_sq_naturalItoProcessRepresentative_sub
              hB hsm U _ _
      _ = ∑ i ∈ Finset.range n,
            (‖naturalItoProcess hB hsm rfl U
                (uniformPartitionTime t n (i + 1))‖ ^ 2 -
              ‖naturalItoProcess hB hsm rfl U
                (uniformPartitionTime t n i)‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply norm_sq_naturalItoProcess_sub hB hsm U
            unfold uniformPartitionTime
            gcongr
            omega
      _ = ‖naturalItoProcess hB hsm rfl U
              (uniformPartitionTime t n n)‖ ^ 2 -
            ‖naturalItoProcess hB hsm rfl U
              (uniformPartitionTime t n 0)‖ ^ 2 := by
            exact Finset.sum_range_sub
              (fun i => ‖naturalItoProcess hB hsm rfl U
                (uniformPartitionTime t n i)‖ ^ 2) n
      _ = ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 := by
            have hn0 : (n : ℝ≥0) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt hn
            simp [uniformPartitionTime, hn0]
  · intro i _hi
    exact integrable_sq_naturalItoProcessRepresentative_sub hB hsm U _ _

end StochasticCalculus
