/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.UniformPartitionSums

/-!
# Quadratic variation contracts at a fixed time

Quadratic variation in `L²` and in probability at a fixed time, and the
closure of the in-probability contract under almost-everywhere
modification, sums with a zero-variation term, products by time-constant
random variables, and stopping.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace

noncomputable section
set_option linter.unusedDecidableInType false

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

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

end StochasticCalculus
