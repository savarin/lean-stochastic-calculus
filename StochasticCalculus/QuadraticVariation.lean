/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.QuadraticVariationContract

/-!
# Quadratic variation of Brownian motion

`⟨B⟩_t = t`: squared-increment sums along uniform partitions converge in
`L²(P)` and in probability, for the driver itself, for stopped and
time-changed versions, and for disjoint blocks, together with the
covariation of stopped and interval Brownian blocks with the full path.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace

noncomputable section
set_option linter.unusedDecidableInType false

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

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
  exact (quadraticVariation_brownian_after_time hB a t).to_inProbability

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
  exact (quadraticVariation_brownian_interval hB hab t).to_inProbability

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
  exact (quadraticVariation_stopped_preBrownianReal hB a t).to_inProbability

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
  exact (quadraticVariation_brownianMotion hB t).to_inProbability

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
  exact (quadraticVariation_preBrownianReal hB t).to_inProbability

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
