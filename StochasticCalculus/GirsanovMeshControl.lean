/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovComplexEuler

/-!
# Mesh and variation controls

Fourth-variation and maximal-increment controls of the driver along uniform
partitions, the stopped mesh controls of the complex combination, its
bracket and its compensator, the total-variation approximations of the
integrated drift, and the terminal variation bound with its tightness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The fourth-root Brownian mesh control extracted from the fourth
variation.  Two square roots are used to keep the quantity in the real
ordered-field API. -/
noncomputable def fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega))

/-- Every Brownian grid increment is bounded by the fourth-root control of
the whole grid. -/
theorem abs_uniformPartition_increment_le_fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) {n : ℕ}
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range n) :
    |B (uniformPartitionTime U n (i + 1)) omega -
        B (uniformPartitionTime U n i) omega| ≤
      fourthVariationRootApprox B U n omega := by
  let d := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have hterm : d ^ 4 ≤ fourthVariationApprox B U n omega := by
    unfold fourthVariationApprox
    simpa only [d] using Finset.single_le_sum
      (s := Finset.range n)
      (f := fun j => (B (uniformPartitionTime U n (j + 1)) omega -
        B (uniformPartitionTime U n j) omega) ^ 4)
      (fun j _hj => by positivity) hi
  have hfourth : 0 ≤ fourthVariationApprox B U n omega :=
    fourthVariationApprox_nonneg B U n omega
  have hsq : (|d| ^ 2) ^ 2 ≤ fourthVariationApprox B U n omega := by
    calc
      (|d| ^ 2) ^ 2 = d ^ 4 := by rw [sq_abs]; ring
      _ ≤ fourthVariationApprox B U n omega := hterm
  have hfirst : |d| ^ 2 ≤
      Real.sqrt (fourthVariationApprox B U n omega) :=
    Real.le_sqrt_of_sq_le hsq
  have hsecond : |d| ≤
      Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega)) :=
    Real.le_sqrt_of_sq_le hfirst
  simpa only [d, fourthVariationRootApprox] using hsecond

/-- For a pre-Brownian process, the fourth-root mesh control vanishes in
probability without assuming continuity of the chosen sample paths. -/
theorem fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P
      (fun n => fourthVariationRootApprox B U (n + 1)) atTop
      (fun _ => 0) := by
  have hbase := fourthVariationApprox_preBrownianReal_tendstoInMeasure_zero
    hB U
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fourthVariationApprox B U (n + 1)) P :=
    aestronglyMeasurable_fourthVariationApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable) U (n + 1)
  have hfirst := TendstoInMeasure.continuous_comp hmeas hbase
    Real.continuous_sqrt
  have hsqrtMeas (n : ℕ) : AEStronglyMeasurable
      (fun omega => Real.sqrt (fourthVariationApprox B U (n + 1) omega)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hmeas n)
  have hsecond := TendstoInMeasure.continuous_comp hsqrtMeas hfirst
    Real.continuous_sqrt
  change TendstoInMeasure P
    (fun n omega => Real.sqrt
      (Real.sqrt (fourthVariationApprox B U (n + 1) omega))) atTop
    (fun _ => 0)
  simpa only [Real.sqrt_zero] using hsecond

/-- Maximum absolute increment on the positive uniform `(n+1)`-partition.
The shifted indexing makes the defining finite set nonempty at every outer
index. -/
noncomputable def uniformPartitionMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun i =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|

theorem uniformPartitionMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ uniformPartitionMaxAbsIncrement X U n omega := by
  exact (abs_nonneg (X (uniformPartitionTime U (n + 1) 1) omega -
    X (uniformPartitionTime U (n + 1) 0) omega)).trans
      (Finset.le_sup' (fun i =>
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Each cell increment is bounded by the uniform-partition maximum. -/
theorem abs_uniformPartition_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
        X (uniformPartitionTime U (n + 1) i) omega| ≤
      uniformPartitionMaxAbsIncrement X U n omega :=
  Finset.le_sup' (fun j =>
    |X (uniformPartitionTime U (n + 1) (j + 1)) omega -
      X (uniformPartitionTime U (n + 1) j) omega|) hi

theorem stronglyMeasurable_uniformPartitionMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {X : ℝ≥0 → W → ℝ}
    (hX : ∀ s, StronglyMeasurable (X s)) (U : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (uniformPartitionMaxAbsIncrement X U n) := by
  apply Measurable.stronglyMeasurable
  unfold uniformPartitionMaxAbsIncrement
  let f : ℕ → W → ℝ := fun i omega =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|
  have hf : ∀ i ∈ Finset.range (n + 1), Measurable (f i) := by
    intro i _hi
    simpa only [f, Pi.sub_apply, Real.norm_eq_abs] using
      ((hX _).sub (hX _)).norm.measurable
  have hsup := Finset.measurable_sup' Finset.nonempty_range_add_one hf
  convert hsup using 1
  ext omega
  rw [Finset.sup'_apply]

/-- Uniform continuity makes the maximum mesh increment vanish pointwise. -/
theorem uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (omega : W)
    (hX : Continuous fun s => X s omega) :
    Tendsto (fun n => uniformPartitionMaxAbsIncrement X U n omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (continuous_uniformPartition_increments_tendsto
      (fun s => X s omega) hX U epsilon hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (uniformPartitionMaxAbsIncrement_nonneg X U n omega)]
  rw [uniformPartitionMaxAbsIncrement, Finset.sup'_lt_iff]
  intro i hi
  exact hN n hn i hi

/-- A process with measurable time sections and continuous paths has
vanishing maximum uniform-grid increments in probability. -/
theorem uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement X U n)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement
      hXmeas U n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega =>
      uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
        X U omega (hXcont omega)

/-- The pre-Brownian maximum mesh increment is dominated by the fourth-root
variation control, so it vanishes in probability for arbitrary versions. -/
theorem uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement B U n)
      atTop (fun _ => 0) := by
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas
    (fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero hB U)
  · intro n omega
    exact Real.sqrt_nonneg _
  · intro n omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (uniformPartitionMaxAbsIncrement_nonneg B U n omega)]
    rw [uniformPartitionMaxAbsIncrement, Finset.sup'_le_iff]
    intro i hi
    exact abs_uniformPartition_increment_le_fourthVariationRootApprox
      B U omega hi

/-- A stopped-grid mesh control: the endpoint mesh maximum plus the square
root of the sole possible boundary-cell quadratic contribution. -/
noncomputable def uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionMaxAbsIncrement X U n omega +
    Real.sqrt (quadraticVariationCrossingStopApprox
      X U (n + 1) (min t U) omega)

theorem uniformPartitionStoppedMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) :
    0 ≤ uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact add_nonneg
    (uniformPartitionMaxAbsIncrement_nonneg X U n omega)
    (Real.sqrt_nonneg _)

theorem aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℝ≥0 → W → ℝ} (hX : ∀ s, StronglyMeasurable (X s))
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (uniformPartitionStoppedMaxAbsIncrement X U n t) P := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement hX U n
    |>.aestronglyMeasurable).add
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (aestronglyMeasurable_quadraticVariationCrossingStopApprox
          (fun s => (hX s).aestronglyMeasurable) U (n + 1) (min t U)))

/-- Every increment stopped at an arbitrary deterministic observation time
is controlled by the full-cell mesh and the unique crossing-cell term. -/
theorem abs_uniformPartition_stopped_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    |X (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        X (min t (uniformPartitionTime U (n + 1) i)) omega| ≤
      uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  let a := min t U
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hrightU : uniformPartitionTime U (n + 1) (i + 1) ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi1).2
  have hleftU : uniformPartitionTime U (n + 1) i ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi0).2
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  rw [hmin _ hrightU, hmin _ hleftU]
  by_cases hright : uniformPartitionTime U (n + 1) (i + 1) ≤ a
  · have hleft : uniformPartitionTime U (n + 1) i ≤ a :=
      (monotone_uniformPartitionTime_general U (n + 1)
        (Nat.le_succ i)).trans hright
    rw [min_eq_right hright, min_eq_right hleft]
    exact (abs_uniformPartition_increment_le_max X U n omega hi).trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have haright : a ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      le_of_not_ge hright
    by_cases hleft : uniformPartitionTime U (n + 1) i ≤ a
    · rw [min_eq_left haright, min_eq_right hleft]
      have hicross : i ∈ uniformPartitionCrossingCells U (n + 1) a := by
        simp only [uniformPartitionCrossingCells, Finset.mem_filter, hi,
          hleft, hright, not_false_eq_true, and_self]
      have hsquare :
          (X a omega - X (uniformPartitionTime U (n + 1) i) omega) ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        unfold quadraticVariationCrossingStopApprox
        exact Finset.single_le_sum
          (fun j _hj => sq_nonneg
            (X a omega - X (uniformPartitionTime U (n + 1) j) omega))
          hicross
      have habsSquare :
          |X a omega - X (uniformPartitionTime U (n + 1) i) omega| ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        simpa only [sq_abs] using hsquare
      exact (Real.le_sqrt_of_sq_le habsSquare).trans
        (le_add_of_nonneg_left
          (uniformPartitionMaxAbsIncrement_nonneg X U n omega))
    · have haleft : a ≤ uniformPartitionTime U (n + 1) i :=
        le_of_not_ge hleft
      rw [min_eq_left haright, min_eq_left haleft, sub_self, abs_zero]
      exact uniformPartitionStoppedMaxAbsIncrement_nonneg X U n t omega

/-- Continuous measurable paths make the stopped mesh control vanish in
probability at every deterministic observation time. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement X U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement X U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hXmeas hXcont U
  have hmod : IsContinuousProcessModification X X P :=
    ⟨fun _ => Filter.Eventually.of_forall fun _ => rfl,
      Filter.Eventually.of_forall hXcont⟩
  have hcross : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X U (n + 1) a)
      atTop (fun _ => 0) :=
    hmod.quadraticVariationCrossingStopApprox_tendstoInMeasure
      (fun s => (hXmeas s).aestronglyMeasurable) U a
      ⟨bot_le, min_le_right t U⟩
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox X U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hXmeas s).aestronglyMeasurable) U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement X U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        X U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- The stopped mesh control also vanishes for an arbitrary pre-Brownian
representative; Gaussian boundary-cell control replaces path continuity. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement B U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh :=
    uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U
  have hcross :=
    quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
      hB U a
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox B U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement B U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        B U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- Stopped-grid mesh control for the complex martingale combination. -/
noncomputable def girsanovComplexCombinationStoppedMeshControl
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement M U n t omega +
    |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega

theorem girsanovComplexCombinationStoppedMeshControl_nonneg
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCombinationStoppedMeshControl
      M B c U n t omega := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact add_nonneg
    (uniformPartitionStoppedMaxAbsIncrement_nonneg M U n t omega)
    (mul_nonneg (abs_nonneg c)
      (uniformPartitionStoppedMaxAbsIncrement_nonneg B U n t omega))

/-- Every stopped complex-combination cell is bounded by the stopped mesh
control. -/
theorem
    norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dM := M u omega - M s omega
  let dB := B u omega - B s omega
  have heq :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dM : ℂ)‖ + ‖((c * dB : ℝ) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |dM| + |c| * |dB| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one]
    _ ≤ uniformPartitionStoppedMaxAbsIncrement M U n t omega +
        |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega := by
      apply add_le_add
      · simpa only [dM, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            M U n t omega hi
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        simpa only [dB, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            B U n t omega hi
    _ = girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := rfl

/-- The stopped complex-combination mesh vanishes in probability under the
Challenge path and pre-Brownian hypotheses. -/
theorem girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M B : ℝ≥0 → W → ℝ} (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCombinationStoppedMeshControl M B c U n t)
      atTop (fun _ => 0) := by
  have hM :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hMmeas hMcont U t
  have hBmesh :=
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U t
  have hsum := hM.add_real_noMeas
    (hBmesh.const_mul_real_noMeas |c|)
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement M U n t omega +
      |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega)
    atTop (fun _ => 0)
  simpa only [mul_zero, add_zero] using hsum

/-- Stopping a uniform cell at a deterministic observation time cannot
increase the cell's time width. -/
theorem abs_stopped_uniformPartition_time_increment_le_mesh
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (i : ℕ) :
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
  let u := (uniformPartitionTime U (n + 1) (i + 1) : ℝ)
  let s := (uniformPartitionTime U (n + 1) i : ℝ)
  have hmin := abs_min_sub_min_le_max u (t : ℝ) s (t : ℝ)
  have hdist := dist_uniformPartitionTime_succ_eq U
    (Nat.zero_lt_succ n) i
  calc
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| =
        |min u (t : ℝ) - min s (t : ℝ)| := by
      simp only [u, s, min_comm]
    _ ≤ |u - s| := by
      simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - s))]
        using hmin
    _ = ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      simpa only [u, s, NNReal.dist_eq, Nat.succ_eq_add_one] using hdist

/-- Stopped-grid mesh control for the proposed complex bracket. -/
noncomputable def girsanovComplexBracketStoppedMeshControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
    c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega

theorem girsanovComplexBracketStoppedMeshControl_nonneg
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexBracketStoppedMeshControl
      bracket C c U n t omega := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact add_nonneg
    (add_nonneg
      (uniformPartitionStoppedMaxAbsIncrement_nonneg bracket U n t omega)
      (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (uniformPartitionStoppedMaxAbsIncrement_nonneg C U n t omega))

theorem aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : ∀ s, StronglyMeasurable (bracket s))
    (hC : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c U n t) P := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
      (P := P) hbracket U n t).add aestronglyMeasurable_const).add
    (aestronglyMeasurable_const.mul
      (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        (P := P) hC U n t))

/-- Every stopped complex-bracket cell increment is bounded by its stopped
mesh control. -/
theorem
    norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dA := bracket u omega - bracket s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have htime : |dt| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    dsimp only [dt, u, s]
    rw [NNReal.coe_min, NNReal.coe_min]
    exact abs_stopped_uniformPartition_time_increment_le_mesh U n t i
  have heq :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
        ((2 * c * dC : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ)‖ +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ (‖(dA : ℂ)‖ + ‖((c ^ 2 * dt : ℝ) : ℂ)‖) +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = |dA| + c ^ 2 * |dt| + 2 * |c| * |dC| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one, abs_pow]
      rw [sq_abs]
      ring
    _ ≤ |dA| + c ^ 2 *
          ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * |dC| := by
      gcongr
    _ ≤ uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
          c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega := by
      gcongr
      · simpa only [dA, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            bracket U n t omega hi
      · simpa only [dC, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            C U n t omega hi
    _ = girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := rfl

/-- Continuous bracket and drift paths make the stopped complex-bracket
mesh vanish in probability. -/
theorem girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c U n t) atTop (fun _ => 0) := by
  have hA :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hbracketMeas hbracketCont U t
  have hC :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hCMeas hCCont U t
  have hmesh : Tendsto (fun n : ℕ =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (nhds 0) := by
    have hdiv : Tendsto (fun n : ℕ =>
        ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
        (nhds 0) := by
      have hNN : Tendsto (fun n : ℕ =>
          U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat U)
      change Tendsto (NNReal.toReal ∘ fun n : ℕ =>
        U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds (0 : ℝ))
      simpa only [NNReal.coe_zero] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hNN
    simpa only [mul_zero] using hdiv.const_mul (c ^ 2)
  have hmeshMeasure : TendstoInMeasure P (fun n _omega =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro _n
      exact aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _omega => hmesh
  have hsum := (hA.add_real_noMeas hmeshMeasure).add_real_noMeas
    (hC.const_mul_real_noMeas (2 * |c|))
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
      2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega)
    atTop (fun _ => 0)
  simpa only [add_zero, mul_zero] using hsum

/-- Uniform stopped-grid control for the compensated complex logarithmic
increment `ΔX - ΔQ/2`. -/
noncomputable def girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
    girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2

theorem girsanovComplexCompensatedStoppedMeshControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCompensatedStoppedMeshControl
      M bracket B C c U n t omega := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  exact add_nonneg
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c U n t omega)
    (div_nonneg
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c U n t omega) (by norm_num))

/-- Every stopped compensated complex cell is bounded by the combined
stopped mesh control. -/
theorem norm_girsanov_compensated_stopped_uniformPartition_increment_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖(complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega) -
      (complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ ≤
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := by
  calc
    _ ≤ ‖complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
        ‖complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ / 2 := by
      calc
        _ ≤ ‖complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
            ‖(complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    _ ≤ girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
        girsanovComplexBracketStoppedMeshControl bracket C c U n t omega /
          2 := by
      gcongr
      · exact
          norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
            M B c U n t omega hi
      · exact
          norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
            bracket C c U n t omega hi
    _ = girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := rfl

/-- The stopped compensated mesh vanishes in probability. -/
theorem girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) atTop (fun _ => 0) := by
  have hX :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c U t
  have hQ :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hbracketMeas hbracketCont hCMeas hCCont c U t
  have hsum := hX.add_real_noMeas
    (hQ.const_mul_real_noMeas (1 / 2 : ℝ))
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
      girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2)
    atTop (fun _ => 0)
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by ring
  · exact Filter.Eventually.of_forall fun _omega => by ring

theorem aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M B : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCombinationStoppedMeshControl M B c U n t) P := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    hMmeas U n t).add
      ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        hBmeas U n t).const_mul |c|)

theorem aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) P := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  have hX :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c U n t
  have hQ := aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    (P := P) hbracketMeas hCMeas c U n t
  exact hX.add (by simpa only [div_eq_mul_inv] using hQ.mul_const (2 : ℝ)⁻¹)

/-- Discrete total variation of a complex-valued process on a uniform grid. -/
noncomputable def complexTotalVariationApprox
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega‖

theorem complexTotalVariationApprox_nonneg
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ complexTotalVariationApprox Q U n omega := by
  unfold complexTotalVariationApprox
  exact Finset.sum_nonneg fun _i _hi => norm_nonneg _

/-- Stopping a uniform grid at an arbitrary deterministic time can add at
most one partial-cell contribution to its total variation.  The parameter
`delta` is any common bound for the stopped cell increments. -/
theorem complexTotalVariationApprox_stop_le_of_cell_bound
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hinc : ∀ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖ ≤ delta) :
    complexTotalVariationApprox (fun s w => Q (min t s) w)
        U n omega ≤
      complexTotalVariationApprox Q U n omega + delta := by
  classical
  let a := min t U
  let S := uniformPartitionCrossingCells U n a
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖ ≤
        ‖Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega‖ +
          if i ∈ S then delta else 0 := by
    have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
    have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
    have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
    have hrightU : uniformPartitionTime U n (i + 1) ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2
    have hleftU : uniformPartitionTime U n i ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2
    rw [hmin _ hrightU, hmin _ hleftU]
    by_cases hright : uniformPartitionTime U n (i + 1) ≤ a
    · have hleft : uniformPartitionTime U n i ≤ a :=
        (monotone_uniformPartitionTime_general U n
          (Nat.le_succ i)).trans hright
      rw [min_eq_right hright, min_eq_right hleft]
      exact le_add_of_nonneg_right (ite_nonneg hdelta (le_refl 0))
    · have haright : a ≤ uniformPartitionTime U n (i + 1) :=
        le_of_not_ge hright
      by_cases hleft : uniformPartitionTime U n i ≤ a
      · have hicross : i ∈ S := by
          simp only [S, uniformPartitionCrossingCells, Finset.mem_filter,
            hi, hleft, hright, not_false_eq_true, and_self]
        have hpartial := hinc i hi
        rw [hmin _ hrightU, hmin _ hleftU,
          min_eq_left haright, min_eq_right hleft] at hpartial
        rw [min_eq_left haright, min_eq_right hleft, if_pos hicross]
        exact hpartial.trans
          (le_add_of_nonneg_left
            (norm_nonneg (Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega)))
      · have haleft : a ≤ uniformPartitionTime U n i :=
          le_of_not_ge hleft
        rw [min_eq_left haright, min_eq_left haleft, sub_self, norm_zero]
        exact add_nonneg (norm_nonneg _) (ite_nonneg hdelta (le_refl 0))
  unfold complexTotalVariationApprox
  calc
    (∑ i ∈ Finset.range n,
        ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖) ≤
        ∑ i ∈ Finset.range n,
          (‖Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega‖ +
            if i ∈ S then delta else 0) :=
      Finset.sum_le_sum hcell
    _ = (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) +
        ∑ i ∈ Finset.range n, if i ∈ S then delta else 0 := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) + delta := by
      gcongr
      have hcard : S.card ≤ 1 := by
        simpa only [S] using card_uniformPartitionCrossingCells_le_one U n a
      calc
        (∑ i ∈ Finset.range n, if i ∈ S then delta else 0) =
            ∑ _i ∈ (Finset.range n).filter (· ∈ S), delta := by
          rw [Finset.sum_filter]
        _ = ∑ _i ∈ S, delta := by
          congr 1
          ext i
          simp only [Finset.mem_filter, S, uniformPartitionCrossingCells]
          tauto
        _ = S.card * delta := by simp
        _ ≤ 1 * delta := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hdelta
        _ = delta := one_mul delta

/-- The total variation of the time coordinate on a positive uniform
partition is exactly the length of the interval. -/
theorem totalVariationApprox_time_uniformPartition_succ
    (U : ℝ≥0) (n : ℕ) :
    totalVariationApprox (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () =
      (U : ℝ) := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime U (n + 1) i : ℝ)|) =
        ∑ i ∈ Finset.range (n + 1),
          ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr
        (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = (uniformPartitionTime U (n + 1) (n + 1) : ℝ) -
        (uniformPartitionTime U (n + 1) 0 : ℝ) := by
      exact Finset.sum_range_sub
        (fun i => (uniformPartitionTime U (n + 1) i : ℝ)) (n + 1)
    _ = (U : ℝ) := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        NNReal.coe_zero, sub_zero]

/-- Total variation of a nondecreasing real path telescopes on every
positive uniform partition. -/
theorem totalVariationApprox_monotone_uniformPartition_succ
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmono : Monotone fun s => X s omega) :
    totalVariationApprox X U (n + 1) omega = X U omega - X 0 omega := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|) =
        ∑ i ∈ Finset.range (n + 1),
          (X (uniformPartitionTime U (n + 1) (i + 1)) omega -
            X (uniformPartitionTime U (n + 1) i) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr
        (hmono (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = X (uniformPartitionTime U (n + 1) (n + 1)) omega -
        X (uniformPartitionTime U (n + 1) 0) omega := by
      exact Finset.sum_range_sub
        (fun i => X (uniformPartitionTime U (n + 1) i) omega) (n + 1)
    _ = X U omega - X 0 omega := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]

/-- Negating a real process does not change any discrete total-variation
sum. -/
theorem totalVariationApprox_neg_process
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    totalVariationApprox (fun s omega => -X s omega) U n omega =
      totalVariationApprox X U n omega := by
  unfold totalVariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show -X (uniformPartitionTime U n (i + 1)) omega -
      -X (uniformPartitionTime U n i) omega =
      -(X (uniformPartitionTime U n (i + 1)) omega -
        X (uniformPartitionTime U n i) omega) by ring, abs_neg]

/-- The discrete variation of an absolutely continuous drift path is
bounded by the `L¹` norm of its time integrand. -/
theorem totalVariationApprox_integratedDrift_le
    {W : Type*} (mu : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmu : IntegrableOn (fun r : ℝ => mu r.toNNReal omega)
      (Set.Icc (0 : ℝ) (U : ℝ))) :
    totalVariationApprox (integratedDrift mu) U n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |mu r.toNNReal omega| := by
  let g : ℝ → ℝ := fun r => mu r.toNNReal omega
  change totalVariationApprox
      (fun s (_u : Unit) => nnrealIntegralPrimitive g s) U n () ≤
    ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |g r|
  exact totalVariationApprox_nnrealIntegralPrimitive_le hmu n

/-- Up to its terminal horizon, the totalized Girsanov drift has the same
variation bound as its absolutely continuous real-time primitive. -/
theorem totalVariationApprox_girsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    (theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W)
    (htheta : IntegrableOn (fun r : ℝ => theta r.toNNReal omega)
      (Set.Icc (0 : ℝ) (T : ℝ))) :
    totalVariationApprox (girsanovIntegratedDrift theta T) T n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  cases n with
  | zero =>
      unfold totalVariationApprox
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  | succ n =>
      have hn : 0 < n + 1 := Nat.zero_lt_succ n
      calc
        totalVariationApprox (girsanovIntegratedDrift theta T)
            T (n + 1) omega =
            totalVariationApprox (integratedDrift theta) T (n + 1) omega := by
          unfold totalVariationApprox
          apply Finset.sum_congr rfl
          intro i hi
          have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
          have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
          rw [girsanovIntegratedDrift_eq_integratedDrift,
            girsanovIntegratedDrift_eq_integratedDrift,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi1).2,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi0).2]
        _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
              |theta r.toNNReal omega| :=
          totalVariationApprox_integratedDrift_le theta T (n + 1) omega htheta

/-- A scalar control for the total variation of the proposed complex
bracket `A - c² t + 2 i c C` on a positive uniform grid. -/
noncomputable def girsanovComplexBracketVariationControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
    2 * |c| * totalVariationApprox C U (n + 1) omega

/-- For genuine Girsanov density data, the bracket contribution to the
variation control is exactly its terminal value. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket C c T n omega =
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| * totalVariationApprox C T (n + 1) omega := by
  unfold girsanovComplexBracketVariationControl
  rw [totalVariationApprox_monotone_uniformPartition_succ bracket T n omega
    (hdata.continuous_monotone_bracket omega).2,
    hdata.bracket_zero omega, sub_zero]

/-- The regularized predictable drift has uniformly bounded discrete
variation.  The zero-bracket branch is identically zero; the other branch
uses the terminal square integral to recover the required `L²`, hence `L¹`,
time integrability. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        T (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaInt : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          T (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            T (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          T (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) T (n + 1) omega
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta T (n + 1) omega hthetaInt

/-- The terminally regularized Girsanov drift has the same pathwise
variation bound on every earlier deterministic horizon. This separates the
horizon used in the zero-bracket regularization from the grid horizon. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        U (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaIntT : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    have hthetaIntU : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
      apply hthetaIntT.mono_set
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hUT)
    have hdriftEq : ∀ s, s ≤ U →
        girsanovIntegratedDrift theta T s omega =
          girsanovIntegratedDrift theta U s omega := by
      intro s hs
      unfold girsanovIntegratedDrift
      rw [min_eq_left (hs.trans hUT), min_eq_left hs]
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            U (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          U (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) U (n + 1) omega
      _ = totalVariationApprox (girsanovIntegratedDrift theta U)
          U (n + 1) omega := by
        unfold totalVariationApprox
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
        have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
        rw [hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
          (Nat.zero_lt_succ n) hi1).2,
          hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
            (Nat.zero_lt_succ n) hi0).2]
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (U : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta U (n + 1) omega hthetaIntU

/-- The complex bracket variation for the continuous regularized drift is
bounded uniformly in the grid by an explicit terminal random variable. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| *
          ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| := by
  rw [hdata.girsanovComplexBracketVariationControl_eq]
  gcongr
  exact totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    htheta hbracketTerminal n omega

/-- Terminal random bound for the variation of the regularized complex
Girsanov bracket.  Writing the `L¹` time norm as another predictable drift
keeps measurability available through the existing adaptedness theorem. -/
noncomputable def girsanovComplexTerminalVariationBound
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (omega : W) : ℝ :=
  bracket T omega + c ^ 2 * (T : ℝ) +
    2 * |c| * girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega

theorem GirsanovDensityData.girsanovComplexTerminalVariationBound_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (omega : W) :
    0 ≤ girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbracket : 0 ≤ bracket T omega := by
    rw [← hdata.bracket_zero omega]
    exact (hdata.continuous_monotone_bracket omega).2 bot_le
  have hdrift : 0 ≤ girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega := by
    unfold girsanovIntegratedDrift
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  unfold girsanovComplexTerminalVariationBound
  exact add_nonneg
    (add_nonneg hbracket (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg T)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c)) hdrift)

theorem GirsanovDensityData.stronglyMeasurable_girsanovComplexTerminalVariationBound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta) (c : ℝ) :
    StronglyMeasurable
      (girsanovComplexTerminalVariationBound bracket theta c T) := by
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega => |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W => |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  have hdrift : StronglyMeasurable (girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T) :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs T T).mono (V.le T)
  unfold girsanovComplexTerminalVariationBound
  exact (hbracket.add stronglyMeasurable_const).add
    (stronglyMeasurable_const.mul hdrift)

/-- The grid-dependent bracket-variation control is dominated by its
measurable terminal bound. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbound := hdata.girsanovComplexBracketVariationControl_le
    htheta hbracketTerminal c n omega
  rw [show (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
      |theta r.toNNReal omega|) = girsanovIntegratedDrift
        (fun s omega => |theta s omega|) T T omega by
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega => |theta s omega|) T omega).symm] at hbound
  exact hbound

/-- Every finite-valued strongly measurable real random variable has
vanishing upper tails on a finite measure space. -/
theorem StronglyMeasurable.exists_measureReal_ge_lt_finite
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ P.real {omega | R ≤ Q omega} < delta := by
  intro delta hdelta
  let S : ℕ → Set W := fun n => {omega | (n : ℝ) ≤ Q omega}
  have hSnull (n : ℕ) : NullMeasurableSet (S n) P := by
    change NullMeasurableSet (Q ⁻¹' Set.Ici (n : ℝ)) P
    exact hQ.aemeasurable.nullMeasurable measurableSet_Ici
  have hSanti : Antitone S := by
    intro n m hnm omega homega
    exact (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ)).trans homega
  have hSinter : ⋂ n, S n = ∅ := by
    ext omega
    simp only [Set.mem_iInter, S, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    intro hall
    obtain ⟨n, hn⟩ := exists_nat_gt (Q omega)
    exact (not_lt_of_ge (hall n)) hn
  have hmeasure : Tendsto (fun n => P (S n)) atTop (nhds 0) := by
    have hraw := tendsto_measure_iInter_atTop hSnull hSanti
      ⟨0, measure_ne_top P (S 0)⟩
    rw [hSinter, measure_empty] at hraw
    change Tendsto (P ∘ S) atTop (nhds 0)
    exact hraw
  have hmeasureReal : Tendsto (fun n => P.real (S n)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmeasureReal delta hdelta
  refine ⟨(N + 1 : ℕ), by positivity, ?_⟩
  have hclose := hN (N + 1) (Nat.le_add_right N 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hclose
  simpa only [S, Nat.cast_add, Nat.cast_one] using hclose

/-- A family pointwise dominated by one finite-valued strongly measurable
random variable is uniformly tight. -/
theorem StronglyMeasurable.eventually_tight_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) (q : ℕ → W → ℝ)
    (hle : ∀ n omega, q n omega ≤ Q omega) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ q n omega} < delta := by
  intro delta hdelta
  obtain ⟨R, hR, htail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P)
      hQ delta hdelta
  refine ⟨R, hR, Filter.Eventually.of_forall fun n ↦ ?_⟩
  apply (measureReal_mono ?_).trans_lt htail
  intro omega homega
  exact homega.trans (hle n omega)

/-- The variation of a monotone Girsanov bracket is uniformly tight along
every positive grid schedule. -/
theorem GirsanovDensityData.eventually_tight_totalVariationApprox_bracket
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox bracket T (N n) omega} <
          delta := by
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hbracket
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_monotone_uniformPartition_succ
    bracket T (N n - 1) omega (hdata.continuous_monotone_bracket omega).2
  rw [hpred, hdata.bracket_zero omega, sub_zero] at hvariation
  exact hvariation.le

/-- The variation of the deterministic time coordinate is uniformly tight
along every positive grid schedule. -/
theorem eventually_tight_totalVariationApprox_time
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (T : ℝ≥0) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} < delta := by
  intro delta hdelta
  refine ⟨(T : ℝ) + 1, by positivity,
    Filter.Eventually.of_forall fun n ↦ ?_⟩
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_time_uniformPartition_succ
    T (N n - 1)
  rw [hpred] at hvariation
  have hempty : {omega : W | (T : ℝ) + 1 ≤ totalVariationApprox
      (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} = ∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have heq : totalVariationApprox (fun t (_omega : W) ↦ (t : ℝ))
        T (N n) omega = (T : ℝ) := by
      simpa only [totalVariationApprox] using hvariation
    rw [heq]
    linarith
  rw [hempty, measureReal_empty]
  exact hdelta

/-- Uniform tightness of the terminally regularized drift variation persists
when the uniform grids range over an earlier horizon. -/
theorem
    eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t omega ↦
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (N n) omega} < delta := by
  let H : W → ℝ := girsanovIntegratedDrift
    (fun s omega ↦ |theta s omega|) U U
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega ↦ |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W ↦ |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hH : StronglyMeasurable H := by
    exact (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs U U).mono (V.le U)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hH
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation :=
    totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
      htheta hbracketTerminal hUT (N n - 1) omega
  rw [hpred] at hvariation
  have hIntegral : (∫ r in Set.Icc (0 : ℝ) (U : ℝ),
      |theta r.toNNReal omega|) = H omega := by
    dsimp only [H]
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega ↦ |theta s omega|) U omega).symm
  rwa [hIntegral] at hvariation

end StochasticCalculus
