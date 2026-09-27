/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovMartingaleTransform

/-!
# Block sums along common refinements

Cross-variation mass carried by blocks of cells, the maximal complex step
error along common refinements and its vanishing for continuous paths,
closure of the martingale property under limits in measure with uniform
integrability in a Banach space, and fourth-moment maximal inequalities for
pre-Brownian block oscillations.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- Cross-variation mass carried by the cells between two prefix indices. -/
noncomputable def quadraticCovariationBlockApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n lo hi : ℕ) (omega : W) : ℝ :=
  quadraticCovariationPrefixApprox X Y T n hi omega -
    quadraticCovariationPrefixApprox X Y T n lo omega

/-- Two common-refinement prefix limits give the corresponding
cross-variation block limit, with no positivity restriction on either
endpoint. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationBlockApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (lo hi : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (lo * (n + 1)) (hi * (n + 1))) atTop
      (fun omega ↦
        C (T * (hi : ℝ≥0) / (k : ℝ≥0)) omega -
          C (T * (lo : ℝ≥0) / (k : ℝ≥0)) omega) := by
  have hhi := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk hi
  have hlo := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk lo
  exact hhi.sub_real_noMeas hlo

/-- A complete random coarse-step weight can be integrated against the
cross-variation blocks on every common refinement. -/
theorem
    HasCrossVariationProcessInProbability.fullStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℝ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega)) := by
  apply tendstoInMeasure_finset_sum_mul_fixed_real (Finset.range k)
    (fun i n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)))
    (fun i omega ↦ C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega) c
  · intro i _hi
    simpa only [uniformPartitionTime] using
      h.quadraticCovariationBlockApprox_common_refinement T hk i (i + 1)
  · intro i _hi n
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  · exact hcmeas

/-- Complex random coarse-step weights can likewise be integrated against a
real cross variation on common refinements.  The two real component limits
are synchronized before they are reassembled. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  let R : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let I : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let r : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  let im : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  have hR : TendstoInMeasure P R atTop r := by
    simpa only [R, r] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).re)
        (fun i hi ↦ Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hI : TendstoInMeasure P I atTop im := by
    simpa only [I, im] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).im)
        (fun i hi ↦ Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hblockmeas (i n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (i * (n + 1)) ((i + 1) * (n + 1))) P := by
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) P := by
    dsimp only [R]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hImeas (n : ℕ) : AEStronglyMeasurable (I n) P := by
    dsimp only [I]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  let combine : ℝ → ℝ → ℂ := fun x y ↦ (x : ℂ) + (y : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hparts := TendstoInMeasure.continuous_comp₂ hRmeas hImeas hR hI hcombine
  apply hparts.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, R, I, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, R, I, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add]
  · exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, r, im, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, r, im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_zero, mul_zero,
          zero_add]

/-- Fixed-time cross variation also controls complex frozen coarse-step
weights when the common-refinement sums are written with completed cells.
This is the form used by the complex Girsanov bracket residual. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_beforeStop_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k (i + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k i) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  have hblock := h.fullComplexStepWeight_common_refinement
    hXmeas hYmeas T hk c hcmeas
  apply hblock.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < k := Finset.mem_range.mp hi
    rw [quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) (Nat.succ_le_iff.mpr hilt) omega,
      quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) hilt.le omega]
    unfold quadraticCovariationBlockApprox
    push_cast
    simp only [Nat.succ_eq_add_one]

/-- Complex-valued frozen weights satisfy the same completed-block identity
against a real covariation. -/
theorem quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k j) omega : ℂ)) =
      ∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0) *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ) := by
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticCovariationBeforeStopApprox
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  let r := uniformPartitionTime t n (i + 1)
  let a := uniformPartitionTime t k j
  let b := uniformPartitionTime t k (j + 1)
  have hab : a ≤ b := hgrid j
  by_cases hra : r ≤ a
  · have hrb : r ≤ b := hra.trans hab
    have hnot : ¬a < r := not_lt_of_ge hra
    simp only [r, a, b] at hra hrb hnot ⊢
    simp only [hra, hrb, hnot, false_and, ↓reduceIte, sub_self,
      zero_mul, mul_zero]
  · by_cases hrb : r ≤ b
    · have har : a < r := lt_of_not_ge hra
      simp only [r, a, b] at hra hrb har ⊢
      simp only [hra, hrb, har, true_and, ↓reduceIte]
      push_cast
      ring
    · simp only [r, a, b] at hra hrb ⊢
      simp only [hra, hrb, and_false, ↓reduceIte, sub_self,
        zero_mul, mul_zero]

/-- A right endpoint in a positive uniform partition activates exactly one
coarse complex step. -/
theorem uniformPartition_rightEndpoint_complexStep_sum_eq
    (t r : ℝ≥0) (k : ℕ) (ht : 0 < t) (hk : 0 < k)
    (c : ℕ → ℂ) {j : ℕ} (hj : j ∈ Finset.range k)
    (hactive : uniformPartitionTime t k j < r ∧
      r ≤ uniformPartitionTime t k (j + 1)) :
    (∑ l ∈ Finset.range k,
      if uniformPartitionTime t k l < r ∧
          r ≤ uniformPartitionTime t k (l + 1) then c l else 0) = c j := by
  have hstrict : StrictMono (uniformPartitionTime t k) := by
    intro a b hab
    unfold uniformPartitionTime
    have hk' : (0 : ℝ≥0) < (k : ℕ) := by exact_mod_cast hk
    gcongr
  rw [Finset.sum_eq_single j]
  · simp only [hactive, and_self, ↓reduceIte]
  · intro l hl hlj
    have hnot : ¬(uniformPartitionTime t k l < r ∧
        r ≤ uniformPartitionTime t k (l + 1)) := by
      intro hlactive
      rcases lt_trichotomy l j with hlt | heq | hgt
      · have hle : l + 1 ≤ j := by omega
        exact (not_lt_of_ge hlactive.2)
          ((hstrict.monotone hle).trans_lt hactive.1)
      · exact hlj heq
      · have hle : j + 1 ≤ l := by omega
        exact (not_lt_of_ge hactive.2)
          ((hstrict.monotone hle).trans_lt hlactive.1)
    simp only [hnot, ↓reduceIte]
  · exact fun hnot ↦ (hnot hj).elim

/-- A complex scalar close to the unique active coarse block is close to
the corresponding complex right-endpoint step sum. -/
theorem norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    (t r : ℝ≥0) (k : ℕ) (hk : 0 < k) (hr0 : 0 < r) (hrt : r ≤ t)
    (weight : ℂ) (c : ℕ → ℂ) (K : ℝ)
    (hclose : ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < r ∧
        r ≤ uniformPartitionTime t k (j + 1) →
      ‖weight - c j‖ ≤ K) :
    ‖weight - ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        c j
      else 0‖ ≤ K := by
  have hone := uniformPartition_rightEndpoint_blocks_sum_one
    t r k hk hr0 hrt
  have honeC : (∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        (1 : ℂ)
      else 0) = 1 := by
    exact_mod_cast hone
  have hweightSum : weight = ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        weight
      else 0 := by
    calc
      weight = weight * 1 := by ring
      _ = weight * ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            (1 : ℂ)
          else 0 := by rw [honeC]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  have hdiff :
      (weight - (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            c j
          else 0)) =
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            weight - c j
          else 0) := by
    calc
      _ = (∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0 := congrArg (fun z ↦ z - ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then c j else 0)
                hweightSum
      _ = ∑ j ∈ Finset.range k,
          ((if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0) := by rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  rw [hdiff]
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        ‖if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          weight - c j
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          K
        else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hactive
      · exact hclose j hj hactive
      · norm_num
    _ = K := by
      have hscaled := congrArg (fun x : ℝ ↦ K * x) hone
      simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul,
        one_mul] using hscaled

/-- Maximum error made by freezing a complex weight on the coarse cells of
a positive common refinement. -/
noncomputable def commonRefinementMaxComplexStepError
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
  (k n : ℕ) (omega : W) : ℝ :=
  (Finset.range ((k + 1) * (n + 1))).sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖

theorem commonRefinementMaxComplexStepError_nonneg
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
    (k n : ℕ) (omega : W) :
    0 ≤ commonRefinementMaxComplexStepError A T k n omega := by
  unfold commonRefinementMaxComplexStepError
  exact (norm_nonneg _).trans
    (Finset.le_sup' (fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖)
      (Finset.mem_range.mpr (Nat.mul_pos
        (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))))

theorem stronglyMeasurable_commonRefinementMaxComplexStepError
    {W : Type*} [MeasurableSpace W] {A : ℝ≥0 → W → ℂ}
    (hA : ∀ s, StronglyMeasurable (A s)) (T : ℝ≥0) (k n : ℕ) :
    StronglyMeasurable (commonRefinementMaxComplexStepError A T k n) := by
  apply Measurable.stronglyMeasurable
  unfold commonRefinementMaxComplexStepError
  let f : ℕ → W → ℝ := fun i omega ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hf : ∀ i ∈ Finset.range ((k + 1) * (n + 1)), Measurable (f i) := by
    intro i _hi
    let g : ℕ → W → ℂ := fun j omega ↦
      if uniformPartitionTime T (k + 1) j <
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
          uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
            uniformPartitionTime T (k + 1) (j + 1) then
        A (uniformPartitionTime T (k + 1) j) omega
      else 0
    have hg : ∀ j ∈ Finset.range (k + 1), StronglyMeasurable (g j) := by
      intro j _hj
      dsimp only [g]
      split_ifs
      · exact hA _
      · exact stronglyMeasurable_const
    have hsumFun : StronglyMeasurable
        (∑ j ∈ Finset.range (k + 1), g j) :=
      Finset.stronglyMeasurable_sum (Finset.range (k + 1)) hg
    have hsum : StronglyMeasurable (fun omega ↦
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0) := by
      convert hsumFun using 1
      funext omega
      simp only [Finset.sum_apply, g]
    have hnorm :=
      ((hA (uniformPartitionTime T ((k + 1) * (n + 1)) i)).sub hsum)
        |>.norm.measurable
    simpa only [f, Pi.sub_apply] using hnorm
  have hsup := Finset.measurable_sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) hf
  convert hsup using 1
  ext omega
  symm
  exact Finset.sup'_apply _ f omega

/-- The common-refinement freezing error of a continuous complex path
vanishes, uniformly over an arbitrary number of inner subdivisions. -/
theorem commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0) (hT : 0 < T)
    (omega : W) (hA : Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    Tendsto (fun k ↦ commonRefinementMaxComplexStepError A T k (n k) omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := commonRefinement_continuousWeight_close
    (fun s ↦ A s omega) hA T (epsilon / 2) (by positivity)
  refine ⟨K, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (commonRefinementMaxComplexStepError_nonneg
      A T k (n k) omega)]
  let s := Finset.range ((k + 1) * (n k + 1))
  let f : ℕ → ℝ := fun i ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.mul_pos
    (Nat.zero_lt_succ k) (Nat.zero_lt_succ (n k)))⟩
  change s.sup' hs f < epsilon
  rw [Finset.sup'_lt_iff]
  intro i hi
  change i ∈ Finset.range ((k + 1) * (n k + 1)) at hi
  change ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖ < epsilon
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hnpos : 0 < n k + 1 := Nat.zero_lt_succ (n k)
  have hkn : 0 < (k + 1) * (n k + 1) := Nat.mul_pos hkpos hnpos
  have hi1 : i + 1 ≤ (k + 1) * (n k + 1) := Finset.mem_range.mp hi
  have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
  have hr0 :
      0 < uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) := by
    have hstrict : StrictMono
        (uniformPartitionTime T ((k + 1) * (n k + 1))) := by
      intro a b hab
      unfold uniformPartitionTime
      have hden : (0 : ℝ≥0) < ((k + 1) * (n k + 1) : ℕ) := by
        exact_mod_cast hkn
      gcongr
    have hpos := hstrict (Nat.zero_lt_succ i)
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      using hpos
  refine (norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    T (uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1))
      (k + 1) hkpos hr0 hrt
      (A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega)
      (fun j ↦ A (uniformPartitionTime T (k + 1) j) omega)
      (epsilon / 2) ?_).trans_lt (by linarith)
  intro j hj hactive
  exact (hK (k + 1) (by omega) hkpos (n k + 1) hnpos i hi j hj
    hactive).le

/-- Measurable continuous complex paths have vanishing common-refinement
freezing error in probability, uniformly over arbitrary inner counts. -/
theorem commonRefinementMaxComplexStepError_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {A : ℝ≥0 → W → ℂ} (hAmeas : ∀ s, StronglyMeasurable (A s))
    (T : ℝ≥0) (hT : 0 < T)
    (hAcont : ∀ omega, Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    TendstoInMeasure P
      (fun k ↦ commonRefinementMaxComplexStepError A T k (n k))
      atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro k
    exact (stronglyMeasurable_commonRefinementMaxComplexStepError
      hAmeas T k (n k)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
        A T hT omega (hAcont omega) n

/-- The completed-block freezing estimate remains sharp for complex left
weights; no loss from splitting into real and imaginary components is
needed. -/
theorem norm_complexWeightedQuadraticCovariation_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (weight c : ℕ → W → ℂ) (K : ℝ) (hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      ‖weight i omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0‖ ≤ K) :
    ‖(∑ i ∈ Finset.range n, weight i omega *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k (j + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k j) omega : ℂ)‖ ≤
      K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
  rw [quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range n,
        (weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, K *
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, ← Complex.ofReal_sub,
        ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs]
      simp only [Real.norm_eq_abs]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * (∑ i ∈ Finset.range n,
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_uniformPartition_increment_mul_le_sqrt X Y t n omega) hK

/-- The coherent stopped-grid covariation agrees with the ordinary
covariation approximant at its terminal horizon. -/
theorem uniformStoppedCovariationApprox_terminal
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformStoppedCovariationApprox X Y T (n + 1) T omega =
      quadraticCovariationApprox X Y T (n + 1) omega := by
  unfold uniformStoppedCovariationApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right hright.2, min_eq_right hleft.2]

/-- Process-level discrete integration by parts on one fixed uniform grid. -/
theorem uniformStopped_product_decomposition
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T (n + 1) t omega +
        uniformAdaptedMartingaleSmulProcess X Y T (n + 1) t omega +
          uniformStoppedCovariationApprox X Y T (n + 1) t omega := by
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  unfold uniformStoppedCovariationApprox
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  symm
  calc
    (∑ i ∈ Finset.range (n + 1),
        (((Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega) •
              X (uniformPartitionTime T (n + 1) i) omega +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) •
              Y (uniformPartitionTime T (n + 1) i) omega) +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) *
          (Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega))) =
        ∑ i ∈ Finset.range (n + 1),
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega *
              Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega *
              Y (min t (uniformPartitionTime T (n + 1) i)) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : uniformPartitionTime T (n + 1) i ≤ t
      · rw [min_eq_right hi]
        simp only [smul_eq_mul]
        ring
      · have hright : t ≤ uniformPartitionTime T (n + 1) i := le_of_not_ge hi
        have hnext : uniformPartitionTime T (n + 1) i ≤
            uniformPartitionTime T (n + 1) (i + 1) :=
          monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i)
        rw [min_eq_left hright, min_eq_left (hright.trans hnext)]
        simp only [sub_self, zero_smul, zero_mul, add_zero]
    _ = X (min t (uniformPartitionTime T (n + 1) (n + 1))) omega *
          Y (min t (uniformPartitionTime T (n + 1) (n + 1))) omega -
        X (min t (uniformPartitionTime T (n + 1) 0)) omega *
          Y (min t (uniformPartitionTime T (n + 1) 0)) omega := by
      exact Finset.sum_range_sub
        (fun i ↦ X (min t (uniformPartitionTime T (n + 1) i)) omega *
          Y (min t (uniformPartitionTime T (n + 1) i)) omega) (n + 1)
    _ = X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega := by
      have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      have htop : uniformPartitionTime T (n + 1) (n + 1) = T := by
        rw [uniformPartitionTime]
        exact mul_div_cancel_right₀ T hn
      rw [htop]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        min_zero]

/-- Positive-grid form of the coherent discrete product decomposition. -/
theorem uniformStopped_product_decomposition_pos
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T n t omega +
        uniformAdaptedMartingaleSmulProcess X Y T n t omega +
          uniformStoppedCovariationApprox X Y T n t omega := by
  have hn' : 1 ≤ n := hn
  simpa only [Nat.sub_add_cancel hn'] using
    uniformStopped_product_decomposition X Y T (n - 1) t omega

/-- A Banach-valued `L¹`-norm limit of integrable functions is
integrable. -/
theorem integrable_of_tendsto_eLpNorm_one_sub_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {f : ℕ → W → E} {g : W → E}
    (hf : ∀ n, Integrable (f n) P)
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g - f n) 1 P)
      Filter.atTop (nhds 0)) :
    Integrable g P := by
  have hlt : ∀ᶠ n in Filter.atTop,
      eLpNorm (g - f n) 1 P < 1 :=
    (tendsto_order.1 hconv).2 1 (by simp)
  rcases hlt.exists with ⟨n, hn⟩
  have hdiff : Integrable (g - f n) P :=
    memLp_one_iff_integrable.mp (hn.trans (by simp))
  simpa only [sub_add_cancel] using hdiff.add (hf n)

/-- A strongly adapted pointwise-in-time `L¹`-norm limit of Banach-valued
martingales is a martingale. -/
theorem martingale_of_tendsto_eLpNorm_one_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hconv : ∀ t, Filter.Tendsto
      (fun n ↦ eLpNorm (Y t - X n t) 1 P) Filter.atTop (nhds 0)) :
    Martingale Y V P := by
  have hYint : ∀ t, Integrable (Y t) P := fun t ↦
    integrable_of_tendsto_eLpNorm_one_sub_banach
      (fun n ↦ (hX n).integrable t)
      (hconv t)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff one_ne_zero]
  apply le_antisymm
  · have hconvS : Filter.Tendsto (fun n ↦ eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      convert hconv s using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Filter.Tendsto (fun n ↦
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      simpa only [add_zero] using (hconv t).add hconvS
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hdecomp :
        P[Y t | V s] - Y s =ᵐ[P]
          P[Y t - X n t | V s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (V s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      abel
    calc
      eLpNorm (P[Y t | V s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | V s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | V s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- Banach-valued Vitali convergence in `L¹`: convergence in measure plus
uniform integrability gives convergence of the `L¹` distance. -/
theorem tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {X : ℕ → W → E} {Y : W → E}
    (hUI : UniformIntegrable X 1 P)
    (hconv : TendstoInMeasure P X atTop Y) :
    Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (nhds 0) := by
  have hYmem : MemLp Y 1 P := hUI.memLp_of_tendstoInMeasure hconv
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ (hUI.memLp n).aestronglyMeasurable) hYmem hUI.unifIntegrable hconv

/-- Banach-valued Vitali closure for martingales: convergence in measure
plus uniform integrability at every time gives the `L¹` convergence required
by `martingale_of_tendsto_eLpNorm_one_banach`. -/
theorem martingale_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hUI : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) :
    Martingale Y V P := by
  apply martingale_of_tendsto_eLpNorm_one_banach hX hYadapt
  intro t
  have hLp : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI t) (hconv t)
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- Uniform integrability passes from one measurable family to any
Banach-valued family whose pointwise norm it dominates.  The source and
target spaces may differ. -/
theorem UniformIntegrable.mono_norm_banach
    {W I E F : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {P : Measure W} {f : I → W → E} {g : I → W → F}
    {p : ℝ≥0∞} (hf : UniformIntegrable f p P)
    (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hgf : ∀ i omega, ‖g i omega‖ ≤ ‖f i omega‖) :
    UniformIntegrable g p P := by
  refine ⟨unifIntegrable_iff.2 ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := unifIntegrable_iff.1 hf.1 epsilon hepsilon
    refine ⟨delta, hdelta, fun i s hPs ↦ ?_⟩
    exact (eLpNorm_mono ((hg i).mono_measure Measure.restrict_le_self) (hgf i)).trans
      (hbound i s hPs)
  · obtain ⟨C, hC⟩ := hf.2
    exact ⟨C, fun i ↦ (eLpNorm_mono (hg i) (hgf i)).trans (hC i)⟩

/-- Uniform integrability is preserved when restricting to an arbitrary
reindexed subfamily. -/
theorem UniformIntegrable.comp_index
    {W I J E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (g : J → I) :
    UniformIntegrable (fun j => f (g j)) p P := by
  refine ⟨UnifIntegrable.comp g hf.1, ?_⟩
  · obtain ⟨C, hC⟩ := hf.2
    exact ⟨C, fun j => hC (g j)⟩

/-- The sum of two uniformly integrable Banach-valued families is uniformly
integrable. -/
theorem UniformIntegrable.add_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f g : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hg : UniformIntegrable g p P)
    (hp : 1 ≤ p) :
    UniformIntegrable (fun i omega => f i omega + g i omega) p P := by
  refine ⟨?_, ?_⟩
  · change UnifIntegrable (f + g) p P
    exact hf.1.add hg.1 hp
  · obtain ⟨Cf, hCf⟩ := hf.2
    obtain ⟨Cg, hCg⟩ := hg.2
    refine ⟨Cf + Cg, fun i => ?_⟩
    exact (eLpNorm_add_le hp).trans
      (add_le_add (hCf i) (hCg i))

/-- A fixed natural multiple of a uniformly integrable Banach-valued family
is uniformly integrable. -/
theorem UniformIntegrable.nsmul_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hp : 1 ≤ p) (n : ℕ) :
    UniformIntegrable (fun i omega => n • f i omega) p P := by
  induction n with
  | zero =>
      simp only [zero_nsmul]
      refine ⟨unifIntegrable_iff.2 ?_, ⟨0, fun _ => by simp⟩⟩
      intro epsilon hepsilon
      exact ⟨1, one_pos, fun _ _ _ => by simp⟩
  | succ n hn =>
      simpa only [Nat.succ_eq_add_one, add_nsmul, one_nsmul] using
        UniformIntegrable.add_banach hn hf hp

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right continuation of its filtration when its values are
uniformly integrable along every convergent deterministic-time sequence. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => X (a n)) atTop (X r))
    (hUI : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        UniformIntegrable (fun n => X (a n)) 1 P) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t =>
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ => (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n =>
    min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ => t) atTop (nhds t) :=
      tendsto_const_nhds
    have hs : Tendsto
        (fun n : ℕ => s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by
      simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  have hL1 : Tendsto (fun n => eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI s u hu) (hstoch s u hu)
  have hIntegral : Tendsto
      (fun n => ∫ omega in A, X (u n) omega ∂P) atTop
      (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s)
      (Filter.Eventually.of_forall fun n => hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) =
        ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n => ∫ omega in A, X (u n) omega ∂P) =
      fun _ => ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right-continuation of its filtration when it is bounded on
each deterministic time interval.  The local bound supplies uniform
integrability for the values just to the right of the conditioning time. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n ↦ X (a n)) atTop (X r))
    (hbound : ∀ T : ℝ≥0, ∃ K : ℝ≥0, ∀ t ≤ T, ∀ omega,
      ‖X t omega‖ ≤ K) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t ↦
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ ↦ (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n ↦ min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t) := tendsto_const_nhds
    have hs : Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  obtain ⟨K, hK⟩ := hbound t
  have hmeas (n : ℕ) : AEStronglyMeasurable (X (u n)) P :=
    (hX.integrable (u n)).aestronglyMeasurable
  have hconst : UniformIntegrable
      (fun _ : ℕ ↦ fun _ : W ↦ (K : ℝ)) 1 P :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr (integrable_const (K : ℝ)))
  have hUI : UniformIntegrable (fun n ↦ X (u n)) 1 P :=
    UniformIntegrable.mono_norm_banach hconst hmeas fun n omega ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] using
        hK (u n) (hut n) omega
  have hL1 : Tendsto (fun n ↦ eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      hUI (hstoch s u hu)
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s)
      (Filter.Eventually.of_forall fun n ↦ hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) = ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n ↦ ∫ omega in A, X (u n) omega ∂P) =
      fun _ ↦ ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- Doob's fourth-moment maximal estimate for a pre-Brownian process sampled
on a finite uniform grid.  Applied to a shifted pre-Brownian process, this
uniformly controls all fine-grid oscillations inside one coarse interval. -/
theorem preBrownian_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (uniformPartitionTime t n k) omega) ^ 4)} ≤
      ENNReal.ofReal (3 * (t : ℝ) ^ 2) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒱 := monotoneReindexFiltration (Filtration.natural B hsm)
    (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hmart : Martingale (fun k => B (uniformPartitionTime t n k)) 𝒱 P := by
    exact martingale_comp_monotone (martingale_brownian_natural hB hsm)
      (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hfourth : ∀ k, Integrable
      (fun omega => (B (uniformPartitionTime t n k) omega) ^ 4) P := fun k =>
    integrable_pow_four_of_hasLaw_gaussianReal _
      (hB.hasLaw_eval (uniformPartitionTime t n k))
  have hmax := martingale_maximal_pow_four_ineq hmart hfourth epsilon n
  have htop : uniformPartitionTime t n n = t := by
    unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    exact mul_div_cancel_right₀ t hn0
  rw [htop,
    integral_pow_four_of_hasLaw_gaussianReal t (hB.hasLaw_eval t)] at hmax
  exact hmax

/-- Fourth-moment maximal control for all sampled increments inside a
deterministic interval.  The estimate is independent of the number of fine
grid points. -/
theorem preBrownian_interval_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (a b : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (a + uniformPartitionTime (b - a) n k) omega -
            B a omega) ^ 4)} ≤
      ENNReal.ofReal (3 * ((b - a : ℝ≥0) : ℝ) ^ 2) := by
  let Bs : ℝ≥0 → W → ℝ := fun t omega => B (a + t) omega - B a omega
  have hBs : IsPreBrownianReal Bs P := by
    simpa only [Bs] using hB.shift a
  have hBsmeas : ∀ t, StronglyMeasurable (Bs t) := fun t =>
    (hsm (a + t)).sub (hsm a)
  simpa only [Bs] using preBrownian_uniformPartition_maximal_pow_four_ineq
    hBs hBsmeas (b - a) hn epsilon

/-- A union bound over a coarse uniform partition controls every sampled
Brownian oscillation inside every coarse block.  Its right-hand side is of
order `k * (T/k)²`, hence vanishes as the coarse mesh tends to zero. -/
theorem preBrownian_uniformBlocks_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (T : ℝ≥0) (k : ℕ) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P (⋃ j ∈ Finset.range k, {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T k j +
                uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
              B (uniformPartitionTime T k j) omega) ^ 4)}) ≤
      (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
  let E : ℕ → Set W := fun j => {omega |
    (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4)}
  have hblock (j : ℕ) : epsilon * P (E j) ≤
      ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
    have hraw := preBrownian_interval_uniformPartition_maximal_pow_four_ineq
      hB hsm (uniformPartitionTime T k j)
        (uniformPartitionTime T k j + T / (k : ℝ≥0)) hn epsilon
    simpa only [E, add_tsub_cancel_left] using hraw
  change epsilon * P (⋃ j ∈ Finset.range k, E j) ≤ _
  calc
    epsilon * P (⋃ j ∈ Finset.range k, E j) ≤
        epsilon * ∑ j ∈ Finset.range k, P (E j) := by
      gcongr
      exact measure_biUnion_finset_le (Finset.range k) E
    _ = ∑ j ∈ Finset.range k, epsilon * P (E j) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range k, ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun j _hj => hblock j
    _ = (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Outside the coarse-block maximal event, every sampled oscillation is
bounded by the chosen fourth-root threshold. -/
theorem blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
    {W : Type*} (B : ℝ≥0 → W → ℝ) (T : ℝ≥0) {k n : ℕ}
    (delta : ℝ≥0) (_hdelta : 0 < delta) {omega : W}
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ∀ j ∈ Finset.range k, ∀ r ∈ Finset.range (n + 1),
      |B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta := by
  intro j hj r hr
  have hjnot : omega ∉ {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)} := by
    intro hmem
    apply homega
    simp only [Set.mem_iUnion]
    exact ⟨j, hj, hmem⟩
  simp only [Set.mem_ofPred_eq] at hjnot
  have hsup : (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4) <
      (delta : ℝ) ^ 4 := lt_of_not_ge hjnot
  have hterm := Finset.le_sup'
    (fun r =>
      (B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega) ^ 4) hr
  have hpow : |B (uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
      B (uniformPartitionTime T k j) omega| ^ 4 < (delta : ℝ) ^ 4 := by
    rw [← abs_pow]
    rw [abs_of_nonneg (by positivity)]
    exact hterm.trans_lt hsup
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _)
    delta.coe_nonneg (by norm_num : (4 : ℕ) ≠ 0)).mp hpow |>.le

/-- A concrete diagonal scale: `(k+1)^5` coarse blocks and oscillation
threshold `1/(k+1)` make the exceptional probability vanish, uniformly in
the positive number of inner subdivisions. -/
theorem tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (T : ℝ≥0)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k =>
      let K := (k + 1) ^ 5
      let delta : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0)⁻¹
      P.real (⋃ j ∈ Finset.range K, {omega |
        ((delta : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T K j +
                uniformPartitionTime (T / (K : ℝ≥0)) (n k) r) omega -
              B (uniformPartitionTime T K j) omega) ^ 4)}))
      atTop (nhds 0) := by
  let d : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let b : ℕ → ℝ := fun k => 3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)
  have hb : Tendsto b atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (3 * (T : ℝ) ^ 2)
    have hc := h.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ =>
      3 * (T : ℝ) ^ 2 / ((k + 1 : ℕ) : ℝ)) atTop (nhds 0) at hc
    simpa only [b, Nat.cast_add, Nat.cast_one] using hc
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun k => ?_) hb
  let E : Set W := ⋃ j ∈ Finset.range (K k), {omega |
    ((d k : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T (K k) j +
            uniformPartitionTime (T / (K k : ℝ≥0)) (n k) r) omega -
          B (uniformPartitionTime T (K k) j) omega) ^ 4)}
  have hK : 0 < K k := by
    dsimp only [K]
    positivity
  have hd : 0 < d k := by
    dsimp only [d]
    positivity
  have hraw := preBrownian_uniformBlocks_maximal_pow_four_ineq
    hB hsm T (K k) (hn k) ((d k) ^ 4)
  change ((d k : ℝ≥0∞) ^ 4) * P E ≤ _ at hraw
  have htop : ((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
  change (d k : ℝ) ^ 4 * P.real E ≤
    (((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)).toReal at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  change P.real E ≤ b k
  have hdivide : P.real E ≤
      ((K k : ℝ) *
        (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)) /
        (d k : ℝ) ^ 4 := by
    apply (le_div_iff₀ (pow_pos (show (0 : ℝ) < d k by exact_mod_cast hd) 4)).2
    simpa only [mul_comm] using hreal
  calc
    P.real E ≤ _ := hdivide
    _ = b k := by
      dsimp only [K, d, b]
      simp only [NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_div]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
      push_cast
      ring

/-- Ordinary fixed-time quadratic-variation convergence supplies the
geometric-mean tightness needed by the polynomial two-scale argument.  The
limit assumption is deliberately phrased for the sum: this is exactly the
coercive quantity controlling the geometric mean. -/
theorem HasQuadraticVariationProcessInProbability.polynomialBlocks_eventually_tight_sqrt_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X B QX QB : ℝ≥0 → W → ℝ}
    (hX : HasQuadraticVariationProcessInProbability X QX P)
    (hB : HasQuadraticVariationProcessInProbability B QB P)
    (T : ℝ≥0)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox X T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  intro n hn
  let s : ℕ → ℕ := fun k => ((k + 1) ^ 5) * n k
  let r : ℕ → ℕ := fun k => s k - 1
  have hs_pos : ∀ k, 0 < s k := fun k => by
    dsimp only [s]
    exact Nat.mul_pos (by positivity) (hn k)
  have hr : Tendsto r atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ s a := by
      exact Nat.le_mul_of_pos_right _ (hn a)
    have halt : a < s a := by omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hr_add : ∀ k, r k + 1 = s k := fun k => by
    dsimp only [r]
    exact Nat.sub_add_cancel (hs_pos k)
  have hqX : TendstoInMeasure P
      (fun k => quadraticVariationApprox X T (s k)) atTop (QX T) := by
    convert (hX T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox X T) (hr_add k).symm
  have hqB : TendstoInMeasure P
      (fun k => quadraticVariationApprox B T (s k)) atTop (QB T) := by
    convert (hB T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox B T) (hr_add k).symm
  have htight := hqX.eventually_tight_sqrt_mul hqB
    (fun k omega => quadraticVariationApprox_nonneg X T (s k) omega)
    (fun k omega => quadraticVariationApprox_nonneg B T (s k) omega)
    hQint hQnonneg
  simpa only [s] using htight

/-- Girsanov density data and a pre-Brownian driver automatically satisfy
the polynomial-grid tightness condition for the martingale--Brownian
quadratic sums.  In particular, Novikov supplies the only random first
moment needed here. -/
theorem GirsanovDensityData.polynomialBlocks_eventually_tight_sqrt_martingale_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox M T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  apply h.localQuadraticVariation.toProcess
    |>.polynomialBlocks_eventually_tight_sqrt_mul
      (fun t => quadraticVariation_preBrownianReal_inProbability hB t) T
  · exact h.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← h.bracket_zero omega]
        exact (h.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

end StochasticCalculus
