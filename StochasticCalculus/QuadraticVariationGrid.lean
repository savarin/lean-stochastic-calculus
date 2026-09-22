/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.QuadraticVariationTightness

/-!
# Quadratic variation on a common rational grid

Terminal quadratic variation at several horizons does not automatically put
the corresponding sums on one partition.  This file introduces the prefix
sum on a common uniform grid and proves the exact rescaling identity.  As a
first coherent-process consequence, every fixed rational prefix converges in
probability along common refinements of that grid.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators NNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [MeasurableSpace W] {P : Measure W}
  {X : ℝ≥0 → W → ℝ}

/-- Deterministic stopping of a natural Itô integral inherits quadratic
variation from the time-restricted predictable integrand.  This is the
representative-level bridge needed to obtain prefix limits on arbitrary
uniform grids, rather than only on common refinements. -/
theorem quadraticVariation_stopped_naturalItoProcessRepresentative
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
    {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s => naturalItoProcessRepresentative hB.toIsPreBrownianReal
        hsm rfl U (min s a)) P t
      (predictableQuadraticVariation hsm
        (predictableTimeRestrict (Filtration.natural B hsm) a U) t) := by
  have hstopped := quadraticVariation_naturalItoProcessRepresentative
    hB hsm (predictableTimeRestrict (Filtration.natural B hsm) a U) t
  apply hstopped.congr
  · intro s
    exact naturalItoProcessRepresentative_predictableTimeRestrict_ae
      hB.toIsPreBrownianReal hsm rfl U s a
  · exact Filter.EventuallyEq.rfl

/-- The bracket of a deterministically restricted integrand is the original
bracket stopped at the same deterministic time. -/
theorem predictableQuadraticVariation_timeRestrict_ae
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
    {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (a t : ℝ≥0) :
    predictableQuadraticVariation hsm
        (predictableTimeRestrict (Filtration.natural B hsm) a U) t =ᵐ[P]
      predictableQuadraticVariation hsm U (min t a) := by
  have hswap := (Measure.measurePreserving_swap
    (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp
      (predictableTimeRestrict_coeFn (Filtration.natural B hsm) a U)
  have hsections := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hsections] with omega homega
  unfold predictableQuadraticVariation
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((predictableTimeRestrict (Filtration.natural B hsm) a U :
          ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) =
        ∫ s in Set.Ioc (0 : ℝ≥0) t,
          ((predictableTimeFrame (W := W) a).indicator
            (U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae homega] with s hs
      have hs' :
          (predictableTimeRestrict (Filtration.natural B hsm) a U :
            ℝ≥0 × W → ℝ) (s, omega) =
          (predictableTimeFrame (W := W) a).indicator
            (U : ℝ≥0 × W → ℝ) (s, omega) := by
        simpa only [Function.comp_apply, Prod.swap_prod_mk] using hs
      rw [hs']
    _ = ∫ s in Set.Ioc (0 : ℝ≥0) (min t a),
          ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      rw [← integral_indicator measurableSet_Ioc,
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with s
      by_cases hst : s ∈ Set.Ioc (0 : ℝ≥0) t
      · by_cases hsa : s ∈ Set.Ioc (0 : ℝ≥0) a
        · have hmin : s ∈ Set.Ioc (0 : ℝ≥0) (min t a) :=
            ⟨hst.1, le_min hst.2 hsa.2⟩
          rw [Set.indicator_of_mem hst, Set.indicator_of_mem hmin,
            Set.indicator_of_mem]
          exact ⟨hsa, Set.mem_univ _⟩
        · have hmin : s ∉ Set.Ioc (0 : ℝ≥0) (min t a) := by
            intro hs
            exact hsa ⟨hs.1, hs.2.trans (min_le_right t a)⟩
          rw [Set.indicator_of_mem hst, Set.indicator_of_notMem hmin,
            Set.indicator_of_notMem]
          · norm_num
          · exact fun hs => hsa hs.1
      · have hmin : s ∉ Set.Ioc (0 : ℝ≥0) (min t a) := by
          intro hs
          exact hst ⟨hs.1, hs.2.trans (min_le_left t a)⟩
        rw [Set.indicator_of_notMem hst, Set.indicator_of_notMem hmin]

/-- A natural Itô integral stopped at `a` has its original bracket stopped at
`a`, on arbitrary uniform partitions of any terminal horizon `t`. -/
theorem quadraticVariation_stopped_naturalItoProcessRepresentative_bracket
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
    {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (a t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s => naturalItoProcessRepresentative hB.toIsPreBrownianReal
        hsm rfl U (min s a)) P t
      (predictableQuadraticVariation hsm U (min t a)) := by
  exact (quadraticVariation_stopped_naturalItoProcessRepresentative
    hB hsm U a t).congr (fun _ => Filter.EventuallyEq.rfl)
      (predictableQuadraticVariation_timeRestrict_ae hsm U a t)

/-- The squared increments whose right endpoints lie before a deterministic
stopping time. -/
noncomputable def quadraticVariationBeforeStopApprox
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (a : ℝ≥0)
    (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    if uniformPartitionTime t n (i + 1) ≤ a then
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega) ^ 2
    else 0

/-- Fixed-time measurability of a process makes its completed-cell stopped
quadratic sum measurable. -/
theorem aestronglyMeasurable_quadraticVariationBeforeStopApprox
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) (a : ℝ≥0) :
    AEStronglyMeasurable (quadraticVariationBeforeStopApprox X t n a) P := by
  unfold quadraticVariationBeforeStopApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        if uniformPartitionTime t n (i + 1) ≤ a then
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2
        else 0) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    by_cases hright : uniformPartitionTime t n (i + 1) ≤ a
    · simp only [hright, ↓reduceIte]
      exact ((hXmeas (uniformPartitionTime t n (i + 1))).sub
        (hXmeas (uniformPartitionTime t n i))).pow 2
    · simp only [hright, ↓reduceIte]
      exact aestronglyMeasurable_const
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

omit [MeasurableSpace W] in
/-- A completed coarse-block sum is exactly a fine-cell weighted quadratic
sum.  A fine cell is assigned to the unique coarse block containing its
right endpoint; using the right endpoint is what removes boundary cells. -/
theorem quadraticVariationBeforeStop_uniform_blocks_eq_weighted_cells
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (c : ℕ → W → ℝ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticVariationBeforeStopApprox X t n
          (uniformPartitionTime t k (j + 1)) omega -
        quadraticVariationBeforeStopApprox X t n
          (uniformPartitionTime t k j) omega)) =
      ∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0) *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) ^ 2 := by
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticVariationBeforeStopApprox
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
      simp only [hra, hrb, har, true_and, ↓reduceIte, sub_zero]
    · simp only [r, a, b] at hra hrb ⊢
      simp only [hra, hrb, and_false, ↓reduceIte, sub_self, zero_mul, mul_zero]

omit [MeasurableSpace W] in
/-- The half-open right-endpoint blocks of a positive uniform partition form
a partition of `(0,t]`, expressed as a real-valued indicator identity. -/
theorem uniformPartition_rightEndpoint_blocks_sum_one
    (t r : ℝ≥0) (k : ℕ) (hk : 0 < k) (hr0 : 0 < r) (hrt : r ≤ t) :
    (∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        (1 : ℝ)
      else 0) = 1 := by
  let F : ℕ → ℝ := fun j =>
    if r ≤ uniformPartitionTime t k j then 1 else 0
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  have hcell : ∀ j : ℕ,
      (if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        (1 : ℝ)
      else 0) = F (j + 1) - F j := by
    intro j
    dsimp only [F]
    by_cases hrj : r ≤ uniformPartitionTime t k j
    · have hrj1 := hrj.trans (hgrid j)
      have hnot := not_lt_of_ge hrj
      simp only [hrj, hrj1, hnot, false_and, ↓reduceIte, sub_self]
    · by_cases hrj1 : r ≤ uniformPartitionTime t k (j + 1)
      · have hjr := lt_of_not_ge hrj
        simp only [hrj, hrj1, hjr, true_and, ↓reduceIte, sub_zero]
      · simp only [hrj, hrj1, and_false, ↓reduceIte, sub_self]
  rw [Finset.sum_congr rfl (fun j _hj => hcell j)]
  rw [Finset.sum_range_sub]
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have htop : uniformPartitionTime t k k = t := by
    unfold uniformPartitionTime
    exact mul_div_cancel_right₀ t hk0
  have hzero : uniformPartitionTime t k 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  simp only [F, htop, hzero, hrt, if_true, not_le.mpr hr0, if_false,
    sub_zero]

omit [MeasurableSpace W] in
/-- If a scalar is close to every active coarse right-endpoint block value,
then it is close to their indicator sum.  The preceding partition identity
means no factor depending on the number of coarse blocks is lost. -/
theorem abs_sub_uniformPartition_rightEndpoint_step_sum_le
    (t r : ℝ≥0) (k : ℕ) (hk : 0 < k) (hr0 : 0 < r) (hrt : r ≤ t)
    (weight : ℝ) (c : ℕ → ℝ) (K : ℝ)
    (hclose : ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < r ∧
        r ≤ uniformPartitionTime t k (j + 1) →
      |weight - c j| ≤ K) :
    |weight - ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        c j
      else 0| ≤ K := by
  have hone := uniformPartition_rightEndpoint_blocks_sum_one
    t r k hk hr0 hrt
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
            (1 : ℝ)
          else 0 := by rw [hone]
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
            else 0 := congrArg (fun z => z - ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then c j else 0) hweightSum
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
  calc
    _ = |∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          weight - c j
        else 0| := by
      exact congrArg abs hdiff
    _ ≤ ∑ j ∈ Finset.range k,
        |if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          weight - c j
        else 0| := Finset.abs_sum_le_sum_abs _ _
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
      have hscaled := congrArg (fun x : ℝ => K * x) hone
      simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul,
        one_mul] using hscaled

omit [MeasurableSpace W] in
/-- If a fine right endpoint lies in a coarse right-endpoint block, then its
fine left endpoint is within one fine mesh plus one coarse mesh of the
coarse left endpoint. -/
theorem dist_uniformPartition_left_to_active_coarse_left_le
    (t : ℝ≥0) (n k i j : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hactive : uniformPartitionTime t k j <
        uniformPartitionTime t n (i + 1) ∧
      uniformPartitionTime t n (i + 1) ≤
        uniformPartitionTime t k (j + 1)) :
    dist (uniformPartitionTime t n i) (uniformPartitionTime t k j) ≤
      ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) +
        ((t / (k : ℝ≥0) : ℝ≥0) : ℝ) := by
  let s := uniformPartitionTime t n i
  let r := uniformPartitionTime t n (i + 1)
  let a := uniformPartitionTime t k j
  let b := uniformPartitionTime t k (j + 1)
  have hsa : dist r a ≤ dist b a := by
    have har : (a : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast hactive.1.le
    have hab : (a : ℝ) ≤ (b : ℝ) := by
      norm_cast
      dsimp only [a, b]
      unfold uniformPartitionTime
      gcongr
      omega
    have hrb : (r : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hactive.2
    rw [NNReal.dist_eq, NNReal.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr har),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact sub_le_sub_right hrb _
  calc
    dist s a ≤ dist s r + dist r a := dist_triangle _ _ _
    _ ≤ dist s r + dist b a := add_le_add le_rfl hsa
    _ = ((t / (n : ℝ≥0) : ℝ≥0) : ℝ) +
        ((t / (k : ℝ≥0) : ℝ≥0) : ℝ) := by
      rw [show dist s r = dist r s from dist_comm _ _,
        dist_uniformPartitionTime_succ_eq t hn i,
        dist_uniformPartitionTime_succ_eq t hk j]

omit [MeasurableSpace W] in
/-- Once the fine-cell weight is uniformly close to its right-endpoint
coarse-step freezing, the actual weighted quadratic sum is close to the
completed coarse-block sum.  The error is controlled by the unweighted
quadratic variation and has no separate boundary term. -/
theorem abs_weightedQuadraticVariation_sub_completedBlocks_le
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (weight : ℕ → W → ℝ) (c : ℕ → W → ℝ) (K : ℝ) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      |weight i omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0| ≤ K)
    :
    |(∑ i ∈ Finset.range n, weight i omega *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) ^ 2) -
      ∑ j ∈ Finset.range k, c j omega *
        (quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k j) omega)| ≤
      K * quadraticVariationApprox X t n omega := by
  rw [quadraticVariationBeforeStop_uniform_blocks_eq_weighted_cells]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ i ∈ Finset.range n,
        (weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range n,
        |(weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, K *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_sq]
      exact mul_le_mul_of_nonneg_right (hweight i hi) (sq_nonneg _)
    _ = K * quadraticVariationApprox X t n omega := by
      unfold quadraticVariationApprox
      rw [← Finset.mul_sum]

/-- Cells of a uniform partition whose left endpoint is at or before `a`
and whose right endpoint is strictly after `a`.  Monotonicity of the grid
implies that this finset contains at most one cell. -/
noncomputable def uniformPartitionCrossingCells
    (t : ℝ≥0) (n : ℕ) (a : ℝ≥0) : Finset ℕ :=
  (Finset.range n).filter fun i =>
    uniformPartitionTime t n i ≤ a ∧
      ¬uniformPartitionTime t n (i + 1) ≤ a

/-- A monotone uniform grid has at most one cell crossing a fixed time. -/
theorem card_uniformPartitionCrossingCells_le_one
    (t : ℝ≥0) (n : ℕ) (a : ℝ≥0) :
    (uniformPartitionCrossingCells t n a).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [uniformPartitionCrossingCells, Finset.mem_filter,
    Finset.mem_range] at hi hj
  have htime : ∀ {p q : ℕ}, p ≤ q →
      uniformPartitionTime t n p ≤ uniformPartitionTime t n q := by
    intro p q hpq
    unfold uniformPartitionTime
    gcongr
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hi.2.2 ((htime (Nat.succ_le_iff.mpr hij)).trans hj.2.1)
  · exact hj.2.2 ((htime (Nat.succ_le_iff.mpr hji)).trans hi.2.1)

/-- On a continuous path, the partial increment in the unique cell crossing
a fixed time tends uniformly to zero as the uniform mesh vanishes. -/
theorem continuousOn_uniformPartition_crossing_increments_tendsto
    (g : ℝ≥0 → ℝ) (t a : ℝ≥0) (ha : a ∈ Set.Icc 0 t)
    (hg : ContinuousOn g (Set.Icc 0 t)) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ uniformPartitionCrossingCells t (n + 1) a,
        |g a - g (uniformPartitionTime t (n + 1) i)| < delta := by
  have huc : UniformContinuousOn g (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  intro delta hdelta
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc delta hdelta
  have hdivNN : Filter.Tendsto
      (fun n : ℕ => t / ((n + 1 : ℕ) : ℝ≥0)) Filter.atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun n : ℕ => ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun n : ℕ => t / ((n + 1 : ℕ) : ℝ≥0))
      Filter.atTop (𝓝 (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv eta heta
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro i hi
  have hi' := hi
  simp only [uniformPartitionCrossingCells, Finset.mem_filter,
    Finset.mem_range] at hi'
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hile : i ≤ n + 1 := Nat.le_of_lt hi'.1
  have hleftMem := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hrightOrder :
      a ≤ uniformPartitionTime t (n + 1) (i + 1) :=
    le_of_not_ge hi'.2.2
  have hgridOrder :
      uniformPartitionTime t (n + 1) i ≤
        uniformPartitionTime t (n + 1) (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  have hdistLe :
      dist a (uniformPartitionTime t (n + 1) i) ≤
        dist (uniformPartitionTime t (n + 1) (i + 1))
          (uniformPartitionTime t (n + 1) i) := by
    rw [NNReal.dist_eq, NNReal.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hi'.2.1)),
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgridOrder))]
    exact sub_le_sub_right (by exact_mod_cast hrightOrder) _
  have hmesh :
      ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta := by
    have hnear := hN n hn
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  have hdist :
      dist a (uniformPartitionTime t (n + 1) i) < eta :=
    hdistLe.trans_lt ((dist_uniformPartitionTime_succ_eq t hnpos i).trans_lt hmesh)
  have hout := hmod a ha
    (uniformPartitionTime t (n + 1) i) hleftMem hdist
  simpa only [Real.dist_eq] using hout

/-- The sole possible partial-cell contribution when a deterministic stop
does not coincide with a partition point. -/
noncomputable def quadraticVariationCrossingStopApprox
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (a : ℝ≥0)
    (omega : W) : ℝ :=
  ∑ i ∈ uniformPartitionCrossingCells t n a,
    (X a omega - X (uniformPartitionTime t n i) omega) ^ 2

omit [MeasurableSpace W] in
/-- A stopped quadratic-variation sum is exactly the sum of its completed
cells and its (at most one) boundary-cell contribution. -/
theorem quadraticVariationApprox_stop_eq_before_add_crossing
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (a : ℝ≥0)
    (omega : W) :
    quadraticVariationApprox (fun s => X (min s a)) t n omega =
      quadraticVariationBeforeStopApprox X t n a omega +
        quadraticVariationCrossingStopApprox X t n a omega := by
  have htime : ∀ i : ℕ,
      uniformPartitionTime t n i ≤ uniformPartitionTime t n (i + 1) := by
    intro i
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticVariationApprox quadraticVariationBeforeStopApprox
    quadraticVariationCrossingStopApprox uniformPartitionCrossingCells
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hright : uniformPartitionTime t n (i + 1) ≤ a
  · have hleft : uniformPartitionTime t n i ≤ a := (htime i).trans hright
    simp only [hright, hleft, not_true_eq_false, and_false, ↓reduceIte,
      min_eq_left]
    ring
  · have haright : a ≤ uniformPartitionTime t n (i + 1) := le_of_not_ge hright
    by_cases hleft : uniformPartitionTime t n i ≤ a
    · simp only [hright, hleft, not_false_eq_true, and_self, ↓reduceIte,
        min_eq_left, min_eq_right haright, zero_add]
    · have haleft : a ≤ uniformPartitionTime t n i := le_of_not_ge hleft
      simp only [hright, hleft, false_and, ↓reduceIte, min_eq_right haright,
        min_eq_right haleft, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]

omit [MeasurableSpace W] in
/-- The boundary-cell term in the stopped-sum decomposition vanishes along
uniform partitions for every path continuous on the time interval. -/
theorem quadraticVariationCrossingStopApprox_tendsto_zero_of_continuousOn
    (X : ℝ≥0 → W → ℝ) (t a : ℝ≥0) (omega : W)
    (ha : a ∈ Set.Icc 0 t)
    (hcontinuous : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => quadraticVariationCrossingStopApprox X t (n + 1) a omega)
      Filter.atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun epsilon hepsilon => ?_
  let delta : ℝ := min (1 / 2 : ℝ) (epsilon / 2)
  have hdelta : 0 < delta := by
    exact lt_min (by norm_num) (half_pos hepsilon)
  have hdelta_le_one : delta ≤ 1 := by
    exact (min_le_left _ _).trans (by norm_num)
  have hdelta_lt_epsilon : delta < epsilon := by
    exact (min_le_right _ _).trans_lt (half_lt_self hepsilon)
  have hdelta_sq_lt_epsilon : delta ^ 2 < epsilon := by
    nlinarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (continuousOn_uniformPartition_crossing_increments_tendsto
      (fun s => X s omega) t a ha hcontinuous delta hdelta)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n hn
  let S := uniformPartitionCrossingCells t (n + 1) a
  have hcard : S.card ≤ 1 :=
    card_uniformPartitionCrossingCells_le_one t (n + 1) a
  have hnonneg :
      0 ≤ quadraticVariationCrossingStopApprox X t (n + 1) a omega := by
    unfold quadraticVariationCrossingStopApprox
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  rcases S.eq_empty_or_nonempty with hS | ⟨i, hi⟩
  · simp only [quadraticVariationCrossingStopApprox, S] at hS ⊢
    rw [hS, Finset.sum_empty]
    exact hepsilon
  · have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcard_eq : S.card = 1 := Nat.le_antisymm hcard hcard_pos
    obtain ⟨j, hS⟩ := Finset.card_eq_one.mp hcard_eq
    have hj : j ∈ uniformPartitionCrossingCells t (n + 1) a := by
      change j ∈ S
      rw [hS]
      simp only [Finset.mem_singleton]
    have hjsmall := hsmall j hj
    have hj_sq :
        (X a omega - X (uniformPartitionTime t (n + 1) j) omega) ^ 2 <
          delta ^ 2 := by
      have hsquare := (sq_lt_sq₀
        (abs_nonneg (X a omega -
          X (uniformPartitionTime t (n + 1) j) omega))
        (le_of_lt hdelta)).mpr hjsmall
      simpa only [sq_abs] using hsquare
    unfold quadraticVariationCrossingStopApprox
    change (∑ j ∈ S,
      (X a omega - X (uniformPartitionTime t (n + 1) j) omega) ^ 2) < epsilon
    rw [hS, Finset.sum_singleton]
    exact hj_sq.trans hdelta_sq_lt_epsilon

/-- Fixed-time measurability of a process makes the boundary-cell quadratic
increment measurable. -/
theorem aestronglyMeasurable_quadraticVariationCrossingStopApprox
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) (a : ℝ≥0) :
    AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox X t n a) P := by
  unfold quadraticVariationCrossingStopApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ uniformPartitionCrossingCells t n a, fun omega =>
        (X a omega - X (uniformPartitionTime t n i) omega) ^ 2) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    exact ((hXmeas a).sub
      (hXmeas (uniformPartitionTime t n i))).pow 2
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

/-- Boundary-cell quadratic increments are unchanged almost everywhere when
the process is replaced by any fixed-time modification. -/
theorem quadraticVariationCrossingStopApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (t : ℝ≥0) (n : ℕ) (a : ℝ≥0) :
    quadraticVariationCrossingStopApprox X t n a =ᵐ[P]
      quadraticVariationCrossingStopApprox Y t n a := by
  have hall : ∀ᵐ omega ∂P,
      ∀ i ∈ uniformPartitionCrossingCells t n a,
        X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega :=
    (uniformPartitionCrossingCells t n a).eventually_all.mpr
      fun i _hi => hXY (uniformPartitionTime t n i)
  filter_upwards [hXY a, hall] with omega haeq homega
  unfold quadraticVariationCrossingStopApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [haeq, homega i hi]

/-- A finite sum of sequences converging in measure may be multiplied by
fixed measurable random coefficients term by term. -/
theorem tendstoInMeasure_finset_sum_mul_fixed_real
    [IsFiniteMeasure P]
    {I : Type*} (S : Finset I)
    (u : I → ℕ → W → ℝ) (U c : I → W → ℝ)
    (hu : ∀ i ∈ S, TendstoInMeasure P (u i) Filter.atTop (U i))
    (humeas : ∀ i ∈ S, ∀ n, AEStronglyMeasurable (u i n) P)
    (hcmeas : ∀ i ∈ S, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ S, c i omega * u i n omega)
      Filter.atTop (fun omega => ∑ i ∈ S, c i omega * U i omega) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hzero : TendstoInMeasure P
          (fun _ : ℕ => fun _ : W => (0 : ℝ)) Filter.atTop
          (fun _ : W => 0) :=
        tendstoInMeasure_of_tendsto_ae
          (fun _ => aestronglyMeasurable_const)
          (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
      simpa only [Finset.sum_empty] using hzero
  | @insert i S hi hind =>
      have hhead := (hu i (Finset.mem_insert_self i S)).mul_fixed_real
        (fun n => humeas i (Finset.mem_insert_self i S) n)
        (hcmeas i (Finset.mem_insert_self i S))
      have htail := hind
        (fun j hj => hu j (Finset.mem_insert_of_mem hj))
        (fun j hj n => humeas j (Finset.mem_insert_of_mem hj) n)
        (fun j hj => hcmeas j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hhead.add_real_noMeas htail

end StochasticCalculus
