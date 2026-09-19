/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.WeightedBracketRiemann
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Doléans–Dade stochastic exponential

This file starts the process-level layer above the fixed-time Itô formula.  It
defines continuous local martingales using Mathlib's generic `Locally`
predicate, defines the real stochastic exponential from a process and a
chosen bracket, and records the analytic cancellation used by its Itô proof.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- A real process is a local martingale when its indicated stopped processes
are martingales along a Mathlib localizing sequence. -/
def IsLocalMartingale
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) : Prop :=
  Locally (fun N => Martingale N 𝓕 P) 𝓕 M P

/-- A continuous local martingale has a local-martingale localization and
almost-everywhere continuous sample paths. -/
def IsContinuousLocalMartingale
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) : Prop :=
  IsLocalMartingale M 𝓕 P ∧
    ∀ᵐ omega ∂P, Continuous (fun t => M t omega)

/-- A process-valued quadratic variation: at every fixed time, the uniform
partition squared-increment sums converge in probability to the selected
bracket value. -/
def HasQuadraticVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ t, HasQuadraticVariationInProbabilityAt M P t (bracket t)

/-- A process-level quadratic-variation contract robust under truncating a
fine uniform grid at any earlier deterministic time.  This is strictly the
interface needed by two-scale weighted-bracket arguments; fixed-time uniform
partitions alone do not provide it. -/
def HasQuadraticVariationBeforeStopProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ T a, TendstoInMeasure P
    (fun n ↦ quadraticVariationBeforeStopApprox M T (n + 1) a)
    Filter.atTop (bracket (min T a))

/-- Completed-cell covariation before a deterministic cutoff on a fixed
uniform horizon. -/
noncomputable def quadraticCovariationBeforeStopApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (a : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    if uniformPartitionTime T n (i + 1) ≤ a then
      (X (uniformPartitionTime T n (i + 1)) omega -
        X (uniformPartitionTime T n i) omega) *
      (Y (uniformPartitionTime T n (i + 1)) omega -
        Y (uniformPartitionTime T n i) omega)
    else 0

/-- Robust process covariation, tested on completed cells before every
deterministic cutoff and horizon. -/
def HasCrossVariationBeforeStopProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (X Y covariation : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ T a, TendstoInMeasure P
    (fun n ↦ quadraticCovariationBeforeStopApprox X Y T (n + 1) a)
    Filter.atTop (covariation (min T a))

/-- Polarization on completed cells before a cutoff. -/
theorem two_mul_quadraticCovariationBeforeStopApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (a : ℝ≥0) (omega : W) :
    2 * quadraticCovariationBeforeStopApprox X Y T n a omega =
      quadraticVariationBeforeStopApprox (X + Y) T n a omega -
        quadraticVariationBeforeStopApprox X T n a omega -
          quadraticVariationBeforeStopApprox Y T n a omega := by
  unfold quadraticCovariationBeforeStopApprox
    quadraticVariationBeforeStopApprox
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hcell : uniformPartitionTime T n (i + 1) ≤ a
  · simp only [hcell, ↓reduceIte, Pi.add_apply]
    ring
  · simp only [hcell, ↓reduceIte, mul_zero, sub_zero]

/-- Robust brackets and robust covariation determine the robust bracket of
the sum process. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.add_of_cross
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y QX QY C : ℝ≥0 → W → ℝ}
    (hX : HasQuadraticVariationBeforeStopProcessInProbability X QX P)
    (hY : HasQuadraticVariationBeforeStopProcessInProbability Y QY P)
    (hC : HasCrossVariationBeforeStopProcessInProbability X Y C P) :
    HasQuadraticVariationBeforeStopProcessInProbability (X + Y)
      (fun t omega ↦ QX t omega + QY t omega + 2 * C t omega) P := by
  intro T a
  have hlimit := ((hX T a).add_real_noMeas (hY T a)).add_real_noMeas
    ((hC T a).const_mul_real_noMeas 2)
  apply hlimit.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    have hpolar := two_mul_quadraticCovariationBeforeStopApprox
      X Y T (n + 1) a omega
    linarith

/-- Robust before-stop quadratic variation scales by the square of a
deterministic scalar. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P)
    (c : ℝ) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun t omega => c * M t omega)
      (fun t omega => c ^ 2 * bracket t omega) P := by
  intro T a
  have hscaled := (h T a).const_mul_real_noMeas (c ^ 2)
  apply hscaled.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by
      change c ^ 2 * quadraticVariationBeforeStopApprox M T (n + 1) a omega =
        quadraticVariationBeforeStopApprox
          (fun t omega => c * M t omega) T (n + 1) a omega
      unfold quadraticVariationBeforeStopApprox
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases htime : uniformPartitionTime T (n + 1) (i + 1) ≤ a
      · simp only [htime, ↓reduceIte]
        ring
      · simp only [htime, ↓reduceIte, mul_zero]
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Standard stopped-process formulation of robust process quadratic
variation: stopping at any deterministic time stops the selected bracket at
the same time. -/
def HasStoppedQuadraticVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ T a, TendstoInMeasure P
    (fun n ↦ quadraticVariationApprox (fun s ↦ M (min s a)) T (n + 1))
    Filter.atTop (bracket (min T a))

/-- Before-stop quadratic variation contains the ordinary fixed-time
uniform-partition quadratic-variation statement as its terminal case. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.toProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P) :
    HasQuadraticVariationProcessInProbability M bracket P := by
  intro t
  have hterminal := h t t
  simp only [min_self] at hterminal
  apply hterminal.congr_left
  intro n
  filter_upwards with omega
  unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  simp only [uniformPartitionTime_mem_Icc_of_le t
    (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]

/-- Truncating a before-stop boundary to the deterministic horizon does not
change the approximant. -/
theorem quadraticVariationBeforeStopApprox_min_horizon
    {W : Type*} (X : ℝ≥0 → W → ℝ) (T b : ℝ≥0)
    (n : ℕ) (omega : W) :
    quadraticVariationBeforeStopApprox X T n b omega =
      quadraticVariationBeforeStopApprox X T n (min T b) omega := by
  unfold quadraticVariationBeforeStopApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hn : 0 < n := (Nat.zero_lt_succ i).trans_le hi1
  have hendT : uniformPartitionTime T n (i + 1) ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T hn hi1).2
  have hiff : uniformPartitionTime T n (i + 1) ≤ b ↔
      uniformPartitionTime T n (i + 1) ≤ min T b := by
    constructor
    · exact fun hb ↦ le_min hendT hb
    · exact fun hd ↦ hd.trans (min_le_right T b)
  by_cases hb : uniformPartitionTime T n (i + 1) ≤ b
  · simp only [hb, hiff.mp hb, ↓reduceIte]
  · have hd : ¬ uniformPartitionTime T n (i + 1) ≤ min T b :=
      fun hd ↦ hb (hiff.mpr hd)
    simp only [hb, hd, ↓reduceIte]

/-- Stopping beyond a deterministic horizon is identical, on that horizon's
uniform grid, to stopping at the minimum of the two times. -/
theorem quadraticVariationApprox_stop_eq_min_horizon
    {W : Type*} (X : ℝ≥0 → W → ℝ) (T a : ℝ≥0)
    (n : ℕ) (omega : W) :
    quadraticVariationApprox (fun s ↦ X (min s a)) T n omega =
      quadraticVariationApprox (fun s ↦ X (min s (min T a)))
        T n omega := by
  unfold quadraticVariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
  have hn : 0 < n := (Nat.zero_lt_succ i).trans_le hi1
  have htime (j : ℕ) (hj : j ≤ n) :
      min (uniformPartitionTime T n j) a =
        min (uniformPartitionTime T n j) (min T a) := by
    have hjT := (uniformPartitionTime_mem_Icc_of_le T hn hj).2
    calc
      min (uniformPartitionTime T n j) a =
          min (min (uniformPartitionTime T n j) T) a := by
            rw [min_eq_left hjT]
      _ = min (uniformPartitionTime T n j) (min T a) := min_assoc _ _ _
  change (X (min (uniformPartitionTime T n (i + 1)) a) omega -
      X (min (uniformPartitionTime T n i) a) omega) ^ 2 =
    (X (min (uniformPartitionTime T n (i + 1)) (min T a)) omega -
      X (min (uniformPartitionTime T n i) (min T a)) omega) ^ 2
  rw [htime (i + 1) hi1, htime i hi0]

/-- The expected quadratic mass in the single cell crossing a deterministic
time is at most the uniform mesh width for a pre-Brownian process. -/
theorem integral_quadraticVariationCrossingStopApprox_preBrownianReal_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (T a : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ omega, quadraticVariationCrossingStopApprox B T n a omega ∂P ≤
      ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
  let S := uniformPartitionCrossingCells T n a
  have hint (i : ℕ) : Integrable
      (fun omega => (B a omega - B (uniformPartitionTime T n i) omega) ^ 2) P := by
    change Integrable (fun omega =>
      ((B a - B (uniformPartitionTime T n i)) omega) ^ 2) P
    exact integrable_pow_two_of_hasLaw_gaussianReal _ (hB.hasLaw_sub _ _)
  unfold quadraticVariationCrossingStopApprox
  rw [integral_finsetSum S (fun i _hi => hint i)]
  calc
    ∑ i ∈ S, ∫ omega,
        (B a omega - B (uniformPartitionTime T n i) omega) ^ 2 ∂P =
        ∑ i ∈ S,
          (nndist (a : ℝ) (uniformPartitionTime T n i : ℝ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      change (∫ omega,
        ((B a - B (uniformPartitionTime T n i)) omega) ^ 2 ∂P) = _
      exact integral_pow_two_of_hasLaw_gaussianReal _ (hB.hasLaw_sub _ _)
    _ ≤ ∑ _i ∈ S, ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := hi
      simp only [S, uniformPartitionCrossingCells, Finset.mem_filter,
        Finset.mem_range] at hi'
      have hile : i ≤ n := Nat.le_of_lt hi'.1
      have hright : a ≤ uniformPartitionTime T n (i + 1) :=
        le_of_not_ge hi'.2.2
      have hgrid : uniformPartitionTime T n i ≤
          uniformPartitionTime T n (i + 1) := by
        unfold uniformPartitionTime
        gcongr
        omega
      have hdist : dist a (uniformPartitionTime T n i) ≤
          dist (uniformPartitionTime T n (i + 1))
            (uniformPartitionTime T n i) := by
        rw [NNReal.dist_eq, NNReal.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hi'.2.1)),
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgrid))]
        exact sub_le_sub_right (by exact_mod_cast hright) _
      exact hdist.trans_eq (dist_uniformPartitionTime_succ_eq T hn i)
    _ ≤ ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((S.card : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast card_uniformPartitionCrossingCells_le_one T n a
      nlinarith [NNReal.coe_nonneg (T / (n : ℝ≥0))]

/-- The boundary-cell quadratic mass of a pre-Brownian process vanishes in
probability.  This replaces the usual path-continuity argument by the exact
Gaussian second moment of the increment. -/
theorem quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (T a : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox B T (n + 1) a)
      Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hbound : Filter.Tendsto
      (fun n : ℕ => (((T / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) / epsilon))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto
        (fun n : ℕ => ((T / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
        Filter.atTop (nhds 0) := by
      have hnn : Filter.Tendsto
          (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ≥0))
          Filter.atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat T)
      change Filter.Tendsto
        (NNReal.toReal ∘ fun n : ℕ => T / ((n + 1 : ℕ) : ℝ≥0))
        Filter.atTop (nhds 0)
      simpa only [NNReal.coe_zero] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hnn
    simpa only [zero_div] using hbase.div_const epsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hbound) delta hdelta
  refine ⟨N, fun n hn => ?_⟩
  have hint : Integrable
      (quadraticVariationCrossingStopApprox B T (n + 1) a) P := by
    unfold quadraticVariationCrossingStopApprox
    apply integrable_finsetSum
    intro i _hi
    change Integrable (fun omega =>
      ((B a - B (uniformPartitionTime T (n + 1) i)) omega) ^ 2) P
    exact integrable_pow_two_of_hasLaw_gaussianReal _ (hB.hasLaw_sub _ _)
  have hmarkov : epsilon * P.real {omega |
      epsilon ≤ quadraticVariationCrossingStopApprox B T (n + 1) a omega} ≤
      ∫ omega, quadraticVariationCrossingStopApprox B T (n + 1) a omega ∂P := by
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun omega => by
        unfold quadraticVariationCrossingStopApprox
        exact Finset.sum_nonneg fun i _hi => sq_nonneg _) hint epsilon
  have hmeasure : P.real {omega |
      epsilon ≤ quadraticVariationCrossingStopApprox B T (n + 1) a omega} ≤
      ((T / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) / epsilon := by
    apply (le_div_iff₀ hepsilon).2
    rw [mul_comm]
    exact hmarkov.trans
      (integral_quadraticVariationCrossingStopApprox_preBrownianReal_le
        hB T a (Nat.zero_lt_succ n))
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) hepsilon.le)] at hsmall
  change dist (P.real {omega | epsilon ≤
    ‖quadraticVariationCrossingStopApprox B T (n + 1) a omega - 0‖}) 0 < delta
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hnonneg (omega : W) :
      0 ≤ quadraticVariationCrossingStopApprox B T (n + 1) a omega := by
    unfold quadraticVariationCrossingStopApprox
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hset : {omega | epsilon ≤
      ‖quadraticVariationCrossingStopApprox B T (n + 1) a omega - 0‖} =
      {omega | epsilon ≤
        quadraticVariationCrossingStopApprox B T (n + 1) a omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg omega)]
  rw [hset]
  exact hmeasure.trans_lt hsmall

/-- Every pre-Brownian version has the robust completed-cell quadratic
variation contract.  The possible boundary cell is controlled in probability
by its Gaussian variance, so no path regularity of the chosen version is
needed. -/
theorem hasQuadraticVariationBeforeStop_preBrownianReal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) :
    HasQuadraticVariationBeforeStopProcessInProbability B
      (fun t (_omega : W) => (t : ℝ)) P := by
  intro T a
  let d : ℝ≥0 := min T a
  have hdT : d ≤ T := min_le_left T a
  have hstop : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s => B (min s d))
        T (n + 1)) Filter.atTop (fun _ => (d : ℝ)) := by
    have hraw :=
      quadraticVariation_stopped_preBrownianReal_inProbability hB d T
    change TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s => B (min s d))
        T (n + 1)) Filter.atTop (fun _ => ((min T d : ℝ≥0) : ℝ)) at hraw
    simpa only [min_eq_right hdT] using hraw
  have hcross :=
    quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
      hB T d
  have hsub := hstop.sub_real_noMeas hcross
  have hd : TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox B T (n + 1) d)
      Filter.atTop (fun _ => (d : ℝ)) := by
    simpa only [sub_zero] using hsub.congr_left (fun n =>
      Filter.Eventually.of_forall fun omega => by
        rw [quadraticVariationApprox_stop_eq_before_add_crossing]
        ring)
  change TendstoInMeasure P
    (fun n => quadraticVariationBeforeStopApprox B T (n + 1) a)
    Filter.atTop (fun _ => (d : ℝ))
  apply hd.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (quadraticVariationBeforeStopApprox_min_horizon
      B T a (n + 1) omega).symm

/-- The crossing-cell quadratic mass of a sum is bounded by twice the two
component masses. -/
theorem quadraticVariationCrossingStopApprox_add_le
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (a : ℝ≥0) (omega : W) :
    quadraticVariationCrossingStopApprox (X + Y) T n a omega ≤
      2 * quadraticVariationCrossingStopApprox X T n a omega +
        2 * quadraticVariationCrossingStopApprox Y T n a omega := by
  unfold quadraticVariationCrossingStopApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg
    ((X a omega - X (uniformPartitionTime T n i) omega) -
      (Y a omega - Y (uniformPartitionTime T n i) omega))]

/-- Vanishing crossing-cell mass is stable under addition. -/
theorem tendstoInMeasure_quadraticVariationCrossingStopApprox_add_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y : ℝ≥0 → W → ℝ}
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T a : ℝ≥0)
    (hX : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X T (n + 1) a)
      Filter.atTop (fun _ => 0))
    (hY : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox Y T (n + 1) a)
      Filter.atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox (X + Y) T (n + 1) a)
      Filter.atTop (fun _ => 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox (X + Y) T (n + 1) a) P :=
    fun n => aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hXmeas s).add (hYmeas s)) T (n + 1) a
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ms, hms, hXae⟩ :=
    (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hYsub : TendstoInMeasure P
      (fun i => quadraticVariationCrossingStopApprox Y T
        (ns (ms i) + 1) a) Filter.atTop (fun _ => 0) := by
    change TendstoInMeasure P
      ((fun n => quadraticVariationCrossingStopApprox Y T (n + 1) a) ∘
        (ns ∘ ms)) Filter.atTop (fun _ => 0)
    exact hY.comp (hns.comp hms).tendsto_atTop
  obtain ⟨ls, hls, hYae⟩ := hYsub.exists_seq_tendsto_ae
  refine ⟨ms ∘ ls, hms.comp hls, ?_⟩
  filter_upwards [hXae, hYae] with omega hXomega hYomega
  have hXomega' := hXomega.comp hls.tendsto_atTop
  have hupper : Filter.Tendsto
      (fun i => 2 * quadraticVariationCrossingStopApprox X T
          (ns (ms (ls i)) + 1) a omega +
        2 * quadraticVariationCrossingStopApprox Y T
          (ns (ms (ls i)) + 1) a omega)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero, add_zero] using
      (hXomega'.const_mul 2).add (hYomega.const_mul 2)
  apply squeeze_zero
  · intro i
    unfold quadraticVariationCrossingStopApprox
    exact Finset.sum_nonneg fun j _hj => sq_nonneg _
  · intro i
    exact quadraticVariationCrossingStopApprox_add_le
      X Y T (ns (ms (ls i)) + 1) a omega
  · exact hupper

/-- Completed cells plus the vanishing crossing cell identify the quadratic
variation of a process stopped before the deterministic horizon. -/
theorem
    HasQuadraticVariationBeforeStopProcessInProbability.quadraticVariation_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (T a : ℝ≥0) (haT : a ≤ T) :
    TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox (fun s ↦ M (min s a))
        T (n + 1)) Filter.atTop (bracket a) := by
  have hMself : IsContinuousProcessModification M M P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hMcont⟩
  have hcross := hMself.quadraticVariationCrossingStopApprox_tendstoInMeasure
    hMmeas T a ⟨bot_le, haT⟩
  have hsum := (hbefore T a).add_real_noMeas hcross
  apply hsum.congr
  · intro n
    filter_upwards with omega
    rw [quadraticVariationApprox_stop_eq_before_add_crossing]
  · filter_upwards with omega
    simp only [min_eq_right haT, add_zero]

/-- Stopped-process quadratic variation implies the completed-cell
before-stop contract whenever the single crossing-cell contribution is known
to vanish.  This is the path-regularity-free core of `toBeforeStop`. -/
theorem HasStoppedQuadraticVariationProcessInProbability.toBeforeStop_of_crossing
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket : ℝ≥0 → W → ℝ}
    (hstopped : HasStoppedQuadraticVariationProcessInProbability M bracket P)
    (hcrossing : ∀ T a, a ≤ T → TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox M T (n + 1) a)
      Filter.atTop (fun _ => 0)) :
    HasQuadraticVariationBeforeStopProcessInProbability M bracket P := by
  intro T a
  let d : ℝ≥0 := min T a
  have hdT : d ≤ T := min_le_left T a
  have hstop : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s => M (min s d))
        T (n + 1)) Filter.atTop (bracket d) := by
    simpa only [d, min_eq_right hdT] using hstopped T d
  have hsub := hstop.sub_real_noMeas (hcrossing T d hdT)
  have hd : TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox M T (n + 1) d)
      Filter.atTop (bracket d) := by
    simpa only [sub_zero] using hsub.congr_left (fun n =>
      Filter.Eventually.of_forall fun omega => by
        rw [quadraticVariationApprox_stop_eq_before_add_crossing]
        ring)
  change TendstoInMeasure P
    (fun n => quadraticVariationBeforeStopApprox M T (n + 1) a)
    Filter.atTop (bracket d)
  apply hd.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega =>
    (quadraticVariationBeforeStopApprox_min_horizon
      M T a (n + 1) omega).symm

/-- Stopped-process quadratic variation implies the completed-cell
before-stop contract when paths are continuous. -/
theorem HasStoppedQuadraticVariationProcessInProbability.toBeforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hstopped : HasStoppedQuadraticVariationProcessInProbability M bracket P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega)) :
    HasQuadraticVariationBeforeStopProcessInProbability M bracket P := by
  have hself : IsContinuousProcessModification M M P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hMcont⟩
  intro T a
  let d : ℝ≥0 := min T a
  have hdT : d ≤ T := min_le_left T a
  have hstop : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox (fun s ↦ M (min s d))
        T (n + 1)) Filter.atTop (bracket d) := by
    simpa only [d, min_eq_right hdT] using hstopped T d
  have hd := hself.quadraticVariationBeforeStopApprox_tendstoInMeasure
    hMmeas T d ⟨bot_le, hdT⟩ (bracket d) hstop
  change TendstoInMeasure P
    (fun n ↦ quadraticVariationBeforeStopApprox M T (n + 1) a)
    Filter.atTop (bracket d)
  apply hd.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦
    (quadraticVariationBeforeStopApprox_min_horizon
      M T a (n + 1) omega).symm

/-- Conversely, completed-cell before-stop quadratic variation and path
continuity recover quadratic variation for every deterministic stopped
process. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.toStopped
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega)) :
    HasStoppedQuadraticVariationProcessInProbability M bracket P := by
  intro T a
  let d : ℝ≥0 := min T a
  have hdT : d ≤ T := min_le_left T a
  have hd := hbefore.quadraticVariation_stop hMmeas hMcont T d hdT
  change TendstoInMeasure P
    (fun n ↦ quadraticVariationApprox (fun s ↦ M (min s a))
      T (n + 1)) Filter.atTop (bracket d)
  apply hd.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦
    (quadraticVariationApprox_stop_eq_min_horizon
      M T a (n + 1) omega).symm

/-- Fixed-horizon form of deterministic-stop stability for the before-stop
quadratic-variation contract. -/
theorem tendstoInMeasure_quadraticVariationBeforeStop_stopped
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (a T b : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ quadraticVariationBeforeStopApprox
        (fun s omega ↦ M (min s a) omega) T (n + 1) b)
      Filter.atTop (bracket (min (min T b) a)) := by
  have hXmeas : ∀ s, AEStronglyMeasurable
      ((fun r omega ↦ M (min r a) omega) s) P :=
    fun s ↦ hMmeas (min s a)
  have hXcont : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ M (min s a) omega) := by
    filter_upwards [hMcont] with omega homega
    exact homega.comp (continuous_id.min continuous_const)
  have hXself : IsContinuousProcessModification
      (fun s omega ↦ M (min s a) omega)
      (fun s omega ↦ M (min s a) omega) P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hXcont⟩
  let d : ℝ≥0 := min T b
  let c : ℝ≥0 := min d a
  have hdT : d ≤ T := min_le_left T b
  have hcT : c ≤ T := (min_le_left d a).trans hdT
  have hstoppedM : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox (fun s ↦ M (min s c))
        T (n + 1)) Filter.atTop (bracket c) :=
    hbefore.quadraticVariation_stop hMmeas hMcont T c hcT
  have hstopX : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox
        (fun s omega ↦ M (min (min s d) a) omega)
        T (n + 1)) Filter.atTop (bracket c) := by
    apply hstoppedM.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      congr 1
      funext s
      simp only [c, min_assoc]
  have hd := hXself.quadraticVariationBeforeStopApprox_tendstoInMeasure
    hXmeas T d ⟨bot_le, hdT⟩ (bracket c) hstopX
  have hsource : ∀ n, quadraticVariationBeforeStopApprox
      (fun s omega ↦ M (min s a) omega) T (n + 1) b =ᵐ[P]
      quadraticVariationBeforeStopApprox
        (fun s omega ↦ M (min s a) omega) T (n + 1) d := fun n ↦
    Filter.Eventually.of_forall fun omega ↦ by
      exact quadraticVariationBeforeStopApprox_min_horizon
        (fun s omega ↦ M (min s a) omega) T b (n + 1) omega
  change TendstoInMeasure P
    (fun n ↦ quadraticVariationBeforeStopApprox
      (fun s omega ↦ M (min s a) omega) T (n + 1) b)
    Filter.atTop (bracket c)
  exact hd.congr_left fun n ↦ (hsource n).symm

/-- The before-stop quadratic-variation contract is stable under stopping at
a deterministic time.  Continuity removes the single grid cell crossing the
new stopping boundary. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (a : ℝ≥0) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun s omega ↦ M (min s a) omega)
      (fun s omega ↦ bracket (min s a) omega) P := by
  intro T b
  exact tendstoInMeasure_quadraticVariationBeforeStop_stopped
    hbefore hMmeas hMcont a T b

/-- A continuous quadratic-variation process has the fixed-time bracket
limits, almost-everywhere continuous nondecreasing paths, and starts at zero. -/
def IsContinuousQuadraticVariationProcess
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  HasQuadraticVariationProcessInProbability M bracket P ∧
    (∀ᵐ omega ∂P,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega)) ∧
    bracket 0 =ᵐ[P] fun _ => 0

/-- Process-valued quadratic variation scales by the square of a
deterministic scalar. -/
theorem HasQuadraticVariationProcessInProbability.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbracket : HasQuadraticVariationProcessInProbability M bracket P)
    (hMmeas : ∀ t, AEStronglyMeasurable (M t) P) (c : ℝ) :
    HasQuadraticVariationProcessInProbability
      (fun t omega => c * M t omega)
      (fun t omega => c ^ 2 * bracket t omega) P := by
  intro t
  exact (hbracket t).const_mul hMmeas c

/-- Continuous quadratic-variation processes scale together with their
underlying process, preserving continuity, monotonicity, and the zero start. -/
theorem IsContinuousQuadraticVariationProcess.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hMmeas : ∀ t, AEStronglyMeasurable (M t) P) (c : ℝ) :
    IsContinuousQuadraticVariationProcess
      (fun t omega => c * M t omega)
      (fun t omega => c ^ 2 * bracket t omega) P := by
  refine ⟨hbracket.1.const_mul hMmeas c, ?_, ?_⟩
  · filter_upwards [hbracket.2.1] with omega homega
    refine ⟨continuous_const.mul homega.1, ?_⟩
    intro a b hab
    exact mul_le_mul_of_nonneg_left (homega.2 hab) (sq_nonneg c)
  · filter_upwards [hbracket.2.2] with omega hzero
    simp only [hzero, mul_zero]

/-- A process-valued quadratic variation is unique up to fixed-time almost
everywhere equality. -/
theorem HasQuadraticVariationProcessInProbability.ae_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket₁ bracket₂ : ℝ≥0 → W → ℝ}
    (h₁ : HasQuadraticVariationProcessInProbability M bracket₁ P)
    (h₂ : HasQuadraticVariationProcessInProbability M bracket₂ P) (t : ℝ≥0) :
    bracket₁ t =ᵐ[P] bracket₂ t :=
  tendstoInMeasure_ae_unique (h₁ t) (h₂ t)

/-- Every continuous martingale is a continuous local martingale, using the
constant-top localizing sequence. -/
theorem isContinuousLocalMartingale_of_martingale
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W}
    (hM : Martingale M 𝓕 P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun t => M t omega)) :
    IsContinuousLocalMartingale M 𝓕 P :=
  ⟨Locally.of_prop hM, hcontinuous⟩

/-- Local martingales are closed under multiplication by a deterministic
real constant, reusing the same localizing sequence. -/
theorem IsLocalMartingale.const_mul
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} (hM : IsLocalMartingale M 𝓕 P) (c : ℝ) :
    IsLocalMartingale (fun t omega => c * M t omega) 𝓕 P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun n => ?_⟩
  have hindicator :
      (fun i => {omega | ⊥ < tau n omega}.indicator
        (fun omega => c * M i omega)) =
      c • (fun i => {omega | ⊥ < tau n omega}.indicator (M i)) := by
    ext i omega
    by_cases homega : omega ∈ {omega | ⊥ < tau n omega}
    · simp only [Set.indicator_of_mem homega, Pi.smul_apply, smul_eq_mul]
    · simp only [Set.indicator_of_notMem homega, Pi.smul_apply, smul_zero]
  rw [hindicator, stoppedProcess_const_smul]
  exact (hstopped n).smul c

/-- Adding a deterministic constant preserves a local martingale.  The same
localizing sequence works: on the exceptional event where a localizer is
zero, Mathlib's `Locally` convention kills both summands, while on its
complement the constant is already measurable at time zero. -/
theorem IsLocalMartingale.const_add
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} [IsFiniteMeasure P]
    (hM : IsLocalMartingale M 𝓕 P) (c : ℝ) :
    IsLocalMartingale (fun t omega => c + M t omega) 𝓕 P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun n => ?_⟩
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau n omega}
  have hA : MeasurableSet[𝓕 0] A := by
    change MeasurableSet[𝓕 0]
      {omega | (⊥ : WithTop ℝ≥0) < tau n omega}
    rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact (htau.isStoppingTime n).measurableSet_gt 0
  have hconst_meas : StronglyMeasurable[𝓕 0]
      (A.indicator (fun _ => c)) :=
    stronglyMeasurable_const.indicator hA
  have hconst_int : Integrable (A.indicator (fun _ => c)) P :=
    (integrable_const c).indicator (𝓕.le 0 A hA)
  have hconst : Martingale (fun _ => A.indicator (fun _ => c)) 𝓕 P :=
    martingale_const_fun 𝓕 P hconst_meas hconst_int
  have hindicator :
      (fun i => A.indicator (fun omega => c + M i omega)) =
        (fun _ => A.indicator (fun _ => c)) +
          fun i => A.indicator (M i) := by
    ext i omega
    by_cases homega : omega ∈ A
    · simp only [Set.indicator_of_mem homega, Pi.add_apply]
    · simp only [Set.indicator_of_notMem homega, Pi.add_apply, add_zero]
  change Martingale
    (stoppedProcess
      (fun i => A.indicator (fun omega => c + M i omega)) (tau n)) 𝓕 P
  rw [hindicator, stoppedProcess_add, stoppedProcess_const]
  exact hconst.add (hstopped n)

/-- Adding a deterministic constant on the right preserves a local
martingale. -/
theorem IsLocalMartingale.add_const
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} [IsFiniteMeasure P]
    (hM : IsLocalMartingale M 𝓕 P) (c : ℝ) :
    IsLocalMartingale (fun t omega => M t omega + c) 𝓕 P := by
  simpa only [add_comm] using hM.const_add c

/-- Continuous local martingales are closed under deterministic scalar
multiplication. -/
theorem IsContinuousLocalMartingale.const_mul
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} (hM : IsContinuousLocalMartingale M 𝓕 P) (c : ℝ) :
    IsContinuousLocalMartingale (fun t omega => c * M t omega) 𝓕 P := by
  refine ⟨hM.1.const_mul c, ?_⟩
  filter_upwards [hM.2] with omega hcontinuous
  exact continuous_const.mul hcontinuous

/-- The zero process is a local martingale. -/
theorem isLocalMartingale_zero
    {W : Type*} [MeasurableSpace W]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :
    IsLocalMartingale (fun _ _ => (0 : ℝ)) 𝓕 P :=
  Locally.of_prop (martingale_zero ℝ 𝓕 P)

/-- The zero process is a continuous local martingale. -/
theorem isContinuousLocalMartingale_zero
    {W : Type*} [MeasurableSpace W]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :
    IsContinuousLocalMartingale (fun _ _ => (0 : ℝ)) 𝓕 P :=
  ⟨isLocalMartingale_zero 𝓕 P,
    Filter.Eventually.of_forall fun _ => continuous_const⟩

/-- Two local-martingale candidates localized by the same sequence can be
added. This is the common-sequence core needed before any use of a theorem
that combines distinct localizing sequences. -/
theorem isLocalMartingale_add_of_common_localizingSequence
    {W : Type*} [MeasurableSpace W]
    {M N : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} (tau : ℕ → W → WithTop ℝ≥0)
    (htau : IsLocalizingSequence 𝓕 tau P)
    (hM : ∀ n, Martingale
      (stoppedProcess
        (fun i => {omega | ⊥ < tau n omega}.indicator (M i)) (tau n)) 𝓕 P)
    (hN : ∀ n, Martingale
      (stoppedProcess
        (fun i => {omega | ⊥ < tau n omega}.indicator (N i)) (tau n)) 𝓕 P) :
    IsLocalMartingale (fun t omega => M t omega + N t omega) 𝓕 P := by
  refine ⟨tau, htau, fun n => ?_⟩
  have hindicator :
      (fun i => {omega | ⊥ < tau n omega}.indicator
        (fun omega => M i omega + N i omega)) =
      (fun i => {omega | ⊥ < tau n omega}.indicator (M i)) +
        fun i => {omega | ⊥ < tau n omega}.indicator (N i) := by
    ext i omega
    by_cases homega : omega ∈ {omega | ⊥ < tau n omega}
    · simp only [Set.indicator_of_mem homega, Pi.add_apply]
    · simp only [Set.indicator_of_notMem homega, Pi.add_apply, add_zero]
  rw [hindicator, stoppedProcess_add]
  exact (hM n).add (hN n)

/-- If continuous-time martingales are stable under stopping for the chosen
filtration, two local martingales can be added even when their original
localizing sequences differ.  The explicit stability premise isolates the
continuous-time optional-stopping interface not currently supplied by
Mathlib. -/
theorem IsLocalMartingale.add_of_isStable_martingale
    {W : Type*} [MeasurableSpace W]
    {M N : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W}
    (hstable : IsStable 𝓕
      (fun X : ℝ≥0 → W → ℝ => Martingale X 𝓕 P))
    (hM : IsLocalMartingale M 𝓕 P) (hN : IsLocalMartingale N 𝓕 P) :
    IsLocalMartingale (fun t omega => M t omega + N t omega) 𝓕 P := by
  let tau := hM.localSeq
  let sigma := hN.localSeq
  have htau : IsLocalizingSequence 𝓕 tau P :=
    hM.isLocalizingSequence_localSeq
  have hsigma : IsLocalizingSequence 𝓕 sigma P :=
    hN.isLocalizingSequence_localSeq
  refine ⟨tau ⊓ sigma, htau.min hsigma, fun n => ?_⟩
  have hMmin : Martingale
      (stoppedProcess
        (fun i => {omega | ⊥ < (tau ⊓ sigma) n omega}.indicator (M i))
        ((tau ⊓ sigma) n)) 𝓕 P := by
    convert!
      hstable _ (hM.stoppedProcess_localSeq n) (sigma n)
        (hsigma.isStoppingTime n) using 1
    ext i omega
    simp_rw [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff,
      inf_comm (tau n)]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      Set.ofPred_and, Set.inter_comm]
    simp_rw [← Set.indicator_indicator]
    rfl
  have hNmin : Martingale
      (stoppedProcess
        (fun i => {omega | ⊥ < (tau ⊓ sigma) n omega}.indicator (N i))
        ((tau ⊓ sigma) n)) 𝓕 P := by
    convert!
      hstable _ (hN.stoppedProcess_localSeq n) (tau n)
        (htau.isStoppingTime n) using 1
    ext i omega
    simp_rw [stoppedProcess_indicator_comm, Pi.inf_apply, lt_inf_iff]
    rw [← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm,
      Set.ofPred_and]
    simp_rw [← Set.indicator_indicator]
    rfl
  have hindicator :
      (fun i => {omega | ⊥ < (tau ⊓ sigma) n omega}.indicator
        (fun omega => M i omega + N i omega)) =
      (fun i => {omega | ⊥ < (tau ⊓ sigma) n omega}.indicator (M i)) +
        fun i => {omega | ⊥ < (tau ⊓ sigma) n omega}.indicator (N i) := by
    ext i omega
    by_cases homega : omega ∈ {omega | ⊥ < (tau ⊓ sigma) n omega}
    · simp only [Set.indicator_of_mem homega, Pi.add_apply]
    · simp only [Set.indicator_of_notMem homega, Pi.add_apply, add_zero]
  rw [hindicator, stoppedProcess_add]
  exact hMmin.add hNmin

/-- Local martingales are closed under pointwise negation. -/
theorem IsLocalMartingale.neg
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} (hM : IsLocalMartingale M 𝓕 P) :
    IsLocalMartingale (fun t omega => -M t omega) 𝓕 P := by
  simpa only [neg_one_mul] using hM.const_mul (-1)

/-- Under stopping stability, local martingales are closed under
subtraction even when their localizing sequences differ. -/
theorem IsLocalMartingale.sub_of_isStable_martingale
    {W : Type*} [MeasurableSpace W]
    {M N : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W}
    (hstable : IsStable 𝓕
      (fun X : ℝ≥0 → W → ℝ => Martingale X 𝓕 P))
    (hM : IsLocalMartingale M 𝓕 P) (hN : IsLocalMartingale N 𝓕 P) :
    IsLocalMartingale (fun t omega => M t omega - N t omega) 𝓕 P := by
  simpa only [sub_eq_add_neg] using hM.add_of_isStable_martingale hstable hN.neg

/-- Under continuous-time stopping stability, continuous local martingales
are closed under addition. -/
theorem IsContinuousLocalMartingale.add_of_isStable_martingale
    {W : Type*} [MeasurableSpace W]
    {M N : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W}
    (hstable : IsStable 𝓕
      (fun X : ℝ≥0 → W → ℝ => Martingale X 𝓕 P))
    (hM : IsContinuousLocalMartingale M 𝓕 P)
    (hN : IsContinuousLocalMartingale N 𝓕 P) :
    IsContinuousLocalMartingale
      (fun t omega => M t omega + N t omega) 𝓕 P := by
  refine ⟨hM.1.add_of_isStable_martingale hstable hN.1, ?_⟩
  filter_upwards [hM.2, hN.2] with omega hMcontinuous hNcontinuous
  exact hMcontinuous.add hNcontinuous

/-- Continuous local martingales are closed under pointwise negation. -/
theorem IsContinuousLocalMartingale.neg
    {W : Type*} [MeasurableSpace W]
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W} (hM : IsContinuousLocalMartingale M 𝓕 P) :
    IsContinuousLocalMartingale (fun t omega => -M t omega) 𝓕 P := by
  simpa only [neg_one_mul] using hM.const_mul (-1)

/-- Under continuous-time stopping stability, continuous local martingales
are closed under subtraction. -/
theorem IsContinuousLocalMartingale.sub_of_isStable_martingale
    {W : Type*} [MeasurableSpace W]
    {M N : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {P : Measure W}
    (hstable : IsStable 𝓕
      (fun X : ℝ≥0 → W → ℝ => Martingale X 𝓕 P))
    (hM : IsContinuousLocalMartingale M 𝓕 P)
    (hN : IsContinuousLocalMartingale N 𝓕 P) :
    IsContinuousLocalMartingale
      (fun t omega => M t omega - N t omega) 𝓕 P := by
  simpa only [sub_eq_add_neg] using
    hM.add_of_isStable_martingale hstable hN.neg

/-- An `Lᵖ` bound at a later time propagates backwards along a martingale for
every exponent `p ≥ 1`. -/
theorem martingale_memLp_of_le
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {p : ℝ≥0∞}
    {ι : Type*} [Preorder ι] {𝓥 : Filtration ι ‹MeasurableSpace W›}
    {M : ι → W → E} (hM : Martingale M 𝓥 P)
    {s t : ι} (hst : s ≤ t) (hp : 1 ≤ p) (hMt : MemLp (M t) p P) :
    MemLp (M s) p P :=
  (hMt.condExp hp).ae_eq (hM.condExp_ae_eq hst)

/-- Conditional-expectation contraction gives the corresponding backwards
monotonicity of martingale `Lᵖ` seminorms. -/
theorem martingale_eLpNorm_le_of_le
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {p : ℝ≥0∞}
    {ι : Type*} [Preorder ι] {𝓥 : Filtration ι ‹MeasurableSpace W›}
    {M : ι → W → E} (hM : Martingale M 𝓥 P)
    {s t : ι} (hst : s ≤ t) (hp : 1 ≤ p) :
    eLpNorm (M s) p P ≤ eLpNorm (M t) p P := by
  rw [← eLpNorm_congr_ae (hM.condExp_ae_eq hst)]
  exact eLpNorm_condExp_le_eLpNorm _ hp

/-- Stopping a continuous-time martingale at a deterministic time preserves
the martingale property in the original filtration.  Unlike monotone
reindexing, this records that `M (min t a)` is adapted to `𝓥 t` and handles
the interval after `a` as a conditionally constant process. -/
theorem martingale_deterministicStop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {ι : Type*} [LinearOrder ι]
    {𝓥 : Filtration ι ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ι → W → ℝ} (hM : Martingale M 𝓥 P) (a : ι) :
    Martingale (fun t => M (min t a)) 𝓥 P := by
  refine ⟨fun t => (hM.stronglyMeasurable (min t a)).mono
      (𝓥.mono (min_le_left _ _)), ?_⟩
  intro s t hst
  rcases le_total s a with hsa | has
  · simpa only [min_eq_left hsa] using
      hM.condExp_ae_eq (le_min hst hsa)
  · have hat : a ≤ t := has.trans hst
    simp only [min_eq_right has, min_eq_right hat]
    exact Filter.Eventually.of_forall (congrFun
      (condExp_of_stronglyMeasurable (𝓥.le s)
        ((hM.stronglyMeasurable a).mono (𝓥.mono has))
        (hM.integrable a)))

/-- If the terminal value at a deterministic stopping horizon is in `Lᵖ`,
then every value of the stopped process is in `Lᵖ`. -/
theorem martingale_memLp_deterministicStop
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {p : ℝ≥0∞}
    {ι : Type*} [LinearOrder ι] {𝓥 : Filtration ι ‹MeasurableSpace W›}
    {M : ι → W → E} (hM : Martingale M 𝓥 P)
    (a : ι) (hp : 1 ≤ p) (hMa : MemLp (M a) p P) :
    ∀ t, MemLp (M (min t a)) p P := by
  intro t
  exact martingale_memLp_of_le hM (min_le_right _ _) hp hMa

/-- In discrete time, stopping a real martingale at an arbitrary stopping
time preserves the martingale property.  Mathlib packages the corresponding
result for submartingales; applying it to both `M` and `-M` recovers equality
of conditional expectations. -/
theorem martingale_stoppedProcess_nat
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℕ ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℕ → W → ℝ} (hM : Martingale M 𝓥 P)
    {tau : W → WithTop ℕ} (htau : IsStoppingTime 𝓥 tau) :
    Martingale (stoppedProcess M tau) 𝓥 P := by
  rw [martingale_iff]
  refine ⟨?_, hM.submartingale.stoppedProcess htau⟩
  have hneg : Submartingale (stoppedProcess (-M) tau) 𝓥 P :=
    hM.neg.submartingale.stoppedProcess htau
  have hsuper : Supermartingale (-stoppedProcess (-M) tau) 𝓥 P := hneg.neg
  have heq : -stoppedProcess (-M) tau = stoppedProcess M tau := by
    ext n omega
    change -(-M (min (n : WithTop ℕ) (tau omega)).untopA omega) =
      M (min (n : WithTop ℕ) (tau omega)).untopA omega
    simp only [neg_neg]
  rw [heq] at hsuper
  exact hsuper

/-- A bounded discrete stopping time needs only one terminal `Lᵖ` hypothesis
to make every value of the stopped martingale `Lᵖ`. -/
theorem memLp_stoppedProcess_nat_of_bdd_terminal
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {p : ℝ≥0∞}
    {𝓥 : Filtration ℕ ‹MeasurableSpace W›}
    {M : ℕ → W → E} (hM : Martingale M 𝓥 P)
    {tau : W → WithTop ℕ} (htau : IsStoppingTime 𝓥 tau)
    (N : ℕ) (htauN : ∀ omega, tau omega ≤ N)
    (hp : 1 ≤ p) (hMN : MemLp (M N) p P) :
    ∀ n, MemLp (stoppedProcess M tau n) p P := by
  let Q : ℕ → W → E := fun n => M (min n N)
  have hQ2 : ∀ n, MemLp (Q n) p P :=
    martingale_memLp_deterministicStop hM N hp hMN
  have hQeq : Q = stoppedProcess M (fun _ => (N : WithTop ℕ)) := by
    ext n omega
    simp only [Q, stoppedProcess]
    have hmin : min (n : WithTop ℕ) (N : WithTop ℕ) =
        (min n N : ℕ) := (WithTop.coe_min n N).symm
    apply congrArg (fun k => M k omega)
    have hminA := congrArg (fun x : WithTop ℕ => x.untopA) hmin
    have hcoe : ((min n N : ℕ) : WithTop ℕ) ≠ ⊤ := WithTop.coe_ne_top
    rw [WithTop.untopA_eq_untop hcoe] at hminA
    exact hminA.symm
  have hstopEq : stoppedProcess Q tau = stoppedProcess M tau := by
    rw [hQeq, stoppedProcess_stoppedProcess]
    congr 1
    funext omega
    exact inf_eq_left.mpr (htauN omega)
  intro n
  rw [← hstopEq]
  exact memLp_stoppedProcess htau hQ2 n

/-- A bounded stopped discrete martingale is simultaneously a martingale and
an `Lᵖ` process as soon as the original martingale has one `Lᵖ` terminal
value at the deterministic bound. -/
theorem martingale_stoppedProcess_nat_of_bdd_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℕ ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℕ → W → ℝ} (hM : Martingale M 𝓥 P)
    {tau : W → WithTop ℕ} (htau : IsStoppingTime 𝓥 tau)
    (N : ℕ) (htauN : ∀ omega, tau omega ≤ N)
    (hMN : MemLp (M N) 2 P) :
    Martingale (stoppedProcess M tau) 𝓥 P ∧
      ∀ n, MemLp (stoppedProcess M tau n) 2 P :=
  ⟨martingale_stoppedProcess_nat hM htau,
    memLp_stoppedProcess_nat_of_bdd_terminal
      hM htau N htauN one_le_two hMN⟩

/-- A bounded discrete stopping time remains a stopping time after mapping its
finite values monotonically into a linearly ordered time domain.  Boundedness
rules out `⊤`; the sublevel event is then a countable union of its measurable
discrete fibers. -/
theorem isStoppingTime_map_bounded_nat
    {W ι : Type*} [MeasurableSpace W] [LinearOrder ι]
    {𝓥 : Filtration ι ‹MeasurableSpace W›}
    (u : ℕ → ι) (hu : Monotone u)
    {tau : W → WithTop ℕ}
    (htau : IsStoppingTime (monotoneReindexFiltration 𝓥 u hu) tau)
    (N : ℕ) (htauN : ∀ omega, tau omega ≤ N) :
    IsStoppingTime 𝓥 (fun omega => (u (tau omega).untopA : WithTop ι)) := by
  intro t
  have heq :
      {omega | (u (tau omega).untopA : WithTop ι) ≤ t} =
        ⋃ k : {k : ℕ // u k ≤ t}, {omega | tau omega = (k : ℕ)} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro homega
      have hne : tau omega ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (htauN omega)
      refine ⟨⟨(tau omega).untopA, ?_⟩, ?_⟩
      · exact WithTop.coe_le_coe.mp homega
      · change tau omega = ((tau omega).untopA : WithTop ℕ)
        rw [WithTop.untopA_eq_untop hne]
        exact (WithTop.coe_untop (tau omega) hne).symm
    · rintro ⟨⟨k, hukt⟩, hk⟩
      have hne : tau omega ≠ ⊤ := by rw [hk]; exact WithTop.coe_ne_top
      have huntop : (tau omega).untopA = k := by
        rw [WithTop.untopA_eq_untop hne]
        exact WithTop.coe_eq_coe.mp ((WithTop.coe_untop _ hne).trans hk)
      rw [huntop]
      exact_mod_cast hukt
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  have hk := htau.measurableSet_eq k.1
  change MeasurableSet[𝓥 (u k.1)]
    {omega | tau omega = (k.1 : WithTop ℕ)} at hk
  exact 𝓥.mono k.2 _ hk

/-- A finite-range stopped process is strongly adapted whenever the original
process is.  The stopped process is a finite sum over the measurable fibers
of the stopping time. -/
theorem stronglyAdapted_stoppedProcess_of_finiteRange
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted 𝓥 X)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝓥 tau)
    (S : Finset ℝ≥0) (htauS : ∀ omega, tau omega ∈ WithTop.some '' S) :
    StronglyAdapted 𝓥 (stoppedProcess X tau) := by
  intro t
  rw [stoppedProcess_eq_of_mem_finset t (fun omega _ => htauS omega)]
  apply StronglyMeasurable.add
  · exact (hX t).indicator (htau.measurableSet_ge t)
  · apply Finset.stronglyMeasurable_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    exact ((hX i).mono (𝓥.mono hi.2.le)).indicator
      (𝓥.mono hi.2.le _ (htau.measurableSet_eq i))

/-- Stopping a martingale at a finite-range stopping time preserves the
martingale property.  Optional sampling is applied between a
deterministic time `s` and `max s (min tau t)`; splitting on `tau ≤ s` then
recovers the conditional-expectation identity for the stopped process. -/
theorem martingale_stoppedProcess_of_finiteRange
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝓥 tau)
    (S : Finset ℝ≥0) (htauS : ∀ omega, tau omega ∈ WithTop.some '' S) :
    Martingale (stoppedProcess M tau) 𝓥 P := by
  have hrange : (Set.range tau).Countable := by
    apply ((S.finite_toSet.image ((↑) : ℝ≥0 → WithTop ℝ≥0))).countable.mono
    rintro x ⟨omega, rfl⟩
    exact htauS omega
  have hYadapt : StronglyAdapted 𝓥 (stoppedProcess M tau) :=
    stronglyAdapted_stoppedProcess_of_finiteRange
      hM.stronglyAdapted htau S htauS
  have hYint (t : ℝ≥0) : Integrable (stoppedProcess M tau t) P :=
    integrable_stoppedProcess_of_mem_finset htau hM.integrable t
      (fun omega _ => htauS omega)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  let A : Set W := {omega | tau omega ≤ (s : WithTop ℝ≥0)}
  let rho : W → WithTop ℝ≥0 := fun omega =>
    max (s : WithTop ℝ≥0) (min (tau omega) (t : WithTop ℝ≥0))
  have hA : MeasurableSet[𝓥 s] A := htau s
  have hrho : IsStoppingTime 𝓥 rho :=
    (isStoppingTime_const 𝓥 s).max (htau.min (isStoppingTime_const 𝓥 t))
  have hrho_le : ∀ omega, rho omega ≤ (t : WithTop ℝ≥0) := by
    intro omega
    exact max_le (mod_cast hst) (min_le_right _ _)
  have hs_le_rho : (fun _ : W => (s : WithTop ℝ≥0)) ≤ rho := by
    intro omega
    exact le_max_left _ _
  have hrho_range : (Set.range rho).Countable := by
    have heq : Set.range rho =
        (fun x : WithTop ℝ≥0 => max (s : WithTop ℝ≥0)
          (min x (t : WithTop ℝ≥0))) '' Set.range tau := by
      rw [← Set.range_comp]
      rfl
    rw [heq]
    exact hrange.image _
  have hconst_range :
      (Set.range (fun _ : W => (s : WithTop ℝ≥0))).Countable := by
    apply (Set.countable_singleton (s : WithTop ℝ≥0)).mono
    rintro x ⟨omega, rfl⟩
    exact Set.mem_singleton _
  have hoptional :
      M s =ᵐ[P] P[stoppedValue M rho | 𝓥 s] := by
    have h := hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      hrho (isStoppingTime_const 𝓥 s) hs_le_rho hrho_le
      hrho_range hconst_range
    simpa only [stoppedValue_const,
      IsStoppingTime.measurableSpace_const] using h
  have hrhoS : ∀ omega, rho omega ∈
      WithTop.some '' (S.image fun x => max s (min x t)) := by
    intro omega
    obtain ⟨x, hxS, hxtau⟩ := htauS omega
    have hx : (x : WithTop ℝ≥0) = tau omega := hxtau
    refine ⟨max s (min x t), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨x, hxS, rfl⟩
    · dsimp only [rho]
      rw [← hx]
      simp only [WithTop.coe_min, WithTop.coe_max]
  have hrhoInt : Integrable (stoppedValue M rho) P := by
    apply integrable_stoppedValue_of_mem_finset hrho hM.integrable hrhoS
  have hdecompT : stoppedProcess M tau t =
      A.indicator (stoppedProcess M tau s) +
        Aᶜ.indicator (stoppedValue M rho) := by
    funext omega
    by_cases homega : tau omega ≤ (s : WithTop ℝ≥0)
    · have htaut : tau omega ≤ (t : WithTop ℝ≥0) :=
        homega.trans (WithTop.coe_le_coe.mpr hst)
      have hmemA : omega ∈ A := homega
      have hnotAc : omega ∉ Aᶜ := fun hAc => hAc hmemA
      simp only [Set.indicator_of_mem hmemA, Set.indicator_of_notMem hnotAc,
        Pi.add_apply, add_zero, stoppedProcess, min_eq_right homega,
        min_eq_right htaut]
    · have hstau : (s : WithTop ℝ≥0) ≤ tau omega := le_of_not_ge homega
      have hsmin : (s : WithTop ℝ≥0) ≤
          min (tau omega) (t : WithTop ℝ≥0) :=
        le_min hstau (WithTop.coe_le_coe.mpr hst)
      have hnotA : omega ∉ A := homega
      have hmemAc : omega ∈ Aᶜ := hnotA
      simp only [Set.indicator_of_notMem hnotA, Set.indicator_of_mem hmemAc,
        Pi.add_apply, zero_add, stoppedProcess,
        stoppedValue, rho, max_eq_right hsmin, min_comm]
  have hdecompS : stoppedProcess M tau s =
      A.indicator (stoppedProcess M tau s) + Aᶜ.indicator (M s) := by
    funext omega
    by_cases homega : tau omega ≤ (s : WithTop ℝ≥0)
    · have hmemA : omega ∈ A := homega
      have hnotAc : omega ∉ Aᶜ := fun hAc => hAc hmemA
      simp only [Set.indicator_of_mem hmemA, Set.indicator_of_notMem hnotAc,
        Pi.add_apply, add_zero]
    · have hstau : (s : WithTop ℝ≥0) ≤ tau omega := le_of_not_ge homega
      have hnotA : omega ∉ A := homega
      have hmemAc : omega ∈ Aᶜ := hnotA
      simp only [Set.indicator_of_notMem hnotA, Set.indicator_of_mem hmemAc,
        Pi.add_apply, zero_add, stoppedProcess, min_eq_left hstau,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hdecompT]
  have hfirstInt : Integrable
      (A.indicator (stoppedProcess M tau s)) P :=
    (hYint s).indicator (𝓥.le s A hA)
  have hsecondInt : Integrable (Aᶜ.indicator (stoppedValue M rho)) P :=
    hrhoInt.indicator (𝓥.le s Aᶜ hA.compl)
  have hfirstCond :
      P[A.indicator (stoppedProcess M tau s) | 𝓥 s] =
        A.indicator (stoppedProcess M tau s) :=
    condExp_of_stronglyMeasurable (𝓥.le s)
      ((hYadapt s).indicator hA) hfirstInt
  calc
    P[A.indicator (stoppedProcess M tau s) +
          Aᶜ.indicator (stoppedValue M rho) | 𝓥 s] =ᵐ[P]
        P[A.indicator (stoppedProcess M tau s) | 𝓥 s] +
          P[Aᶜ.indicator (stoppedValue M rho) | 𝓥 s] :=
      condExp_add hfirstInt hsecondInt (𝓥 s)
    _ =ᵐ[P] A.indicator (stoppedProcess M tau s) +
        Aᶜ.indicator P[stoppedValue M rho | 𝓥 s] := by
      rw [hfirstCond]
      exact Filter.EventuallyEq.rfl.add
        (condExp_indicator hrhoInt hA.compl)
    _ =ᵐ[P] A.indicator (stoppedProcess M tau s) +
        Aᶜ.indicator (M s) :=
      Filter.EventuallyEq.rfl.add hoptional.symm.indicator
    _ = stoppedProcess M tau s := hdecompS.symm

/-- Sample a continuous-time process on a deterministic uniform grid. -/
def uniformPartitionSample
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) :
    ℕ → W → ℝ :=
  fun k => M (uniformPartitionTime T n k)

/-- The first grid index, up to `n`, at which a uniformly sampled process
enters `S`; if it never enters, the index is `n`. -/
noncomputable def uniformPartitionHittingTime
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) : W → WithTop ℕ :=
  fun omega =>
    ((hittingBtwn (uniformPartitionSample M T n) S 0 n omega : ℕ) :
      WithTop ℕ)

/-- The preceding grid hitting index mapped back to continuous nonnegative
time. -/
noncomputable def uniformPartitionHittingTimeNNReal
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) : W → WithTop ℝ≥0 :=
  fun omega =>
    (uniformPartitionTime T n
      (uniformPartitionHittingTime M T n S omega).untopA : WithTop ℝ≥0)

/-- A finite-grid hitting index is bounded by the terminal grid index. -/
theorem uniformPartitionHittingTime_le
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (omega : W) :
    uniformPartitionHittingTime M T n S omega ≤ (n : WithTop ℕ) := by
  change ((hittingBtwn (uniformPartitionSample M T n) S 0 n omega : ℕ) :
    WithTop ℕ) ≤ (n : WithTop ℕ)
  exact_mod_cast
    (hittingBtwn_le (u := uniformPartitionSample M T n)
      (s := S) (n := 0) (m := n) omega)

/-- A martingale sampled on a uniform grid remains a martingale for the
correspondingly sampled filtration. -/
theorem martingale_uniformPartitionSample
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformPartitionSample M T n)
      (uniformPartitionFiltration 𝓥 T n) P :=
  martingale_comp_monotone hM (uniformPartitionTime T n)
    (monotone_uniformPartitionTime_general T n)

/-- The bounded hitting index of a uniformly sampled martingale is a
stopping time for the sampled filtration. -/
theorem isStoppingTime_uniformPartitionHittingTime_of_stronglyAdapted
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    IsStoppingTime (uniformPartitionFiltration 𝓥 T n)
      (uniformPartitionHittingTime M T n S) := by
  have hsample : StronglyAdapted (uniformPartitionFiltration 𝓥 T n)
      (uniformPartitionSample M T n) := fun k =>
    hM (uniformPartitionTime T n k)
  exact hsample.adapted.isStoppingTime_hittingBtwn hS

/-- The martingale specialization of the adapted grid-hitting theorem. -/
theorem isStoppingTime_uniformPartitionHittingTime
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    IsStoppingTime (uniformPartitionFiltration 𝓥 T n)
      (uniformPartitionHittingTime M T n S) := by
  exact isStoppingTime_uniformPartitionHittingTime_of_stronglyAdapted
    hM.stronglyAdapted T n hS

/-- The continuous-time value of a finite-grid hitting index is a stopping
time for the original filtration. -/
theorem
    isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    IsStoppingTime 𝓥 (uniformPartitionHittingTimeNNReal M T n S) := by
  apply isStoppingTime_map_bounded_nat
    (uniformPartitionTime T n)
    (monotone_uniformPartitionTime_general T n)
    (isStoppingTime_uniformPartitionHittingTime_of_stronglyAdapted
      hM T n hS)
    n
  exact uniformPartitionHittingTime_le M T n S

/-- The martingale specialization of the adapted continuous-time grid-hit
stopping theorem. -/
theorem isStoppingTime_uniformPartitionHittingTimeNNReal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    IsStoppingTime 𝓥 (uniformPartitionHittingTimeNNReal M T n S) := by
  exact
    isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
      hM.stronglyAdapted T n hS

/-- Continuous-time finite-grid hitting times have finite range. -/
theorem uniformPartitionHittingTimeNNReal_mem_rangeFinset
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (S : Set ℝ) (omega : W) :
    uniformPartitionHittingTimeNNReal M T n S omega ∈
      WithTop.some '' ((Finset.range (n + 1)).image
        (uniformPartitionTime T n)) := by
  let tau := uniformPartitionHittingTime M T n S
  have hne : tau omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top
      (uniformPartitionHittingTime_le M T n S omega)
  let k : ℕ := (tau omega).untopA
  have hk : k ≤ n := by
    have hcoe : (k : WithTop ℕ) = tau omega := by
      dsimp only [k]
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop (tau omega) hne
    exact WithTop.coe_le_coe.mp
      (hcoe.trans_le (uniformPartitionHittingTime_le M T n S omega))
  refine ⟨uniformPartitionTime T n k, ?_, rfl⟩
  exact Finset.mem_image.mpr
    ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- A martingale stopped when a finite uniform grid first enters a measurable
set is a martingale in the original continuous-time filtration. -/
theorem
    martingale_stoppedProcess_uniformPartitionHittingTimeNNReal_of_adapted
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M Z : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hZ : StronglyAdapted 𝓥 Z)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    Martingale
      (stoppedProcess M (uniformPartitionHittingTimeNNReal Z T n S))
      𝓥 P := by
  apply martingale_stoppedProcess_of_finiteRange hM
    (isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
      hZ T n hS)
    ((Finset.range (n + 1)).image (uniformPartitionTime T n))
  exact uniformPartitionHittingTimeNNReal_mem_rangeFinset Z T n S

/-- The preceding theorem specialized to stopping at a grid hit of the
martingale itself. -/
theorem martingale_stoppedProcess_uniformPartitionHittingTimeNNReal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    Martingale
      (stoppedProcess M (uniformPartitionHittingTimeNNReal M T n S))
      𝓥 P := by
  exact
    martingale_stoppedProcess_uniformPartitionHittingTimeNNReal_of_adapted
      hM hM.stronglyAdapted T n hS

/-- The closed complement of the real ball of radius `R`. -/
def outsideClosedBall (R : ℝ≥0) : Set ℝ := {x | (R : ℝ) ≤ |x|}

/-- First visit to the complement of the radius-`R` ball on the dyadic grid
of level `n`, mapped back to continuous nonnegative time. -/
noncomputable def dyadicHittingTimeNNReal
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (n : ℕ) :
    W → WithTop ℝ≥0 :=
  uniformPartitionHittingTimeNNReal M T (2 ^ n) (outsideClosedBall R)

/-- The pointwise minimum of two dyadic-grid exit rules on the same grid. -/
noncomputable def pairedDyadicHittingTimeNNReal
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (n : ℕ) :
    W → WithTop ℝ≥0 :=
  fun omega => min (dyadicHittingTimeNNReal Z T R n omega)
    (dyadicHittingTimeNNReal Q T S n omega)

/-- A dyadic exit rule takes values in its finite uniform time grid. -/
theorem dyadicHittingTimeNNReal_mem_rangeFinset
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (n : ℕ)
    (omega : W) :
    dyadicHittingTimeNNReal Z T R n omega ∈
      WithTop.some '' ((Finset.range (2 ^ n + 1)).image
        (uniformPartitionTime T (2 ^ n))) := by
  exact uniformPartitionHittingTimeNNReal_mem_rangeFinset
    Z T (2 ^ n) (outsideClosedBall R) omega

/-- A paired dyadic exit still takes values in the common finite grid. -/
theorem pairedDyadicHittingTimeNNReal_mem_rangeFinset
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (n : ℕ)
    (omega : W) :
    pairedDyadicHittingTimeNNReal Z Q T R S n omega ∈
      WithTop.some '' ((Finset.range (2 ^ n + 1)).image
        (uniformPartitionTime T (2 ^ n))) := by
  let grid := (Finset.range (2 ^ n + 1)).image
    (uniformPartitionTime T (2 ^ n))
  obtain ⟨z, hz, hZeq⟩ :=
    dyadicHittingTimeNNReal_mem_rangeFinset Z T R n omega
  obtain ⟨q, hq, hQeq⟩ :=
    dyadicHittingTimeNNReal_mem_rangeFinset Q T S n omega
  refine ⟨min z q, ?_, ?_⟩
  · change min z q ∈ grid
    rcases min_choice z q with h | h
    · rw [h]
      exact hz
    · rw [h]
      exact hq
  · unfold pairedDyadicHittingTimeNNReal
    rw [← hZeq, ← hQeq, WithTop.coe_min]

/-- Every bounded-horizon dyadic hitting time is at most its horizon. -/
theorem dyadicHittingTimeNNReal_le
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (n : ℕ)
    (omega : W) : dyadicHittingTimeNNReal M T R n omega ≤ T := by
  let tau := uniformPartitionHittingTime M T (2 ^ n) (outsideClosedBall R)
  have hne : tau omega ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top
    (uniformPartitionHittingTime_le M T (2 ^ n) (outsideClosedBall R) omega)
  have hk : (tau omega).untopA ≤ 2 ^ n := by
    have hcoe : ((tau omega).untopA : WithTop ℕ) = tau omega := by
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop (tau omega) hne
    exact WithTop.coe_le_coe.mp (hcoe.trans_le
      (uniformPartitionHittingTime_le M T (2 ^ n)
        (outsideClosedBall R) omega))
  change (uniformPartitionTime T (2 ^ n) (tau omega).untopA :
    WithTop ℝ≥0) ≤ T
  exact_mod_cast (uniformPartitionTime_mem_Icc_of_le T (by positivity) hk).2

/-- Dyadic hitting times decrease under grid refinement, since every coarse
grid point also occurs on the next grid. -/
theorem antitone_dyadicHittingTimeNNReal
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    Antitone (fun n => dyadicHittingTimeNNReal M T R n omega) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ihm =>
      apply le_trans ?_ ihm
      let Xn := uniformPartitionSample M T (2 ^ m)
      let Xs := uniformPartitionSample M T (2 ^ (m + 1))
      let hn := hittingBtwn Xn (outsideClosedBall R) 0 (2 ^ m) omega
      let hs := hittingBtwn Xs (outsideClosedBall R) 0 (2 ^ (m + 1)) omega
      by_cases hex :
          ∃ j ∈ Set.Icc 0 (2 ^ m), Xn j omega ∈ outsideClosedBall R
      · have hmem : Xn hn omega ∈ outsideClosedBall R :=
          hittingBtwn_mem_set hex
        have hhn : hn ≤ 2 ^ m := hittingBtwn_le omega
        have hindex : 2 * hn ≤ 2 ^ (m + 1) := by
          rw [pow_succ]
          omega
        have hsample : Xs (2 * hn) omega = Xn hn omega := by
          dsimp only [Xs, Xn, uniformPartitionSample]
          apply congrArg (fun t => M t omega)
          unfold uniformPartitionTime
          rw [pow_succ]
          norm_num
          ring
        have hhs : hs ≤ 2 * hn := by
          apply hittingBtwn_le_of_mem (n := 0) (m := 2 ^ (m + 1))
          · omega
          · exact hindex
          · rw [hsample]
            exact hmem
        change (uniformPartitionTime T (2 ^ (m + 1)) hs :
            WithTop ℝ≥0) ≤
          (uniformPartitionTime T (2 ^ m) hn : WithTop ℝ≥0)
        apply WithTop.coe_le_coe.mpr
        calc
          uniformPartitionTime T (2 ^ (m + 1)) hs ≤
              uniformPartitionTime T (2 ^ (m + 1)) (2 * hn) :=
            monotone_uniformPartitionTime_general T (2 ^ (m + 1)) hhs
          _ = uniformPartitionTime T (2 ^ m) hn := by
            unfold uniformPartitionTime
            rw [pow_succ]
            norm_num
            ring
      · have hhn : hn = 2 ^ m := by
          simp only [hn, hittingBtwn, if_neg hex]
        change (uniformPartitionTime T (2 ^ (m + 1)) hs :
            WithTop ℝ≥0) ≤
          (uniformPartitionTime T (2 ^ m) hn : WithTop ℝ≥0)
        rw [hhn]
        apply WithTop.coe_le_coe.mpr
        calc
          uniformPartitionTime T (2 ^ (m + 1)) hs ≤ T :=
            (uniformPartitionTime_mem_Icc_of_le T (by positivity)
              (hittingBtwn_le omega)).2
          _ = uniformPartitionTime T (2 ^ m) (2 ^ m) := by
            unfold uniformPartitionTime
            exact (mul_div_cancel_right₀ T (by positivity)).symm

/-- The bounded continuous-time exit rule obtained as the decreasing limit
of the dyadic-grid hitting times. -/
noncomputable def continuousExitTime
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) :
    W → WithTop ℝ≥0 :=
  fun omega => ⨅ n, dyadicHittingTimeNNReal M T R n omega

/-- Enlarging the exit radius can only delay a dyadic-grid hitting time. -/
theorem dyadicHittingTimeNNReal_mono_radius
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (hRS : R ≤ S)
    (n : ℕ) (omega : W) :
    dyadicHittingTimeNNReal Z T R n omega ≤
      dyadicHittingTimeNNReal Z T S n omega := by
  let u := uniformPartitionSample Z T (2 ^ n)
  let hR := hittingBtwn u (outsideClosedBall R) 0 (2 ^ n) omega
  let hS := hittingBtwn u (outsideClosedBall S) 0 (2 ^ n) omega
  have hindex : hR ≤ hS := by
    by_cases hs : hS < 2 ^ n
    · have hmemS : u hS omega ∈ outsideClosedBall S :=
        hittingBtwn_mem_set_of_hittingBtwn_lt hs
      have hmemR : u hS omega ∈ outsideClosedBall R := by
        change (R : ℝ) ≤ |u hS omega|
        change (S : ℝ) ≤ |u hS omega| at hmemS
        have hRSreal : (R : ℝ) ≤ (S : ℝ) := by exact_mod_cast hRS
        exact hRSreal.trans hmemS
      exact hittingBtwn_le_of_mem bot_le (hittingBtwn_le omega) hmemR
    · exact (hittingBtwn_le omega).trans (le_of_not_gt hs)
  unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
    uniformPartitionHittingTime
  change (uniformPartitionTime T (2 ^ n) hR : WithTop ℝ≥0) ≤
    (uniformPartitionTime T (2 ^ n) hS : WithTop ℝ≥0)
  exact_mod_cast monotone_uniformPartitionTime_general T (2 ^ n) hindex

/-- Enlarging the exit radius can only delay the bounded continuous exit
time. -/
theorem continuousExitTime_mono_radius
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (hRS : R ≤ S)
    (omega : W) :
    continuousExitTime Z T R omega ≤ continuousExitTime Z T S omega := by
  apply iInf_mono
  intro n
  exact dyadicHittingTimeNNReal_mono_radius Z T R S hRS n omega

/-- The complement of the open real ball of radius `R` is measurable. -/
theorem measurableSet_outsideClosedBall (R : ℝ≥0) :
    MeasurableSet (outsideClosedBall R) := by
  exact measurableSet_le measurable_const continuous_abs.measurable

/-- A paired dyadic exit is a finite-range stopping time in the original
continuous-time filtration. -/
theorem isStoppingTime_pairedDyadicHittingTimeNNReal
    {W : Type*} [MeasurableSpace W]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {Z Q : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝒱 Z)
    (hQ : StronglyAdapted 𝒱 Q) (T R S : ℝ≥0) (n : ℕ) :
    IsStoppingTime 𝒱 (pairedDyadicHittingTimeNNReal Z Q T R S n) := by
  exact
    (isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
      hZ T (2 ^ n) (measurableSet_outsideClosedBall R)).min
      (isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
        hQ T (2 ^ n) (measurableSet_outsideClosedBall S))

/-- Under the standard right-continuity hypothesis on the filtration, the
decreasing limit of the dyadic hitting times is a stopping time. -/
theorem isStoppingTime_continuousExitTime_of_stronglyAdapted
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M) (T R : ℝ≥0) :
    IsStoppingTime 𝓥 (continuousExitTime M T R) := by
  apply IsStoppingTime.iInf
  intro n
  exact
    isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
      hM T (2 ^ n) (measurableSet_outsideClosedBall R)

/-- The martingale specialization of the adapted continuous exit-time
theorem. -/
theorem isStoppingTime_continuousExitTime
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P) (T R : ℝ≥0) :
    IsStoppingTime 𝓥 (continuousExitTime M T R) := by
  exact isStoppingTime_continuousExitTime_of_stronglyAdapted
    hM.stronglyAdapted T R

/-- The continuous exit rule remains bounded by its deterministic horizon. -/
theorem continuousExitTime_le
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    continuousExitTime M T R omega ≤ T := by
  exact (iInf_le (fun n => dyadicHittingTimeNNReal M T R n omega) 0).trans
    (dyadicHittingTimeNNReal_le M T R 0 omega)

/-- The bounded continuous exit rule never takes the value `∞`. -/
theorem continuousExitTime_ne_top
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    continuousExitTime M T R omega ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top
    (continuousExitTime_le M T R omega)

/-- A continuous path that starts strictly inside a positive-radius exit
region cannot leave it at time zero.  The conclusion is stated for the
dyadic definition of `continuousExitTime`; continuity supplies one common
positive lower bound for every dyadic hitting time. -/
theorem continuousExitTime_pos_of_initial_lt
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W)
    (hZcont : Continuous (fun t ↦ Z t omega))
    (hT : 0 < T) (hzero : |Z 0 omega| < R) :
    (⊥ : WithTop ℝ≥0) < continuousExitTime Z T R omega := by
  have hgap : 0 < (R : ℝ) - |Z 0 omega| := sub_pos.mpr hzero
  have hcontAt : ContinuousAt (fun t ↦ |Z t omega|) 0 :=
    (continuous_abs.comp hZcont).continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨delta, hdelta, hclose⟩ :=
    hcontAt ((R : ℝ) - |Z 0 omega|) hgap
  let aReal : ℝ := min (T : ℝ) delta / 2
  have haReal : 0 < aReal := by
    dsimp only [aReal]
    positivity
  let a : ℝ≥0 := ⟨aReal, haReal.le⟩
  have ha : 0 < a := NNReal.coe_pos.mp haReal
  have haT : a < T := by
    rw [← NNReal.coe_lt_coe]
    dsimp only [a, aReal]
    change min (T : ℝ) delta / 2 < (T : ℝ)
    have hminT : min (T : ℝ) delta ≤ T := min_le_left _ _
    have hminPos : 0 < min (T : ℝ) delta := by positivity
    linarith
  have haDelta : (a : ℝ) < delta := by
    dsimp only [a, aReal]
    change min (T : ℝ) delta / 2 < delta
    have hminDelta : min (T : ℝ) delta ≤ delta := min_le_right _ _
    have hminPos : 0 < min (T : ℝ) delta := by positivity
    linarith
  have hin (q : ℝ≥0) (hqa : q < a) : |Z q omega| < R := by
    have hdistTime : dist q 0 < delta := by
      rw [NNReal.dist_eq]
      simp only [NNReal.coe_zero, sub_zero,
        abs_of_nonneg (NNReal.coe_nonneg q)]
      exact (NNReal.coe_lt_coe.mpr hqa).trans haDelta
    have hdist := hclose hdistTime
    rw [Real.dist_eq] at hdist
    have hle : |Z q omega| - |Z 0 omega| ≤
        abs (|Z q omega| - |Z 0 omega|) := le_abs_self _
    linarith
  have hdyadic (n : ℕ) : (a : WithTop ℝ≥0) ≤
      dyadicHittingTimeNNReal Z T R n omega := by
    by_contra hnot
    have hhitA : dyadicHittingTimeNNReal Z T R n omega < a :=
      lt_of_not_ge hnot
    let j := hittingBtwn (uniformPartitionSample Z T (2 ^ n))
      (outsideClosedBall R) 0 (2 ^ n) omega
    have hjle : j ≤ 2 ^ n := hittingBtwn_le omega
    have hjne : j ≠ 2 ^ n := by
      intro hj
      have htimeT : dyadicHittingTimeNNReal Z T R n omega = T := by
        unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
          uniformPartitionHittingTime
        change (uniformPartitionTime T (2 ^ n) j : WithTop ℝ≥0) = T
        rw [hj]
        exact_mod_cast mul_div_cancel_right₀ T
          (by positivity : (2 ^ n : ℝ≥0) ≠ 0)
      rw [htimeT] at hhitA
      have hTa : T < a := WithTop.coe_lt_coe.mp hhitA
      exact (not_lt_of_ge haT.le) hTa
    have hjlt : j < 2 ^ n := lt_of_le_of_ne hjle hjne
    have hjout : uniformPartitionSample Z T (2 ^ n) j omega ∈
        outsideClosedBall R :=
      hittingBtwn_mem_set_of_hittingBtwn_lt hjlt
    have htimeIn : |Z (uniformPartitionTime T (2 ^ n) j) omega| < R := by
      apply hin
      apply WithTop.coe_lt_coe.mp
      change (uniformPartitionTime T (2 ^ n) j : WithTop ℝ≥0) < a
      exact hhitA
    exact (not_le_of_gt htimeIn) hjout
  have hale : (a : WithTop ℝ≥0) ≤ continuousExitTime Z T R omega := by
    unfold continuousExitTime
    exact le_iInf hdyadic
  exact (WithTop.coe_pos.mpr ha).trans_le hale

/-- The pointwise minimum of two continuous exit times is positive when
both paths start strictly inside their respective exit regions. -/
theorem min_continuousExitTime_pos_of_initial_lt
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (omega : W)
    (hZcont : Continuous (fun t ↦ Z t omega))
    (hQcont : Continuous (fun t ↦ Q t omega))
    (hT : 0 < T) (hZzero : |Z 0 omega| < R)
    (hQzero : |Q 0 omega| < S) :
    (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega) := by
  exact lt_min (continuousExitTime_pos_of_initial_lt Z T R omega
    hZcont hT hZzero) (continuousExitTime_pos_of_initial_lt Q T S omega
      hQcont hT hQzero)

/-- Every dyadic approximation is positive under the same interior-start
hypotheses as its continuous-exit infimum. -/
theorem dyadicHittingTimeNNReal_pos_of_initial_lt
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (n : ℕ) (omega : W)
    (hZcont : Continuous (fun t ↦ Z t omega))
    (hT : 0 < T) (hzero : |Z 0 omega| < R) :
    (⊥ : WithTop ℝ≥0) < dyadicHittingTimeNNReal Z T R n omega := by
  exact (continuousExitTime_pos_of_initial_lt Z T R omega
    hZcont hT hzero).trans_le (iInf_le _ n)

/-- Paired dyadic exits are positive when both paths start in the interiors
of their exit regions. -/
theorem pairedDyadicHittingTimeNNReal_pos_of_initial_lt
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (n : ℕ)
    (omega : W) (hZcont : Continuous (fun t ↦ Z t omega))
    (hQcont : Continuous (fun t ↦ Q t omega))
    (hT : 0 < T) (hZzero : |Z 0 omega| < R)
    (hQzero : |Q 0 omega| < S) :
    (⊥ : WithTop ℝ≥0) <
      pairedDyadicHittingTimeNNReal Z Q T R S n omega := by
  exact lt_min
    (dyadicHittingTimeNNReal_pos_of_initial_lt Z T R n omega
      hZcont hT hZzero)
    (dyadicHittingTimeNNReal_pos_of_initial_lt Q T S n omega
      hQcont hT hQzero)

/-- A bounded stopping time can be extended past its bound on the event
where it reaches the bound. -/
noncomputable def extendBoundedStoppingTime
    {W : Type*} (tau : W → WithTop ℝ≥0) (T S : ℝ≥0) :
    W → WithTop ℝ≥0 :=
  fun omega => if tau omega < T then tau omega else S

/-- Extending a bounded stopping time to a later deterministic time on the
event where it reaches its bound preserves the stopping-time property. -/
theorem isStoppingTime_extendBoundedStoppingTime
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝓥 tau)
    (T S : ℝ≥0) (htauT : ∀ omega, tau omega ≤ T) (hTS : T ≤ S) :
    IsStoppingTime 𝓥 (extendBoundedStoppingTime tau T S) := by
  intro u
  rcases lt_or_ge u T with huT | hTu
  · have hSu : ¬(S : WithTop ℝ≥0) ≤ u :=
      not_le_of_gt (WithTop.coe_lt_coe.mpr (huT.trans_le hTS))
    convert htau u using 1
    ext omega
    simp only [extendBoundedStoppingTime, Set.mem_ofPred_eq]
    by_cases hlt : tau omega < (T : WithTop ℝ≥0)
    · rw [if_pos hlt]
    · have hTeq : tau omega = (T : WithTop ℝ≥0) :=
        le_antisymm (htauT omega) (le_of_not_gt hlt)
      rw [if_neg hlt, hTeq]
      exact iff_of_false hSu (not_le_of_gt (WithTop.coe_lt_coe.mpr huT))
  · by_cases hSu : S ≤ u
    · have hall : {omega | extendBoundedStoppingTime tau T S omega ≤ u} =
          Set.univ := by
        ext omega
        simp only [extendBoundedStoppingTime, Set.mem_ofPred_eq,
          Set.mem_univ, iff_true]
        by_cases hlt : tau omega < (T : WithTop ℝ≥0)
        · rw [if_pos hlt]
          exact (htauT omega).trans (WithTop.coe_le_coe.mpr hTu)
        · rw [if_neg hlt]
          exact WithTop.coe_le_coe.mpr hSu
      rw [hall]
      exact MeasurableSet.univ
    · have heq : {omega | extendBoundedStoppingTime tau T S omega ≤ u} =
          {omega | tau omega < (T : WithTop ℝ≥0)} := by
        ext omega
        simp only [extendBoundedStoppingTime, Set.mem_ofPred_eq]
        by_cases hlt : tau omega < (T : WithTop ℝ≥0)
        · rw [if_pos hlt]
          exact iff_of_true
            ((htauT omega).trans (WithTop.coe_le_coe.mpr hTu)) hlt
        · rw [if_neg hlt]
          exact iff_of_false
            (not_le_of_gt (WithTop.coe_lt_coe.mpr (lt_of_not_ge hSu))) hlt
      rw [heq]
      exact 𝓥.mono hTu _ (htau.measurableSet_lt T)

/-- If a process stays strictly inside the radius on the whole horizon,
its bounded continuous exit time is the terminal horizon. -/
theorem continuousExitTime_eq_terminal_of_norm_lt
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W)
    (hbound : ∀ t, t ≤ T → |Z t omega| < R) :
    continuousExitTime Z T R omega = T := by
  have hdyadic : ∀ n, dyadicHittingTimeNNReal Z T R n omega = T := by
    intro n
    have hnone : ¬∃ j ∈ Set.Icc 0 (2 ^ n),
        uniformPartitionSample Z T (2 ^ n) j omega ∈
          outsideClosedBall R := by
      rintro ⟨j, hj, hjout⟩
      have hjT : uniformPartitionTime T (2 ^ n) j ≤ T :=
        (uniformPartitionTime_mem_Icc_of_le T (by positivity) hj.2).2
      have hin := hbound (uniformPartitionTime T (2 ^ n) j) hjT
      exact (not_le_of_gt hin) hjout
    unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
      uniformPartitionHittingTime
    rw [show hittingBtwn (uniformPartitionSample Z T (2 ^ n))
        (outsideClosedBall R) 0 (2 ^ n) omega = 2 ^ n by
      unfold hittingBtwn
      rw [if_neg hnone]]
    change (uniformPartitionTime T (2 ^ n) (2 ^ n) : WithTop ℝ≥0) = T
    apply WithTop.coe_eq_coe.mpr
    unfold uniformPartitionTime
    apply mul_div_cancel_right₀
    exact_mod_cast (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  unfold continuousExitTime
  simp_rw [hdyadic]
  exact iInf_const

/-- The radius-`n+1` exit on `[0,T]`, extended to `T+n+1` when no exit
occurs, is the canonical continuous-exit exhaustion. -/
noncomputable def continuousExitLocalizingSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T : ℝ≥0) :
    ℕ → W → WithTop ℝ≥0 :=
  fun n => extendBoundedStoppingTime
    (continuousExitTime Z T (n + 1)) T (T + (n + 1))

/-- Each member of the continuous-exit exhaustion is a stopping time. -/
theorem isStoppingTime_continuousExitLocalizingSequence
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {Z : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝓥 Z) (T : ℝ≥0)
    (n : ℕ) :
    IsStoppingTime 𝓥 (continuousExitLocalizingSequence Z T n) := by
  apply isStoppingTime_extendBoundedStoppingTime
    (isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T (n + 1))
  · exact continuousExitTime_le Z T (n + 1)
  · exact le_add_right le_rfl

/-- The continuous-exit exhaustion is pointwise increasing. -/
theorem monotone_continuousExitLocalizingSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    Monotone (fun n => continuousExitLocalizingSequence Z T n omega) := by
  intro n m hnm
  let tauN := continuousExitTime Z T (n + 1) omega
  let tauM := continuousExitTime Z T (m + 1) omega
  have htau : tauN ≤ tauM :=
    continuousExitTime_mono_radius Z T (n + 1) (m + 1)
      (by exact_mod_cast Nat.add_le_add_right hnm 1) omega
  have hnAdd : (T + (n + 1) : ℝ≥0) ≤ T + (m + 1) := by
    gcongr
  unfold continuousExitLocalizingSequence extendBoundedStoppingTime
  change (if tauN < (T : WithTop ℝ≥0) then tauN else T + (n + 1)) ≤
    if tauM < (T : WithTop ℝ≥0) then tauM else T + (m + 1)
  by_cases hn : tauN < (T : WithTop ℝ≥0)
  · rw [if_pos hn]
    by_cases hm : tauM < (T : WithTop ℝ≥0)
    · rw [if_pos hm]
      exact htau
    · rw [if_neg hm]
      exact hn.le.trans (WithTop.coe_le_coe.mpr (le_add_right le_rfl))
  · rw [if_neg hn]
    have hnEq : tauN = (T : WithTop ℝ≥0) :=
      le_antisymm (continuousExitTime_le Z T (n + 1) omega)
        (le_of_not_gt hn)
    have hmEq : tauM = (T : WithTop ℝ≥0) :=
      le_antisymm (continuousExitTime_le Z T (m + 1) omega)
        (hnEq ▸ htau)
    rw [if_neg (not_lt.mpr hmEq.ge)]
    exact WithTop.coe_le_coe.mpr hnAdd

/-- Every extended continuous-exit localizer is bounded by its advertised
deterministic extension time. -/
theorem continuousExitLocalizingSequence_le
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W) :
    continuousExitLocalizingSequence Z T n omega ≤ T + (n + 1) := by
  unfold continuousExitLocalizingSequence extendBoundedStoppingTime
  by_cases h : continuousExitTime Z T (n + 1) omega <
      (T : WithTop ℝ≥0)
  · rw [if_pos h]
    exact h.le.trans (WithTop.coe_le_coe.mpr (le_add_right le_rfl))
  · rw [if_neg h]
    exact WithTop.coe_le_coe.mpr le_rfl

/-- Along every continuous path, the continuous-exit exhaustion tends to
infinity. -/
theorem tendsto_continuousExitLocalizingSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W)
    (hZcont : Continuous (fun t => Z t omega)) :
    Tendsto (fun n => continuousExitLocalizingSequence Z T n omega)
      Filter.atTop (𝓝 ⊤) := by
  have hAbs : Continuous (fun t => |Z t omega|) := continuous_abs.comp hZcont
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hAbs.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  have hexit : ∀ᶠ n : ℕ in Filter.atTop,
      continuousExitTime Z T (n + 1) omega = T := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply continuousExitTime_eq_terminal_of_norm_lt
    intro t ht
    have hCt : |Z t omega| ≤ C := hC ⟨t, ⟨bot_le, ht⟩, rfl⟩
    calc
      |Z t omega| ≤ C := hCt
      _ ≤ (N : ℝ) := hN
      _ < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
      _ = ((n + 1 : ℝ≥0) : ℝ) := by norm_num
  have hseq : ∀ᶠ n : ℕ in Filter.atTop,
      continuousExitLocalizingSequence Z T n omega =
        ((T + (n + 1) : ℝ≥0) : WithTop ℝ≥0) := by
    filter_upwards [hexit] with n hn
    unfold continuousExitLocalizingSequence extendBoundedStoppingTime
    rw [hn, if_neg (lt_irrefl _)]
  have hbase : Tendsto (fun n : ℕ => (T + (n + 1) : ℝ≥0))
      Filter.atTop Filter.atTop := by
    rw [tendsto_atTop]
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    calc
      b ≤ (N : ℝ≥0) := hN
      _ ≤ n := by exact_mod_cast hn
      _ ≤ (n + 1 : ℝ≥0) := le_add_right le_rfl
      _ ≤ T + (n + 1) := le_add_left le_rfl
  have hseq' : (fun n : ℕ => ((T + (n + 1) : ℝ≥0) : WithTop ℝ≥0))
      =ᶠ[Filter.atTop]
      (fun n => continuousExitLocalizingSequence Z T n omega) := by
    filter_upwards [hseq] with n hn
    exact hn.symm
  exact (WithTop.tendsto_coe_atTop.comp hbase).congr' hseq'

/-- Continuous adapted processes admit a canonical localizing sequence
built from their increasing-radius bounded exits. -/
theorem isLocalizingSequence_continuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {Z : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝓥 Z)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega)) (T : ℝ≥0) :
    IsLocalizingSequence 𝓥 (continuousExitLocalizingSequence Z T) P where
  isStoppingTime n :=
    isStoppingTime_continuousExitLocalizingSequence hZ T n
  mono := Filter.Eventually.of_forall
    (monotone_continuousExitLocalizingSequence Z T)
  tendsto_top := Filter.Eventually.of_forall fun omega =>
    tendsto_continuousExitLocalizingSequence Z T omega (hZcont omega)

/-- The pointwise minimum of the continuous-exit exhaustions for two
controllers localizes both processes simultaneously. -/
noncomputable def pairedContinuousExitLocalizingSequence
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T : ℝ≥0) :
    ℕ → W → WithTop ℝ≥0 :=
  fun n omega => min (continuousExitLocalizingSequence Z T n omega)
    (continuousExitLocalizingSequence Q T n omega)

/-- The paired continuous-exit localizer has the same deterministic bound. -/
theorem pairedContinuousExitLocalizingSequence_le
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    pairedContinuousExitLocalizingSequence Z Q T n omega ≤ T + (n + 1) := by
  exact (min_le_left _ _).trans
    (continuousExitLocalizingSequence_le Z T n omega)

/-- Two continuous adapted controllers admit a common continuous-exit
localizing sequence. -/
theorem isLocalizingSequence_pairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {Z Q : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝓥 Z)
    (hQ : StronglyAdapted 𝓥 Q)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hQcont : ∀ omega, Continuous (fun t => Q t omega)) (T : ℝ≥0) :
    IsLocalizingSequence 𝓥
      (pairedContinuousExitLocalizingSequence Z Q T) P := by
  exact (isLocalizingSequence_continuousExit hZ hZcont T).min
    (isLocalizingSequence_continuousExit hQ hQcont T)

/-- Dropping the first paired exit gives the radius-`n+2` exhaustion.  This
shift is convenient when a normalized stochastic exponential starts exactly
on the radius-one boundary. -/
noncomputable def shiftedPairedContinuousExitLocalizingSequence
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T : ℝ≥0) :
    ℕ → W → WithTop ℝ≥0 :=
  fun n => pairedContinuousExitLocalizingSequence Z Q T (n + 1)

/-- The shifted paired continuous-exit exhaustion is still a localizing
sequence. -/
theorem isLocalizingSequence_shiftedPairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {Z Q : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝒱 Z)
    (hQ : StronglyAdapted 𝒱 Q)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hQcont : ∀ omega, Continuous (fun t => Q t omega)) (T : ℝ≥0) :
    IsLocalizingSequence 𝒱
      (shiftedPairedContinuousExitLocalizingSequence Z Q T) P := by
  have hbase := isLocalizingSequence_pairedContinuousExit (P := P)
    hZ hQ hZcont hQcont T
  refine {
    isStoppingTime := fun n => hbase.isStoppingTime (n + 1)
    mono := ?_
    tendsto_top := ?_ }
  · filter_upwards [hbase.tendsto_top] with omega homega
    exact homega.comp (tendsto_add_atTop_nat 1)
  · filter_upwards [hbase.mono] with omega homega
    exact homega.comp (fun _ _ h => Nat.add_le_add_right h 1)

/-- The dyadic exit rules converge to the continuous exit rule. -/
theorem tendsto_dyadicHittingTimeNNReal_continuousExitTime
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (omega : W) :
    Tendsto (fun n => dyadicHittingTimeNNReal M T R n omega)
      Filter.atTop (𝓝 (continuousExitTime M T R omega)) := by
  exact tendsto_atTop_iInf (antitone_dyadicHittingTimeNNReal M T R omega)

/-- Paired dyadic exits converge pointwise to the minimum of the two
continuous exits. -/
theorem tendsto_pairedDyadicHittingTimeNNReal_continuousExitTime
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (omega : W) :
    Tendsto (fun n => pairedDyadicHittingTimeNNReal Z Q T R S n omega)
      Filter.atTop
      (nhds (min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega))) := by
  exact (tendsto_dyadicHittingTimeNNReal_continuousExitTime
    Z T R omega).min
      (tendsto_dyadicHittingTimeNNReal_continuousExitTime Q T S omega)

/-- Capping paired dyadic exits by a pair of larger-radius continuous exits
does not change their limit.  This outer-exit sandwich is useful for keeping
dyadic overshoots uniformly bounded. -/
theorem tendsto_pairedDyadic_min_outerContinuousExit
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ)
    (T R S R' S' : ℝ≥0) (hRR' : R ≤ R') (hSS' : S ≤ S')
    (omega : W) :
    Tendsto
      (fun n => min (pairedDyadicHittingTimeNNReal Z Q T R S n omega)
        (min (continuousExitTime Z T R' omega)
          (continuousExitTime Q T S' omega)))
      Filter.atTop
      (nhds (min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega))) := by
  have houter :
      min (continuousExitTime Z T R omega)
          (continuousExitTime Q T S omega) ≤
        min (continuousExitTime Z T R' omega)
          (continuousExitTime Q T S' omega) :=
    min_le_min (continuousExitTime_mono_radius Z T R R' hRR' omega)
      (continuousExitTime_mono_radius Q T S S' hSS' omega)
  have hlimit : Tendsto
      (fun n => min (pairedDyadicHittingTimeNNReal Z Q T R S n omega)
        (min (continuousExitTime Z T R' omega)
          (continuousExitTime Q T S' omega)))
      Filter.atTop
      (nhds (min
        (min (continuousExitTime Z T R omega)
          (continuousExitTime Q T S omega))
        (min (continuousExitTime Z T R' omega)
          (continuousExitTime Q T S' omega)))) :=
    (tendsto_pairedDyadicHittingTimeNNReal_continuousExitTime
      Z Q T R S omega).min
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => min (continuousExitTime Z T R' omega)
            (continuousExitTime Q T S' omega)) Filter.atTop
          (nhds (min (continuousExitTime Z T R' omega)
            (continuousExitTime Q T S' omega))))
  simpa only [min_eq_left houter] using hlimit

/-- The left dyadic-grid approximation of a time in `[0, T]` lies no later
than that time. -/
theorem uniformPartitionTime_dyadicApproxIndex_le
    {s T : ℝ≥0} (hst : s ≤ T) (n : ℕ) :
    uniformPartitionTime T (2 ^ n) (dyadicApproxIndex s T n) ≤ s := by
  by_cases hT : T = 0
  · have hs : s = 0 := le_antisymm (hT ▸ hst) bot_le
    subst T
    subst s
    simp [uniformPartitionTime]
  rw [← NNReal.coe_le_coe]
  have hTpos : (0 : ℝ) < (T : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hnonneg : 0 ≤ (s : ℝ) / (T : ℝ) * (2 : ℝ) ^ n :=
    mul_nonneg (div_nonneg (NNReal.coe_nonneg s) hTpos.le) (by positivity)
  have hfloor := Nat.floor_le hnonneg
  simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, Nat.cast_pow, Nat.cast_ofNat, dyadicApproxIndex]
  calc
    (T : ℝ) * ↑⌊(s : ℝ) / (T : ℝ) * 2 ^ n⌋₊ / 2 ^ n ≤
        (T : ℝ) * (((s : ℝ) / (T : ℝ)) * 2 ^ n) / 2 ^ n := by
      gcongr
    _ = (s : ℝ) := by
      field_simp

/-- Along a continuous path, the process remains in the closed radius-`R`
ball at every time strictly before its dyadic continuous exit time. -/
theorem norm_le_of_lt_continuousExitTime
    {W : Type*} {Z : ℝ≥0 → W → ℝ}
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R s : ℝ≥0) (omega : W)
    (hs : (s : WithTop ℝ≥0) < continuousExitTime Z T R omega) :
    |Z s omega| ≤ R := by
  have hsT : s ≤ T := by
    exact WithTop.coe_le_coe.mp
      (hs.le.trans (continuousExitTime_le Z T R omega))
  let q : ℕ → ℝ≥0 := fun n =>
    uniformPartitionTime T (2 ^ n) (dyadicApproxIndex s T n)
  have hq_le (n : ℕ) : q n ≤ s :=
    uniformPartitionTime_dyadicApproxIndex_le hsT n
  have hq_not_mem (n : ℕ) : Z (q n) omega ∉ outsideClosedBall R := by
    intro hmem
    let k := dyadicApproxIndex s T n
    have hk : k ≤ 2 ^ n := dyadicApproxIndex_le_pow hsT n
    have hindex : hittingBtwn (uniformPartitionSample Z T (2 ^ n))
        (outsideClosedBall R) 0 (2 ^ n) omega ≤ k := by
      apply hittingBtwn_le_of_mem (n := 0) (m := 2 ^ n)
      · exact bot_le
      · exact hk
      · exact hmem
    have htime : dyadicHittingTimeNNReal Z T R n omega ≤ q n := by
      unfold dyadicHittingTimeNNReal
      unfold uniformPartitionHittingTimeNNReal uniformPartitionHittingTime
      exact_mod_cast
        (monotone_uniformPartitionTime_general T (2 ^ n) hindex)
    have hexit_le : continuousExitTime Z T R omega ≤
        dyadicHittingTimeNNReal Z T R n omega := iInf_le _ n
    have : continuousExitTime Z T R omega ≤ s :=
      hexit_le.trans (htime.trans (mod_cast hq_le n))
    exact (not_le_of_gt hs) this
  have hq_abs (n : ℕ) : |Z (q n) omega| ≤ R := by
    exact le_of_not_ge (hq_not_mem n)
  have hq_tendsto : Tendsto q Filter.atTop (𝓝 s) :=
    tendsto_uniformPartitionTime_dyadicApproxIndex hsT
  have habs_tendsto : Tendsto (fun n => |Z (q n) omega|)
      Filter.atTop (𝓝 |Z s omega|) :=
    continuous_abs.continuousAt.tendsto.comp
      ((hZcont omega).continuousAt.tendsto.comp hq_tendsto)
  exact le_of_tendsto habs_tendsto
    (Filter.Eventually.of_forall hq_abs)

/-- A continuous path is still within the radius at a positive exit time.
This follows by taking the closure of the times strictly before the exit. -/
theorem norm_at_continuousExitTime_le
    {W : Type*} {Z : ℝ≥0 → W → ℝ}
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R : ℝ≥0) (omega : W)
    (hpos : (⊥ : WithTop ℝ≥0) < continuousExitTime Z T R omega) :
    |Z (continuousExitTime Z T R omega).untopA omega| ≤ R := by
  let tau := continuousExitTime Z T R omega
  have hne : tau ≠ ⊤ := continuousExitTime_ne_top Z T R omega
  let a : ℝ≥0 := tau.untopA
  have hcoe : (a : WithTop ℝ≥0) = tau := by
    dsimp only [a]
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_untop tau hne
  have ha0 : 0 < a := by
    apply WithTop.coe_lt_coe.mp
    rw [hcoe]
    simpa using hpos
  let C : Set ℝ≥0 := {s | |Z s omega| ≤ (R : ℝ)}
  have hCclosed : IsClosed C := by
    exact isClosed_le (hZcont omega).abs continuous_const
  have hsub : Set.Iio a ⊆ C := by
    intro s hs
    have hsa : s < a := hs
    exact norm_le_of_lt_continuousExitTime hZcont T R s omega
      (by change (s : WithTop ℝ≥0) < tau
          rw [← hcoe]
          exact WithTop.coe_lt_coe.mpr hsa)
  have haClosure : a ∈ closure (Set.Iio a) := by
    have hc : closure (Set.Iio a) = Set.Iic a :=
      closure_Iio' ⟨0, ha0⟩
    rw [hc]
    exact Set.mem_Iic.mpr le_rfl
  exact closure_minimal hsub hCclosed haClosure

/-- If a path stays strictly inside the exit radius before `u ≤ T`, then
the dyadic continuous exit cannot occur before `u`. -/
theorem le_continuousExitTime_of_norm_lt
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R u : ℝ≥0) (omega : W)
    (huT : u ≤ T) (hbound : ∀ s, s < u → |Z s omega| < R) :
    (u : WithTop ℝ≥0) ≤ continuousExitTime Z T R omega := by
  have hdyadic (n : ℕ) : (u : WithTop ℝ≥0) ≤
      dyadicHittingTimeNNReal Z T R n omega := by
    by_contra hnot
    have hhitU : dyadicHittingTimeNNReal Z T R n omega < u :=
      lt_of_not_ge hnot
    let j := hittingBtwn (uniformPartitionSample Z T (2 ^ n))
      (outsideClosedBall R) 0 (2 ^ n) omega
    have hjle : j ≤ 2 ^ n := hittingBtwn_le omega
    have hjne : j ≠ 2 ^ n := by
      intro hj
      have htimeT : dyadicHittingTimeNNReal Z T R n omega = T := by
        unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
          uniformPartitionHittingTime
        change (uniformPartitionTime T (2 ^ n) j : WithTop ℝ≥0) = T
        rw [hj]
        exact_mod_cast mul_div_cancel_right₀ T
          (by positivity : (2 ^ n : ℝ≥0) ≠ 0)
      rw [htimeT] at hhitU
      exact (not_lt_of_ge (WithTop.coe_le_coe.mpr huT)) hhitU
    have hjlt : j < 2 ^ n := lt_of_le_of_ne hjle hjne
    have hjout : uniformPartitionSample Z T (2 ^ n) j omega ∈
        outsideClosedBall R :=
      hittingBtwn_mem_set_of_hittingBtwn_lt hjlt
    have htimeIn :
        |Z (uniformPartitionTime T (2 ^ n) j) omega| < R := by
      apply hbound
      apply WithTop.coe_lt_coe.mp
      change (uniformPartitionTime T (2 ^ n) j : WithTop ℝ≥0) < u
      exact hhitU
    exact (not_le_of_gt htimeIn) hjout
  unfold continuousExitTime
  exact le_iInf hdyadic

/-- For a positive continuous exit that occurs before the terminal horizon,
strictly enlarging the radius strictly delays the exit. -/
theorem continuousExitTime_lt_of_radius_lt_of_lt_terminal
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (omega : W)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hpos : (⊥ : WithTop ℝ≥0) < continuousExitTime Z T R omega)
    (hRS : R < S)
    (htauT : continuousExitTime Z T R omega < (T : WithTop ℝ≥0)) :
    continuousExitTime Z T R omega < continuousExitTime Z T S omega := by
  let tau := continuousExitTime Z T R omega
  have htau_ne : tau ≠ ⊤ := continuousExitTime_ne_top Z T R omega
  let a : ℝ≥0 := tau.untopA
  have hcoe : (a : WithTop ℝ≥0) = tau := by
    dsimp only [a]
    rw [WithTop.untopA_eq_untop htau_ne]
    exact WithTop.coe_untop tau htau_ne
  have haT : a < T := by
    apply WithTop.coe_lt_coe.mp
    rw [hcoe]
    exact htauT
  have hata : |Z a omega| ≤ R :=
    norm_at_continuousExitTime_le hZcont T R omega hpos
  have hgap : 0 < (S : ℝ) - |Z a omega| := by
    have hRSreal : (R : ℝ) < (S : ℝ) := by exact_mod_cast hRS
    linarith
  have hcontAt : ContinuousAt (fun t => |Z t omega|) a :=
    (continuous_abs.comp (hZcont omega)).continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨delta, hdelta, hclose⟩ :=
    hcontAt ((S : ℝ) - |Z a omega|) hgap
  let bReal : ℝ := min ((T : ℝ) - (a : ℝ)) delta / 2
  have hbReal : 0 < bReal := by
    dsimp only [bReal]
    have : (a : ℝ) < (T : ℝ) := by exact_mod_cast haT
    positivity
  let b : ℝ≥0 := ⟨bReal, hbReal.le⟩
  let u : ℝ≥0 := a + b
  have hab : a < u := by
    dsimp only [u]
    exact lt_add_of_pos_right a (NNReal.coe_pos.mp hbReal)
  have huT : u ≤ T := by
    rw [← NNReal.coe_le_coe]
    dsimp only [u, b, bReal]
    change (a : ℝ) + min ((T : ℝ) - (a : ℝ)) delta / 2 ≤ T
    have hmin : min ((T : ℝ) - (a : ℝ)) delta ≤
        (T : ℝ) - (a : ℝ) := min_le_left _ _
    have hminPos : 0 < min ((T : ℝ) - (a : ℝ)) delta := by
      have : (a : ℝ) < (T : ℝ) := by exact_mod_cast haT
      positivity
    linarith
  have hbDelta : (b : ℝ) < delta := by
    dsimp only [b, bReal]
    change min ((T : ℝ) - (a : ℝ)) delta / 2 < delta
    have hmin : min ((T : ℝ) - (a : ℝ)) delta ≤ delta :=
      min_le_right _ _
    have hminPos : 0 < min ((T : ℝ) - (a : ℝ)) delta := by
      have : (a : ℝ) < (T : ℝ) := by exact_mod_cast haT
      positivity
    linarith
  have hubound : ∀ q, q < u → |Z q omega| < S := by
    intro q hqu
    rcases lt_or_ge q a with hqa | haq
    · have hqnorm := norm_le_of_lt_continuousExitTime
        hZcont T R q omega (by
          change (q : WithTop ℝ≥0) < tau
          rw [← hcoe]
          exact WithTop.coe_lt_coe.mpr hqa)
      exact hqnorm.trans_lt (by exact_mod_cast hRS)
    · by_cases hqaEq : q = a
      · rw [hqaEq]
        exact hata.trans_lt (by exact_mod_cast hRS)
      · have haq' : a < q := lt_of_le_of_ne haq (Ne.symm hqaEq)
        have hdist : dist q a < delta := by
          rw [NNReal.dist_eq]
          change ‖(q : ℝ) - (a : ℝ)‖ < delta
          rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (by
            exact_mod_cast haq))]
          have hquReal : (q : ℝ) < (u : ℝ) := by exact_mod_cast hqu
          have huReal : (u : ℝ) = (a : ℝ) + (b : ℝ) := by rfl
          rw [huReal] at hquReal
          linarith
        have hdistZ := hclose hdist
        rw [Real.dist_eq] at hdistZ
        have hle : |Z q omega| - |Z a omega| ≤
            abs (|Z q omega| - |Z a omega|) := le_abs_self _
        linarith
  have huExit : (u : WithTop ℝ≥0) ≤
      continuousExitTime Z T S omega :=
    le_continuousExitTime_of_norm_lt Z T S u omega huT hubound
  have htauu : tau < (u : WithTop ℝ≥0) := by
    rw [← hcoe]
    exact WithTop.coe_lt_coe.mpr hab
  exact htauu.trans_le huExit

/-- For continuous paths, a dyadic exit at a strictly smaller radius is
eventually no later than the larger-radius continuous exit. -/
theorem eventually_dyadicHittingTimeNNReal_le_continuousExitTime_of_lt_radius
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0) (omega : W)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hpos : (⊥ : WithTop ℝ≥0) < continuousExitTime Z T R omega)
    (hRS : R < S) :
    ∀ᶠ n in Filter.atTop,
      dyadicHittingTimeNNReal Z T R n omega ≤
        continuousExitTime Z T S omega := by
  by_cases htauT : continuousExitTime Z T R omega < (T : WithTop ℝ≥0)
  · have hstrict := continuousExitTime_lt_of_radius_lt_of_lt_terminal
      Z T R S omega hZcont hpos hRS htauT
    exact ((tendsto_dyadicHittingTimeNNReal_continuousExitTime
      Z T R omega).eventually (Iio_mem_nhds hstrict)).mono
        (fun _ hn => hn.le)
  · have heqR : continuousExitTime Z T R omega = (T : WithTop ℝ≥0) :=
      le_antisymm (continuousExitTime_le Z T R omega) (le_of_not_gt htauT)
    have heqS : continuousExitTime Z T S omega = (T : WithTop ℝ≥0) := by
      apply le_antisymm (continuousExitTime_le Z T S omega)
      rw [← heqR]
      exact continuousExitTime_mono_radius Z T R S hRS.le omega
    exact Filter.Eventually.of_forall fun n => by
      rw [heqS]
      exact dyadicHittingTimeNNReal_le Z T R n omega

/-- Doubling both the horizon and the dyadic mesh count preserves every old
grid point, so increasing the exit radius can only delay the discrete exit. -/
theorem dyadicHittingTimeNNReal_le_double_horizon_succ
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0)
    (hRS : R ≤ S) (m : ℕ) (omega : W) :
    dyadicHittingTimeNNReal Z T R m omega ≤
      dyadicHittingTimeNNReal Z (T + T) S (m + 1) omega := by
  let uL := uniformPartitionSample Z T (2 ^ m)
  let uR := uniformPartitionSample Z (T + T) (2 ^ (m + 1))
  let hL := hittingBtwn uL (outsideClosedBall R) 0 (2 ^ m) omega
  let hR := hittingBtwn uR (outsideClosedBall S) 0 (2 ^ (m + 1)) omega
  have hsample (j : ℕ) : uR j omega = uL j omega := by
    dsimp only [uR, uL, uniformPartitionSample]
    apply congrArg (fun t => Z t omega)
    unfold uniformPartitionTime
    rw [pow_succ]
    norm_num
    ring
  by_cases hj : hR ≤ 2 ^ m
  · have hRlt : hR < 2 ^ (m + 1) := by
      have hp : 0 < 2 ^ m := by positivity
      rw [pow_succ]
      omega
    have hmemS : uR hR omega ∈ outsideClosedBall S :=
      hittingBtwn_mem_set_of_hittingBtwn_lt hRlt
    have hmemR : uL hR omega ∈ outsideClosedBall R := by
      change (R : ℝ) ≤ |uL hR omega|
      change (S : ℝ) ≤ |uR hR omega| at hmemS
      rw [hsample] at hmemS
      have hRSreal : (R : ℝ) ≤ (S : ℝ) := by exact_mod_cast hRS
      exact hRSreal.trans hmemS
    have hindex : hL ≤ hR :=
      hittingBtwn_le_of_mem bot_le hj hmemR
    unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
      uniformPartitionHittingTime
    change (uniformPartitionTime T (2 ^ m) hL : WithTop ℝ≥0) ≤
      (uniformPartitionTime (T + T) (2 ^ (m + 1)) hR : WithTop ℝ≥0)
    apply WithTop.coe_le_coe.mpr
    calc
      uniformPartitionTime T (2 ^ m) hL ≤
          uniformPartitionTime T (2 ^ m) hR :=
        monotone_uniformPartitionTime_general T (2 ^ m) hindex
      _ = uniformPartitionTime (T + T) (2 ^ (m + 1)) hR := by
        unfold uniformPartitionTime
        rw [pow_succ]
        norm_num
        ring
  · have hj' : 2 ^ m ≤ hR := le_of_not_ge hj
    unfold dyadicHittingTimeNNReal uniformPartitionHittingTimeNNReal
      uniformPartitionHittingTime
    change (uniformPartitionTime T (2 ^ m) hL : WithTop ℝ≥0) ≤
      (uniformPartitionTime (T + T) (2 ^ (m + 1)) hR : WithTop ℝ≥0)
    apply WithTop.coe_le_coe.mpr
    calc
      uniformPartitionTime T (2 ^ m) hL ≤ T :=
        (uniformPartitionTime_mem_Icc_of_le T (by positivity)
          (hittingBtwn_le omega)).2
      _ = uniformPartitionTime (T + T) (2 ^ (m + 1)) (2 ^ m) := by
        unfold uniformPartitionTime
        rw [pow_succ]
        norm_num
        field_simp
        ring
      _ ≤ uniformPartitionTime (T + T) (2 ^ (m + 1)) hR :=
        monotone_uniformPartitionTime_general (T + T) (2 ^ (m + 1)) hj'

/-- A larger-radius continuous exit over twice the horizon is no earlier than
the original continuous exit. -/
theorem continuousExitTime_le_double_horizon
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R S : ℝ≥0)
    (hRS : R ≤ S) (omega : W) :
    continuousExitTime Z T R omega ≤
      continuousExitTime Z (T + T) S omega := by
  unfold continuousExitTime
  apply le_iInf
  intro m
  calc
    ⨅ n, dyadicHittingTimeNNReal Z T R n omega ≤
        dyadicHittingTimeNNReal Z T R m omega := iInf_le _ m
    _ ≤ dyadicHittingTimeNNReal Z (T + T) S (m + 1) omega :=
      dyadicHittingTimeNNReal_le_double_horizon_succ
        Z T R S hRS m omega
    _ ≤ dyadicHittingTimeNNReal Z (T + T) S m omega :=
      antitone_dyadicHittingTimeNNReal Z (T + T) S omega
        (Nat.le_succ m)

/-- Continuous exits along exponentially growing horizons and linearly
growing radii. -/
noncomputable def globalContinuousExitSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ) :
    ℕ → W → WithTop ℝ≥0 :=
  fun n => continuousExitTime Z (2 ^ n) (n + 2)

theorem monotone_globalContinuousExitSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (omega : W) :
    Monotone (fun n => globalContinuousExitSequence Z n omega) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold globalContinuousExitSequence
  have hradius : ((n : ℕ) : ℝ≥0) + 2 ≤ (((n + 1 : ℕ) : ℝ≥0) + 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    gcongr
    exact le_add_of_nonneg_right zero_le_one
  have h := continuousExitTime_le_double_horizon
    Z (2 ^ n) (((n : ℕ) : ℝ≥0) + 2)
      (((n + 1 : ℕ) : ℝ≥0) + 2) hradius omega
  simpa [pow_succ, mul_two] using h

/-- For a continuous path, the growing-horizon continuous exits tend to
infinity. -/
theorem tendsto_globalContinuousExitSequence
    {W : Type*} (Z : ℝ≥0 → W → ℝ)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega)) (omega : W) :
    Tendsto (fun n => globalContinuousExitSequence Z n omega)
      Filter.atTop (nhds ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro b
  let u : ℝ≥0 := b + 1
  have hbu : b < u := lt_add_one b
  have hAbs : Continuous (fun t => |Z t omega|) :=
    continuous_abs.comp (hZcont omega)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hAbs.continuousOn
  have hpow : ∀ᶠ n : ℕ in Filter.atTop, u ≤ (2 : ℝ≥0) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ≥0) < 2 by norm_num)).eventually_ge_atTop u
  have hradius : ∀ᶠ n : ℕ in Filter.atTop,
      C < ((((n : ℕ) : ℝ≥0) + 2 : ℝ≥0) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt C
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn2 : N ≤ n + 2 := hn.trans (Nat.le_add_right n 2)
    exact hN.trans_le (by exact_mod_cast hNn2)
  filter_upwards [hpow, hradius] with n hnu hnC
  have hbound : ∀ s, s < u →
      |Z s omega| < ((((n : ℕ) : ℝ≥0) + 2 : ℝ≥0) : ℝ) := by
    intro s hsu
    have hsIcc : s ∈ Set.Icc (0 : ℝ≥0) u := ⟨bot_le, hsu.le⟩
    have hsC : |Z s omega| ≤ C := hC ⟨s, hsIcc, rfl⟩
    exact hsC.trans_lt hnC
  have huexit : (u : WithTop ℝ≥0) ≤
      globalContinuousExitSequence Z n omega := by
    unfold globalContinuousExitSequence
    exact le_continuousExitTime_of_norm_lt Z (2 ^ n)
      (((n : ℕ) : ℝ≥0) + 2)
      u omega hnu hbound
  exact (WithTop.coe_lt_coe.mpr hbu).trans_le huexit

/-- The growing-horizon exits of a continuous adapted process form a
localizing sequence on the whole time axis. -/
theorem isLocalizingSequence_globalContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {Z : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝒱 Z)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega)) :
    IsLocalizingSequence 𝒱 (globalContinuousExitSequence Z) P where
  isStoppingTime n :=
    isStoppingTime_continuousExitTime_of_stronglyAdapted hZ (2 ^ n) (n + 2)
  mono := Filter.Eventually.of_forall fun omega =>
    monotone_globalContinuousExitSequence Z omega
  tendsto_top := Filter.Eventually.of_forall fun omega =>
    tendsto_globalContinuousExitSequence Z hZcont omega

/-- The minimum of two growing-horizon continuous-exit sequences. -/
noncomputable def globalPairedContinuousExitSequence
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ) :
    ℕ → W → WithTop ℝ≥0 :=
  fun n omega => min (globalContinuousExitSequence Z n omega)
    (globalContinuousExitSequence Q n omega)

/-- Two continuous adapted controllers admit a common global continuous-exit
localizing sequence. -/
theorem isLocalizingSequence_globalPairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {Z Q : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝒱 Z)
    (hQ : StronglyAdapted 𝒱 Q)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hQcont : ∀ omega, Continuous (fun t => Q t omega)) :
    IsLocalizingSequence 𝒱
      (globalPairedContinuousExitSequence Z Q) P := by
  exact (isLocalizingSequence_globalContinuousExit hZ hZcont).min
    (isLocalizingSequence_globalContinuousExit hQ hQcont)

/-- Paired smaller-radius dyadic exits are eventually no later than the
corresponding pair of strictly larger continuous exits. -/
theorem eventually_pairedDyadicHittingTimeNNReal_le_outerContinuousExit
    {W : Type*} (Z Q : ℝ≥0 → W → ℝ)
    (T R S R' S' : ℝ≥0) (omega : W)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hQcont : ∀ omega, Continuous (fun t => Q t omega))
    (hpos : (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega))
    (hRR' : R < R') (hSS' : S < S') :
    ∀ᶠ n in Filter.atTop,
      pairedDyadicHittingTimeNNReal Z Q T R S n omega ≤
        min (continuousExitTime Z T R' omega)
          (continuousExitTime Q T S' omega) := by
  have hposZ : (⊥ : WithTop ℝ≥0) < continuousExitTime Z T R omega :=
    hpos.trans_le (min_le_left _ _)
  have hposQ : (⊥ : WithTop ℝ≥0) < continuousExitTime Q T S omega :=
    hpos.trans_le (min_le_right _ _)
  filter_upwards
    [eventually_dyadicHittingTimeNNReal_le_continuousExitTime_of_lt_radius
      Z T R R' omega hZcont hposZ hRR',
     eventually_dyadicHittingTimeNNReal_le_continuousExitTime_of_lt_radius
      Q T S S' omega hQcont hposQ hSS'] with n hZ hQ
  unfold pairedDyadicHittingTimeNNReal
  exact le_min ((min_le_left _ _).trans hZ) ((min_le_right _ _).trans hQ)

/-- The exceptional event on which a smaller-radius paired dyadic exit
overshoots the larger-radius continuous exits has probability tending to
zero. -/
theorem tendsto_measure_outerContinuousExit_lt_pairedDyadic
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {Z Q : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝒱 Z)
    (hQ : StronglyAdapted 𝒱 Q)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (hQcont : ∀ omega, Continuous (fun t => Q t omega))
    (T R S R' S' : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega))
    (hRR' : R < R') (hSS' : S < S') :
    Tendsto
      (fun n => P {omega |
        min (continuousExitTime Z T R' omega)
            (continuousExitTime Q T S' omega) <
          pairedDyadicHittingTimeNNReal Z Q T R S n omega})
      Filter.atTop (nhds 0) := by
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime Z T R' omega)
      (continuousExitTime Q T S' omega)
  let sigma : ℕ → W → WithTop ℝ≥0 :=
    pairedDyadicHittingTimeNNReal Z Q T R S
  have htheta : IsStoppingTime 𝒱 theta :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R').min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hQ T S')
  have hsigma (n : ℕ) : IsStoppingTime 𝒱 (sigma n) :=
    isStoppingTime_pairedDyadicHittingTimeNNReal hZ hQ T R S n
  have hmeas (n : ℕ) : MeasurableSet {omega | theta omega < sigma n omega} :=
    measurableSet_lt htheta.measurable' (hsigma n).measurable'
  have hlim : ∀ omega, ∀ᶠ n in Filter.atTop,
      (omega ∈ {omega | theta omega < sigma n omega} ↔
        omega ∈ (∅ : Set W)) := by
    intro omega
    filter_upwards
      [eventually_pairedDyadicHittingTimeNNReal_le_outerContinuousExit
        Z Q T R S R' S' omega hZcont hQcont (hpos omega) hRR' hSS']
      with n hn
    simp only [Set.notMem_empty, iff_false]
    exact not_lt_of_ge hn
  simpa only [theta, sigma, measure_empty] using
    (tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
      (A := (∅ : Set W)) Filter.atTop P hmeas hlim)

/-- A process killed at and after its bounded continuous exit time.  This is
the predictable-side coefficient used in stopped transform estimates. -/
def beforeContinuousExitProcessOf
    {W : Type*} (Z H : ℝ≥0 → W → ℝ) (T R : ℝ≥0) :
    ℝ≥0 → W → ℝ :=
  fun t => {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega}.indicator
    (H t)

/-- The before-exit process whose coefficient is the exit process itself. -/
def beforeContinuousExitProcess
    {W : Type*} (Z : ℝ≥0 → W → ℝ) (T R : ℝ≥0) :
    ℝ≥0 → W → ℝ :=
  fun t => {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega}.indicator
    (Z t)

/-- Killing one adapted process according to the continuous exit of another
adapted process preserves strong adaptation. -/
theorem stronglyAdapted_beforeContinuousExitProcessOf
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {Z H : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝓥 Z)
    (hH : StronglyAdapted 𝓥 H) (T R : ℝ≥0) :
    StronglyAdapted 𝓥 (beforeContinuousExitProcessOf Z H T R) := by
  have htau := isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R
  intro t
  have hset :
      {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} =
        {omega | continuousExitTime Z T R omega ≤
          (t : WithTop ℝ≥0)}ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [beforeContinuousExitProcessOf, hset]
  exact (hH t).indicator (htau t).compl

/-- A coefficient with a deterministic bound before another process exits
retains that bound after being killed at the exit. -/
theorem norm_beforeContinuousExitProcessOf_le
    {W : Type*} {Z H : ℝ≥0 → W → ℝ}
    (T R K : ℝ≥0)
    (hH : ∀ (t : ℝ≥0) omega,
      (t : WithTop ℝ≥0) < continuousExitTime Z T R omega →
        ‖H t omega‖ ≤ K)
    (t : ℝ≥0) (omega : W) :
    ‖beforeContinuousExitProcessOf Z H T R t omega‖ ≤ K := by
  by_cases h : (t : WithTop ℝ≥0) < continuousExitTime Z T R omega
  · unfold beforeContinuousExitProcessOf
    have hmem : omega ∈
        {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} := h
    rw [Set.indicator_of_mem hmem]
    exact hH t omega h
  · unfold beforeContinuousExitProcessOf
    have hmem : omega ∉
        {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} := h
    rw [Set.indicator_of_notMem hmem, norm_zero]
    exact K.coe_nonneg

/-- Killing an adapted process at and after its continuous exit preserves
strong adaptation. -/
theorem stronglyAdapted_beforeContinuousExitProcess
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝓥.IsRightContinuous]
    {Z : ℝ≥0 → W → ℝ} (hZ : StronglyAdapted 𝓥 Z)
    (T R : ℝ≥0) :
    StronglyAdapted 𝓥 (beforeContinuousExitProcess Z T R) := by
  have htau := isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R
  intro t
  have hset :
      {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} =
        {omega | continuousExitTime Z T R omega ≤
          (t : WithTop ℝ≥0)}ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [beforeContinuousExitProcess, hset]
  exact (hZ t).indicator (htau t).compl

/-- Before-exit coefficients have the deterministic radius bound. -/
theorem norm_beforeContinuousExitProcess_le
    {W : Type*} {Z : ℝ≥0 → W → ℝ}
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R t : ℝ≥0) (omega : W) :
    ‖beforeContinuousExitProcess Z T R t omega‖ ≤ R := by
  by_cases h : (t : WithTop ℝ≥0) < continuousExitTime Z T R omega
  · unfold beforeContinuousExitProcess
    have hmem : omega ∈
        {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} := h
    rw [Set.indicator_of_mem hmem, Real.norm_eq_abs]
    exact norm_le_of_lt_continuousExitTime hZcont T R t omega h
  · unfold beforeContinuousExitProcess
    have hmem : omega ∉
        {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega} := h
    rw [Set.indicator_of_notMem hmem, norm_zero]
    exact R.coe_nonneg

/-- Evaluating a continuous path at stopped times is continuous under
pointwise convergence of the stopping times. -/
theorem tendsto_stoppedProcess_of_tendsto_of_continuous
    {W : Type*} {X : ℝ≥0 → W → ℝ}
    {tauN : ℕ → W → WithTop ℝ≥0} {tau : W → WithTop ℝ≥0}
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (htau : ∀ omega, Tendsto (fun n => tauN n omega)
      Filter.atTop (nhds (tau omega))) (t : ℝ≥0) (omega : W) :
    Tendsto (fun n => stoppedProcess X (tauN n) t omega)
      Filter.atTop (nhds (stoppedProcess X tau t omega)) := by
  have htime : Tendsto
      (fun n => min (t : WithTop ℝ≥0) (tauN n omega))
      Filter.atTop
      (nhds (min (t : WithTop ℝ≥0) (tau omega))) :=
    tendsto_const_nhds.min (htau omega)
  have hne : min (t : WithTop ℝ≥0) (tau omega) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have huntop : Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (tauN n omega)).untopA)
      Filter.atTop
      (nhds ((min (t : WithTop ℝ≥0) (tau omega)).untopA)) :=
    (WithTop.tendsto_untopA hne).comp htime
  exact (hXcont omega).continuousAt.tendsto.comp huntop

/-- For a continuous path, stopping at the decreasing dyadic exit rules
converges pointwise to stopping at their continuous-time limit. -/
theorem
    tendsto_stoppedProcess_dyadicHittingTime_continuousExitTime_of_continuous
    {W : Type*} {M Z : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T R t : ℝ≥0) (omega : W) :
    Tendsto
      (fun n => stoppedProcess M (dyadicHittingTimeNNReal Z T R n) t omega)
      Filter.atTop
      (𝓝 (stoppedProcess M (continuousExitTime Z T R) t omega)) := by
  have htime : Tendsto
      (fun n => min (t : WithTop ℝ≥0)
        (dyadicHittingTimeNNReal Z T R n omega))
      Filter.atTop
      (𝓝 (min (t : WithTop ℝ≥0)
        (continuousExitTime Z T R omega))) :=
    tendsto_const_nhds.min
      (tendsto_dyadicHittingTimeNNReal_continuousExitTime Z T R omega)
  have hne : min (t : WithTop ℝ≥0)
      (continuousExitTime Z T R omega) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have huntop : Tendsto
      (fun n => (min (t : WithTop ℝ≥0)
        (dyadicHittingTimeNNReal Z T R n omega)).untopA)
      Filter.atTop
      (𝓝 ((min (t : WithTop ℝ≥0)
        (continuousExitTime Z T R omega)).untopA)) :=
    (WithTop.tendsto_untopA hne).comp htime
  exact (hMcont omega).continuousAt.tendsto.comp huntop

/-- The preceding convergence theorem specialized to exits of the stopped
process itself. -/
theorem tendsto_stoppedProcess_dyadicHittingTime_continuousExitTime
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T R t : ℝ≥0) (omega : W) :
    Tendsto
      (fun n => stoppedProcess M (dyadicHittingTimeNNReal M T R n) t omega)
      Filter.atTop
      (𝓝 (stoppedProcess M (continuousExitTime M T R) t omega)) :=
  tendsto_stoppedProcess_dyadicHittingTime_continuousExitTime_of_continuous
    hMcont T R t omega

/-- Stopping a uniformly sampled martingale at its first visit to a
measurable set gives a bounded square-integrable discrete martingale.  Only
the continuous-time terminal value at `T` is required to lie in `L²`. -/
theorem martingale_uniformPartitionSample_stoppedAtHittingTime
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (n : ℕ) (hMT : MemLp (M T) 2 P)
    {S : Set ℝ} (hS : MeasurableSet S) :
    Martingale
        (stoppedProcess (uniformPartitionSample M T (n + 1))
          (uniformPartitionHittingTime M T (n + 1) S))
        (uniformPartitionFiltration 𝓥 T (n + 1)) P ∧
      ∀ k, MemLp
        (stoppedProcess (uniformPartitionSample M T (n + 1))
          (uniformPartitionHittingTime M T (n + 1) S) k) 2 P := by
  let X := uniformPartitionSample M T (n + 1)
  let G := uniformPartitionFiltration 𝓥 T (n + 1)
  let tau := uniformPartitionHittingTime M T (n + 1) S
  have hX : Martingale X G P := martingale_uniformPartitionSample hM T (n + 1)
  have htau : IsStoppingTime G tau :=
    isStoppingTime_uniformPartitionHittingTime hM T (n + 1) hS
  have htaubdd : ∀ omega, tau omega ≤ (n + 1 : ℕ) := by
    intro omega
    dsimp only [tau, uniformPartitionHittingTime]
    exact_mod_cast (hittingBtwn_le (u := X) (s := S) (n := 0) omega)
  have hterminal : MemLp (X (n + 1)) 2 P := by
    have htime : uniformPartitionTime T (n + 1) (n + 1) = T := by
      unfold uniformPartitionTime
      exact mul_div_cancel_right₀ T (by positivity)
    simpa only [X, uniformPartitionSample, htime] using hMT
  exact martingale_stoppedProcess_nat_of_bdd_terminal
    hX htau (n + 1) htaubdd hterminal

/-- The elementary stochastic integral with coefficient `Z` on the
half-open deterministic interval `(a, b]`.  Stopping both endpoints at
`t` makes the process identically zero before `a`, equal to the weighted
martingale increment between `a` and `t` on the interval, and constant
after `b`. -/
def elementaryMartingaleIntegralProcess
    {W : Type*} (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  Z omega * (M (min t b) omega - M (min t a) omega)

/-- Elementary stochastic-integral processes inherit path continuity from
their integrator. -/
theorem continuous_elementaryMartingaleIntegralProcess
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (a b : ℝ≥0) (Z : W → ℝ) (omega : W) :
    Continuous (fun t =>
      elementaryMartingaleIntegralProcess M a b Z t omega) := by
  unfold elementaryMartingaleIntegralProcess
  exact continuous_const.mul
    (((hMcont omega).comp (continuous_id.min continuous_const)).sub
      ((hMcont omega).comp (continuous_id.min continuous_const)))

/-- Elementary predictable integrals preserve strong adaptation without any
integrability or martingale hypothesis on the integrator. -/
theorem stronglyAdapted_elementaryMartingaleIntegralProcess
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M)
    {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓥 a] Z) :
    StronglyAdapted 𝓥 (elementaryMartingaleIntegralProcess M a b Z) := by
  intro t
  rcases le_total t a with hta | hat
  · have hzero : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    rw [hzero]
    exact stronglyMeasurable_zero
  · exact hZ.mono (𝓥.mono hat) |>.mul
      ((hM (min t b)).mono (𝓥.mono (min_le_left _ _)) |>.sub
        ((hM (min t a)).mono (𝓥.mono (min_le_left _ _))))

/-- A bounded coefficient measurable at the left endpoint gives a
martingale when integrated over one deterministic time interval against a
martingale.  This is the first arbitrary-integrator construction needed for
the process-level stochastic integral: unlike the Gaussian specialization,
the driving martingale is completely general. -/
theorem martingale_elementaryMartingaleIntegralProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝓥 P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓥 a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    Martingale (elementaryMartingaleIntegralProcess M a b Z) 𝓥 P := by
  have hInt (t : ℝ≥0) : Integrable
      (elementaryMartingaleIntegralProcess M a b Z t) P := by
    have hDelta : Integrable
        (fun omega ↦ M (min t b) omega - M (min t a) omega) P :=
      (hM.integrable _).sub (hM.integrable _)
    exact hDelta.bdd_mul (hZ.mono (𝓥.le a)).aestronglyMeasurable
      (Filter.Eventually.of_forall hZbound)
  have hadapt : StronglyAdapted 𝓥
      (elementaryMartingaleIntegralProcess M a b Z) := by
    intro t
    rcases le_total t a with hta | hat
    · have hzero : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
        funext omega
        simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
          min_eq_left (hta.trans hab)]
      rw [hzero]
      exact stronglyMeasurable_zero
    · exact hZ.mono (𝓥.mono hat) |>.mul
        ((hM.stronglyMeasurable (min t b)).mono
          (𝓥.mono (min_le_left _ _)) |>.sub
            ((hM.stronglyMeasurable (min t a)).mono
              (𝓥.mono (min_le_left _ _))))
  refine ⟨hadapt, ?_⟩
  intro s t hst
  rcases le_total t a with hta | hat
  · have hIt : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    have hIs : elementaryMartingaleIntegralProcess M a b Z s = 0 := by
      funext omega
      have hsa : s ≤ a := hst.trans hta
      simp [elementaryMartingaleIntegralProcess, min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
    rw [hIt, hIs, condExp_zero]
  · rcases le_total s a with hsa | has
    · have hIs : elementaryMartingaleIntegralProcess M a b Z s = 0 := by
        funext omega
        simp [elementaryMartingaleIntegralProcess, min_eq_left hsa,
          min_eq_left (hsa.trans hab)]
      rw [hIs]
      have hIa : P[Z * (M (min t b) - M a) | 𝓥 a] =ᵐ[P] 0 := by
        have hamin : a ≤ min t b := le_min hat hab
        have hprod : Integrable
            (fun omega ↦ Z omega * (M (min t b) omega - M a omega)) P := by
          have hInt' := hInt t
          change Integrable (fun omega ↦
            Z omega * (M (min t b) omega - M (min t a) omega)) P at hInt'
          simpa only [min_eq_right hat] using hInt'
        have hpull := condExp_mul_of_stronglyMeasurable_left hZ
          hprod ((hM.integrable _).sub (hM.integrable a))
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (𝓥 a)
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hamin,
          Filter.Eventually.of_forall (congrFun
            (condExp_of_stronglyMeasurable (𝓥.le a)
              (hM.stronglyMeasurable a) (hM.integrable a)))]
            with omega hp hd hfuture hpast
        change P[Z * (fun xi ↦ M (min t b) xi - M a xi) | 𝓥 a] omega = 0
        have hd' : P[(fun xi ↦ M (min t b) xi - M a xi) | 𝓥 a] omega =
            (P[M (min t b) | 𝓥 a] - P[M a | 𝓥 a]) omega := by
          exact hd
        rw [hp, Pi.mul_apply, hd', Pi.sub_apply, hfuture, hpast,
          sub_self, mul_zero]
      have htower := condExp_condExp_of_le (μ := P)
        (𝓥.mono hsa) (𝓥.le a) (f := Z * (M (min t b) - M a))
      have hzeroCond : P[Z * (M (min t b) - M a) | 𝓥 s] =ᵐ[P] 0 := by
        filter_upwards [htower, condExp_congr_ae hIa,
          Filter.Eventually.of_forall (congrFun
            (condExp_zero (μ := P) (m := 𝓥 s) (E := ℝ)))]
            with omega htow hcongr hzero
        rw [← htow, hcongr, hzero]
      have hprocess : elementaryMartingaleIntegralProcess M a b Z t =
          Z * (M (min t b) - M a) := by
        funext omega
        simp only [elementaryMartingaleIntegralProcess, min_eq_right hat,
          Pi.mul_apply, Pi.sub_apply]
      rw [hprocess]
      exact hzeroCond
    · rcases le_total b s with hbs | hsb
      · have hconst : elementaryMartingaleIntegralProcess M a b Z t =
            elementaryMartingaleIntegralProcess M a b Z s := by
          funext omega
          simp [elementaryMartingaleIntegralProcess,
            min_eq_right (hbs.trans hst), min_eq_right hbs,
            min_eq_right (has.trans hst), min_eq_right has]
        rw [hconst]
        exact Filter.Eventually.of_forall (congrFun
          (condExp_of_stronglyMeasurable (𝓥.le s) (hadapt s) (hInt s)))
      · have hsmin : s ≤ min t b := le_min hst hsb
        have hprod : Integrable
            (fun omega ↦ Z omega * (M (min t b) omega - M a omega)) P := by
          have hInt' := hInt t
          change Integrable (fun omega ↦
            Z omega * (M (min t b) omega - M (min t a) omega)) P at hInt'
          simpa only [min_eq_right hat] using hInt'
        have hpull := condExp_mul_of_stronglyMeasurable_left
          (hZ.mono (𝓥.mono has)) hprod
          ((hM.integrable _).sub (hM.integrable a))
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (𝓥 s)
        have hpast := condExp_of_stronglyMeasurable (𝓥.le s)
          ((hM.stronglyMeasurable a).mono (𝓥.mono has)) (hM.integrable a)
        have hprocess : elementaryMartingaleIntegralProcess M a b Z t =
            Z * (fun xi ↦ M (min t b) xi - M a xi) := by
          funext omega
          simp only [elementaryMartingaleIntegralProcess, min_eq_right hat,
            Pi.mul_apply]
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hsmin,
          Filter.Eventually.of_forall (congrFun hpast)]
            with omega hp hd hfuture hpast'
        rw [hprocess]
        simp only [elementaryMartingaleIntegralProcess, min_eq_right has,
          min_eq_left hsb]
        have hd' : P[(fun xi ↦ M (min t b) xi - M a xi) | 𝓥 s] omega =
            (P[M (min t b) | 𝓥 s] - P[M a | 𝓥 s]) omega := by
          exact hd
        rw [hp, Pi.mul_apply, hd', Pi.sub_apply, hfuture, hpast']

/-- Bounded predictable martingale increments on disjoint ordered intervals
are orthogonal in `L²`.  This is the cross-term cancellation behind the
second-moment estimate for elementary martingale transforms. -/
theorem integral_mul_weighted_martingaleIncrements_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {Z Y : W → ℝ}
    (hZ : StronglyMeasurable[𝓥 a] Z) (K : ℝ≥0)
    (hZK : ∀ omega, ‖Z omega‖ ≤ K)
    (hY : StronglyMeasurable[𝓥 c] Y) (L : ℝ≥0)
    (hYL : ∀ omega, ‖Y omega‖ ≤ L) :
    ∫ omega, (Z omega * (M b omega - M a omega)) *
      (Y omega * (M d omega - M c omega)) ∂P = 0 := by
  let A : W → ℝ := fun omega ↦ Z omega * (M b omega - M a omega)
  let D : W → ℝ := fun omega ↦ M d omega - M c omega
  have hDeltaAB2 : MemLp (fun omega ↦ M b omega - M a omega) 2 P :=
    (hM2 b).sub (hM2 a)
  have hDeltaCD2 : MemLp D 2 P := by
    change MemLp (M d - M c) 2 P
    exact (hM2 d).sub (hM2 c)
  have hAmeas : AEStronglyMeasurable A P := by
    exact (hZ.mono (𝓥.le a)).aestronglyMeasurable.mul hDeltaAB2.1
  have hA2 : MemLp A 2 P := by
    refine hDeltaAB2.of_le_mul (c := K) hAmeas ?_
    filter_upwards with omega
    simp only [A, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hZK omega) (abs_nonneg _)
  have hYDmeas : AEStronglyMeasurable (Y * D) P :=
    (hY.mono (𝓥.le c)).aestronglyMeasurable.mul hDeltaCD2.1
  have hYD2 : MemLp (Y * D) 2 P := by
    refine hDeltaCD2.of_le_mul (c := L) hYDmeas ?_
    filter_upwards with omega
    simp only [Pi.mul_apply, D, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hYL omega) (abs_nonneg _)
  have hprodAssoc : Integrable (A * (Y * D)) P :=
    memLp_one_iff_integrable.mp (hYD2.mul hA2)
  have hprod : Integrable ((A * Y) * D) P := by
    apply hprodAssoc.congr
    filter_upwards with omega
    simp only [Pi.mul_apply]
    ring
  have hAYmeas : StronglyMeasurable[𝓥 c] (A * Y) := by
    apply StronglyMeasurable.mul _ hY
    exact (hZ.mono (𝓥.mono (hab.trans hbc))).mul
      ((hM.stronglyMeasurable b).mono (𝓥.mono hbc) |>.sub
        ((hM.stronglyMeasurable a).mono (𝓥.mono (hab.trans hbc))))
  have hDint : Integrable D P := by
    change Integrable (M d - M c) P
    exact (hM.integrable d).sub (hM.integrable c)
  have hpull := condExp_mul_of_stronglyMeasurable_left hAYmeas hprod hDint
  have hDzero : P[D | 𝓥 c] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable d) (hM.integrable c) (𝓥 c)
    filter_upwards [hsub, hM.condExp_ae_eq hcd,
      Filter.Eventually.of_forall (congrFun
        (condExp_of_stronglyMeasurable (𝓥.le c)
          (hM.stronglyMeasurable c) (hM.integrable c)))]
        with omega hsubOmega hdOmega hcOmega
    change P[D | 𝓥 c] omega = 0
    rw [show P[D | 𝓥 c] omega =
      (P[M d | 𝓥 c] - P[M c | 𝓥 c]) omega by exact hsubOmega]
    simp only [Pi.sub_apply, hdOmega, hcOmega, sub_self]
  have hcondZero : P[(A * Y) * D | 𝓥 c] =ᵐ[P] 0 := by
    filter_upwards [hpull, hDzero] with omega hpullOmega hDOmega
    simpa only [Pi.mul_apply, Pi.zero_apply, hDOmega, mul_zero] using hpullOmega
  calc
    ∫ omega, (Z omega * (M b omega - M a omega)) *
        (Y omega * (M d omega - M c omega)) ∂P =
        ∫ omega, ((A * Y) * D) omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          simp only [A, D, Pi.mul_apply]
          ring
    _ = ∫ omega, P[(A * Y) * D | 𝓥 c] omega ∂P :=
      (integral_condExp (𝓥.le c)).symm
    _ = 0 := by
      rw [integral_congr_ae hcondZero]
      simp

/-- The second moment of a finite sum of pairwise orthogonal real `L²`
functions is the sum of their second moments. -/
theorem integral_sq_sum_range_of_pairwise_orthogonal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℕ → W → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    (horth : ∀ i j, i < j → ∫ omega, f i omega * f j omega ∂P = 0)
    (n : ℕ) :
    ∫ omega, (∑ i ∈ Finset.range n, f i omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range n, ∫ omega, (f i omega) ^ 2 ∂P := by
  have hsq (g : W → ℝ) (hg : MemLp g 2 P) :
      Integrable (fun omega ↦ (g omega) ^ 2) P := by
    have hmul : MemLp (g * g) 1 P := hg.mul hg
    apply (memLp_one_iff_integrable.mp hmul).congr
    filter_upwards with omega
    simp only [Pi.mul_apply, pow_two]
  induction n with
  | zero => simp
  | succ n ih =>
      let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range n, f i omega
      have hS2 : MemLp S 2 P := by
        exact memLp_finsetSum (Finset.range n) (fun i _ ↦ hf i)
      have hSn : Integrable (S * f n) P :=
        memLp_one_iff_integrable.mp ((hf n).mul hS2)
      have hcross : ∫ omega, S omega * f n omega ∂P = 0 := by
        simp only [S, Finset.sum_mul]
        rw [integral_finsetSum]
        · apply Finset.sum_eq_zero
          intro i hi
          exact horth i n (Finset.mem_range.mp hi)
        · intro i _
          exact memLp_one_iff_integrable.mp ((hf n).mul (hf i))
      simp_rw [Finset.sum_range_succ]
      change ∫ omega, (S omega + f n omega) ^ 2 ∂P =
        (∑ i ∈ Finset.range n, ∫ omega, f i omega ^ 2 ∂P) +
          ∫ omega, f n omega ^ 2 ∂P
      calc
        ∫ omega, (S omega + f n omega) ^ 2 ∂P =
            ∫ omega, S omega ^ 2 +
              (2 * (S omega * f n omega) + f n omega ^ 2) ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = (∫ omega, S omega ^ 2 ∂P) +
            ((∫ omega, 2 * (S omega * f n omega) ∂P) +
              ∫ omega, f n omega ^ 2 ∂P) := by
          rw [integral_add (hsq S hS2)]
          · rw [integral_add]
            · exact hSn.const_mul 2
            · exact hsq (f n) (hf n)
          · exact (hSn.const_mul 2).add (hsq (f n) (hf n))
        _ = (∫ omega, S omega ^ 2 ∂P) +
            ∫ omega, f n omega ^ 2 ∂P := by
          rw [integral_const_mul, hcross]
          ring
        _ = (∑ i ∈ Finset.range n, ∫ omega, f i omega ^ 2 ∂P) +
            ∫ omega, f n omega ^ 2 ∂P := by rw [ih]

/-- Forming a single elementary integral commutes exactly with Mathlib's
stopped-process convention and its exceptional-event indicator.  This
identity is the stopping compatibility needed to reuse an integrator's
localizing sequence. -/
theorem stoppedProcess_indicator_elementaryMartingaleIntegralProcess
    {W : Type*} (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → ℝ)
    (A : Set W) (tau : W → WithTop ℝ≥0) :
    stoppedProcess
        (fun i ↦ A.indicator
          (elementaryMartingaleIntegralProcess M a b Z i)) tau =
      elementaryMartingaleIntegralProcess
        (stoppedProcess (fun i ↦ A.indicator (M i)) tau) a b Z := by
  funext t omega
  simp only [elementaryMartingaleIntegralProcess, stoppedProcess]
  by_cases hA : omega ∈ A
  · simp only [Set.indicator_of_mem hA]
    simp only [elementaryMartingaleIntegralProcess]
    congr 1
    have hcoe_untopA (x : WithTop ℝ≥0) (hx : x ≠ ⊤) :
        ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
      rw [WithTop.untopA_eq_untop hx, WithTop.coe_untop]
    have hcoe_min (x y : ℝ≥0) :
        ((min x y : ℝ≥0) : WithTop ℝ≥0) =
          min (x : WithTop ℝ≥0) (y : WithTop ℝ≥0) := by
      norm_cast
    have hstopmin (c : ℝ≥0) :
        min (min (t : WithTop ℝ≥0) (tau omega)).untopA c =
          (min ((min t c : ℝ≥0) : WithTop ℝ≥0) (tau omega)).untopA := by
      apply WithTop.coe_injective
      rw [hcoe_min, hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)),
        hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)), hcoe_min]
      ac_rfl
    rw [hstopmin b, hstopmin a]
  · simp only [Set.indicator_of_notMem hA, sub_self, mul_zero]

/-- An elementary predictable integral against a local martingale is a local
martingale.  The proof uses the integrator's own localizing sequence and the
exact stopping-compatibility identity above. -/
theorem IsLocalMartingale.elementaryMartingaleIntegralProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ}
    (hM : IsLocalMartingale M 𝓥 P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓥 a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    IsLocalMartingale (elementaryMartingaleIntegralProcess M a b Z) 𝓥 P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun n ↦ ?_⟩
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau n omega}
  let N : ℝ≥0 → W → ℝ :=
    stoppedProcess (fun i ↦ A.indicator (M i)) (tau n)
  have hN : Martingale N 𝓥 P := hstopped n
  have hIntegral : Martingale
      (StochasticCalculus.elementaryMartingaleIntegralProcess N a b Z) 𝓥 P :=
    martingale_elementaryMartingaleIntegralProcess hN hab hZ C hZbound
  change Martingale (stoppedProcess
    (fun i ↦ A.indicator
      (StochasticCalculus.elementaryMartingaleIntegralProcess M a b Z i)) (tau n)) 𝓥 P
  rw [stoppedProcess_indicator_elementaryMartingaleIntegralProcess]
  exact hIntegral

/-- A finite sum of martingales is a martingale.  The pointwise finite-sum
form is convenient for assembling elementary stochastic integrals without
introducing an artificial ordering on their interval index type. -/
theorem Martingale.finset_sum
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : I → ℝ≥0 → W → ℝ} (S : Finset I)
    (hX : ∀ i ∈ S, Martingale (X i) 𝓥 P) :
    Martingale (∑ i ∈ S, X i) 𝓥 P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using martingale_zero ℝ 𝓥 P
  | @insert i S hi ih =>
      have hhead : Martingale (X i) 𝓥 P :=
        hX i (Finset.mem_insert_self i S)
      have htail : Martingale (∑ j ∈ S, X j) 𝓥 P :=
        ih fun j hj ↦ hX j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using hhead.add htail

/-- Finite pointwise sums preserve strong adaptation. -/
theorem StronglyAdapted.finset_sum
    {W I : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : I → ℝ≥0 → W → ℝ} (S : Finset I)
    (hX : ∀ i ∈ S, StronglyAdapted 𝓥 (X i)) :
    StronglyAdapted 𝓥 (∑ i ∈ S, X i) := by
  intro t
  simpa only [Finset.sum_apply] using
    S.stronglyMeasurable_sum fun i hi ↦ hX i hi t

/-- An almost-everywhere strongly measurable `L¹`-norm limit of integrable
functions is integrable.  Convergence to zero makes one difference have
finite `L¹` norm, after which integrability follows by adding back the
corresponding approximant. -/
theorem integrable_of_tendsto_eLpNorm_one_sub
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : ℕ → W → ℝ} {g : W → ℝ}
    (hf : ∀ n, Integrable (f n) P)
    (hg : AEStronglyMeasurable g P)
    (hconv : Tendsto (fun n ↦ eLpNorm (g - f n) 1 P)
      Filter.atTop (𝓝 0)) :
    Integrable g P := by
  have hlt : ∀ᶠ n in Filter.atTop,
      eLpNorm (g - f n) 1 P < 1 :=
    (tendsto_order.1 hconv).2 1 (by simp)
  rcases hlt.exists with ⟨n, hn⟩
  have hdiff : Integrable (g - f n) P :=
    memLp_one_iff_integrable.mp
      ⟨hg.sub (hf n).1, hn.trans (by simp)⟩
  simpa only [sub_add_cancel] using hdiff.add (hf n)

/-- On a probability space, uniform integrability in `L²` implies uniform
integrability in `L¹`. -/
theorem UniformIntegrable.mono_one_of_two
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] {f : I → W → ℝ}
    (hUI : UniformIntegrable f 2 P) :
    UniformIntegrable f 1 P := by
  refine ⟨hUI.1, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hUI.2.1 hε
    refine ⟨δ, hδpos, fun i s hs hPs ↦ ?_⟩
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      ((hUI.1 i).indicator hs)).trans (hδ i s hs hPs)
  · obtain ⟨C, hC⟩ := hUI.2.2
    refine ⟨C, fun i ↦ ?_⟩
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      (hUI.1 i)).trans (hC i)

/-- A uniformly `L²`-bounded family on a probability space is uniformly
integrable in `L¹`.  This is the standard higher-moment route to the Vitali
hypothesis used below: the remaining probabilistic obligation can therefore
be discharged by a uniform second-moment estimate for the explicit
martingale-transform approximations. -/
theorem uniformIntegrable_one_of_uniform_eLpNorm_two
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} [IsProbabilityMeasure P] {f : I → W → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) 2 P ≤ C) :
    UniformIntegrable f 1 P := by
  refine ⟨hf, ?_, ⟨C, fun i ↦ ?_⟩⟩
  · intro ε hε
    let d : ℝ := ε / ((C : ℝ) + 1)
    have hd : 0 < d := div_pos hε (by positivity)
    refine ⟨d ^ 2, sq_pos_of_pos hd, fun i s hs hPs ↦ ?_⟩
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    calc
      eLpNorm (f i) 1 (P.restrict s) ≤
          eLpNorm (f i) 2 (P.restrict s) *
            (P.restrict s) Set.univ ^ (1 / 2 : ℝ) := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
            (f := f i) (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
            ((hf i).mono_measure Measure.restrict_le_self) using 1;
          norm_num
      _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (d ^ 2)) ^ (1 / 2 : ℝ) := by
        simp only [Measure.restrict_apply_univ]
        exact mul_le_mul'
          ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i))
          (ENNReal.rpow_le_rpow hPs (by norm_num))
      _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_pos (sq_pos_of_pos hd)]
        rw [show (d ^ 2) ^ (1 / 2 : ℝ) = d by
          rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast hd.le
            (show (2 : ℕ) ≠ 0 by norm_num)]
        rw [← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (C.coe_nonneg)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [d]
        calc
          (C : ℝ) * (ε / ((C : ℝ) + 1)) ≤
              ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
            gcongr
            norm_num
          _ = ε := by field_simp
  · exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hf i)).trans
      (hC i)

/-- A strongly adapted pointwise-in-time `L¹`-norm limit of martingales is a
martingale.  Integrability of the limit follows from convergence, and
conditional expectation is an `L¹` contraction, so the martingale identities
pass to the limit at every pair of times. -/
theorem martingale_of_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓥 P)
    (hYadapt : StronglyAdapted 𝓥 Y)
    (hconv : ∀ t, Tendsto
      (fun n ↦ eLpNorm (Y t - X n t) 1 P) Filter.atTop (𝓝 0)) :
    Martingale Y 𝓥 P := by
  have hYint : ∀ t, Integrable (Y t) P := fun t ↦
    integrable_of_tendsto_eLpNorm_one_sub
      (fun n ↦ (hX n).integrable t)
      ((hYadapt t).mono (𝓥.le t)).aestronglyMeasurable (hconv t)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff
    ((stronglyMeasurable_condExp.mono (𝓥.le s)).sub
      ((hYadapt s).mono (𝓥.le s))).aestronglyMeasurable one_ne_zero]
  apply le_antisymm
  · have hconvS : Tendsto (fun n ↦ eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (𝓝 0) := by
      convert hconv s using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Tendsto (fun n ↦
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (𝓝 0) := by
      simpa only [add_zero] using (hconv t).add hconvS
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hdecomp :
        P[Y t | 𝓥 s] - Y s =ᵐ[P]
          P[Y t - X n t | 𝓥 s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (𝓥 s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      ring
    calc
      eLpNorm (P[Y t | 𝓥 s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | 𝓥 s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | 𝓥 s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le
          (integrable_condExp (μ := P) (m := 𝓥 s)
            (f := Y t - X n t)).1
          ((((hX n).stronglyMeasurable s).mono
            (𝓥.le s)).aestronglyMeasurable.sub (hYint s).1) le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- Vitali closure for martingales: a strongly adapted limit in measure of a
uniformly integrable sequence of martingales is a martingale. -/
theorem martingale_of_tendstoInMeasure_of_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓥 P)
    (hYadapt : StronglyAdapted 𝓥 Y)
    (hUI : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ X n t)
      Filter.atTop (Y t)) :
    Martingale Y 𝓥 P := by
  apply martingale_of_tendsto_eLpNorm_one hX hYadapt
  intro t
  have hYmem : MemLp (Y t) 1 P :=
    (hUI t).memLp_of_tendstoInMeasure (hconv t)
  have hLp : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P)
      Filter.atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (by simp) (by simp)
      (fun n ↦ ((hX n).integrable t).1) hYmem
      (hUI t).unifIntegrable (hconv t)
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- Stopping a continuous-path martingale at its bounded continuous exit
time preserves the martingale property.  The proof closes the dyadic
finite-range martingales under convergence in measure.  Uniform
integrability follows from optional sampling: at each deterministic time
the approximants are conditional expectations of the original martingale. -/
theorem martingale_stoppedProcess_continuousExitTime_of_adapted
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M Z : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝓥 Z)
    (T R : ℝ≥0) :
    Martingale (stoppedProcess M (continuousExitTime Z T R)) 𝓥 P := by
  let tau : W → WithTop ℝ≥0 := continuousExitTime Z T R
  let tauN : ℕ → W → WithTop ℝ≥0 :=
    fun n => dyadicHittingTimeNNReal Z T R n
  let X : ℕ → ℝ≥0 → W → ℝ := fun n => stoppedProcess M (tauN n)
  have htau : IsStoppingTime 𝓥 tau :=
    isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R
  have hX (n : ℕ) : Martingale (X n) 𝓥 P := by
    dsimp only [X, tauN]
    exact
      martingale_stoppedProcess_uniformPartitionHittingTimeNNReal_of_adapted
        hM hZ T (2 ^ n) (measurableSet_outsideClosedBall R)
  have hYadapt : StronglyAdapted 𝓥 (stoppedProcess M tau) :=
    hM.stronglyAdapted.stoppedProcess hMcont htau
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable hX hYadapt
  · intro t
    let sigma : ℕ → W → WithTop ℝ≥0 := fun n omega =>
      min (t : WithTop ℝ≥0) (tauN n omega)
    have hsigma (n : ℕ) : IsStoppingTime 𝓥 (sigma n) :=
      (isStoppingTime_const 𝓥 t).min
        (isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
          hZ T (2 ^ n) (measurableSet_outsideClosedBall R))
    have hsigma_le (n : ℕ) (omega : W) : sigma n omega ≤ t :=
      min_le_left _ _
    have hsigma_range (n : ℕ) : (Set.range (sigma n)).Countable := by
      have heq : Set.range (sigma n) =
          (fun x : WithTop ℝ≥0 => min (t : WithTop ℝ≥0) x) ''
            Set.range (tauN n) := by
        rw [← Set.range_comp]
        rfl
      rw [heq]
      apply Set.Countable.image
      apply ((((Finset.range (2 ^ n + 1)).image
        (uniformPartitionTime T (2 ^ n))).finite_toSet.image
          ((↑) : ℝ≥0 → WithTop ℝ≥0)).countable).mono
      rintro x ⟨omega, rfl⟩
      exact uniformPartitionHittingTimeNNReal_mem_rangeFinset Z T (2 ^ n)
        (outsideClosedBall R) omega
    have hae (n : ℕ) : X n t =ᵐ[P]
        P[M t | (hsigma n).measurableSpace] := by
      exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
        (hsigma n) (hsigma_le n) (hsigma_range n)
    have hUI : UniformIntegrable
        (fun n => P[M t | (hsigma n).measurableSpace]) 1 P :=
      (hM.integrable t).uniformIntegrable_condExp
        (fun n => (hsigma n).measurableSpace_le)
    exact hUI.ae_eq (fun n => (hae n).symm)
  · intro t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hX n).integrable t).1
    · exact Filter.Eventually.of_forall fun omega =>
        tendsto_stoppedProcess_dyadicHittingTime_continuousExitTime_of_continuous
          hMcont T R t omega

/-- Stopping a continuous-path martingale when it exits a ball preserves the
martingale property. -/
theorem martingale_stoppedProcess_continuousExitTime
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T R : ℝ≥0) :
    Martingale (stoppedProcess M (continuousExitTime M T R)) 𝓥 P :=
  martingale_stoppedProcess_continuousExitTime_of_adapted
    hM hMcont hM.stronglyAdapted T R

/-- The stopped-and-indicated process used in Mathlib's definition of a
local property.  Naming it keeps local `L¹` approximation statements
readable. -/
noncomputable def localizingStoppedProcess
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0) :
    ℝ≥0 → W → ℝ :=
  stoppedProcess
    (fun t ↦ {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator (X t)) tau

/-- Before a strictly positive localizing time, stopped-and-indicated
localization agrees pointwise with the original process. -/
theorem localizingStoppedProcess_eq_of_lt
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (t : ℝ≥0) (omega : W) (ht : (t : WithTop ℝ≥0) < tau omega) :
    localizingStoppedProcess X tau t omega = X t omega := by
  have hpos : (⊥ : WithTop ℝ≥0) < tau omega :=
    (show (⊥ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) from bot_le).trans_lt ht
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
  unfold localizingStoppedProcess
  rw [stoppedProcess_indicator_comm, Set.indicator_of_mem hmem,
    stoppedProcess_eq_of_le ht.le]

/-- Deterministic scalar multiplication commutes with Mathlib's
stopped-and-indicated localization convention. -/
theorem localizingStoppedProcess_const_mul
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0) (c : ℝ) :
    localizingStoppedProcess (fun t omega => c * X t omega) tau =
      fun t omega => c * localizingStoppedProcess X tau t omega := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  by_cases hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  · simp only [Set.indicator_of_mem hmem]
  · simp only [Set.indicator_of_notMem hmem, mul_zero]

/-- A local quadratic-variation contract with an explicit common localizer.
Along one localizing sequence, `M` becomes a genuine martingale and the
localized `bracket` satisfies the robust completed-cell quadratic-variation
contract.  Unlike a hypothesis phrased using `Locally.localSeq`, this
definition does not expose the witness chosen from a proof of locality. -/
def HasLocalQuadraticVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ)
    (𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) : Prop :=
  ∃ tau : ℕ → W → WithTop ℝ≥0,
    IsLocalizingSequence 𝒱 tau P ∧
      (∀ k, Martingale (localizingStoppedProcess M (tau k)) 𝒱 P) ∧
      ∀ k, HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P

/-- A common-localizer quadratic-variation contract implies ordinary
fixed-time quadratic variation.  At each deterministic time, all partition
values agree with their localized versions off an exceptional event whose
probability vanishes along the localizing sequence. -/
theorem HasLocalQuadraticVariationProcessInProbability.toProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P) :
    HasQuadraticVariationProcessInProbability M bracket P := by
  obtain ⟨tau, htau, _hmart, hqv⟩ := h
  intro t
  unfold HasQuadraticVariationInProbabilityAt
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have hbadInMeasure : TendstoInMeasure P
      (fun k omega ↦
        {omega | tau k omega ≤ (t : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) omega)
      Filter.atTop (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro k
      have hset : MeasurableSet {omega | tau k omega ≤ (t : WithTop ℝ≥0)} :=
        𝒱.le t _ ((htau.isStoppingTime k).measurableSet_le t)
      exact (stronglyMeasurable_const.indicator hset).aestronglyMeasurable
    · filter_upwards [htau.tendsto_top] with omega homega
      have heventually : ∀ᶠ k in Filter.atTop,
          (t : WithTop ℝ≥0) < tau k omega :=
        homega (Ioi_mem_nhds (WithTop.coe_lt_top t))
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [heventually] with k hk
      rw [Set.indicator_of_notMem]
      exact fun hle ↦ (not_lt_of_ge hle) hk
  have hbad : Tendsto
      (fun k ↦ P.real {omega | tau k omega ≤ (t : WithTop ℝ≥0)})
      Filter.atTop (nhds 0) := by
    have hhalf := (tendstoInMeasure_iff_measureReal_dist.mp hbadInMeasure)
      (1 / 2 : ℝ) (by norm_num)
    convert hhalf using 1
    funext k
    congr 1
    ext omega
    simp only [Set.mem_ofPred_eq]
    by_cases hle : tau k omega ≤ (t : WithTop ℝ≥0)
    · have homegaMem : omega ∈
          {omega : W | tau k omega ≤ (t : WithTop ℝ≥0)} := hle
      rw [Set.indicator_of_mem homegaMem]
      norm_num [Real.dist_eq]
      exact hle
    · have homegaNotMem : omega ∉
          {omega : W | tau k omega ≤ (t : WithTop ℝ≥0)} := hle
      rw [Set.indicator_of_notMem homegaNotMem]
      norm_num [Real.dist_eq, hle]
      exact hle
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hbad) (delta / 2) (by positivity)
  have hlocal := tendstoInMeasure_iff_measureReal_dist.mp
    ((hqv k).toProcess t) epsilon hepsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlocal) (delta / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hk' := hk k le_rfl
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hk' hN'
  have hsubset :
      {omega | epsilon ≤
          dist (quadraticVariationApprox M t (n + 1) omega) (bracket t omega)} ⊆
        {omega | tau k omega ≤ (t : WithTop ℝ≥0)} ∪
          {omega | epsilon ≤ dist
            (quadraticVariationApprox (localizingStoppedProcess M (tau k))
              t (n + 1) omega)
            (localizingStoppedProcess bracket (tau k) t omega)} := by
    intro omega homega
    by_cases hgood : (t : WithTop ℝ≥0) < tau k omega
    · right
      have hbracket := localizingStoppedProcess_eq_of_lt bracket (tau k) t omega hgood
      have happ : quadraticVariationApprox (localizingStoppedProcess M (tau k))
          t (n + 1) omega = quadraticVariationApprox M t (n + 1) omega := by
        unfold quadraticVariationApprox
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
        have hright : uniformPartitionTime t (n + 1) (i + 1) ≤ t :=
          (uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) hi1).2
        have hleft : uniformPartitionTime t (n + 1) i ≤ t :=
          (uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
            ((Nat.le_add_right i 1).trans hi1)).2
        rw [localizingStoppedProcess_eq_of_lt M (tau k) _ omega
              (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hright) hgood),
          localizingStoppedProcess_eq_of_lt M (tau k) _ omega
              (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hleft) hgood)]
      change epsilon ≤ dist
        (quadraticVariationApprox (localizingStoppedProcess M (tau k))
          t (n + 1) omega)
        (localizingStoppedProcess bracket (tau k) t omega)
      rw [happ, hbracket]
      exact homega
    · left
      exact le_of_not_gt hgood
  have hmeasure :
      P.real {omega | epsilon ≤
          dist (quadraticVariationApprox M t (n + 1) omega) (bracket t omega)} ≤
        P.real ({omega | tau k omega ≤ (t : WithTop ℝ≥0)} ∪
          {omega | epsilon ≤ dist
            (quadraticVariationApprox (localizingStoppedProcess M (tau k))
              t (n + 1) omega)
            (localizingStoppedProcess bracket (tau k) t omega)}) :=
    measureReal_mono hsubset (measure_ne_top P _)
  calc
    dist (P.real {omega | epsilon ≤
        dist (quadraticVariationApprox M t (n + 1) omega) (bracket t omega)}) 0 =
        P.real {omega | epsilon ≤
          dist (quadraticVariationApprox M t (n + 1) omega) (bracket t omega)} := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    _ ≤ P.real ({omega | tau k omega ≤ (t : WithTop ℝ≥0)} ∪
        {omega | epsilon ≤ dist
          (quadraticVariationApprox (localizingStoppedProcess M (tau k))
            t (n + 1) omega)
          (localizingStoppedProcess bracket (tau k) t omega)}) := hmeasure
    _ ≤ P.real {omega | tau k omega ≤ (t : WithTop ℝ≥0)} +
        P.real {omega | epsilon ≤ dist
          (quadraticVariationApprox (localizingStoppedProcess M (tau k))
            t (n + 1) omega)
          (localizingStoppedProcess bracket (tau k) t omega)} :=
      measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add hk' hN'
    _ = delta := by ring

/-- The common-localizer contract also promotes to the global robust
before-stop bracket.  On the event where the localizing time exceeds the
fixed horizon, every completed-cell value and the bracket endpoint agree
literally with their localized counterparts. -/
theorem HasLocalQuadraticVariationProcessInProbability.toBeforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P) :
    HasQuadraticVariationBeforeStopProcessInProbability M bracket P := by
  obtain ⟨tau, htau, _hmart, hqv⟩ := h
  intro T a
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have hbadInMeasure : TendstoInMeasure P
      (fun k omega ↦
        {omega | tau k omega ≤ (T : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) omega)
      Filter.atTop (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro k
      have hset : MeasurableSet {omega | tau k omega ≤ (T : WithTop ℝ≥0)} :=
        𝒱.le T _ ((htau.isStoppingTime k).measurableSet_le T)
      exact (stronglyMeasurable_const.indicator hset).aestronglyMeasurable
    · filter_upwards [htau.tendsto_top] with omega homega
      have heventually : ∀ᶠ k in Filter.atTop,
          (T : WithTop ℝ≥0) < tau k omega :=
        homega (Ioi_mem_nhds (WithTop.coe_lt_top T))
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [heventually] with k hk
      rw [Set.indicator_of_notMem]
      exact fun hle ↦ (not_lt_of_ge hle) hk
  have hbad : Tendsto
      (fun k ↦ P.real {omega | tau k omega ≤ (T : WithTop ℝ≥0)})
      Filter.atTop (nhds 0) := by
    have hhalf := (tendstoInMeasure_iff_measureReal_dist.mp hbadInMeasure)
      (1 / 2 : ℝ) (by norm_num)
    convert hhalf using 1
    funext k
    congr 1
    ext omega
    simp only [Set.mem_ofPred_eq]
    by_cases hle : tau k omega ≤ (T : WithTop ℝ≥0)
    · have homegaMem : omega ∈
          {omega : W | tau k omega ≤ (T : WithTop ℝ≥0)} := hle
      rw [Set.indicator_of_mem homegaMem]
      norm_num [Real.dist_eq]
      exact hle
    · have homegaNotMem : omega ∉
          {omega : W | tau k omega ≤ (T : WithTop ℝ≥0)} := hle
      rw [Set.indicator_of_notMem homegaNotMem]
      norm_num [Real.dist_eq, hle]
      exact hle
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hbad) (delta / 2) (by positivity)
  have hlocal := tendstoInMeasure_iff_measureReal_dist.mp
    (hqv k T a) epsilon hepsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlocal) (delta / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hk' := hk k le_rfl
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hk' hN'
  have hsubset :
      {omega | epsilon ≤ dist
          (quadraticVariationBeforeStopApprox M T (n + 1) a omega)
          (bracket (min T a) omega)} ⊆
        {omega | tau k omega ≤ (T : WithTop ℝ≥0)} ∪
          {omega | epsilon ≤ dist
            (quadraticVariationBeforeStopApprox
              (localizingStoppedProcess M (tau k)) T (n + 1) a omega)
            (localizingStoppedProcess bracket (tau k) (min T a) omega)} := by
    intro omega homega
    by_cases hgood : (T : WithTop ℝ≥0) < tau k omega
    · right
      have hbracket := localizingStoppedProcess_eq_of_lt bracket (tau k)
        (min T a) omega
        (lt_of_le_of_lt (WithTop.coe_le_coe.mpr (min_le_left T a)) hgood)
      have happ : quadraticVariationBeforeStopApprox
          (localizingStoppedProcess M (tau k)) T (n + 1) a omega =
          quadraticVariationBeforeStopApprox M T (n + 1) a omega := by
        unfold quadraticVariationBeforeStopApprox
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hcell : uniformPartitionTime T (n + 1) (i + 1) ≤ a
        · have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
          have hi0 : i ≤ n + 1 := (Nat.le_add_right i 1).trans hi1
          have hright : uniformPartitionTime T (n + 1) (i + 1) ≤ T :=
            (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hi1).2
          have hleft : uniformPartitionTime T (n + 1) i ≤ T :=
            (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hi0).2
          simp only [hcell, ↓reduceIte]
          rw [localizingStoppedProcess_eq_of_lt M (tau k) _ omega
                (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hright) hgood),
            localizingStoppedProcess_eq_of_lt M (tau k) _ omega
                (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hleft) hgood)]
        · simp only [hcell, ↓reduceIte]
      change epsilon ≤ dist
        (quadraticVariationBeforeStopApprox
          (localizingStoppedProcess M (tau k)) T (n + 1) a omega)
        (localizingStoppedProcess bracket (tau k) (min T a) omega)
      rw [happ, hbracket]
      exact homega
    · left
      exact le_of_not_gt hgood
  have hmeasure := measureReal_mono hsubset (measure_ne_top P _)
  calc
    dist (P.real {omega | epsilon ≤ dist
        (quadraticVariationBeforeStopApprox M T (n + 1) a omega)
        (bracket (min T a) omega)}) 0 =
        P.real {omega | epsilon ≤ dist
          (quadraticVariationBeforeStopApprox M T (n + 1) a omega)
          (bracket (min T a) omega)} := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    _ ≤ P.real ({omega | tau k omega ≤ (T : WithTop ℝ≥0)} ∪
        {omega | epsilon ≤ dist
          (quadraticVariationBeforeStopApprox
            (localizingStoppedProcess M (tau k)) T (n + 1) a omega)
          (localizingStoppedProcess bracket (tau k) (min T a) omega)}) := hmeasure
    _ ≤ P.real {omega | tau k omega ≤ (T : WithTop ℝ≥0)} +
        P.real {omega | epsilon ≤ dist
          (quadraticVariationBeforeStopApprox
            (localizingStoppedProcess M (tau k)) T (n + 1) a omega)
          (localizingStoppedProcess bracket (tau k) (min T a) omega)} :=
      measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add hk' hN'
    _ = delta := by ring

/-- The proof-independent common-localizer quadratic-variation contract is
closed under deterministic scaling, with the bracket scaled by `c²`. -/
theorem HasLocalQuadraticVariationProcessInProbability.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (c : ℝ) :
    HasLocalQuadraticVariationProcessInProbability
      (fun t omega => c * M t omega)
      (fun t omega => c ^ 2 * bracket t omega) 𝒱 P := by
  obtain ⟨tau, htau, hmart, hQV⟩ := h
  refine ⟨tau, htau, ?_, ?_⟩
  · intro k
    rw [localizingStoppedProcess_const_mul]
    change Martingale (c • localizingStoppedProcess M (tau k)) 𝒱 P
    exact (hmart k).smul c
  · intro k
    simpa only [localizingStoppedProcess_const_mul] using (hQV k).const_mul c

/-- The common-localizer quadratic-variation contract includes the local
martingale property of its integrator. -/
theorem HasLocalQuadraticVariationProcessInProbability.isLocalMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P) :
    IsLocalMartingale M 𝒱 P := by
  obtain ⟨tau, htau, hmart, _⟩ := h
  exact ⟨tau, htau, hmart⟩

/-- With continuous paths, a process carrying the local quadratic-variation
contract is a continuous local martingale. -/
theorem
    HasLocalQuadraticVariationProcessInProbability.isContinuousLocalMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega)) :
    IsContinuousLocalMartingale M 𝒱 P :=
  ⟨h.isLocalMartingale, Filter.Eventually.of_forall hMcont⟩

/-- Stopped-and-indicated localization preserves every continuous sample
path, including on the exceptional event where the stopping time is zero. -/
theorem continuous_localizingStoppedProcess
    {W : Type*} {X : ℝ≥0 → W → ℝ}
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (tau : W → WithTop ℝ≥0) (omega : W) :
    Continuous (fun t => localizingStoppedProcess X tau t omega) := by
  unfold localizingStoppedProcess stoppedProcess
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    simp only [Set.indicator_of_mem hmem]
    cases htau : tau omega with
    | top =>
        convert hXcont omega using 1
        funext t
        rw [min_eq_left le_top, WithTop.untopA_eq_untop
          WithTop.coe_ne_top, WithTop.untop_coe]
    | coe a =>
        have heq : (fun t : ℝ≥0 =>
            X (min (t : WithTop ℝ≥0) (a : WithTop ℝ≥0)).untopA
              omega) = fun t => X (min t a) omega := by
          funext t
          have hmin : min (t : WithTop ℝ≥0) (a : WithTop ℝ≥0) =
              ((min t a : ℝ≥0) : WithTop ℝ≥0) :=
            (WithTop.coe_min t a).symm
          rw [hmin, WithTop.untopA_eq_untop WithTop.coe_ne_top,
            WithTop.untop_coe]
        rw [heq]
        exact (hXcont omega).comp
          (continuous_id.min (continuous_const :
            Continuous (fun _ : ℝ≥0 => a)))
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    simp only [Set.indicator_of_notMem hmem]
    exact continuous_const

/-- Stopped-and-indicated localization preserves pathwise monotonicity. -/
theorem monotone_localizingStoppedProcess
    {W : Type*} {X : ℝ≥0 → W → ℝ}
    (hXmono : ∀ omega, Monotone (fun t => X t omega))
    (tau : W → WithTop ℝ≥0) (omega : W) :
    Monotone (fun t => localizingStoppedProcess X tau t omega) := by
  intro a b hab
  unfold localizingStoppedProcess stoppedProcess
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    simp only [Set.indicator_of_mem hmem]
    apply hXmono omega
    apply WithTop.coe_le_coe.mp
    have hmin : min (a : WithTop ℝ≥0) (tau omega) ≤
        min (b : WithTop ℝ≥0) (tau omega) :=
      min_le_min_right (tau omega) (WithTop.coe_le_coe.mpr hab)
    have hleft : (((min (a : WithTop ℝ≥0) (tau omega)).untopA : ℝ≥0) :
        WithTop ℝ≥0) = min (a : WithTop ℝ≥0) (tau omega) := by
      rw [WithTop.untopA_eq_untop (ne_top_of_le_ne_top
        WithTop.coe_ne_top (min_le_left _ _))]
      exact WithTop.coe_untop _ _
    have hright : (((min (b : WithTop ℝ≥0) (tau omega)).untopA : ℝ≥0) :
        WithTop ℝ≥0) = min (b : WithTop ℝ≥0) (tau omega) := by
      rw [WithTop.untopA_eq_untop (ne_top_of_le_ne_top
        WithTop.coe_ne_top (min_le_left _ _))]
      exact WithTop.coe_untop _ _
    rwa [hleft, hright]
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    simp only [Set.indicator_of_notMem hmem]
    exact le_rfl

/-- A localized stopped value depends only on the value of the stopping
rule at the sample point being evaluated. -/
theorem localizingStoppedProcess_congr_stop_at
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (tau sigma : W → WithTop ℝ≥0) (t : ℝ≥0) (omega : W)
    (h : tau omega = sigma omega) :
    localizingStoppedProcess X tau t omega =
      localizingStoppedProcess X sigma t omega := by
  unfold localizingStoppedProcess stoppedProcess
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega =
    {omega | (⊥ : WithTop ℝ≥0) < sigma omega}.indicator
      (X (min (t : WithTop ℝ≥0) (sigma omega)).untopA) omega
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hpos' : (⊥ : WithTop ℝ≥0) < sigma omega := by rwa [← h]
    have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    have hmem' : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < sigma omega} := hpos'
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', h]
  · have hpos' : ¬ (⊥ : WithTop ℝ≥0) < sigma omega := by rwa [← h]
    have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    have hmem' : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < sigma omega} := hpos'
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']

/-- Stopped-and-indicated localization is linear under subtraction. -/
theorem localizingStoppedProcess_sub
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess (X - Y) tau =
      localizingStoppedProcess X tau - localizingStoppedProcess Y tau := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  simp only [Pi.sub_apply]
  by_cases hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  · simp only [Set.indicator_of_mem hmem, Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hmem, sub_zero]

/-- At time zero, localization at a positive stopping time leaves the
process unchanged. -/
theorem localizingStoppedProcess_zero_of_pos
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (omega : W) (hpos : (⊥ : WithTop ℝ≥0) < tau omega) :
    localizingStoppedProcess X tau 0 omega = X 0 omega := by
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
  unfold localizingStoppedProcess stoppedProcess
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
    (X (min ((0 : ℝ≥0) : WithTop ℝ≥0) (tau omega)).untopA) omega =
      X 0 omega
  rw [Set.indicator_of_mem hmem,
    show (((0 : ℝ≥0) : WithTop ℝ≥0)) = ⊥ by simp,
    min_eq_left hpos.le]
  rfl

/-- With a strictly positive limiting stop, continuity of stopped paths
under pointwise convergence of stopping times also holds for the
stopped-and-indicated process used by `Locally`. -/
theorem tendsto_localizingStoppedProcess_of_tendsto_of_continuous_of_pos
    {W : Type*} {X : ℝ≥0 → W → ℝ}
    {tauN : ℕ → W → WithTop ℝ≥0} {tau : W → WithTop ℝ≥0}
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (htau : ∀ omega, Tendsto (fun n => tauN n omega)
      Filter.atTop (nhds (tau omega)))
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega)
    (t : ℝ≥0) (omega : W) :
    Tendsto (fun n => localizingStoppedProcess X (tauN n) t omega)
      Filter.atTop (nhds (localizingStoppedProcess X tau t omega)) := by
  have hstop := tendsto_stoppedProcess_of_tendsto_of_continuous
    hXcont htau t omega
  have heventually : ∀ᶠ n in Filter.atTop,
      (⊥ : WithTop ℝ≥0) < tauN n omega :=
    (htau omega) (Ioi_mem_nhds (hpos omega))
  have hmem : omega ∈
      {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos omega
  unfold localizingStoppedProcess
  simp_rw [stoppedProcess_indicator_comm]
  rw [Set.indicator_of_mem hmem]
  apply (tendsto_congr' ?_).2 hstop
  filter_upwards [heventually] with n hn
  have hnmem : omega ∈
      {omega | (⊥ : WithTop ℝ≥0) < tauN n omega} := hn
  rw [Set.indicator_of_mem hnmem]

/-- Localizing a continuous process at its own bounded exit gives the
advertised deterministic pathwise bound, including at the exit itself. -/
theorem norm_localizingStoppedProcess_continuousExitTime_le
    {W : Type*} {Z : ℝ≥0 → W → ℝ}
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R t : ℝ≥0) (omega : W) :
    ‖localizingStoppedProcess Z (continuousExitTime Z T R) t omega‖ ≤ R := by
  let tau := continuousExitTime Z T R
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    dsimp only [tau] at hmem hpos
    change ‖{omega | (⊥ : WithTop ℝ≥0) <
        continuousExitTime Z T R omega}.indicator
      (Z (min (t : WithTop ℝ≥0)
        (continuousExitTime Z T R omega)).untopA) omega‖ ≤ R
    rw [Set.indicator_of_mem hmem, Real.norm_eq_abs]
    by_cases ht : (t : WithTop ℝ≥0) < continuousExitTime Z T R omega
    · rw [min_eq_left ht.le,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact norm_le_of_lt_continuousExitTime hZcont T R t omega ht
    · have htau : continuousExitTime Z T R omega ≤
          (t : WithTop ℝ≥0) := le_of_not_gt ht
      rw [min_eq_right htau]
      exact norm_at_continuousExitTime_le hZcont T R omega hpos
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    dsimp only [tau] at hmem
    change ‖{omega | (⊥ : WithTop ℝ≥0) <
        continuousExitTime Z T R omega}.indicator
      (Z (min (t : WithTop ℝ≥0)
        (continuousExitTime Z T R omega)).untopA) omega‖ ≤ R
    rw [Set.indicator_of_notMem hmem, norm_zero]
    exact R.coe_nonneg

/-- Any localization dominated by a continuous exit of the same process
inherits the exit's deterministic pathwise bound. -/
theorem norm_localizingStoppedProcess_of_le_continuousExitTime
    {W : Type*} {Z : ℝ≥0 → W → ℝ}
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R : ℝ≥0) {tau : W → WithTop ℝ≥0}
    (htau : ∀ omega, tau omega ≤ continuousExitTime Z T R omega)
    (t : ℝ≥0) (omega : W) :
    ‖localizingStoppedProcess Z tau t omega‖ ≤ R := by
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    change ‖{omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (Z (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega‖ ≤ R
    rw [Set.indicator_of_mem hmem, Real.norm_eq_abs]
    let sTop := min (t : WithTop ℝ≥0) (tau omega)
    change |Z sTop.untopA omega| ≤ R
    have hs_ne : sTop ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hscoe : ((sTop.untopA : ℝ≥0) : WithTop ℝ≥0) = sTop := by
      rw [WithTop.untopA_eq_untop hs_ne]
      exact WithTop.coe_untop sTop hs_ne
    have hsle : sTop ≤ continuousExitTime Z T R omega :=
      (min_le_right _ _).trans (htau omega)
    rcases hsle.lt_or_eq with hslt | hseq
    · exact norm_le_of_lt_continuousExitTime hZcont T R sTop.untopA omega
        (by rw [hscoe]; exact hslt)
    · have hexitPos : (⊥ : WithTop ℝ≥0) <
          continuousExitTime Z T R omega := hpos.trans_le (htau omega)
      have hat := norm_at_continuousExitTime_le hZcont T R omega hexitPos
      rw [← hseq] at hat
      simpa only [WithTop.untopA_eq_untop hs_ne,
        WithTop.untop_coe] using hat
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    change ‖{omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (Z (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega‖ ≤ R
    rw [Set.indicator_of_notMem hmem, norm_zero]
    exact R.coe_nonneg

/-- Stopping and applying the local-property indicator preserves any
deterministic pathwise norm bound. -/
theorem norm_localizingStoppedProcess_le
    {W : Type*} {X : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (K : ℝ≥0) (hX : ∀ t omega, ‖X t omega‖ ≤ K)
    (t : ℝ≥0) (omega : W) :
    ‖localizingStoppedProcess X tau t omega‖ ≤ K := by
  unfold localizingStoppedProcess stoppedProcess
  change ‖{omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
    (X (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega‖ ≤ K
  by_cases h : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := h
    rw [Set.indicator_of_mem hmem]
    exact hX _ omega
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := h
    rw [Set.indicator_of_notMem hmem, norm_zero]
    exact K.coe_nonneg

/-- Stopped-and-indicated localization at a bounded continuous exit
preserves path continuity. -/
theorem continuous_localizingStoppedProcess_continuousExitTime
    {W : Type*} {X Z : ℝ≥0 → W → ℝ}
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (T R : ℝ≥0) (omega : W) :
    Continuous (fun t =>
      localizingStoppedProcess X (continuousExitTime Z T R) t omega) := by
  let tau := continuousExitTime Z T R
  have hne : tau omega ≠ ⊤ := continuousExitTime_ne_top Z T R omega
  let a : ℝ≥0 := (tau omega).untopA
  have hcoe : (a : WithTop ℝ≥0) = tau omega := by
    dsimp only [a]
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_untop (tau omega) hne
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
      hpos
    have heq : (fun t =>
        localizingStoppedProcess X (continuousExitTime Z T R) t omega) =
        fun t => X (min t a) omega := by
      funext t
      unfold localizingStoppedProcess stoppedProcess
      dsimp only [tau] at hmem hcoe
      change {omega | (⊥ : WithTop ℝ≥0) <
          continuousExitTime Z T R omega}.indicator
        (X (min (t : WithTop ℝ≥0)
          (continuousExitTime Z T R omega)).untopA) omega =
            X (min t a) omega
      rw [Set.indicator_of_mem hmem, ← hcoe, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [heq]
    exact (hXcont omega).comp (continuous_id.min continuous_const)
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
      hpos
    have heq : (fun t =>
        localizingStoppedProcess X (continuousExitTime Z T R) t omega) =
        0 := by
      funext t
      unfold localizingStoppedProcess stoppedProcess
      dsimp only [tau] at hmem
      change {omega | (⊥ : WithTop ℝ≥0) <
          continuousExitTime Z T R omega}.indicator
        (X (min (t : WithTop ℝ≥0)
          (continuousExitTime Z T R omega)).untopA) omega = 0
      rw [Set.indicator_of_notMem hmem]
    rw [heq]
    exact continuous_zero

/-- Multiplying a martingale by the indicator of an event measurable at
time zero preserves the martingale property. -/
theorem Martingale.indicator_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {Y : ℝ≥0 → W → ℝ} (hY : Martingale Y 𝓥 P)
    {A : Set W} (hA : MeasurableSet[𝓥 0] A) :
    Martingale (fun t => A.indicator (Y t)) 𝓥 P := by
  refine ⟨fun t => (hY.stronglyAdapted t).indicator
    (𝓥.mono bot_le A hA), ?_⟩
  intro s t hst
  have hAs : MeasurableSet[𝓥 s] A := 𝓥.mono bot_le A hA
  exact (condExp_indicator (hY.integrable t) hAs).trans
    (hY.condExp_ae_eq hst).indicator

/-- The stopped-and-indicated localization of a martingale at a finite-range
stopping time is a martingale. -/
theorem martingale_localizingStoppedProcess_of_finiteRange
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (S : Finset ℝ≥0) (htauS : ∀ omega, tau omega ∈ WithTop.some '' S) :
    Martingale (localizingStoppedProcess M tau) 𝒱 P := by
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[𝒱 0] A := by
    change MeasurableSet[𝒱 0]
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) =
      ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  have hstop : Martingale (stoppedProcess M tau) 𝒱 P :=
    martingale_stoppedProcess_of_finiteRange hM htau S htauS
  have heq : localizingStoppedProcess M tau =
      fun t => A.indicator (stoppedProcess M tau t) := by
    funext t
    exact stoppedProcess_indicator_comm t
  rw [heq]
  exact StochasticCalculus.Martingale.indicator_zero hstop hA

/-- A continuous-path martingale remains a martingale after stopping at any
stopping rule admitting uniformly bounded finite-range approximants.  The
approximating stopped values are conditional expectations of one integrable
terminal value, so their uniform integrability is automatic. -/
theorem martingale_stoppedProcess_of_finiteRange_approximation
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0)
    (tauN : ℕ → W → WithTop ℝ≥0)
    (htauN : ∀ n, IsStoppingTime 𝒱 (tauN n))
    (S : ℕ → Finset ℝ≥0)
    (hrange : ∀ n omega, tauN n omega ∈ WithTop.some '' S n)
    (htauNT : ∀ n omega, tauN n omega ≤ T)
    (hconv : ∀ omega, Tendsto (fun n => tauN n omega)
      Filter.atTop (nhds (tau omega))) :
    Martingale (stoppedProcess M tau) 𝒱 P := by
  let sigma : ℕ → ℝ≥0 → W → WithTop ℝ≥0 :=
    fun n t omega => min (t : WithTop ℝ≥0) (tauN n omega)
  have hsigma (n : ℕ) (t : ℝ≥0) : IsStoppingTime 𝒱 (sigma n t) :=
    (isStoppingTime_const 𝒱 t).min (htauN n)
  have hsigmaT (n : ℕ) (t : ℝ≥0) (omega : W) :
      sigma n t omega ≤ (T : WithTop ℝ≥0) :=
    (min_le_right _ _).trans (htauNT n omega)
  have hsigmaRange (n : ℕ) (t : ℝ≥0) :
      (Set.range (sigma n t)).Countable := by
    apply ((S n).finite_toSet.image
      (fun s : ℝ≥0 => min (t : WithTop ℝ≥0) (s : WithTop ℝ≥0))).countable.mono
    rintro x ⟨omega, rfl⟩
    obtain ⟨s, hs, hsEq⟩ := hrange n omega
    exact ⟨s, hs, by simp only [sigma, hsEq]⟩
  have hX (n : ℕ) : Martingale (stoppedProcess M (tauN n)) 𝒱 P :=
    martingale_stoppedProcess_of_finiteRange hM (htauN n) (S n) (hrange n)
  have hYadapt : StronglyAdapted 𝒱 (stoppedProcess M tau) :=
    hM.stronglyAdapted.stoppedProcess hMcont htau
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable hX hYadapt
  · intro t
    have hcond : UniformIntegrable
        (fun n => P[M T | (hsigma n t).measurableSpace]) 1 P :=
      (hM.integrable T).uniformIntegrable_condExp
        (fun n => (hsigma n t).measurableSpace_le)
    apply hcond.ae_eq
    intro n
    have heq := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hsigma n t) (hsigmaT n t) (hsigmaRange n t)
    exact heq.symm
  · intro t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (((hX n).stronglyMeasurable t).mono
        (𝒱.le t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        tendsto_stoppedProcess_of_tendsto_of_continuous
          hMcont hconv t omega

/-- A bounded stopping rule is below some point of every positive uniform
partition of its deterministic bound. -/
theorem exists_uniformPartitionTime_ge
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) : ∃ j : ℕ, tau omega ≤
      (uniformPartitionTime T N j : WithTop ℝ≥0) := by
  refine ⟨N, ?_⟩
  convert hbound omega using 1
  unfold uniformPartitionTime
  exact_mod_cast (mul_div_cancel_right₀ T (Nat.cast_ne_zero.mpr hN.ne'))

/-- The first index of a uniform partition lying at or after a bounded
stopping rule. -/
noncomputable def uniformPartitionCeilIndex
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) : ℕ :=
  Nat.find (exists_uniformPartitionTime_ge tau T N hN hbound omega)

/-- Ceiling approximation of a bounded stopping rule on a uniform
partition. -/
noncomputable def uniformPartitionCeilStoppingTime
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    W → WithTop ℝ≥0 :=
  fun omega => uniformPartitionTime T N
    (uniformPartitionCeilIndex tau T N hN hbound omega)

theorem uniformPartitionCeilIndex_spec
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    tau omega ≤ (uniformPartitionTime T N
      (uniformPartitionCeilIndex tau T N hN hbound omega) :
        WithTop ℝ≥0) := by
  classical
  unfold uniformPartitionCeilIndex
  exact Nat.find_spec
    (exists_uniformPartitionTime_ge tau T N hN hbound omega)

theorem uniformPartitionCeilIndex_le
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    uniformPartitionCeilIndex tau T N hN hbound omega ≤ N := by
  classical
  unfold uniformPartitionCeilIndex
  apply Nat.find_min'
  convert hbound omega using 1
  unfold uniformPartitionTime
  exact_mod_cast (mul_div_cancel_right₀ T (Nat.cast_ne_zero.mpr hN.ne'))

/-- The uniform-partition ceiling of a bounded stopping rule is again a
stopping rule. -/
theorem isStoppingTime_uniformPartitionCeilStoppingTime
    {W : Type*} [MeasurableSpace W]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    IsStoppingTime 𝒱
      (uniformPartitionCeilStoppingTime tau T N hN hbound) := by
  intro t
  let I := {j : ℕ // j ≤ N ∧ uniformPartitionTime T N j ≤ t}
  have heq : {omega |
      uniformPartitionCeilStoppingTime tau T N hN hbound omega ≤
        (t : WithTop ℝ≥0)} =
      ⋃ j : I, {omega | tau omega ≤
        (uniformPartitionTime T N j.1 : WithTop ℝ≥0)} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro homega
      let j := uniformPartitionCeilIndex tau T N hN hbound omega
      refine ⟨⟨j, uniformPartitionCeilIndex_le
        tau T N hN hbound omega, ?_⟩, ?_⟩
      · exact WithTop.coe_le_coe.mp homega
      · exact uniformPartitionCeilIndex_spec
          tau T N hN hbound omega
    · rintro ⟨⟨j, hjN, hjt⟩, htauj⟩
      have hindex : uniformPartitionCeilIndex
          tau T N hN hbound omega ≤ j := by
        unfold uniformPartitionCeilIndex
        exact Nat.find_min'
          (exists_uniformPartitionTime_ge tau T N hN hbound omega)
          htauj
      exact WithTop.coe_le_coe.mpr
        ((monotone_uniformPartitionTime_general T N hindex).trans hjt)
  rw [heq]
  apply MeasurableSet.iUnion
  intro j
  exact 𝒱.mono j.2.2 _ (htau (uniformPartitionTime T N j.1))

theorem uniformPartitionCeilStoppingTime_mem_rangeFinset
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    uniformPartitionCeilStoppingTime tau T N hN hbound omega ∈
      WithTop.some '' ((Finset.range (N + 1)).image
        (uniformPartitionTime T N)) := by
  refine ⟨uniformPartitionTime T N
    (uniformPartitionCeilIndex tau T N hN hbound omega), ?_, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨uniformPartitionCeilIndex tau T N hN hbound omega, ?_, rfl⟩
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le
    (uniformPartitionCeilIndex_le tau T N hN hbound omega)

/-- A ceiling approximation exceeds the original stopping rule by at most
one mesh width. -/
theorem uniformPartitionCeilStoppingTime_le_add_mesh
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    uniformPartitionCeilStoppingTime tau T N hN hbound omega ≤
      tau omega + (T / N : ℝ≥0) := by
  let j := uniformPartitionCeilIndex tau T N hN hbound omega
  by_cases hj : j = 0
  · unfold uniformPartitionCeilStoppingTime
    rw [show uniformPartitionCeilIndex tau T N hN hbound omega = 0
      from hj]
    unfold uniformPartitionTime
    norm_num
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hnot : ¬ tau omega ≤
        (uniformPartitionTime T N i : WithTop ℝ≥0) := by
      have hlt : i < uniformPartitionCeilIndex
          tau T N hN hbound omega := by omega
      unfold uniformPartitionCeilIndex at hlt
      exact Nat.find_min
        (exists_uniformPartitionTime_ge tau T N hN hbound omega) hlt
    have hprev : (uniformPartitionTime T N i : WithTop ℝ≥0) <
        tau omega := lt_of_not_ge hnot
    have hstep : uniformPartitionTime T N (i + 1) =
        uniformPartitionTime T N i + T / N := by
      unfold uniformPartitionTime
      push_cast
      field_simp
    unfold uniformPartitionCeilStoppingTime
    rw [show uniformPartitionCeilIndex tau T N hN hbound omega = i + 1
      from hi, hstep]
    have hadd : (uniformPartitionTime T N i : WithTop ℝ≥0) +
        (T / (N : ℝ≥0) : WithTop ℝ≥0) ≤
        tau omega + (T / (N : ℝ≥0) : WithTop ℝ≥0) := by
      exact add_le_add_left hprev.le _
    simpa only [WithTop.coe_add] using hadd

/-- Uniform-partition ceiling approximants converge pointwise to the bounded
stopping rule. -/
theorem tendsto_uniformPartitionCeilStoppingTime
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    Tendsto (fun n => uniformPartitionCeilStoppingTime tau T (n + 1)
        (Nat.zero_lt_succ n) hbound omega)
      Filter.atTop (nhds (tau omega)) := by
  have htau_ne : tau omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hbound omega)
  lift tau omega to ℝ≥0 using htau_ne with a ha
  have hmesh : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ≥0))
      Filter.atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp
      (tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun n : ℕ => tau omega +
        (T / ((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0))
      Filter.atTop (nhds (tau omega)) := by
    have hsum : Tendsto
        (fun n : ℕ => a + T / ((n + 1 : ℕ) : ℝ≥0))
        Filter.atTop (nhds a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hmesh
    have hcoe := WithTop.continuous_coe.continuousAt.tendsto.comp hsum
    rw [← ha]
    change Tendsto
      (fun n : ℕ => ((a + T / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) :
        WithTop ℝ≥0)) Filter.atTop (nhds (a : WithTop ℝ≥0))
    exact hcoe
  rw [← ha] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun n =>
      (show (a : WithTop ℝ≥0) ≤ _ by
        rw [ha]
        exact uniformPartitionCeilIndex_spec tau T (n + 1)
          (Nat.zero_lt_succ n) hbound omega)
  · exact Filter.Eventually.of_forall fun n =>
      (show _ ≤ (a : WithTop ℝ≥0) +
          (T / ((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) by
        rw [ha]
        exact uniformPartitionCeilStoppingTime_le_add_mesh
          tau T (n + 1) (Nat.zero_lt_succ n) hbound omega)

theorem uniformPartitionCeilStoppingTime_le
    {W : Type*} (tau : W → WithTop ℝ≥0) (T : ℝ≥0) (N : ℕ)
    (hN : 0 < N) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0))
    (omega : W) :
    uniformPartitionCeilStoppingTime tau T N hN hbound omega ≤
      (T : WithTop ℝ≥0) := by
  unfold uniformPartitionCeilStoppingTime
  apply le_trans (WithTop.coe_le_coe.mpr
    (monotone_uniformPartitionTime_general T N
      (uniformPartitionCeilIndex_le tau T N hN hbound omega)))
  apply le_of_eq
  congr 1
  unfold uniformPartitionTime
  exact_mod_cast (mul_div_cancel_right₀ T (Nat.cast_ne_zero.mpr hN.ne'))

/-- Bounded optional stopping for continuous-path martingales over `ℝ≥0`.
Uniform ceiling approximants reduce it to finite-range optional sampling. -/
theorem martingale_stoppedProcess_of_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Martingale (stoppedProcess M tau) 𝒱 P := by
  apply martingale_stoppedProcess_of_finiteRange_approximation
    hM hMcont htau T
    (fun n => uniformPartitionCeilStoppingTime tau T (n + 1)
      (Nat.zero_lt_succ n) hbound)
    (fun n => isStoppingTime_uniformPartitionCeilStoppingTime
      htau T (n + 1) (Nat.zero_lt_succ n) hbound)
    (fun n => (Finset.range (n + 1 + 1)).image
      (uniformPartitionTime T (n + 1)))
  · intro n omega
    exact uniformPartitionCeilStoppingTime_mem_rangeFinset
      tau T (n + 1) (Nat.zero_lt_succ n) hbound omega
  · intro n omega
    exact uniformPartitionCeilStoppingTime_le
      tau T (n + 1) (Nat.zero_lt_succ n) hbound omega
  · intro omega
    exact tendsto_uniformPartitionCeilStoppingTime tau T hbound omega

/-- Bounded optional stopping in the stopped-and-indicated convention used
by `Locally`. -/
theorem martingale_localizingStoppedProcess_of_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Martingale (localizingStoppedProcess M tau) 𝒱 P := by
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[𝒱 0] A := by
    change MeasurableSet[𝒱 0]
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) =
      ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  have hstop : Martingale (stoppedProcess M tau) 𝒱 P :=
    martingale_stoppedProcess_of_bounded hM hMcont htau T hbound
  have heq : localizingStoppedProcess M tau =
      fun t => A.indicator (stoppedProcess M tau t) := by
    funext t
    exact stoppedProcess_indicator_comm t
  rw [heq]
  exact StochasticCalculus.Martingale.indicator_zero hstop hA

/-- Bounded stopped-and-indicated localization preserves a continuous local
martingale. The original localizing sequence still works, because each of its
genuine martingales can be stopped by bounded optional stopping. -/
theorem IsLocalMartingale.localizingStoppedProcess_of_bounded
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    IsLocalMartingale (localizingStoppedProcess M tau) 𝒱 P := by
  change Locally (fun N => Martingale N 𝒱 P) 𝒱 M P at hM
  change Locally (fun N => Martingale N 𝒱 P) 𝒱
    (stoppedProcess
      (fun i => {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator (M i)) tau) P
  refine ⟨hM.localSeq, hM.isLocalizingSequence_localSeq, fun n => ?_⟩
  simp_rw [← stoppedProcess_indicator_comm', Set.indicator_indicator,
    Set.inter_comm, ← Set.indicator_indicator, stoppedProcess_stoppedProcess,
    inf_comm, stoppedProcess_indicator_comm', ← stoppedProcess_stoppedProcess]
  exact martingale_localizingStoppedProcess_of_bounded
    (hM.stoppedProcess_localSeq n)
    (continuous_localizingStoppedProcess hMcont (hM.localSeq n))
    htau T hbound

/-- Paired dyadic exit localization preserves martingales. -/
theorem martingale_localizingStoppedProcess_pairedDyadicHittingTimeNNReal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M Z Q : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hZ : StronglyAdapted 𝒱 Z) (hQ : StronglyAdapted 𝒱 Q)
    (T R S : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess M
        (pairedDyadicHittingTimeNNReal Z Q T R S n)) 𝒱 P := by
  exact martingale_localizingStoppedProcess_of_finiteRange hM
    (isStoppingTime_pairedDyadicHittingTimeNNReal hZ hQ T R S n)
    ((Finset.range (2 ^ n + 1)).image
      (uniformPartitionTime T (2 ^ n)))
    (pairedDyadicHittingTimeNNReal_mem_rangeFinset Z Q T R S n)

/-- The stopped-and-indicated localization of a continuous-path martingale
at its own continuous exit is itself a martingale. -/
theorem martingale_localizingStoppedProcess_continuousExitTime_of_adapted
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M Z : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝓥 Z)
    (T R : ℝ≥0) :
    Martingale
      (localizingStoppedProcess M (continuousExitTime Z T R)) 𝓥 P := by
  let tau := continuousExitTime Z T R
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have htau : IsStoppingTime 𝓥 tau :=
    isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R
  have hA : MeasurableSet[𝓥 0] A := by
    change MeasurableSet[𝓥 0]
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) =
      ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  have hstop : Martingale (stoppedProcess M tau) 𝓥 P :=
    martingale_stoppedProcess_continuousExitTime_of_adapted
      hM hMcont hZ T R
  have heq : localizingStoppedProcess M tau =
      fun t => A.indicator (stoppedProcess M tau t) := by
    funext t
    exact stoppedProcess_indicator_comm t
  rw [heq]
  exact StochasticCalculus.Martingale.indicator_zero hstop hA

/-- The preceding theorem specialized to exit localization of the
martingale itself. -/
theorem martingale_localizingStoppedProcess_continuousExitTime
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T R : ℝ≥0) :
    Martingale
      (localizingStoppedProcess M (continuousExitTime M T R)) 𝓥 P :=
  martingale_localizingStoppedProcess_continuousExitTime_of_adapted
    hM hMcont hM.stronglyAdapted T R

/-- Every fixed-time value of the bounded continuous-exit localization lies
in every `Lᵖ` space over a finite measure. -/
theorem memLp_localizingStoppedProcess_continuousExitTime
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T R t : ℝ≥0) (p : ℝ≥0∞) :
    MemLp
      (localizingStoppedProcess M (continuousExitTime M T R) t) p P := by
  have hmart := martingale_localizingStoppedProcess_continuousExitTime
    hM hMcont T R
  exact MemLp.of_bound
    ((hmart.stronglyAdapted t).mono (𝓥.le t)).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_continuousExitTime_le
        hMcont T R t omega)

/-- A strongly progressive process remains strongly adapted after the
stopped-and-indicated localization used by `Locally`. -/
theorem stronglyAdapted_localizingStoppedProcess_of_isStronglyProgressive
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hX : IsStronglyProgressive 𝓥 X)
    (htau : IsStoppingTime 𝓥 tau) :
    StronglyAdapted 𝓥 (localizingStoppedProcess X tau) := by
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[𝓥 0] A := by
    change MeasurableSet[𝓥 0]
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) =
      ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  intro t
  rw [show localizingStoppedProcess X tau t =
      A.indicator (stoppedProcess X tau t) by
    unfold localizingStoppedProcess
    exact stoppedProcess_indicator_comm t]
  exact (hX.stronglyAdapted_stoppedProcess htau t).indicator
    (𝓥.mono bot_le A hA)

/-- A strongly adapted process with continuous paths is strongly progressive,
so it remains strongly adapted after the stopped-and-indicated localization
used by `Locally`. -/
theorem stronglyAdapted_localizingStoppedProcess
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hX : StronglyAdapted 𝓥 X)
    (hXcont : ∀ omega, Continuous (fun t ↦ X t omega))
    (htau : IsStoppingTime 𝓥 tau) :
    StronglyAdapted 𝓥 (localizingStoppedProcess X tau) := by
  exact stronglyAdapted_localizingStoppedProcess_of_isStronglyProgressive
    (hX.isStronglyProgressive_of_continuous hXcont) htau

/-- Positive pointwise limits of stopping times may be passed through a
continuous adapted process in convergence in measure. -/
theorem
    tendstoInMeasure_localizingStoppedProcess_of_tendsto_of_continuous_of_pos
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} {tauN : ℕ → W → WithTop ℝ≥0}
    {tau : W → WithTop ℝ≥0}
    (hX : StronglyAdapted 𝒱 X)
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (htauN : ∀ n, IsStoppingTime 𝒱 (tauN n))
    (htau : ∀ omega, Tendsto (fun n => tauN n omega)
      Filter.atTop (nhds (tau omega)))
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess X (tauN n) t)
      Filter.atTop (localizingStoppedProcess X tau t) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact ((stronglyAdapted_localizingStoppedProcess
      hX hXcont (htauN n) t).mono (𝒱.le t)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega =>
      tendsto_localizingStoppedProcess_of_tendsto_of_continuous_of_pos
        hXcont htau hpos t omega

/-- For a positive minimum exit, paired dyadic localizations of a continuous
adapted process converge in measure to localization at the paired continuous
exit. -/
theorem
    tendstoInMeasure_localizingStoppedProcess_pairedDyadic_of_pos
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X Z Q : ℝ≥0 → W → ℝ}
    (hX : StronglyAdapted 𝒱 X)
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (hZ : StronglyAdapted 𝒱 Z) (hQ : StronglyAdapted 𝒱 Q)
    (T R S : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega)) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess X
        (pairedDyadicHittingTimeNNReal Z Q T R S n) t)
      Filter.atTop
      (localizingStoppedProcess X
        (fun omega => min (continuousExitTime Z T R omega)
          (continuousExitTime Q T S omega)) t) := by
  exact
    tendstoInMeasure_localizingStoppedProcess_of_tendsto_of_continuous_of_pos
      hX hXcont
      (fun n => isStoppingTime_pairedDyadicHittingTimeNNReal
        hZ hQ T R S n)
      (fun omega =>
        tendsto_pairedDyadicHittingTimeNNReal_continuousExitTime
          Z Q T R S omega)
      hpos t

/-- A fixed localizing sequence passes local martingality through
pointwise-in-time `L¹`-norm limits.  Stopped adaptation supplies measurability,
while convergence itself supplies integrability; the conclusion repackages
the resulting stopped martingales as a local martingale. -/
theorem isLocalMartingale_of_stopped_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence 𝓥 tau P)
    (hX : ∀ n k, Martingale
      (localizingStoppedProcess (X n) (tau k)) 𝓥 P)
    (hYadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess Y (tau k)))
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess Y (tau k) t -
        localizingStoppedProcess (X n) (tau k) t) 1 P)
      Filter.atTop (𝓝 0)) :
    IsLocalMartingale Y 𝓥 P := by
  refine ⟨tau, htau, fun k ↦ ?_⟩
  change Martingale (localizingStoppedProcess Y (tau k)) 𝓥 P
  exact martingale_of_tendsto_eLpNorm_one
    (fun n ↦ hX n k) (hYadapt k) (hconv k)

/-- Localized Vitali closure: stopped convergence in measure and stopped
uniform integrability pass martingality through a fixed localizing sequence. -/
theorem isLocalMartingale_of_stopped_tendstoInMeasure_of_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence 𝓥 tau P)
    (hX : ∀ n k, Martingale
      (localizingStoppedProcess (X n) (tau k)) 𝓥 P)
    (hYadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess Y (tau k)))
    (hUI : ∀ k t, UniformIntegrable
      (fun n ↦ localizingStoppedProcess (X n) (tau k) t) 1 P)
    (hconv : ∀ k t, TendstoInMeasure P
      (fun n ↦ localizingStoppedProcess (X n) (tau k) t)
      Filter.atTop (localizingStoppedProcess Y (tau k) t)) :
    IsLocalMartingale Y 𝓥 P := by
  refine ⟨tau, htau, fun k ↦ ?_⟩
  change Martingale (localizingStoppedProcess Y (tau k)) 𝓥 P
  exact martingale_of_tendstoInMeasure_of_uniformIntegrable
    (fun n ↦ hX n k) (hYadapt k) (hUI k) (hconv k)

/-- A uniform-in-time error majorant converging in measure controls
evaluation after any bounded random stopping time.  This is the reusable
analytic interface needed to pass deterministic approximation estimates
through the continuous-exit localizers. -/
theorem tendstoInMeasure_localizingStoppedProcess_of_uniform_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    {U : ℕ → W → ℝ} {tau : W → WithTop ℝ≥0} (S : ℝ≥0)
    (htau : ∀ omega, tau omega ≤ S)
    (hbound : ∀ n s omega, s ≤ S →
      |X n s omega - Y s omega| ≤ |U n omega|)
    (hU : TendstoInMeasure P U Filter.atTop (fun _ => 0))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess (X n) tau t)
      Filter.atTop (localizingStoppedProcess Y tau t) := by
  rw [tendstoInMeasure_iff_norm] at hU ⊢
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hU epsilon hepsilon) ?_ ?_
  · intro n
    exact bot_le
  · intro n
    apply measure_mono
    intro omega homega
    have hnorm : ‖localizingStoppedProcess (X n) tau t omega -
        localizingStoppedProcess Y tau t omega‖ ≤ ‖U n omega‖ := by
      unfold localizingStoppedProcess stoppedProcess
      change ‖{omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
          (X n (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega -
        {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
          (Y (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega‖ ≤
        ‖U n omega‖
      by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
      · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
          hpos
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        let sTop := min (t : WithTop ℝ≥0) (tau omega)
        have hs_ne : sTop ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
        have hscoe : ((sTop.untopA : ℝ≥0) : WithTop ℝ≥0) = sTop := by
          rw [WithTop.untopA_eq_untop hs_ne]
          exact WithTop.coe_untop sTop hs_ne
        have hsS : sTop.untopA ≤ S := by
          apply WithTop.coe_le_coe.mp
          rw [hscoe]
          exact (min_le_right _ _).trans (htau omega)
        simpa only [Real.norm_eq_abs] using hbound n sTop.untopA omega hsS
      · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
          hpos
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
          sub_self, norm_zero]
        exact norm_nonneg _
    change epsilon ≤ ‖U n omega - 0‖
    simpa only [sub_zero] using homega.trans hnorm

/-- Pointwise-in-time convergence in measure can be evaluated at a
finite-range stopping time.  The stopped value is a finite sum over the
stopping-time fibers, so no uniform-in-time convergence is needed here. -/
theorem tendstoInMeasure_stoppedProcess_of_finiteRange
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    {tau : W → WithTop ℝ≥0} (S : Finset ℝ≥0)
    (htauS : ∀ omega, tau omega ∈ WithTop.some '' S)
    (hconv : ∀ s, TendstoInMeasure P (fun n => X n s)
      Filter.atTop (Y s)) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => stoppedProcess (X n) tau t)
      Filter.atTop (stoppedProcess Y tau t) := by
  classical
  let R := S.filter (fun i => i < t)
  have hzero : TendstoInMeasure P
      (fun _ : ℕ => fun _ : W => (0 : ℝ)) Filter.atTop
      (fun _ : W => 0) := by
    simpa only [zero_mul] using
      (hconv t).const_mul_real_noMeas 0
  have hsum : TendstoInMeasure P
      (fun n omega => ∑ i ∈ R,
        {omega | tau omega = (i : WithTop ℝ≥0)}.indicator (X n i) omega)
      Filter.atTop
      (fun omega => ∑ i ∈ R,
        {omega | tau omega = (i : WithTop ℝ≥0)}.indicator (Y i) omega) := by
    induction R using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hzero
    | @insert i R hi hind =>
        have hhead := (hconv i).indicator
          {omega | tau omega = (i : WithTop ℝ≥0)}
        simpa only [Finset.sum_insert hi] using
          hhead.add_real_noMeas hind
  have hterminal := (hconv t).indicator
    {omega | (t : WithTop ℝ≥0) ≤ tau omega}
  have htotal := hterminal.add_real_noMeas hsum
  apply htotal.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by
      rw [stoppedProcess_eq_of_mem_finset t (fun omega _ => htauS omega)]
      simp only [R, Finset.sum_apply, Pi.add_apply]
  · exact Filter.Eventually.of_forall fun omega => by
      rw [stoppedProcess_eq_of_mem_finset t (fun omega _ => htauS omega)]
      simp only [R, Finset.sum_apply, Pi.add_apply]

/-- The finite-range evaluation theorem also respects the exceptional-event
indicator in Mathlib's `Locally` convention. -/
theorem tendstoInMeasure_localizingStoppedProcess_of_finiteRange
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    {tau : W → WithTop ℝ≥0} (S : Finset ℝ≥0)
    (htauS : ∀ omega, tau omega ∈ WithTop.some '' S)
    (hconv : ∀ s, TendstoInMeasure P (fun n => X n s)
      Filter.atTop (Y s)) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess (X n) tau t)
      Filter.atTop (localizingStoppedProcess Y tau t) := by
  have hstop := tendstoInMeasure_stoppedProcess_of_finiteRange
    S htauS hconv t
  have hindicator := hstop.indicator
    {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  apply hindicator.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by
      unfold localizingStoppedProcess
      rw [stoppedProcess_indicator_comm]
  · exact Filter.Eventually.of_forall fun omega => by
      unfold localizingStoppedProcess
      rw [stoppedProcess_indicator_comm]

/-- A two-parameter convergence-in-measure argument may be passed through
uniform approximation of the outer sequence.  The error majorant `U m` is
independent of the outer index `n`; this is the form supplied by a uniform
martingale-modulus estimate when finite-grid stops approximate a continuous
stop. -/
theorem tendstoInMeasure_of_uniform_approximation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : ℕ → W → ℝ} {fm : ℕ → ℕ → W → ℝ}
    {gm U : ℕ → W → ℝ} {g : W → ℝ}
    (happrox : ∀ m n omega,
      ‖f n omega - fm m n omega‖ ≤ ‖U m omega‖)
    (hU : TendstoInMeasure P U Filter.atTop (fun _ => 0))
    (hmiddle : ∀ m, TendstoInMeasure P (fm m) Filter.atTop (gm m))
    (hright : TendstoInMeasure P gm Filter.atTop g) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [tendstoInMeasure_iff_norm] at hU hright ⊢
  intro epsilon hepsilon
  rw [ENNReal.tendsto_atTop_zero]
  intro delta hdelta
  have hepsilonThird : 0 < epsilon / 3 := by
    positivity
  have hdeltaThird : 0 < delta / 3 := by
    exact ENNReal.div_pos hdelta.ne' ENNReal.ofNat_ne_top
  have hU' := hU (epsilon / 3) hepsilonThird
  have hright' := hright (epsilon / 3) hepsilonThird
  rw [ENNReal.tendsto_atTop_zero] at hU' hright'
  obtain ⟨mU, hmU⟩ := hU' (delta / 3) hdeltaThird
  obtain ⟨mright, hmright⟩ := hright' (delta / 3) hdeltaThird
  let m := max mU mright
  have hUm : P {omega | epsilon / 3 ≤ ‖U m omega - 0‖} ≤
      delta / 3 := hmU m (le_max_left _ _)
  have hrightm :
      P {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖} ≤
        delta / 3 := hmright m (le_max_right _ _)
  have hmiddle' := hmiddle m
  rw [tendstoInMeasure_iff_norm] at hmiddle'
  have hmiddleEpsilon := hmiddle' (epsilon / 3) hepsilonThird
  rw [ENNReal.tendsto_atTop_zero] at hmiddleEpsilon
  obtain ⟨N, hN⟩ := hmiddleEpsilon (delta / 3) hdeltaThird
  refine ⟨N, fun n hn => ?_⟩
  calc
    P {omega | epsilon ≤ ‖f n omega - g omega‖} ≤
        P ({omega | epsilon / 3 ≤ ‖U m omega - 0‖} ∪
          {omega | epsilon / 3 ≤ ‖fm m n omega - gm m omega‖} ∪
          {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_contra hnot
      push Not at hnot
      have hleftSmall : ‖f n omega - fm m n omega‖ < epsilon / 3 :=
        lt_of_le_of_lt (happrox m n omega) (by simpa using hnot.1.1)
      have hmiddleSmall :
          ‖fm m n omega - gm m omega‖ < epsilon / 3 := hnot.1.2
      have hrightSmall : ‖gm m omega - g omega‖ < epsilon / 3 :=
        hnot.2
      have htriangle : ‖f n omega - g omega‖ ≤
          ‖f n omega - fm m n omega‖ +
            ‖fm m n omega - gm m omega‖ +
              ‖gm m omega - g omega‖ := by
        calc
          ‖f n omega - g omega‖ =
              ‖(f n omega - fm m n omega) +
                (fm m n omega - gm m omega) +
                  (gm m omega - g omega)‖ := by ring_nf
          _ ≤ ‖(f n omega - fm m n omega) +
                (fm m n omega - gm m omega)‖ +
              ‖gm m omega - g omega‖ := norm_add_le _ _
          _ ≤ (‖f n omega - fm m n omega‖ +
                ‖fm m n omega - gm m omega‖) +
              ‖gm m omega - g omega‖ :=
            add_le_add (norm_add_le _ _) le_rfl
      have hsmall : ‖f n omega - g omega‖ < epsilon := by
        calc
          ‖f n omega - g omega‖ ≤ _ := htriangle
          _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
            gcongr
          _ = epsilon := by ring
      exact (not_lt_of_ge homega) hsmall
    _ ≤ P {omega | epsilon / 3 ≤ ‖U m omega - 0‖} +
          P {omega | epsilon / 3 ≤ ‖fm m n omega - gm m omega‖} +
          P {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖} := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ delta / 3 + delta / 3 + delta / 3 := by
      gcongr
      exact hN n hn
    _ = delta := ENNReal.add_thirds delta

/-- A two-parameter convergence-in-measure argument may be passed through
an approximation whose error tends to zero in measure uniformly in the
outer index.  Unlike `tendstoInMeasure_of_uniform_approximation`, this
version asks directly for the uniform probability estimate and therefore
does not require a pointwise random majorant. -/
theorem tendstoInMeasure_of_uniform_approximation_in_measure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : ℕ → W → ℝ} {fm : ℕ → ℕ → W → ℝ}
    {gm : ℕ → W → ℝ} {g : W → ℝ}
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ M, ∀ m, M ≤ m → ∀ n,
          P {omega | epsilon ≤ ‖f n omega - fm m n omega‖} ≤ delta)
    (hmiddle : ∀ m, TendstoInMeasure P (fm m) Filter.atTop (gm m))
    (hright : TendstoInMeasure P gm Filter.atTop g) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [tendstoInMeasure_iff_norm] at hright ⊢
  intro epsilon hepsilon
  rw [ENNReal.tendsto_atTop_zero]
  intro delta hdelta
  have hepsilonThird : 0 < epsilon / 3 := by positivity
  have hdeltaThird : 0 < delta / 3 :=
    ENNReal.div_pos hdelta.ne' ENNReal.ofNat_ne_top
  obtain ⟨mapprox, hmapprox⟩ :=
    happrox (epsilon / 3) hepsilonThird (delta / 3) hdeltaThird
  have hright' := hright (epsilon / 3) hepsilonThird
  rw [ENNReal.tendsto_atTop_zero] at hright'
  obtain ⟨mright, hmright⟩ := hright' (delta / 3) hdeltaThird
  let m := max mapprox mright
  have hleftm : ∀ n,
      P {omega | epsilon / 3 ≤ ‖f n omega - fm m n omega‖} ≤
        delta / 3 :=
    hmapprox m (le_max_left _ _)
  have hrightm :
      P {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖} ≤
        delta / 3 := hmright m (le_max_right _ _)
  have hmiddle' := hmiddle m
  rw [tendstoInMeasure_iff_norm] at hmiddle'
  have hmiddleEpsilon := hmiddle' (epsilon / 3) hepsilonThird
  rw [ENNReal.tendsto_atTop_zero] at hmiddleEpsilon
  obtain ⟨N, hN⟩ := hmiddleEpsilon (delta / 3) hdeltaThird
  refine ⟨N, fun n hn => ?_⟩
  calc
    P {omega | epsilon ≤ ‖f n omega - g omega‖} ≤
        P ({omega | epsilon / 3 ≤ ‖f n omega - fm m n omega‖} ∪
          {omega | epsilon / 3 ≤ ‖fm m n omega - gm m omega‖} ∪
          {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_contra hnot
      push Not at hnot
      have hleftSmall : ‖f n omega - fm m n omega‖ < epsilon / 3 :=
        hnot.1.1
      have hmiddleSmall :
          ‖fm m n omega - gm m omega‖ < epsilon / 3 := hnot.1.2
      have hrightSmall : ‖gm m omega - g omega‖ < epsilon / 3 :=
        hnot.2
      have htriangle : ‖f n omega - g omega‖ ≤
          ‖f n omega - fm m n omega‖ +
            ‖fm m n omega - gm m omega‖ +
              ‖gm m omega - g omega‖ := by
        calc
          ‖f n omega - g omega‖ =
              ‖(f n omega - fm m n omega) +
                (fm m n omega - gm m omega) +
                  (gm m omega - g omega)‖ := by ring_nf
          _ ≤ ‖(f n omega - fm m n omega) +
                (fm m n omega - gm m omega)‖ +
              ‖gm m omega - g omega‖ := norm_add_le _ _
          _ ≤ (‖f n omega - fm m n omega‖ +
                ‖fm m n omega - gm m omega‖) +
              ‖gm m omega - g omega‖ :=
            add_le_add (norm_add_le _ _) le_rfl
      have hsmall : ‖f n omega - g omega‖ < epsilon := by
        calc
          ‖f n omega - g omega‖ ≤ _ := htriangle
          _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
            gcongr
          _ = epsilon := by ring
      exact (not_lt_of_ge homega) hsmall
    _ ≤ P {omega | epsilon / 3 ≤ ‖f n omega - fm m n omega‖} +
          P {omega | epsilon / 3 ≤ ‖fm m n omega - gm m omega‖} +
          P {omega | epsilon / 3 ≤ ‖gm m omega - g omega‖} := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ delta / 3 + delta / 3 + delta / 3 := by
      gcongr
      · exact hleftm n
      · exact hN n hn
    _ = delta := ENNReal.add_thirds delta

/-- A grid-uniform `L²` error bound tending to zero implies the uniform
convergence-in-probability estimate used by
`tendstoInMeasure_of_uniform_approximation_in_measure`. -/
theorem uniform_approximation_in_measure_of_eLpNorm
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : ℕ → W → ℝ} {fm : ℕ → ℕ → W → ℝ}
    {V : ℕ → ℝ≥0∞}
    (hmeas : ∀ m n, AEStronglyMeasurable (f n - fm m n) P)
    (hV : Tendsto V Filter.atTop (nhds 0))
    (hbound : ∀ m n, eLpNorm (f n - fm m n) 2 P ≤ V m) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ M, ∀ m, M ≤ m → ∀ n,
          P {omega | epsilon ≤ ‖f n omega - fm m n omega‖} ≤ delta := by
  intro epsilon hepsilon delta hdelta
  let e : ℝ≥0∞ := ENNReal.ofReal epsilon
  have he : 0 < e := ENNReal.ofReal_pos.mpr hepsilon
  let target : ℝ≥0∞ := min 1 (e ^ (2 : ℝ) * delta)
  have htarget : 0 < target := by
    dsimp only [target]
    exact lt_min zero_lt_one
      (ENNReal.mul_pos (ENNReal.rpow_pos he (by finiteness)).ne'
        hdelta.ne')
  rw [ENNReal.tendsto_atTop_zero] at hV
  obtain ⟨M, hM⟩ := hV target htarget
  refine ⟨M, fun m hm n ↦ ?_⟩
  have hVm : V m ≤ target := hM m hm
  have hVone : V m ≤ 1 := hVm.trans (min_le_left _ _)
  have hVtarget : V m ≤ e ^ (2 : ℝ) * delta :=
    hVm.trans (min_le_right _ _)
  have hVsquare : V m ^ (2 : ℝ) ≤ V m :=
    ENNReal.rpow_le_self_of_le_one hVone (by norm_num)
  have hmarkov := MeasureTheory.mul_meas_ge_le_pow_eLpNorm'
    (p := (2 : ℝ≥0∞)) P (by norm_num) (by norm_num) (hmeas m n) e
  have he_ne : e ^ (2 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos he (by finiteness)).ne'
  have he_top : e ^ (2 : ℝ) ≠ ∞ := by
    finiteness
  rw [← ENNReal.mul_le_mul_iff_right he_ne he_top]
  calc
    e ^ (2 : ℝ) *
        P {omega | epsilon ≤ ‖f n omega - fm m n omega‖} =
        e ^ (2 : ℝ) *
          P {omega | e ≤ ‖(f n - fm m n) omega‖ₑ} := by
      congr 2
      ext omega
      simp only [Pi.sub_apply, Set.mem_ofPred_eq, e]
      rw [← ofReal_norm,
        ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    _ ≤ eLpNorm (f n - fm m n) 2 P ^ (2 : ℝ) := by
      simpa only [ENNReal.toReal_ofNat] using hmarkov
    _ ≤ V m ^ (2 : ℝ) := by
      exact ENNReal.rpow_le_rpow (hbound m n) (by norm_num)
    _ ≤ V m := hVsquare
    _ ≤ e ^ (2 : ℝ) * delta := hVtarget

/-- On a finite measure space, convergence in measure plus a common
deterministic pointwise bound upgrades to convergence in `L²`. -/
theorem tendsto_eLpNorm_two_of_tendstoInMeasure_of_uniform_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {f : ℕ → W → ℝ} {g : W → ℝ}
    (hfmeas : ∀ n, AEStronglyMeasurable (f n) P)
    (hgmeas : AEStronglyMeasurable g P) (K : ℝ≥0)
    (hfbound : ∀ n omega, ‖f n omega‖ ≤ K)
    (hgbound : ∀ omega, ‖g omega‖ ≤ K)
    (hconv : TendstoInMeasure P f Filter.atTop g) :
    Tendsto (fun n => eLpNorm (f n - g) 2 P)
      Filter.atTop (nhds 0) := by
  have hgLp : MemLp g 2 P :=
    MemLp.of_bound hgmeas K (Filter.Eventually.of_forall hgbound)
  have hui : UnifIntegrable f 2 P := by
    apply unifIntegrable_of one_le_two (by norm_num) hfmeas
    intro epsilon hepsilon
    refine ⟨K + 1, fun n => ?_⟩
    have hempty : {omega | K + 1 ≤ ‖f n omega‖₊} = ∅ := by
      ext omega
      change (K + 1 ≤ ‖f n omega‖₊) ↔ False
      have hnorm : ‖f n omega‖₊ ≤ K := by
        exact_mod_cast hfbound n omega
      constructor
      · exact fun h => (not_le_of_gt (hnorm.trans_lt (lt_add_one K))) h
      · exact False.elim
    rw [hempty]
    simp only [Set.indicator_empty]
    exact eLpNorm_zero.trans_le bot_le
  exact tendsto_Lp_finite_of_tendstoInMeasure one_le_two (by norm_num)
    hfmeas hgLp hui hconv

/-- Stopping a continuous adapted controller at paired dyadic exits capped
by larger continuous exits converges in `L²` to stopping at the inner paired
continuous exit.  The outer exit supplies the common deterministic bound. -/
theorem
    tendsto_eLpNorm_two_localizingStoppedProcess_pairedDyadic_min_outerExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {Z Q : ℝ≥0 → W → ℝ}
    (hZ : StronglyAdapted 𝒱 Z) (hQ : StronglyAdapted 𝒱 Q)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T R S R' S' : ℝ≥0) (hRR' : R ≤ R') (hSS' : S ≤ S')
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime Z T R omega)
        (continuousExitTime Q T S omega)) (t : ℝ≥0) :
    Tendsto
      (fun n => eLpNorm
        (localizingStoppedProcess Z
            (fun omega => min
              (pairedDyadicHittingTimeNNReal Z Q T R S n omega)
              (min (continuousExitTime Z T R' omega)
                (continuousExitTime Q T S' omega))) t -
          localizingStoppedProcess Z
            (fun omega => min (continuousExitTime Z T R omega)
              (continuousExitTime Q T S omega)) t) 2 P)
      Filter.atTop (nhds 0) := by
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime Z T R omega)
      (continuousExitTime Q T S omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime Z T R' omega)
      (continuousExitTime Q T S' omega)
  let rho : ℕ → W → WithTop ℝ≥0 := fun n omega =>
    min (pairedDyadicHittingTimeNNReal Z Q T R S n omega) (theta omega)
  have htauStop : IsStoppingTime 𝒱 tau :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hQ T S)
  have hrhoStop (n : ℕ) : IsStoppingTime 𝒱 (rho n) :=
    (isStoppingTime_pairedDyadicHittingTimeNNReal hZ hQ T R S n).min
      ((isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R').min
        (isStoppingTime_continuousExitTime_of_stronglyAdapted hQ T S'))
  have hrhoTendsto : ∀ omega, Tendsto (fun n => rho n omega)
      Filter.atTop (nhds (tau omega)) := by
    intro omega
    exact tendsto_pairedDyadic_min_outerContinuousExit
      Z Q T R S R' S' hRR' hSS' omega
  have hconv : TendstoInMeasure P
      (fun n => localizingStoppedProcess Z (rho n) t)
      Filter.atTop (localizingStoppedProcess Z tau t) :=
    tendstoInMeasure_localizingStoppedProcess_of_tendsto_of_continuous_of_pos
      hZ hZcont hrhoStop hrhoTendsto hpos t
  have hfmeas (n : ℕ) : AEStronglyMeasurable
      (localizingStoppedProcess Z (rho n) t) P :=
    ((stronglyAdapted_localizingStoppedProcess hZ hZcont (hrhoStop n) t).mono
      (𝒱.le t)).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable
      (localizingStoppedProcess Z tau t) P :=
    ((stronglyAdapted_localizingStoppedProcess hZ hZcont htauStop t).mono
      (𝒱.le t)).aestronglyMeasurable
  have hrho_le (n : ℕ) (omega : W) :
      rho n omega ≤ continuousExitTime Z T R' omega :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htau_le (omega : W) :
      tau omega ≤ continuousExitTime Z T R' omega :=
    (min_le_left _ _).trans
      (continuousExitTime_mono_radius Z T R R' hRR' omega)
  apply tendsto_eLpNorm_two_of_tendstoInMeasure_of_uniform_bound
    hfmeas hgmeas R'
  · intro n omega
    exact norm_localizingStoppedProcess_of_le_continuousExitTime
      hZcont T R' (hrho_le n) t omega
  · intro omega
    exact norm_localizingStoppedProcess_of_le_continuousExitTime
      hZcont T R' htau_le t omega
  · exact hconv

/-- Convergence in measure of real-valued sequences is preserved by
pointwise addition.  The proof uses the subsequence characterization and
diagonal extraction, retaining almost-everywhere convergence of both
summands. -/
theorem TendstoInMeasure.add_real
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {f g : ℕ → W → ℝ} {F G : W → ℝ}
    (hfmeas : ∀ n, AEStronglyMeasurable (f n) P)
    (hgmeas : ∀ n, AEStronglyMeasurable (g n) P)
    (hf : TendstoInMeasure P f Filter.atTop F)
    (hg : TendstoInMeasure P g Filter.atTop G) :
    TendstoInMeasure P (fun n omega ↦ f n omega + g n omega)
      Filter.atTop (fun omega ↦ F omega + G omega) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n ↦ (hfmeas n).add (hgmeas n))).2
  intro ns hns
  obtain ⟨ks, hks, hf_ae⟩ :=
    (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hnsk : StrictMono (ns ∘ ks) := hns.comp hks
  obtain ⟨ls, hls, hg_ae⟩ :=
    (hg.comp hnsk.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ks ∘ ls, hks.comp hls, ?_⟩
  filter_upwards [hf_ae, hg_ae] with omega hfomega hgomega
  exact (hfomega.comp hls.tendsto_atTop).add hgomega

/-- The stochastic integral of a finite elementary predictable integrand
against `M`: each summand has a bounded coefficient known at its left
endpoint and is supported on its own deterministic interval. -/
def elementaryMartingaleIntegralSum
    {W I : Type*} (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → ℝ) : ℝ≥0 → W → ℝ :=
  ∑ i ∈ S, elementaryMartingaleIntegralProcess M (a i) (b i) (Z i)

/-- Finite elementary stochastic-integral sums inherit path continuity from
their integrator. -/
theorem continuous_elementaryMartingaleIntegralSum
    {W I : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (S : Finset I) (a b : I → ℝ≥0) (Z : I → W → ℝ) (omega : W) :
    Continuous (fun t =>
      elementaryMartingaleIntegralSum M S a b Z t omega) := by
  unfold elementaryMartingaleIntegralSum
  simp only [Finset.sum_apply]
  exact continuous_finsetSum S fun i _ =>
    continuous_elementaryMartingaleIntegralProcess
      hMcont (a i) (b i) (Z i) omega

/-- Finite elementary predictable integrals preserve strong adaptation. -/
theorem stronglyAdapted_elementaryMartingaleIntegralSum
    {W I : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → ℝ}
    (hZ : ∀ i ∈ S, StronglyMeasurable[𝓥 (a i)] (Z i)) :
    StronglyAdapted 𝓥 (elementaryMartingaleIntegralSum M S a b Z) := by
  unfold elementaryMartingaleIntegralSum
  exact StronglyAdapted.finset_sum S fun i hi ↦
    stronglyAdapted_elementaryMartingaleIntegralProcess
      hM (hab i hi) (hZ i hi)

/-- Finite elementary predictable stochastic integrals against an arbitrary
martingale are martingales. -/
theorem martingale_elementaryMartingaleIntegralSum
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → ℝ}
    (hZ : ∀ i ∈ S, StronglyMeasurable[𝓥 (a i)] (Z i))
    (C : I → ℝ) (hZbound : ∀ i ∈ S, ∀ omega, ‖Z i omega‖ ≤ C i) :
    Martingale (elementaryMartingaleIntegralSum M S a b Z) 𝓥 P := by
  unfold elementaryMartingaleIntegralSum
  exact Martingale.finset_sum S fun i hi ↦
    martingale_elementaryMartingaleIntegralProcess hM (hab i hi)
      (hZ i hi) (C i) (hZbound i hi)

/-- Stopping an indicator of a pointwise finite sum is the finite sum of the
individually stopped indicators. -/
theorem stoppedProcess_indicator_finset_sum
    {W I : Type*} (X : I → ℝ≥0 → W → ℝ) (S : Finset I)
    (A : Set W) (tau : W → WithTop ℝ≥0) :
    stoppedProcess (fun t ↦ A.indicator ((∑ i ∈ S, X i) t)) tau =
      ∑ i ∈ S, stoppedProcess (fun t ↦ A.indicator (X i t)) tau := by
  classical
  funext t omega
  simp only [stoppedProcess, Finset.sum_apply]
  by_cases hA : omega ∈ A
  · simp only [Set.indicator_of_mem hA, Finset.sum_apply]
  · simp only [Set.indicator_of_notMem hA, Finset.sum_const_zero]

/-- Finite elementary stochastic integrals commute with stopped-process
localization term by term. -/
theorem stoppedProcess_indicator_elementaryMartingaleIntegralSum
    {W I : Type*} (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → ℝ)
    (A : Set W) (tau : W → WithTop ℝ≥0) :
    stoppedProcess
        (fun t ↦ A.indicator
          (elementaryMartingaleIntegralSum M S a b Z t)) tau =
      elementaryMartingaleIntegralSum
        (stoppedProcess (fun t ↦ A.indicator (M t)) tau) S a b Z := by
  classical
  unfold elementaryMartingaleIntegralSum
  rw [stoppedProcess_indicator_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact stoppedProcess_indicator_elementaryMartingaleIntegralProcess
    M (a i) (b i) (Z i) A tau

/-- A finite elementary predictable integral against a local martingale is a
local martingale.  Every summand shares the integrator's localizing sequence,
so no separate localizer-combination or optional-stopping theorem is needed. -/
theorem IsLocalMartingale.elementaryMartingaleIntegralSum
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → ℝ}
    (hZ : ∀ i ∈ S, StronglyMeasurable[𝓥 (a i)] (Z i))
    (C : I → ℝ) (hZbound : ∀ i ∈ S, ∀ omega, ‖Z i omega‖ ≤ C i) :
    IsLocalMartingale (elementaryMartingaleIntegralSum M S a b Z) 𝓥 P := by
  rcases hM with ⟨tau, htau, hstopped⟩
  refine ⟨tau, htau, fun n ↦ ?_⟩
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau n omega}
  let N : ℝ≥0 → W → ℝ :=
    stoppedProcess (fun i ↦ A.indicator (M i)) (tau n)
  have hN : Martingale N 𝓥 P := hstopped n
  have hIntegral : Martingale
      (StochasticCalculus.elementaryMartingaleIntegralSum N S a b Z) 𝓥 P :=
    martingale_elementaryMartingaleIntegralSum hN S hab hZ C hZbound
  change Martingale (stoppedProcess
    (fun t ↦ A.indicator
      (StochasticCalculus.elementaryMartingaleIntegralSum M S a b Z t)) (tau n)) 𝓥 P
  rw [stoppedProcess_indicator_elementaryMartingaleIntegralSum]
  exact hIntegral

/-- The coherent uniform-grid left-sum process for a general time-dependent
integrand `H` and integrator `M`. -/
def uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  elementaryMartingaleIntegralSum M (Finset.range n)
    (fun i ↦ uniformPartitionTime T n i)
    (fun i ↦ uniformPartitionTime T n (i + 1))
    (fun i ↦ H (uniformPartitionTime T n i))

/-- Coherent uniform-grid left-sum processes inherit path continuity from
their integrator. -/
theorem continuous_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} {M H : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    Continuous (fun t =>
      uniformAdaptedMartingaleLeftSumProcess M H T n t omega) := by
  exact continuous_elementaryMartingaleIntegralSum hMcont
    (Finset.range n)
    (fun i => uniformPartitionTime T n i)
    (fun i => uniformPartitionTime T n (i + 1))
    (fun i => H (uniformPartitionTime T n i)) omega

/-- A positive-grid coherent uniform left-sum process is constant after its
deterministic terminal horizon. -/
theorem uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (hTt : T ≤ t) :
    uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) t =
      uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T := by
  funext omega
  unfold uniformAdaptedMartingaleLeftSumProcess
    elementaryMartingaleIntegralSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold elementaryMartingaleIntegralProcess
  have hi' : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have haT : uniformPartitionTime T (n + 1) i ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (by omega) (Nat.le_trans
      (Nat.le_succ i) hi')).2
  have hbT : uniformPartitionTime T (n + 1) (i + 1) ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (by omega) hi').2
  rw [min_eq_right (haT.trans hTt), min_eq_right (hbT.trans hTt),
    min_eq_right haT, min_eq_right hbT]

/-- Stopped-and-indicated localization preserves deterministic eventual
constancy of a process. -/
theorem localizingStoppedProcess_eq_terminal_of_le
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (T t : ℝ≥0) (hTt : T ≤ t)
    (hX : ∀ s, T ≤ s → X s = X T) :
    localizingStoppedProcess X tau t =
      localizingStoppedProcess X tau T := by
  funext omega
  unfold localizingStoppedProcess stoppedProcess
  by_cases htau : tau omega ≤ (T : WithTop ℝ≥0)
  · have htau' : tau omega ≤ (t : WithTop ℝ≥0) :=
      htau.trans (WithTop.coe_le_coe.mpr hTt)
    rw [min_eq_right htau, min_eq_right htau']
  · have hTtau : (T : WithTop ℝ≥0) ≤ tau omega := le_of_not_ge htau
    have hminT : min (T : WithTop ℝ≥0) (tau omega) = T :=
      min_eq_left hTtau
    rw [hminT]
    let sTop := min (t : WithTop ℝ≥0) (tau omega)
    have hs_ne : sTop ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have hTsTop : (T : WithTop ℝ≥0) ≤ sTop :=
      le_min (WithTop.coe_le_coe.mpr hTt) hTtau
    have hscoe : ((sTop.untopA : ℝ≥0) : WithTop ℝ≥0) = sTop := by
      rw [WithTop.untopA_eq_untop hs_ne]
      exact WithTop.coe_untop sTop hs_ne
    have hTs : T ≤ sTop.untopA := by
      apply WithTop.coe_le_coe.mp
      rw [hscoe]
      exact hTsTop
    have hXT := congrFun (hX sTop.untopA hTs) omega
    change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (X sTop.untopA) omega =
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator (X T) omega
    by_cases hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      exact hXT
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- For a process constant after `T`, extending a bounded stopping time past
`T` on the no-exit event does not change its localized process. -/
theorem localizingStoppedProcess_extendBoundedStoppingTime_eq
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (T S : ℝ≥0) (htauT : ∀ omega, tau omega ≤ T)
    (hTpos : 0 < T) (hTS : T ≤ S)
    (hX : ∀ s, T ≤ s → X s = X T) :
    localizingStoppedProcess X (extendBoundedStoppingTime tau T S) =
      localizingStoppedProcess X tau := by
  funext t omega
  by_cases htau : tau omega < (T : WithTop ℝ≥0)
  · have hsigma : extendBoundedStoppingTime tau T S omega = tau omega :=
      if_pos htau
    unfold localizingStoppedProcess stoppedProcess
    change {omega | (⊥ : WithTop ℝ≥0) <
          extendBoundedStoppingTime tau T S omega}.indicator
        (X (min (t : WithTop ℝ≥0)
          (extendBoundedStoppingTime tau T S omega)).untopA) omega =
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (X (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega
    by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
    · have hmemTau : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
      have hmemSigma : omega ∈ {omega | (⊥ : WithTop ℝ≥0) <
          extendBoundedStoppingTime tau T S omega} := by
        change (⊥ : WithTop ℝ≥0) < extendBoundedStoppingTime tau T S omega
        rw [hsigma]
        exact hpos
      rw [Set.indicator_of_mem hmemSigma, Set.indicator_of_mem hmemTau,
        hsigma]
    · have hmemTau : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
      have hmemSigma : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
          extendBoundedStoppingTime tau T S omega} := by
        simpa only [Set.mem_ofPred_eq, hsigma] using hpos
      rw [Set.indicator_of_notMem hmemSigma,
        Set.indicator_of_notMem hmemTau]
  · have hsigma : extendBoundedStoppingTime tau T S omega = S := if_neg htau
    have htauEq : tau omega = (T : WithTop ℝ≥0) :=
      le_antisymm (htauT omega) (le_of_not_gt htau)
    have hTmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := by
      change (⊥ : WithTop ℝ≥0) < tau omega
      rw [htauEq]
      exact WithTop.coe_pos.mpr hTpos
    have hSmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) <
        extendBoundedStoppingTime tau T S omega} := by
      change (⊥ : WithTop ℝ≥0) < extendBoundedStoppingTime tau T S omega
      rw [hsigma]
      exact WithTop.coe_pos.mpr (hTpos.trans_le hTS)
    unfold localizingStoppedProcess stoppedProcess
    change {omega | (⊥ : WithTop ℝ≥0) <
          extendBoundedStoppingTime tau T S omega}.indicator
        (X (min (t : WithTop ℝ≥0)
          (extendBoundedStoppingTime tau T S omega)).untopA) omega =
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (X (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega
    rw [Set.indicator_of_mem hTmem, Set.indicator_of_mem hSmem,
      hsigma, htauEq]
    change X (min t S) omega = X (min t T) omega
    rcases le_total t T with htT | hTt
    · rw [min_eq_left htT, min_eq_left (htT.trans hTS)]
    · rw [min_eq_right hTt]
      have hHmin : T ≤ min t S := le_min hTt hTS
      exact congrFun (hX (min t S) hHmin) omega

/-- Iterated stopped-and-indicated localization is localization at the
pointwise minimum of the two stopping times. -/
theorem localizingStoppedProcess_localizingStoppedProcess
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (tau sigma : W → WithTop ℝ≥0) :
    localizingStoppedProcess (localizingStoppedProcess X tau) sigma =
      localizingStoppedProcess X (fun omega => min (tau omega) (sigma omega)) := by
  unfold localizingStoppedProcess
  rw [← stoppedProcess_indicator_comm']
  simp_rw [Set.indicator_indicator, Set.inter_comm,
    ← Set.indicator_indicator, stoppedProcess_stoppedProcess,
    stoppedProcess_indicator_comm']
  have hstop : (sigma ⊓ tau) =
      (fun omega => min (tau omega) (sigma omega)) := by
    funext omega
    simp [Pi.inf_apply, min_comm]
  rw [hstop]
  ext i omega
  by_cases htau : (⊥ : WithTop ℝ≥0) < tau omega <;>
    by_cases hsigma : (⊥ : WithTop ℝ≥0) < sigma omega <;>
      simp only [Set.indicator_apply]
  · have htauMem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hsigmaMem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < sigma omega} :=
      hsigma
    have hminMem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      change (⊥ : WithTop ℝ≥0) < min (tau omega) (sigma omega)
      exact lt_min htau hsigma
    rw [if_pos htauMem, if_pos hsigmaMem, if_pos hminMem]
  · have htauMem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hsigmaMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < sigma omega} :=
      hsigma
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_right ((⊥ : WithTop ℝ≥0) < tau omega) hsigma)
    rw [if_pos htauMem, if_neg hsigmaMem, if_neg hminMem]
  · have htauMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_left ((⊥ : WithTop ℝ≥0) < sigma omega) htau)
    rw [if_neg htauMem, if_neg hminMem]
  · have htauMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_left ((⊥ : WithTop ℝ≥0) < sigma omega) htau)
    rw [if_neg htauMem, if_neg hminMem]

/-- Two-stage bounded localization can be diagonalized without assuming the
false global stability of martingales under arbitrary unbounded stopping.
Mathlib's pre-localizing extraction supplies a common exhaustion, and bounded
optional stopping repairs its monotone envelope. -/
theorem isLocalMartingale_of_bounded_double_localization
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {X : ℝ≥0 → W → ℝ}
    (hXcont : ∀ omega, Continuous (fun t => X t omega))
    (tau : ℕ → W → WithTop ℝ≥0)
    (htau : IsLocalizingSequence 𝒱 tau P)
    (sigma : ℕ → ℕ → W → WithTop ℝ≥0)
    (hsigma : ∀ n, IsLocalizingSequence 𝒱 (sigma n) P)
    (hsigmaBound : ∀ n j, ∃ T : ℝ≥0, ∀ omega,
      sigma n j omega ≤ (T : WithTop ℝ≥0))
    (hmart : ∀ n j, Martingale
      (localizingStoppedProcess (localizingStoppedProcess X (tau n))
        (sigma n j)) 𝒱 P) :
    IsLocalMartingale X 𝒱 P := by
  obtain ⟨nk, hnk, hpre⟩ :=
    htau.isPrelocalizingSequence_inf_extraction hsigma
  let raw : ℕ → W → WithTop ℝ≥0 := fun n omega =>
    min (tau n omega) (sigma n (nk n) omega)
  let lambda : ℕ → W → WithTop ℝ≥0 := fun n omega =>
    ⨅ j, ⨅ (_ : j ≥ n), raw j omega
  have hlambda : IsLocalizingSequence 𝒱 lambda P := by
    exact hpre.isLocalizingSequence_biInf
  refine ⟨lambda, hlambda, fun n => ?_⟩
  obtain ⟨T, hT⟩ := hsigmaBound n (nk n)
  have hlambdaRaw (omega : W) : lambda n omega ≤ raw n omega := by
    dsimp only [lambda]
    exact (iInf_le _ n).trans (iInf_le _ le_rfl)
  have hrawSigma (omega : W) : raw n omega ≤ sigma n (nk n) omega :=
    min_le_right _ _
  have hlambdaT (omega : W) : lambda n omega ≤
      (T : WithTop ℝ≥0) :=
    (hlambdaRaw omega).trans ((hrawSigma omega).trans (hT omega))
  have hrawMart : Martingale (localizingStoppedProcess X (raw n)) 𝒱 P := by
    have hiter := hmart n (nk n)
    rw [localizingStoppedProcess_localizingStoppedProcess X
      (tau n) (sigma n (nk n))] at hiter
    exact hiter
  have hrawCont : ∀ omega,
      Continuous (fun t => localizingStoppedProcess X (raw n) t omega) :=
    fun omega => continuous_localizingStoppedProcess hXcont (raw n) omega
  have hstop := martingale_localizingStoppedProcess_of_bounded
    hrawMart hrawCont (hlambda.isStoppingTime n) T hlambdaT
  have heq := localizingStoppedProcess_localizingStoppedProcess
    X (raw n) (lambda n)
  have hmin : (fun omega => min (raw n omega) (lambda n omega)) =
      lambda n := by
    funext omega
    exact min_eq_right (hlambdaRaw omega)
  rw [heq, hmin] at hstop
  exact hstop

/-- Stopping a continuous-path martingale at the minimum of two bounded
continuous adapted exits preserves the martingale property. -/
theorem martingale_localizingStoppedProcess_min_continuousExitTime
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M Z Q : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝒱 Z) (hQ : StronglyAdapted 𝒱 Q)
    (T R S : ℝ≥0) :
    Martingale
      (localizingStoppedProcess M (fun omega =>
        min (continuousExitTime Z T R omega)
          (continuousExitTime Q T S omega))) 𝒱 P := by
  let tauZ := continuousExitTime Z T R
  let tauQ := continuousExitTime Q T S
  have hMZ : Martingale (localizingStoppedProcess M tauZ) 𝒱 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hM hMcont hZ T R
  have hMZcont : ∀ omega, Continuous
      (fun t => localizingStoppedProcess M tauZ t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hMcont T R
  have hMiter : Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess M tauZ) tauQ) 𝒱 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hMZ hMZcont hQ T S
  have heq := localizingStoppedProcess_localizingStoppedProcess M tauZ tauQ
  simpa only [tauZ, tauQ] using heq ▸ hMiter

/-- A martingale remains a martingale after stopping at a paired dyadic exit
capped by a pair of continuous outer exits.  The continuous outer stop is
performed first; the remaining finite-range stop then follows from optional
sampling. -/
theorem
    martingale_localizingStoppedProcess_pairedDyadic_min_outerContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M Z Q : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝒱 Z) (hQ : StronglyAdapted 𝒱 Q)
    (T R S R' S' : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess M (fun omega =>
        min (pairedDyadicHittingTimeNNReal Z Q T R S n omega)
          (min (continuousExitTime Z T R' omega)
            (continuousExitTime Q T S' omega)))) 𝒱 P := by
  let tauZ := continuousExitTime Z T R'
  let tauQ := continuousExitTime Q T S'
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (tauZ omega) (tauQ omega)
  let sigma := pairedDyadicHittingTimeNNReal Z Q T R S n
  have hMZ : Martingale (localizingStoppedProcess M tauZ) 𝒱 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hM hMcont hZ T R'
  have hMZcont : ∀ omega, Continuous
      (fun t => localizingStoppedProcess M tauZ t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hMcont T R'
  have hMthetaIter : Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess M tauZ) tauQ) 𝒱 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hMZ hMZcont hQ T S'
  have hMtheta : Martingale (localizingStoppedProcess M theta) 𝒱 P := by
    have heq := localizingStoppedProcess_localizingStoppedProcess
      M tauZ tauQ
    simpa only [theta] using heq ▸ hMthetaIter
  have hsigma : IsStoppingTime 𝒱 sigma :=
    isStoppingTime_pairedDyadicHittingTimeNNReal hZ hQ T R S n
  have hMsigma : Martingale
      (localizingStoppedProcess (localizingStoppedProcess M theta) sigma)
        𝒱 P :=
    martingale_localizingStoppedProcess_of_finiteRange hMtheta hsigma
      ((Finset.range (2 ^ n + 1)).image
        (uniformPartitionTime T (2 ^ n)))
      (pairedDyadicHittingTimeNNReal_mem_rangeFinset Z Q T R S n)
  have heq := localizingStoppedProcess_localizingStoppedProcess M theta sigma
  rw [heq] at hMsigma
  simpa only [theta, tauZ, tauQ, sigma, min_comm] using hMsigma

/-- For a process constant after `T`, localization by the paired extended
exit sequence agrees with iterated localization by the two underlying
bounded exits. -/
theorem localizingStoppedProcess_pairedContinuousExit_eq
    {W : Type*} (X Z Q : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (hTpos : 0 < T) (hX : ∀ s, T ≤ s → X s = X T) :
    localizingStoppedProcess X
        (pairedContinuousExitLocalizingSequence Z Q T n) =
      localizingStoppedProcess
        (localizingStoppedProcess X (continuousExitTime Z T (n + 1)))
        (continuousExitTime Q T (n + 1)) := by
  let tauZ := continuousExitTime Z T (n + 1)
  let tauQ := continuousExitTime Q T (n + 1)
  let sigmaZ := continuousExitLocalizingSequence Z T n
  let sigmaQ := continuousExitLocalizingSequence Q T n
  have hZextend : localizingStoppedProcess X sigmaZ =
      localizingStoppedProcess X tauZ := by
    exact localizingStoppedProcess_extendBoundedStoppingTime_eq X tauZ
      T (T + (n + 1)) (continuousExitTime_le Z T (n + 1)) hTpos
        (le_add_right le_rfl) hX
  have hXtauConst : ∀ s, T ≤ s →
      localizingStoppedProcess X tauZ s =
        localizingStoppedProcess X tauZ T := by
    intro s hTs
    exact localizingStoppedProcess_eq_terminal_of_le X tauZ T s hTs hX
  have hQextend : localizingStoppedProcess
      (localizingStoppedProcess X tauZ) sigmaQ =
      localizingStoppedProcess
        (localizingStoppedProcess X tauZ) tauQ := by
    exact localizingStoppedProcess_extendBoundedStoppingTime_eq
      (localizingStoppedProcess X tauZ) tauQ T (T + (n + 1))
        (continuousExitTime_le Q T (n + 1)) hTpos
        (le_add_right le_rfl) hXtauConst
  calc
    localizingStoppedProcess X
        (pairedContinuousExitLocalizingSequence Z Q T n) =
        localizingStoppedProcess (localizingStoppedProcess X sigmaZ) sigmaQ := by
      exact (localizingStoppedProcess_localizingStoppedProcess
        X sigmaZ sigmaQ).symm
    _ = localizingStoppedProcess (localizingStoppedProcess X tauZ) sigmaQ :=
      congrArg (fun Y => localizingStoppedProcess Y sigmaQ) hZextend
    _ = localizingStoppedProcess
        (localizingStoppedProcess X tauZ) tauQ := hQextend

/-- For a process constant after the base horizon, shifted paired-exit
localization is localization at the minimum of the two unextended
radius-`n+2` continuous exits. -/
theorem localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
    {W : Type*} (X Z Q : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (hTpos : 0 < T) (hX : ∀ s, T ≤ s → X s = X T) :
    localizingStoppedProcess X
        (shiftedPairedContinuousExitLocalizingSequence Z Q T n) =
      localizingStoppedProcess X
        (fun omega => min (continuousExitTime Z T (n + 1 + 1) omega)
          (continuousExitTime Q T (n + 1 + 1) omega)) := by
  have hpaired := localizingStoppedProcess_pairedContinuousExit_eq
    X Z Q T (n + 1) hTpos hX
  have hradius : (((n + 1 : ℕ) : ℝ≥0) + 1) =
      (n : ℝ≥0) + 1 + 1 := by
    norm_num
  rw [hradius] at hpaired
  have hmin := localizingStoppedProcess_localizingStoppedProcess X
    (continuousExitTime Z T (n + 1 + 1))
    (continuousExitTime Q T (n + 1 + 1))
  exact hpaired.trans hmin

/-- Coherent uniform-grid left sums of adapted integrands against an adapted
integrator are strongly adapted. -/
theorem stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M H : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hH : StronglyAdapted 𝓥 H)
    (T : ℝ≥0) (n : ℕ) :
    StronglyAdapted 𝓥
      (uniformAdaptedMartingaleLeftSumProcess M H T n) := by
  apply stronglyAdapted_elementaryMartingaleIntegralSum hM
    (Finset.range n)
    (fun i hi ↦ monotone_uniformPartitionTime_general T n (Nat.le_succ i))
  intro i hi
  exact hH (uniformPartitionTime T n i)

/-- Uniform left-sum processes for bounded adapted integrands against a
martingale are martingales. -/
theorem martingale_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformAdaptedMartingaleLeftSumProcess M H T n) 𝓥 P := by
  apply martingale_elementaryMartingaleIntegralSum hM
    (Finset.range n) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    (fun _ ↦ K) (fun i hi omega ↦ hHK _ _)
  · exact monotone_uniformPartitionTime_general T n (Nat.le_succ i)
  · exact hH (uniformPartitionTime T n i)

/-- Uniform left-sum processes for bounded adapted integrands against a local
martingale are local martingales, using the integrator's localizing
sequence. -/
theorem IsLocalMartingale.uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    IsLocalMartingale
      (StochasticCalculus.uniformAdaptedMartingaleLeftSumProcess M H T n) 𝓥 P := by
  apply hM.elementaryMartingaleIntegralSum
    (Finset.range n) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    (fun _ ↦ K) (fun i hi omega ↦ hHK _ _)
  · exact monotone_uniformPartitionTime_general T n (Nat.le_succ i)
  · exact hH (uniformPartitionTime T n i)

/-- At the terminal horizon, the adapted process-valued construction is the
standard uniform-partition left sum. -/
theorem uniformAdaptedMartingaleLeftSumProcess_terminal
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T omega =
      ∑ i ∈ Finset.range (n + 1),
        H (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega) := by
  simp only [uniformAdaptedMartingaleLeftSumProcess,
    elementaryMartingaleIntegralSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [elementaryMartingaleIntegralProcess,
    min_eq_right hright.2, min_eq_right hleft.2]

/-- Deterministically stopping the integrator at the terminal horizon does
not change a terminal uniform left sum, since every grid point lies before
that horizon. -/
theorem
    uniformAdaptedMartingaleLeftSumProcess_terminal_deterministicStop
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    uniformAdaptedMartingaleLeftSumProcess
        (fun t => M (min t T)) H T (n + 1) T =
      uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T := by
  funext omega
  rw [uniformAdaptedMartingaleLeftSumProcess_terminal,
    uniformAdaptedMartingaleLeftSumProcess_terminal]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [min_eq_left hright.2, min_eq_left hleft.2]

/-- Elementary martingale-transform isometry: the second moment of the
terminal uniform left sum is exactly the sum of the weighted increment second
moments. -/
theorem integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hH : StronglyAdapted 𝓥 H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    ∫ omega,
        (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range (n + 1), ∫ omega,
        (H (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega)) ^ 2 ∂P := by
  let f : ℕ → W → ℝ := fun i omega ↦
    H (uniformPartitionTime T (n + 1) i) omega *
      (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
        M (uniformPartitionTime T (n + 1) i) omega)
  have hf (i : ℕ) : MemLp (f i) 2 P := by
    have hDelta : MemLp
        (M (uniformPartitionTime T (n + 1) (i + 1)) -
          M (uniformPartitionTime T (n + 1) i)) 2 P :=
      (hM2 _).sub (hM2 _)
    have hmeas : AEStronglyMeasurable (f i) P := by
      exact ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul hDelta.1
    refine hDelta.of_le_mul (c := K) hmeas ?_
    filter_upwards with omega
    simp only [f, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hHK _ omega) (abs_nonneg _)
  have horth (i j : ℕ) (hij : i < j) :
      ∫ omega, f i omega * f j omega ∂P = 0 := by
    have hi1j : i + 1 ≤ j := hij
    exact integral_mul_weighted_martingaleIncrements_eq_zero hM hM2
      (monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i))
      (monotone_uniformPartitionTime_general T (n + 1) hi1j)
      (monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ j))
      (hH _) K (hHK _) (hH _) K (hHK _)
  calc
    ∫ omega,
        (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T omega) ^ 2 ∂P =
        ∫ omega, (∑ i ∈ Finset.range (n + 1), f i omega) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
    _ = ∑ i ∈ Finset.range (n + 1),
        ∫ omega, (f i omega) ^ 2 ∂P :=
      integral_sq_sum_range_of_pairwise_orthogonal f hf horth (n + 1)
    _ = ∑ i ∈ Finset.range (n + 1), ∫ omega,
        (H (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega)) ^ 2 ∂P := by
      rfl

/-- A bounded elementary martingale transform has a grid-independent
second-moment bound.  This is the quantitative form of the preceding
isometry needed for localized uniform-integrability arguments. -/
theorem integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hH : StronglyAdapted 𝓥 H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    ∫ omega,
        (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T omega) ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * ∫ omega, (M T omega - M 0 omega) ^ 2 ∂P := by
  let tau : ℕ → ℝ≥0 := fun i ↦ uniformPartitionTime T (n + 1) i
  let d : ℕ → W → ℝ := fun i omega ↦
    M (tau (i + 1)) omega - M (tau i) omega
  let f : ℕ → W → ℝ := fun i omega ↦ H (tau i) omega * d i omega
  have hd2 (i : ℕ) : MemLp (d i) 2 P := by
    change MemLp (M (tau (i + 1)) - M (tau i)) 2 P
    exact (hM2 _).sub (hM2 _)
  have hf2 (i : ℕ) : MemLp (f i) 2 P := by
    have hmeas : AEStronglyMeasurable (f i) P :=
      ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul (hd2 i).1
    refine (hd2 i).of_le_mul (c := K) hmeas ?_
    filter_upwards with omega
    simp only [f, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hHK _ omega) (abs_nonneg _)
  have hsq (g : W → ℝ) (hg : MemLp g 2 P) :
      Integrable (fun omega ↦ (g omega) ^ 2) P := by
    have hmul : MemLp (g * g) 1 P := hg.mul hg
    apply (memLp_one_iff_integrable.mp hmul).congr
    filter_upwards with omega
    simp only [Pi.mul_apply, pow_two]
  have hterm (i : ℕ) :
      (∫ omega, (f i omega) ^ 2 ∂P) ≤
        (K : ℝ) ^ 2 * ∫ omega, (d i omega) ^ 2 ∂P := by
    calc
      (∫ omega, (f i omega) ^ 2 ∂P) ≤
          ∫ omega, (K : ℝ) ^ 2 * (d i omega) ^ 2 ∂P := by
        apply integral_mono (hsq (f i) (hf2 i))
          ((hsq (d i) (hd2 i)).const_mul ((K : ℝ) ^ 2))
        intro omega
        simp only [f]
        rw [← mul_pow, sq_le_sq, abs_mul, abs_mul,
          abs_of_nonneg K.coe_nonneg]
        exact mul_le_mul_of_nonneg_right (hHK _ omega) (abs_nonneg _)
      _ = (K : ℝ) ^ 2 * ∫ omega, (d i omega) ^ 2 ∂P := by
        rw [integral_const_mul]
  have hdorth (i j : ℕ) (hij : i < j) :
      ∫ omega, d i omega * d j omega ∂P = 0 := by
    have hi1j : i + 1 ≤ j := hij
    simpa only [d, tau, one_mul] using
      (integral_mul_weighted_martingaleIncrements_eq_zero hM hM2
        (Z := fun _ ↦ 1) (Y := fun _ ↦ 1)
        (monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i))
        (monotone_uniformPartitionTime_general T (n + 1) hi1j)
        (monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ j))
        stronglyMeasurable_const 1 (fun _ ↦ by norm_num)
        stronglyMeasurable_const 1 (fun _ ↦ by norm_num))
  have hdeltaSum :
      (∑ i ∈ Finset.range (n + 1), ∫ omega, (d i omega) ^ 2 ∂P) =
        ∫ omega, (M T omega - M 0 omega) ^ 2 ∂P := by
    rw [← integral_sq_sum_range_of_pairwise_orthogonal d hd2 hdorth (n + 1)]
    apply integral_congr_ae
    filter_upwards with omega
    congr 1
    simp only [d, tau]
    calc
      (∑ i ∈ Finset.range (n + 1),
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega)) =
          M (uniformPartitionTime T (n + 1) (n + 1)) omega -
            M (uniformPartitionTime T (n + 1) 0) omega := by
        simpa using (Finset.sum_range_sub
          (fun i ↦ M (uniformPartitionTime T (n + 1) i) omega) (n + 1))
      _ = M T omega - M 0 omega := by simp [uniformPartitionTime]
  rw [integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal
    hM hM2 hH K hHK T n]
  calc
    (∑ i ∈ Finset.range (n + 1), ∫ omega,
        (H (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega)) ^ 2 ∂P) =
        ∑ i ∈ Finset.range (n + 1), ∫ omega, (f i omega) ^ 2 ∂P := by
      rfl
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((K : ℝ) ^ 2 * ∫ omega, (d i omega) ^ 2 ∂P) := by
      gcongr with i hi
      exact hterm i
    _ = (K : ℝ) ^ 2 *
        ∑ i ∈ Finset.range (n + 1), ∫ omega, (d i omega) ^ 2 ∂P := by
      rw [Finset.mul_sum]
    _ = (K : ℝ) ^ 2 * ∫ omega, (M T omega - M 0 omega) ^ 2 ∂P := by
      rw [hdeltaSum]

/-- `L²` seminorm form of the bounded elementary martingale-transform
estimate.  The bound is independent of the uniform grid size. -/
theorem eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    (hH : StronglyAdapted 𝓥 H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    eLpNorm (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P ≤
      K * eLpNorm (M T - M 0) 2 P := by
  have hsq {g : W → ℝ} (hg : MemLp g 2 P) :
      (∫ omega, g omega ^ 2 ∂P) = (eLpNorm g 2 P).toReal ^ 2 := by
    rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have hnonneg : 0 ≤ ∫ omega, g omega ^ 2 ∂P :=
      integral_nonneg (fun omega ↦ sq_nonneg (g omega))
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt hnonneg]
  let f : ℕ → W → ℝ := fun i omega ↦
    H (uniformPartitionTime T (n + 1) i) omega *
      (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
        M (uniformPartitionTime T (n + 1) i) omega)
  have hf2 (i : ℕ) : MemLp (f i) 2 P := by
    have hDelta : MemLp
        (M (uniformPartitionTime T (n + 1) (i + 1)) -
          M (uniformPartitionTime T (n + 1) i)) 2 P :=
      (hM2 _).sub (hM2 _)
    have hmeas : AEStronglyMeasurable (f i) P :=
      ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul hDelta.1
    refine hDelta.of_le_mul (c := K) hmeas ?_
    filter_upwards with omega
    simp only [f, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hHK _ omega) (abs_nonneg _)
  have hsum2 : MemLp
      (fun omega ↦ ∑ i ∈ Finset.range (n + 1), f i omega) 2 P :=
    memLp_finsetSum (Finset.range (n + 1)) (fun i _ ↦ hf2 i)
  have hprocessMeas : AEStronglyMeasurable
      (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) P :=
    ((stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess
      hM.stronglyAdapted hH T (n + 1) T).mono (𝓥.le T)).aestronglyMeasurable
  have hprocess2 : MemLp
      (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P := by
    apply hsum2.congr_norm hprocessMeas
    filter_upwards with omega
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal]
  have hdelta2 : MemLp (M T - M 0) 2 P := (hM2 T).sub (hM2 0)
  rw [← ENNReal.toReal_le_toReal hprocess2.2.ne
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hdelta2.2.ne)]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg)).mp
  calc
    (eLpNorm (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P).toReal ^ 2 =
        ∫ omega,
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T omega) ^ 2 ∂P :=
      (hsq hprocess2).symm
    _ ≤ (K : ℝ) ^ 2 * ∫ omega, (M T omega - M 0 omega) ^ 2 ∂P :=
      integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal_le
        hM hM2 hH K hHK T n
    _ = ((K : ℝ) * (eLpNorm (M T - M 0) 2 P).toReal) ^ 2 := by
      have hdeltaSq : (∫ omega, (M T omega - M 0 omega) ^ 2 ∂P) =
          (eLpNorm (M T - M 0) 2 P).toReal ^ 2 := by
        calc
          (∫ omega, (M T omega - M 0 omega) ^ 2 ∂P) =
              ∫ omega, (M T - M 0) omega ^ 2 ∂P := by
            apply integral_congr_ae
            filter_upwards with omega
            simp only [Pi.sub_apply]
          _ = (eLpNorm (M T - M 0) 2 P).toReal ^ 2 := hsq hdelta2
      rw [hdeltaSq]
      ring

/-- Terminal `L²` integrability of the martingale is enough for the
grid-independent transform estimate.  The proof deterministically stops the
integrator at `T`, propagates the terminal `L²` bound backwards, and uses the
fact that this does not alter grid increments on `[0, T]`. -/
theorem
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P)
    (hH : StronglyAdapted 𝓥 H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (n : ℕ) :
    eLpNorm (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T) 2 P ≤
      K * eLpNorm (M T - M 0) 2 P := by
  let N : ℝ≥0 → W → ℝ := fun t => M (min t T)
  have hN : Martingale N 𝓥 P := martingale_deterministicStop hM T
  have hN2 : ∀ t, MemLp (N t) 2 P :=
    martingale_memLp_deterministicStop hM T one_le_two hMT
  have hbound :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le
      hN hN2 hH K hHK T n
  dsimp only [N] at hbound
  rw [uniformAdaptedMartingaleLeftSumProcess_terminal_deterministicStop]
    at hbound
  have h0T : (0 : ℝ≥0) ≤ T := bot_le
  rw [min_eq_left h0T] at hbound
  simpa only [min_self] using hbound

/-- An adapted fixed-time `L¹`-norm limit of coherent uniform left sums for a
bounded adapted integrand is a martingale. -/
theorem
    martingale_of_uniformAdaptedMartingaleLeftSumProcess_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (T : ℝ≥0)
    {Y : ℝ≥0 → W → ℝ} (hYadapt : StronglyAdapted 𝓥 Y)
    (hconv : ∀ t, Tendsto (fun n ↦ eLpNorm
      (Y t - uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) t) 1 P)
      Filter.atTop (𝓝 0)) :
    Martingale Y 𝓥 P := by
  apply martingale_of_tendsto_eLpNorm_one
    (fun n ↦ martingale_uniformAdaptedMartingaleLeftSumProcess
      hM hH K hHK T (n + 1))
    hYadapt hconv

/-- Uniform adapted left-sum processes are linear in their integrator. -/
theorem uniformAdaptedMartingaleLeftSumProcess_sub
    {W : Type*} (M N H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    uniformAdaptedMartingaleLeftSumProcess M H T n -
        uniformAdaptedMartingaleLeftSumProcess N H T n =
      uniformAdaptedMartingaleLeftSumProcess (M - N) H T n := by
  funext t omega
  unfold uniformAdaptedMartingaleLeftSumProcess
    elementaryMartingaleIntegralSum elementaryMartingaleIntegralProcess
  simp only [Finset.sum_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Localization commutes exactly with the uniform adapted left-sum process:
localizing the sum is the same as replacing its integrator by the localized
integrator. -/
theorem localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess
        (uniformAdaptedMartingaleLeftSumProcess M H T n) tau =
      uniformAdaptedMartingaleLeftSumProcess
        (localizingStoppedProcess M tau) H T n := by
  unfold localizingStoppedProcess uniformAdaptedMartingaleLeftSumProcess
  exact stoppedProcess_indicator_elementaryMartingaleIntegralSum
    M (Finset.range n)
      (fun i ↦ uniformPartitionTime T n i)
      (fun i ↦ uniformPartitionTime T n (i + 1))
      (fun i ↦ H (uniformPartitionTime T n i))
      {omega | (⊥ : WithTop ℝ≥0) < tau omega} tau

/-- At the terminal horizon, the difference between two localizations of a
bounded-coefficient uniform transform is controlled by the corresponding
difference of localized integrators. -/
theorem eLpNorm_sub_localized_uniformAdapted_terminal_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M H : ℝ≥0 → W → ℝ} {tau sigma : W → WithTop ℝ≥0}
    (hMtau : Martingale (localizingStoppedProcess M tau) 𝒱 P)
    (hMsigma : Martingale (localizingStoppedProcess M sigma) 𝒱 P)
    (T : ℝ≥0)
    (hNT : MemLp
      ((localizingStoppedProcess M tau -
        localizingStoppedProcess M sigma) T) 2 P)
    (hH : StronglyAdapted 𝒱 H) (J : ℝ≥0)
    (hHJ : ∀ t omega, ‖H t omega‖ ≤ J) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1)) tau T -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1)) sigma T)
        2 P ≤
      J * eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M sigma) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M sigma) 0) 2 P := by
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
    localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  calc
    eLpNorm
        (uniformAdaptedMartingaleLeftSumProcess
            (localizingStoppedProcess M tau) H T (n + 1) T -
          uniformAdaptedMartingaleLeftSumProcess
            (localizingStoppedProcess M sigma) H T (n + 1) T) 2 P =
        eLpNorm
          (uniformAdaptedMartingaleLeftSumProcess
            (localizingStoppedProcess M tau -
              localizingStoppedProcess M sigma) H T (n + 1) T) 2 P := by
      apply congrArg (fun Z => eLpNorm Z 2 P)
      exact congrFun (uniformAdaptedMartingaleLeftSumProcess_sub
        (localizingStoppedProcess M tau)
        (localizingStoppedProcess M sigma) H T (n + 1)) T
    _ ≤ _ :=
      eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
        (hMtau.sub hMsigma) T hNT hH J hHJ n

/-- Once the integrator is stopped at a continuous exit of `Z`, the
coefficient at a deterministic left endpoint can be killed whenever that
endpoint is at or after the exit. -/
theorem elementary_localizing_beforeContinuousExitProcess
    {W : Type*} (M Z : ℝ≥0 → W → ℝ) (T R a b : ℝ≥0)
    (hab : a ≤ b) :
    elementaryMartingaleIntegralProcess
        (localizingStoppedProcess M (continuousExitTime Z T R)) a b (Z a) =
      elementaryMartingaleIntegralProcess
        (localizingStoppedProcess M (continuousExitTime Z T R)) a b
          (beforeContinuousExitProcess Z T R a) := by
  funext t omega
  let tau := continuousExitTime Z T R
  unfold elementaryMartingaleIntegralProcess
  by_cases ha : (a : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (a : WithTop ℝ≥0) < tau omega} := ha
    unfold beforeContinuousExitProcess
    dsimp only [tau] at hmem
    rw [Set.indicator_of_mem hmem]
  · have hmem : omega ∉ {omega | (a : WithTop ℝ≥0) < tau omega} := ha
    have htauA : tau omega ≤ (a : WithTop ℝ≥0) := le_of_not_gt ha
    unfold beforeContinuousExitProcess
    dsimp only [tau] at hmem htauA
    rw [Set.indicator_of_notMem hmem]
    simp only [zero_mul]
    by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left (hta.trans hab), sub_self, mul_zero]
    · have hat : a ≤ t := le_of_not_ge hta
      have hmina : min t a = a := min_eq_right hat
      have habmin : a ≤ min t b := le_min hat hab
      unfold localizingStoppedProcess stoppedProcess
      rw [hmina, min_eq_right htauA,
        min_eq_right (htauA.trans (mod_cast habmin)), sub_self, mul_zero]

/-- Once the integrator is stopped at a continuous exit of `Z`, an arbitrary
coefficient at a deterministic left endpoint can be killed whenever that
endpoint is at or after the exit. -/
theorem elementary_localizing_beforeContinuousExitProcessOf
    {W : Type*} (M Z H : ℝ≥0 → W → ℝ) (T R a b : ℝ≥0)
    (hab : a ≤ b) :
    elementaryMartingaleIntegralProcess
        (localizingStoppedProcess M (continuousExitTime Z T R)) a b (H a) =
      elementaryMartingaleIntegralProcess
        (localizingStoppedProcess M (continuousExitTime Z T R)) a b
          (beforeContinuousExitProcessOf Z H T R a) := by
  funext t omega
  let tau := continuousExitTime Z T R
  unfold elementaryMartingaleIntegralProcess
  by_cases ha : (a : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (a : WithTop ℝ≥0) < tau omega} := ha
    unfold beforeContinuousExitProcessOf
    dsimp only [tau] at hmem
    rw [Set.indicator_of_mem hmem]
  · have hmem : omega ∉ {omega | (a : WithTop ℝ≥0) < tau omega} := ha
    have htauA : tau omega ≤ (a : WithTop ℝ≥0) := le_of_not_gt ha
    unfold beforeContinuousExitProcessOf
    dsimp only [tau] at hmem htauA
    rw [Set.indicator_of_notMem hmem]
    simp only [zero_mul]
    by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left (hta.trans hab), sub_self, mul_zero]
    · have hat : a ≤ t := le_of_not_ge hta
      have hmina : min t a = a := min_eq_right hat
      have habmin : a ≤ min t b := le_min hat hab
      unfold localizingStoppedProcess stoppedProcess
      rw [hmina, min_eq_right htauA,
        min_eq_right (htauA.trans (mod_cast habmin)), sub_self, mul_zero]

/-- Localization of a uniform transform at an exit of its integrand is the
same transform with the bounded adapted before-exit coefficient. -/
theorem
    localizingStoppedProcess_uniformAdapted_beforeContinuousExitProcess
    {W : Type*} (M Z : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (exitT R : ℝ≥0) :
    localizingStoppedProcess
        (uniformAdaptedMartingaleLeftSumProcess M Z T n)
        (continuousExitTime Z exitT R) =
      uniformAdaptedMartingaleLeftSumProcess
        (localizingStoppedProcess M (continuousExitTime Z exitT R))
        (beforeContinuousExitProcess Z exitT R) T n := by
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  unfold uniformAdaptedMartingaleLeftSumProcess
  unfold elementaryMartingaleIntegralSum
  apply Finset.sum_congr rfl
  intro i hi
  exact elementary_localizing_beforeContinuousExitProcess M Z exitT R
    (uniformPartitionTime T n i)
    (uniformPartitionTime T n (i + 1))
    (monotone_uniformPartitionTime_general T n (Nat.le_succ i))

/-- Localization of a uniform transform at an exit of `Z` is the same
transform with its possibly different coefficient killed before that exit. -/
theorem
    localizingStoppedProcess_uniformAdapted_beforeContinuousExitProcessOf
    {W : Type*} (M Z H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (exitT R : ℝ≥0) :
    localizingStoppedProcess
        (uniformAdaptedMartingaleLeftSumProcess M H T n)
        (continuousExitTime Z exitT R) =
      uniformAdaptedMartingaleLeftSumProcess
        (localizingStoppedProcess M (continuousExitTime Z exitT R))
        (beforeContinuousExitProcessOf Z H exitT R) T n := by
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  unfold uniformAdaptedMartingaleLeftSumProcess
  unfold elementaryMartingaleIntegralSum
  apply Finset.sum_congr rfl
  intro i hi
  exact elementary_localizing_beforeContinuousExitProcessOf M Z H exitT R
    (uniformPartitionTime T n i)
    (uniformPartitionTime T n (i + 1))
    (monotone_uniformPartitionTime_general T n (Nat.le_succ i))

/-- If two integrator localizations both occur no later than a controller's
continuous exit, their difference transform may use the coefficient killed
at that outer exit. -/
theorem uniformAdapted_sub_localized_replace_beforeContinuousExit
    {W : Type*} (M Z H : ℝ≥0 → W → ℝ)
    {tau sigma : W → WithTop ℝ≥0}
    (T : ℝ≥0) (n : ℕ) (exitT R : ℝ≥0)
    (htau : ∀ omega, tau omega ≤ continuousExitTime Z exitT R omega)
    (hsigma : ∀ omega, sigma omega ≤ continuousExitTime Z exitT R omega) :
    uniformAdaptedMartingaleLeftSumProcess
        (localizingStoppedProcess M tau -
          localizingStoppedProcess M sigma) H T n =
      uniformAdaptedMartingaleLeftSumProcess
        (localizingStoppedProcess M tau -
          localizingStoppedProcess M sigma)
        (beforeContinuousExitProcessOf Z H exitT R) T n := by
  let exit := continuousExitTime Z exitT R
  let N := localizingStoppedProcess M tau -
    localizingStoppedProcess M sigma
  have hNtau : localizingStoppedProcess
      (localizingStoppedProcess M tau) exit =
      localizingStoppedProcess M tau := by
    have hiter := localizingStoppedProcess_localizingStoppedProcess M tau exit
    rw [hiter]
    congr 1
    funext omega
    exact min_eq_left (htau omega)
  have hNsigma : localizingStoppedProcess
      (localizingStoppedProcess M sigma) exit =
      localizingStoppedProcess M sigma := by
    have hiter := localizingStoppedProcess_localizingStoppedProcess M sigma exit
    rw [hiter]
    congr 1
    funext omega
    exact min_eq_left (hsigma omega)
  have hNexit : localizingStoppedProcess N exit = N := by
    dsimp only [N]
    rw [localizingStoppedProcess_sub, hNtau, hNsigma]
  have hplain :=
    localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
      N H T n exit
  have hkilled :=
    localizingStoppedProcess_uniformAdapted_beforeContinuousExitProcessOf
      N Z H T n exitT R
  rw [hNexit] at hplain hkilled
  exact hplain.symm.trans hkilled

/-- Localizing an integrator at its own bounded exit and then at the bounded
exit of a controller gives a grid-independent `L²` estimate for transforms
whose coefficient is bounded before the controller exits. -/
theorem eLpNorm_doubleExit_localized_uniformAdaptedOf_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M Z H : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝓥 Z) (hH : StronglyAdapted 𝓥 H)
    (T MT K ZT R J : ℝ≥0)
    (hHJ : ∀ (t : ℝ≥0) omega,
      (t : WithTop ℝ≥0) < continuousExitTime Z ZT R omega →
        ‖H t omega‖ ≤ J)
    (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1))
          (continuousExitTime M MT K))
        (continuousExitTime Z ZT R) T) 2 P ≤
      J * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime Z ZT R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime Z ZT R) 0) 2 P := by
  let tauM := continuousExitTime M MT K
  let tauZ := continuousExitTime Z ZT R
  let N1 := localizingStoppedProcess M tauM
  let N2 := localizingStoppedProcess N1 tauZ
  have hN1 : Martingale N1 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime hM hMcont MT K
  have hN1cont : ∀ omega, Continuous (fun t => N1 t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hMcont MT K
  have hN2 : Martingale N2 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hN1 hN1cont hZ ZT R
  have hN2T : MemLp (N2 T) 2 P := by
    apply MemLp.of_bound
      ((hN2.stronglyAdapted T).mono (𝓥.le T)).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_le K
        (norm_localizingStoppedProcess_continuousExitTime_le hMcont MT K)
        T omega
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  rw [localizingStoppedProcess_uniformAdapted_beforeContinuousExitProcessOf]
  exact
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hN2 T hN2T
        (stronglyAdapted_beforeContinuousExitProcessOf hZ hH ZT R) J
        (norm_beforeContinuousExitProcessOf_le ZT R J hHJ) n

/-- Localizing the integrator and integrand at bounded continuous exits
gives a grid-independent `L²` estimate for the resulting martingale
transforms.  This is the localized second-moment bound needed by the general
Doléans--Dade closure argument. -/
theorem eLpNorm_doubleExit_localized_uniformAdapted_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M Z : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝓥 Z)
    (hZcont : ∀ omega, Continuous (fun t => Z t omega))
    (T MT K ZT R : ℝ≥0) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Z T (n + 1))
          (continuousExitTime M MT K))
        (continuousExitTime Z ZT R) T) 2 P ≤
      R * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime Z ZT R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime Z ZT R) 0) 2 P := by
  let tauM := continuousExitTime M MT K
  let tauZ := continuousExitTime Z ZT R
  let N1 := localizingStoppedProcess M tauM
  let N2 := localizingStoppedProcess N1 tauZ
  have hN1 : Martingale N1 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime hM hMcont MT K
  have hN1cont : ∀ omega, Continuous (fun t => N1 t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hMcont MT K
  have hN2 : Martingale N2 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hN1 hN1cont hZ ZT R
  have hN2T : MemLp (N2 T) 2 P := by
    apply MemLp.of_bound
      ((hN2.stronglyAdapted T).mono (𝓥.le T)).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_le K
        (norm_localizingStoppedProcess_continuousExitTime_le hMcont MT K)
        T omega
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  rw [localizingStoppedProcess_uniformAdapted_beforeContinuousExitProcess]
  exact
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hN2 T hN2T
        (stronglyAdapted_beforeContinuousExitProcess hZ ZT R) R
        (norm_beforeContinuousExitProcess_le hZcont ZT R) n

/-- If a stopped integrator is a martingale, then the correspondingly stopped
uniform left-sum process is a martingale. -/
theorem martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hM : Martingale (localizingStoppedProcess M tau) 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (localizingStoppedProcess
      (uniformAdaptedMartingaleLeftSumProcess M H T n) tau) 𝓥 P := by
  rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  exact martingale_uniformAdaptedMartingaleLeftSumProcess
    hM hH K hHK T n

/-- The difference estimate for two localizations holds at every observation
time.  Before the terminal horizon this is martingale contraction; after the
horizon both coherent transform processes are constant. -/
theorem eLpNorm_sub_localized_uniformAdapted_apply_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M H : ℝ≥0 → W → ℝ} {tau sigma : W → WithTop ℝ≥0}
    (hMtau : Martingale (localizingStoppedProcess M tau) 𝒱 P)
    (hMsigma : Martingale (localizingStoppedProcess M sigma) 𝒱 P)
    (T : ℝ≥0)
    (hNT : MemLp
      ((localizingStoppedProcess M tau -
        localizingStoppedProcess M sigma) T) 2 P)
    (hH : StronglyAdapted 𝒱 H) (J : ℝ≥0)
    (hHJ : ∀ t omega, ‖H t omega‖ ≤ J) (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1)) tau t -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M H T (n + 1)) sigma t)
        2 P ≤
      J * eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M sigma) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M sigma) 0) 2 P := by
  have hterminal := eLpNorm_sub_localized_uniformAdapted_terminal_le
    hMtau hMsigma T hNT hH J hHJ n
  let X := uniformAdaptedMartingaleLeftSumProcess M H T (n + 1)
  have hXtau : Martingale (localizingStoppedProcess X tau) 𝒱 P :=
    martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
      hMtau hH J hHJ T (n + 1)
  have hXsigma : Martingale (localizingStoppedProcess X sigma) 𝒱 P :=
    martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
      hMsigma hH J hHJ T (n + 1)
  rcases le_total t T with htT | hTt
  · exact (martingale_eLpNorm_le_of_le
      (hXtau.sub hXsigma) htT one_le_two).trans hterminal
  · have hXconst : ∀ s, T ≤ s → X s = X T := by
      intro s hTs
      exact uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M H T n s hTs
    have htauEq : localizingStoppedProcess X tau t =
        localizingStoppedProcess X tau T :=
      localizingStoppedProcess_eq_terminal_of_le X tau T t hTt hXconst
    have hsigmaEq : localizingStoppedProcess X sigma t =
        localizingStoppedProcess X sigma T :=
      localizingStoppedProcess_eq_terminal_of_le X sigma T t hTt hXconst
    rw [htauEq, hsigmaEq]
    exact hterminal

/-- A common localizing sequence whose stopped integrator processes are
martingales upgrades stopped `L¹` convergence of uniform left sums to a
local-martingale limit. -/
theorem
    isLocalMartingale_of_uniformAdaptedMartingaleLeftSumProcess_stopped_tendsto
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} {tau : ℕ → W → WithTop ℝ≥0}
    (htau : IsLocalizingSequence 𝓥 tau P)
    (hM : ∀ k, Martingale (localizingStoppedProcess M (tau k)) 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (T : ℝ≥0)
    {Y : ℝ≥0 → W → ℝ}
    (hYadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess Y (tau k)))
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess Y (tau k) t -
        localizingStoppedProcess
          (StochasticCalculus.uniformAdaptedMartingaleLeftSumProcess M H T (n + 1))
          (tau k) t) 1 P) Filter.atTop (𝓝 0)) :
    IsLocalMartingale Y 𝓥 P := by
  apply isLocalMartingale_of_stopped_tendsto_eLpNorm_one htau
    (fun n k ↦
      martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
        (hM k) hH K hHK T (n + 1))
    hYadapt hconv

/-- The preceding local-limit theorem specialized to the canonical
localizing sequence carried by a local martingale. -/
theorem IsLocalMartingale.limit_uniformAdaptedMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M H : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hH : StronglyAdapted 𝓥 H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (T : ℝ≥0)
    {Y : ℝ≥0 → W → ℝ}
    (hYadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess Y (hM.localSeq k)))
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess Y (hM.localSeq k) t -
        localizingStoppedProcess
          (StochasticCalculus.uniformAdaptedMartingaleLeftSumProcess M H T (n + 1))
          (hM.localSeq k) t) 1 P) Filter.atTop (𝓝 0)) :
    IsLocalMartingale Y 𝓥 P := by
  exact
    isLocalMartingale_of_uniformAdaptedMartingaleLeftSumProcess_stopped_tendsto
      hM.isLocalizingSequence_localSeq
      (fun k ↦ hM.stoppedProcess_localSeq k)
      hH K hHK T hYadapt hconv

/-- The time-indexed uniform-partition left sum of a state weight against a
process.  Each summand is stopped at the observation time, so this is a
coherent process rather than a family of unrelated fixed-time sums. -/
def uniformMartingaleLeftSumProcess
    {W : Type*} (M : ℝ≥0 → W → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  elementaryMartingaleIntegralSum M (Finset.range n)
    (fun i ↦ uniformPartitionTime T n i)
    (fun i ↦ uniformPartitionTime T n (i + 1))
    (fun i omega ↦ g (M (uniformPartitionTime T n i) omega))

/-- Uniform left-sum processes with a bounded continuous state weight are
martingales whenever the integrator is a martingale. -/
theorem martingale_uniformMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    {g : ℝ → ℝ} (hg : Continuous g)
    (K : ℝ) (hgK : ∀ x, ‖g x‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformMartingaleLeftSumProcess M g T n) 𝓥 P := by
  apply martingale_elementaryMartingaleIntegralSum hM
    (Finset.range n) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    (fun _ ↦ K) (fun i hi omega ↦ hgK _)
  · exact monotone_uniformPartitionTime_general T n (Nat.le_succ i)
  · exact hg.comp_stronglyMeasurable
      (hM.stronglyMeasurable (uniformPartitionTime T n i))

/-- Uniform left-sum processes against an adapted local martingale are local
martingales.  All interval summands reuse the integrator's localizing
sequence. -/
theorem IsLocalMartingale.uniformMartingaleLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    {g : ℝ → ℝ} (hg : Continuous g)
    (K : ℝ) (hgK : ∀ x, ‖g x‖ ≤ K) (T : ℝ≥0) (n : ℕ) :
    IsLocalMartingale (StochasticCalculus.uniformMartingaleLeftSumProcess M g T n) 𝓥 P := by
  apply hM.elementaryMartingaleIntegralSum
    (Finset.range n) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    (fun _ ↦ K) (fun i hi omega ↦ hgK _)
  · exact monotone_uniformPartitionTime_general T n (Nat.le_succ i)
  · exact hg.comp_stronglyMeasurable
      (hMadapt (uniformPartitionTime T n i))

/-- At the terminal horizon, the process-valued construction is exactly the
usual uniform-partition left sum. -/
theorem uniformMartingaleLeftSumProcess_terminal
    {W : Type*} (M : ℝ≥0 → W → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformMartingaleLeftSumProcess M g T (n + 1) T omega =
      ∑ i ∈ Finset.range (n + 1),
        g (M (uniformPartitionTime T (n + 1) i) omega) *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega) := by
  simp only [uniformMartingaleLeftSumProcess,
    elementaryMartingaleIntegralSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [elementaryMartingaleIntegralProcess,
    min_eq_right hright.2, min_eq_right hleft.2]

/-- Any adapted fixed-time `L¹`-norm limit of the coherent uniform left-sum
processes is a martingale.  This packages the elementary
construction and `L¹`-closure into the process-level arbitrary-integrator
interface needed by stochastic-exponential arguments. -/
theorem martingale_of_uniformMartingaleLeftSumProcess_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    {g : ℝ → ℝ} (hg : Continuous g)
    (K : ℝ) (hgK : ∀ x, ‖g x‖ ≤ K) (T : ℝ≥0)
    {Y : ℝ≥0 → W → ℝ} (hYadapt : StronglyAdapted 𝓥 Y)
    (hconv : ∀ t, Tendsto (fun n ↦
      eLpNorm
        (Y t - uniformMartingaleLeftSumProcess M g T (n + 1) t) 1 P)
      Filter.atTop (𝓝 0)) :
    Martingale Y 𝓥 P := by
  apply martingale_of_tendsto_eLpNorm_one
    (fun n ↦ martingale_uniformMartingaleLeftSumProcess
      hM hg K hgK T (n + 1))
    hYadapt hconv

/-- The compensated logarithm `M - (1/2) ⟪M⟫` used in the stochastic
exponential.  The second argument is kept abstract until a bracket API is
available at the process level. -/
def doleansDadeLog
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  M t omega - (1 / 2 : ℝ) * bracket t omega

/-- The real Doléans–Dade exponential associated to a process and a selected
bracket process. -/
def doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (doleansDadeLog M bracket t omega)

/-- Adaptedness of both the martingale and bracket processes makes the
selected Doléans–Dade exponential adapted. -/
theorem stronglyAdapted_doleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket) :
    StronglyAdapted 𝓥 (doleansDadeExponential M bracket) := by
  intro t
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hM t).sub (stronglyMeasurable_const.mul (hbracket t)))

/-- Strong progressiveness of the martingale and bracket processes makes
their selected Doléans--Dade exponential strongly progressive. -/
theorem isStronglyProgressive_doleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsStronglyProgressive 𝓥 M)
    (hbracket : IsStronglyProgressive 𝓥 bracket) :
    IsStronglyProgressive 𝓥 (doleansDadeExponential M bracket) := by
  intro t
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hM t).sub (stronglyMeasurable_const.mul (hbracket t)))

/-- The canonical stochastic-integral candidate in the Doléans--Dade
identity: the stochastic exponential minus its initial constant.  Naming
this process lets the approximation endpoint state its sole analytic input
without quantifying over an otherwise arbitrary integral process. -/
def doleansDadeIntegralCandidate
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential M bracket t omega - 1

/-- The canonical Doléans--Dade integral candidate is adapted whenever the
martingale and selected bracket are adapted. -/
theorem stronglyAdapted_doleansDadeIntegralCandidate
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket) :
    StronglyAdapted 𝓥 (doleansDadeIntegralCandidate M bracket) := by
  intro t
  exact (stronglyAdapted_doleansDadeExponential hM hbracket t).sub
    stronglyMeasurable_const

/-- Strong progressiveness is preserved by passage to the canonical
Doléans--Dade integral candidate. -/
theorem isStronglyProgressive_doleansDadeIntegralCandidate
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsStronglyProgressive 𝓥 M)
    (hbracket : IsStronglyProgressive 𝓥 bracket) :
    IsStronglyProgressive 𝓥
      (doleansDadeIntegralCandidate M bracket) := by
  intro t
  exact (isStronglyProgressive_doleansDadeExponential hM hbracket t).sub
    stronglyMeasurable_const

/-- Continuous martingale and bracket paths give a continuous canonical
Doléans--Dade integral-candidate path. -/
theorem continuous_doleansDadeIntegralCandidate
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    Continuous (fun t ↦ doleansDadeIntegralCandidate M bracket t omega) := by
  exact (Real.continuous_exp.comp
    (hM.sub (continuous_const.mul hbracket))).sub continuous_const

/-- The stochastic exponential is exactly one plus its canonical integral
candidate. -/
theorem doleansDadeExponential_eq_one_add_integralCandidate
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) :
    doleansDadeExponential M bracket =
      fun t omega ↦ 1 + doleansDadeIntegralCandidate M bracket t omega := by
  funext t omega
  simp only [doleansDadeIntegralCandidate]
  ring

/-- The stochastic exponential capped above at a deterministic nonnegative
level.  Positivity of the exponential makes this a bounded adapted
integrand suitable for the elementary arbitrary-integrator construction. -/
def cappedDoleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (R : ℝ≥0)
    (t : ℝ≥0) (omega : W) : ℝ :=
  min (doleansDadeExponential M bracket t omega) R

/-- Deterministic capping preserves adaptedness of the stochastic
exponential. -/
theorem stronglyAdapted_cappedDoleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (R : ℝ≥0) :
    StronglyAdapted 𝓥 (cappedDoleansDadeExponential M bracket R) := by
  intro t
  exact (continuous_id.min continuous_const).comp_stronglyMeasurable
    (stronglyAdapted_doleansDadeExponential hM hbracket t)

/-- The capped stochastic exponential has its advertised deterministic
bound. -/
theorem norm_cappedDoleansDadeExponential_le
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (R : ℝ≥0)
    (t : ℝ≥0) (omega : W) :
    ‖cappedDoleansDadeExponential M bracket R t omega‖ ≤ (R : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact min_le_right _ _
  · exact le_min (Real.exp_pos _).le R.coe_nonneg

/-- Integer cap levels exhaust the uncapped stochastic exponential
pointwise. -/
theorem tendsto_cappedDoleansDadeExponential_nat
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    Tendsto (fun n : ℕ ↦
      cappedDoleansDadeExponential M bracket n t omega)
      Filter.atTop (𝓝 (doleansDadeExponential M bracket t omega)) := by
  obtain ⟨N, hN⟩ :=
    exists_nat_ge (doleansDadeExponential M bracket t omega)
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  unfold cappedDoleansDadeExponential
  rw [min_eq_left]
  exact hN.trans (by exact_mod_cast hn)

/-- On a compact time interval, continuous sample paths make the integer
caps eventually inactive uniformly over the whole interval. -/
theorem eventually_cappedDoleansDadeExponential_eq_on_Icc
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      cappedDoleansDadeExponential M bracket n t omega =
        doleansDadeExponential M bracket t omega := by
  have hE : Continuous
      (fun t ↦ doleansDadeExponential M bracket t omega) :=
    Real.continuous_exp.comp
      (hM.sub (continuous_const.mul hbracket))
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hE.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht
  unfold cappedDoleansDadeExponential
  rw [min_eq_left]
  exact (hC ⟨t, ht, rfl⟩).trans (hN.trans (by exact_mod_cast hn))

/-- The compact-horizon cap-exhaustion statement holds almost surely when
both input processes have almost-everywhere continuous paths. -/
theorem ae_eventually_cappedDoleansDadeExponential_eq_on_Icc
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hM : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracket : ∀ᵐ omega ∂P, Continuous (fun t ↦ bracket t omega)) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      cappedDoleansDadeExponential M bracket n t omega =
        doleansDadeExponential M bracket t omega := by
  filter_upwards [hM, hbracket] with omega hMomega hbracketOmega
  exact eventually_cappedDoleansDadeExponential_eq_on_Icc
    M bracket T omega hMomega hbracketOmega

/-- Uniform left sums of a capped Doléans integrand against an adapted local
martingale are local martingales.  This is the concrete approximation family
for the stochastic integral `∫ capped(E(M)) dM`. -/
theorem
    isLocalMartingale_uniformLeftSumProcess_cappedDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : StronglyAdapted 𝓥 bracket)
    (R : ℝ≥0) (T : ℝ≥0) (n : ℕ) :
    IsLocalMartingale
      (uniformAdaptedMartingaleLeftSumProcess M
        (cappedDoleansDadeExponential M bracket R) T n) 𝓥 P :=
  hM.uniformAdaptedMartingaleLeftSumProcess
    (stronglyAdapted_cappedDoleansDadeExponential hMadapt hbracket R) R
    (norm_cappedDoleansDadeExponential_le M bracket R) T n

/-- For a square-integrable martingale integrator and a fixed cap, the
terminal capped Doléans left sums are uniformly integrable in `L¹`, uniformly
over the grid.  The fixed-cap qualification is essential: the diagonal
approximation below lets its cap grow with the grid. -/
theorem
    uniformIntegrable_uniformLeftSumProcess_cappedDoleansDadeExponential_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P)
    (hbracket : StronglyAdapted 𝓥 bracket)
    (R : ℝ≥0) :
    UniformIntegrable
      (fun n ↦ uniformAdaptedMartingaleLeftSumProcess M
        (cappedDoleansDadeExponential M bracket R) T (n + 1) T) 1 P := by
  let C : ℝ≥0 :=
    (R * eLpNorm (M T - M 0) 2 P).toNNReal
  have hM0 : MemLp (M 0) 2 P :=
    martingale_memLp_of_le hM bot_le one_le_two hMT
  have hfinite : R * eLpNorm (M T - M 0) 2 P ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hMT.sub hM0).2.ne
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C)
  · intro n
    exact ((stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess
      hM.stronglyAdapted
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket R) T (n + 1) T).mono
          (𝓥.le T)).aestronglyMeasurable
  · intro n
    rw [show (C : ℝ≥0∞) =
      R * eLpNorm (M T - M 0) 2 P by
        exact ENNReal.coe_toNNReal hfinite]
    exact
      eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT
        (stronglyAdapted_cappedDoleansDadeExponential
          hM.stronglyAdapted hbracket R)
        R (norm_cappedDoleansDadeExponential_le M bracket R) n

/-- A diagonal approximation to `∫ E(M) dM`: at stage `n`, cap the
Doléans integrand at `n + 1` and use an `n + 1` point uniform grid. -/
def cappedDoleansDadeLeftSumProcess
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  uniformAdaptedMartingaleLeftSumProcess M
    (cappedDoleansDadeExponential M bracket (n + 1)) T (n + 1)

/-- A uniform second-moment bound on the diagonal capped Doléans sums
supplies their `L¹` uniform integrability. -/
theorem
    uniformIntegrable_cappedDoleansDadeLeftSumProcess_of_uniform_eLpNorm_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (T t : ℝ≥0) (C : ℝ≥0)
    (hC : ∀ n,
      eLpNorm (cappedDoleansDadeLeftSumProcess M bracket T n t) 2 P ≤ C) :
    UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P := by
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C) _ hC
  intro n
  unfold cappedDoleansDadeLeftSumProcess
  exact ((stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
    (stronglyAdapted_cappedDoleansDadeExponential
      hM hbracket (n + 1)) T (n + 1) t).mono
        (𝓥.le t)).aestronglyMeasurable

/-- The matching uncapped uniform left-sum process for the stochastic
integral `∫ E(M) dM`. -/
def doleansDadeLeftSumProcess
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  uniformAdaptedMartingaleLeftSumProcess M
    (doleansDadeExponential M bracket) T (n + 1)

/-- Along continuous input paths, the capped diagonal and uncapped left-sum
sample paths are eventually identical.  Thus the caps introduce no
pathwise compact-horizon error. -/
theorem eventually_cappedDoleansDadeLeftSumProcess_eq
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (fun t ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega) =
        fun t ↦ doleansDadeLeftSumProcess M bracket T n t omega := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_cappedDoleansDadeExponential_eq_on_Icc
      M bracket T omega hM hbracket)
  filter_upwards [eventually_ge_atTop N] with n hn
  funext t
  simp only [cappedDoleansDadeLeftSumProcess, doleansDadeLeftSumProcess,
    uniformAdaptedMartingaleLeftSumProcess,
    elementaryMartingaleIntegralSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := Finset.mem_range.mp hi |>.le
  have htime := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hcap := hN (n + 1) (hn.trans (Nat.le_succ n)) _ htime
  simp only [elementaryMartingaleIntegralProcess]
  rw [show cappedDoleansDadeExponential M bracket (n + 1)
      (uniformPartitionTime T (n + 1) i) omega =
        doleansDadeExponential M bracket
          (uniformPartitionTime T (n + 1) i) omega by
    simpa only [Nat.cast_add, Nat.cast_one] using hcap]

/-- Almost-everywhere continuous paths make the capped and uncapped
left-sum sample paths eventually identical almost surely. -/
theorem ae_eventually_cappedDoleansDadeLeftSumProcess_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hM : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracket : ∀ᵐ omega ∂P, Continuous (fun t ↦ bracket t omega)) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop,
      (fun t ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega) =
        fun t ↦ doleansDadeLeftSumProcess M bracket T n t omega := by
  filter_upwards [hM, hbracket] with omega hMomega hbracketOmega
  exact eventually_cappedDoleansDadeLeftSumProcess_eq
    M bracket T omega hMomega hbracketOmega

/-- At every observation time, the capped-minus-uncapped diagonal left sums
converge to zero in measure.  This turns compact-path eventual equality into
the probabilistic convergence interface used elsewhere in the library. -/
theorem tendstoInMeasure_cappedDoleansDadeLeftSumProcess_sub
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracketCont : ∀ᵐ omega ∂P,
      Continuous (fun t ↦ bracket t omega))
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦
        cappedDoleansDadeLeftSumProcess M bracket T n t omega -
          doleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hcap : StronglyAdapted 𝓥
        (cappedDoleansDadeLeftSumProcess M bracket T n) := by
      unfold cappedDoleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_cappedDoleansDadeExponential
          hM hbracket (n + 1)) T (n + 1)
    have huncap : StronglyAdapted 𝓥
        (doleansDadeLeftSumProcess M bracket T n) := by
      unfold doleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_doleansDadeExponential hM hbracket) T (n + 1)
    exact ((hcap t).mono (𝓥.le t)).aestronglyMeasurable.sub
      ((huncap t).mono (𝓥.le t)).aestronglyMeasurable
  · filter_upwards
      [ae_eventually_cappedDoleansDadeLeftSumProcess_eq
        M bracket T hMcont hbracketCont] with omega homega
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [homega] with n hn
    rw [congrFun hn t, sub_self]

/-- Any fixed-time convergence-in-measure result for the classical uncapped
Doléans left sums transfers to the bounded diagonal approximation. -/
theorem tendstoInMeasure_cappedDoleansDadeLeftSumProcess_of_uncapped
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracketCont : ∀ᵐ omega ∂P,
      Continuous (fun t ↦ bracket t omega))
    (T t : ℝ≥0) {I : W → ℝ}
    (huncap : TendstoInMeasure P
      (fun n omega ↦ doleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop I) :
    TendstoInMeasure P
      (fun n omega ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop I := by
  have hcapMeas (n : ℕ) : AEStronglyMeasurable
      (cappedDoleansDadeLeftSumProcess M bracket T n t) P := by
    have hcap : StronglyAdapted 𝓥
        (cappedDoleansDadeLeftSumProcess M bracket T n) := by
      unfold cappedDoleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_cappedDoleansDadeExponential
          hM hbracket (n + 1)) T (n + 1)
    exact ((hcap t).mono (𝓥.le t)).aestronglyMeasurable
  have huncapMeas (n : ℕ) : AEStronglyMeasurable
      (doleansDadeLeftSumProcess M bracket T n t) P := by
    have huncap' : StronglyAdapted 𝓥
        (doleansDadeLeftSumProcess M bracket T n) := by
      unfold doleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_doleansDadeExponential hM hbracket) T (n + 1)
    exact ((huncap' t).mono (𝓥.le t)).aestronglyMeasurable
  have hdiff :=
    tendstoInMeasure_cappedDoleansDadeLeftSumProcess_sub
      hM hbracket hMcont hbracketCont T t
  have hsum := TendstoInMeasure.add_real
    (fun n ↦ (hcapMeas n).sub (huncapMeas n))
    huncapMeas hdiff huncap
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      simp only [Pi.sub_apply]
      ring
  · exact Filter.Eventually.of_forall fun omega ↦ by simp

/-- A total continuous nondecreasing path bundled as a Stieltjes function.
The fallback value makes the construction total; all useful equations expose
the intended path under explicit continuity and monotonicity hypotheses. -/
noncomputable def continuousMonotoneStieltjesFunction
    (A : ℝ≥0 → ℝ) : StieltjesFunction ℝ≥0 := by
  classical
  exact if h : Continuous A ∧ Monotone A then
      { toFun := A
        mono' := h.2
        right_continuous' := fun _ ↦ h.1.continuousWithinAt }
    else 0

@[simp]
theorem continuousMonotoneStieltjesFunction_apply
    {A : ℝ≥0 → ℝ} (hAcont : Continuous A) (hAmono : Monotone A)
    (t : ℝ≥0) :
    continuousMonotoneStieltjesFunction A t = A t := by
  simp [continuousMonotoneStieltjesFunction, hAcont, hAmono]

/-- The Stieltjes measure induced by a continuous nondecreasing path assigns
the expected increment to each half-open interval. -/
@[simp]
theorem continuousMonotoneStieltjesFunction_measure_Ioc
    {A : ℝ≥0 → ℝ} (hAcont : Continuous A) (hAmono : Monotone A)
    (a b : ℝ≥0) :
    (continuousMonotoneStieltjesFunction A).measure (Set.Ioc a b) =
      ENNReal.ofReal (A b - A a) := by
  rw [StieltjesFunction.measure_Ioc]
  simp only [continuousMonotoneStieltjesFunction_apply hAcont hAmono]

/-- Uniform left sums against the increments of a continuous nondecreasing
path converge to integration against its Stieltjes measure. -/
theorem uniformPartition_weighted_stieltjes_tendsto
    (A w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hAcont : Continuous A) (hAmono : Monotone A)
    (hw : Continuous w) :
    Tendsto
      (fun k ↦ ∑ i ∈ Finset.range (k + 1),
        w (uniformPartitionTime t (k + 1) i) *
          (A (uniformPartitionTime t (k + 1) (i + 1)) -
            A (uniformPartitionTime t (k + 1) i)))
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc 0 t, w s ∂
        (continuousMonotoneStieltjesFunction A).measure)) := by
  let F := continuousMonotoneStieltjesFunction A
  let mu : Measure ℝ≥0 := F.measure
  have hF (s : ℝ≥0) : F s = A s := by
    exact continuousMonotoneStieltjesFunction_apply hAcont hAmono s
  have hmu (a b : ℝ≥0) :
      mu (Set.Ioc a b) = ENNReal.ofReal (A b - A a) := by
    simp only [mu, StieltjesFunction.measure_Ioc, hF]
  have hfinite : mu (Set.Ioc 0 t) ≠ ∞ := by
    rw [hmu]
    exact ENNReal.ofReal_ne_top
  have hone : IntegrableOn (fun _ : ℝ≥0 ↦ (1 : ℝ))
      (Set.Ioc 0 t) mu :=
    integrableOn_const hfinite
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    ((isCompact_Icc.image_of_continuousOn hw.continuousOn).isBounded)
  have hwint : IntegrableOn w (Set.Ioc 0 t) mu := by
    refine mu.integrableOn_of_bounded (M := C) hfinite
      hw.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hC (w s) ⟨s, Set.Ioc_subset_Icc_self hs, rfl⟩
  have hraw := uniformPartition_weighted_integral_tendsto
    (μ := mu) (fun _ : ℝ≥0 ↦ (1 : ℝ)) w t hone
      (by simpa only [mul_one] using hwint) (fun _ ↦ zero_le_one)
      hw.continuousOn
  change Tendsto _ Filter.atTop
    (𝓝 (∫ s in Set.Ioc 0 t, w s ∂mu))
  convert hraw using 1
  · funext k
    apply Finset.sum_congr rfl
    intro i _hi
    rw [setIntegral_one_eq_measureReal, setIntegral_one_eq_measureReal]
    simp only [measureReal_def, hmu]
    have hpos1 :
        0 ≤ A (uniformPartitionTime t (k + 1) (i + 1)) - A 0 :=
      sub_nonneg.mpr (hAmono bot_le)
    have hpos0 : 0 ≤ A (uniformPartitionTime t (k + 1) i) - A 0 :=
      sub_nonneg.mpr (hAmono bot_le)
    rw [ENNReal.toReal_ofReal hpos1, ENNReal.toReal_ofReal hpos0]
    ring
  · simp only [mul_one]

/-- Uniform left sums of a process-valued weight against increments of a
candidate bracket process. -/
def bracketWeightedLeftSum
    {W : Type*} (H A : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    H (uniformPartitionTime t n i) omega *
      (A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega)

/-- The pathwise Stieltjes integral of a process-valued weight against a
continuous nondecreasing bracket candidate.  On exceptional paths the total
Stieltjes-function construction uses its zero fallback. -/
def stieltjesBracketIntegral
    {W : Type*} (H A : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  ∫ s in Set.Ioc 0 t, H s omega ∂
    (continuousMonotoneStieltjesFunction (fun r ↦ A r omega)).measure

/-- Fixed-time measurability of the weight and bracket makes each bracket
left sum almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_bracketWeightedLeftSum
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (H A : ℝ≥0 → W → ℝ)
    (hH : ∀ s, AEStronglyMeasurable (H s) P)
    (hA : ∀ s, AEStronglyMeasurable (A s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (bracketWeightedLeftSum H A t n) P := by
  unfold bracketWeightedLeftSum
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega ↦
        H (uniformPartitionTime t n i) omega *
          (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    exact (hH _).mul ((hA _).sub (hA _))
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

/-- Random continuous weights integrated against random continuous
nondecreasing brackets converge in measure to their pathwise Stieltjes
integral. -/
theorem bracketWeightedLeftSum_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (H A : ℝ≥0 → W → ℝ)
    (hH : ∀ s, AEStronglyMeasurable (H s) P)
    (hA : ∀ s, AEStronglyMeasurable (A s) P)
    (hHcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ H s omega))
    (hApath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ A s omega) ∧ Monotone (fun s ↦ A s omega))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ bracketWeightedLeftSum H A t (n + 1))
      Filter.atTop (stieltjesBracketIntegral H A t) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact aestronglyMeasurable_bracketWeightedLeftSum
      H A hH hA t (n + 1)
  · filter_upwards [hHcont, hApath] with omega hHomega hAomega
    exact uniformPartition_weighted_stieltjes_tendsto
      (fun s ↦ A s omega) (fun s ↦ H s omega) t
      hAomega.1 hAomega.2 hHomega

/-- At the terminal horizon, the uncapped process is exactly the classical
Doléans left Riemann sum. -/
theorem doleansDadeLeftSumProcess_terminal
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    doleansDadeLeftSumProcess M bracket T n T omega =
      ∑ i ∈ Finset.range (n + 1),
        doleansDadeExponential M bracket
            (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega) := by
  exact uniformAdaptedMartingaleLeftSumProcess_terminal M
    (doleansDadeExponential M bracket) T n omega

/-- Evaluating a coherent left-sum process at `t` is the same as taking the
terminal left sum of the deterministically stopped integrator, bracket, and
exponential on the original horizon. -/
theorem doleansDadeLeftSumProcess_eq_stopped_terminal
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    doleansDadeLeftSumProcess M bracket T n t omega =
      doleansDadeLeftSumProcess
        (fun s omega ↦ M (min s t) omega)
        (fun s omega ↦ bracket (min s t) omega) T n T omega := by
  rw [doleansDadeLeftSumProcess_terminal]
  unfold doleansDadeLeftSumProcess
    uniformAdaptedMartingaleLeftSumProcess elementaryMartingaleIntegralSum
  simp only [Finset.sum_apply, elementaryMartingaleIntegralProcess]
  apply Finset.sum_congr rfl
  intro i _hi
  let s₀ := uniformPartitionTime T (n + 1) i
  let s₁ := uniformPartitionTime T (n + 1) (i + 1)
  have hs : s₀ ≤ s₁ :=
    monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i)
  by_cases h₀ : s₀ ≤ t
  · have hmin₀ : min t s₀ = s₀ := min_eq_right h₀
    have hmin₀' : min s₀ t = s₀ := min_eq_left h₀
    simp only [s₀] at hmin₀ hmin₀' ⊢
    rw [hmin₀, hmin₀']
    simp only [doleansDadeExponential, doleansDadeLog]
    rw [hmin₀']
    rw [min_comm t (uniformPartitionTime T (n + 1) (i + 1))]
  · have ht₀ : t ≤ s₀ := le_of_not_ge h₀
    have ht₁ : t ≤ s₁ := ht₀.trans hs
    simp only [s₀, s₁] at ht₀ ht₁ ⊢
    rw [min_eq_left ht₀, min_eq_left ht₁,
      min_eq_right ht₀, min_eq_right ht₁]
    simp only [sub_self, mul_zero]

/-- Every stopped diagonal capped-Doléans left sum is a martingale when the
correspondingly stopped integrator is a martingale. -/
theorem
    martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hM : Martingale (localizingStoppedProcess M tau) 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : StronglyAdapted 𝓥 bracket)
    (T : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n) tau) 𝓥 P := by
  unfold cappedDoleansDadeLeftSumProcess
  exact
    martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
      hM (stronglyAdapted_cappedDoleansDadeExponential
        hMadapt hbracket (n + 1))
      (n + 1) (norm_cappedDoleansDadeExponential_le M bracket (n + 1))
      T (n + 1)

/-- A stopped `L¹` limit of the diagonal capped-Doléans left sums is a
local martingale.  This constructs the local-martingale part of the desired
arbitrary-integrator stochastic integral once its analytic convergence is
available. -/
theorem IsLocalMartingale.cappedDoleansDadeLeftSumProcess_limit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : StronglyAdapted 𝓥 bracket) (T : ℝ≥0)
    {integral : ℝ≥0 → W → ℝ}
    (hIadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess integral (hM.localSeq k)))
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess integral (hM.localSeq k) t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (hM.localSeq k) t) 1 P) Filter.atTop (𝓝 0)) :
    IsLocalMartingale integral 𝓥 P := by
  apply isLocalMartingale_of_stopped_tendsto_eLpNorm_one
    hM.isLocalizingSequence_localSeq
    (fun n k ↦
      martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
        (hM.stoppedProcess_localSeq k) hMadapt hbracket T n)
    hIadapt hconv

/-- A stopped convergence-in-measure limit of the diagonal capped-Doléans
left sums is a local martingale when those stopped sums are uniformly
integrable.  This is the Vitali form of
`IsLocalMartingale.cappedDoleansDadeLeftSumProcess_limit`. -/
theorem IsLocalMartingale.cappedDoleansDadeLeftSumProcess_limit_inMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : StronglyAdapted 𝓥 bracket) (T : ℝ≥0)
    {integral : ℝ≥0 → W → ℝ}
    (hIadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess integral (hM.localSeq k)))
    (hUI : ∀ k t, UniformIntegrable (fun n ↦
      localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (hM.localSeq k) t) 1 P)
    (hconv : ∀ k t, TendstoInMeasure P (fun n ↦
      localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (hM.localSeq k) t) Filter.atTop
      (localizingStoppedProcess integral (hM.localSeq k) t)) :
    IsLocalMartingale integral 𝓥 P := by
  apply
    isLocalMartingale_of_stopped_tendstoInMeasure_of_uniformIntegrable
      hM.isLocalizingSequence_localSeq
      (fun n k ↦
        martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
          (hM.stoppedProcess_localSeq k) hMadapt hbracket T n)
      hIadapt hUI hconv

/-- The compensated logarithm is additive when both the martingales and
their selected brackets are added. -/
theorem doleansDadeLog_add
    {W : Type*} (M N bracketM bracketN : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    doleansDadeLog
        (fun s omega => M s omega + N s omega)
        (fun s omega => bracketM s omega + bracketN s omega) t omega =
      doleansDadeLog M bracketM t omega +
        doleansDadeLog N bracketN t omega := by
  simp only [doleansDadeLog]
  ring

/-- Algebraic multiplicativity of stochastic exponentials when the selected
bracket of a sum is the sum of the brackets. No covariation claim is implicit
in this identity. -/
theorem doleansDadeExponential_add
    {W : Type*} (M N bracketM bracketN : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    doleansDadeExponential
        (fun s omega => M s omega + N s omega)
        (fun s omega => bracketM s omega + bracketN s omega) t omega =
      doleansDadeExponential M bracketM t omega *
        doleansDadeExponential N bracketN t omega := by
  rw [doleansDadeExponential, doleansDadeLog_add,
    Real.exp_add]
  rfl

/-- The stochastic exponential associated with the scalar multiple `c M`
and scaled bracket `c² bracket`. -/
theorem doleansDadeExponential_const_mul_apply
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ)
    (t : ℝ≥0) (omega : W) :
    doleansDadeExponential
        (fun s omega => c * M s omega)
        (fun s omega => c ^ 2 * bracket s omega) t omega =
      Real.exp (c * M t omega -
        (1 / 2 : ℝ) * (c ^ 2 * bracket t omega)) :=
  rfl

theorem doleansDadeExponential_pos
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    0 < doleansDadeExponential M bracket t omega :=
  Real.exp_pos _

theorem doleansDadeExponential_zero
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : M 0 omega = 0) (hbracket : bracket 0 omega = 0) :
    doleansDadeExponential M bracket 0 omega = 1 := by
  simp [doleansDadeExponential, doleansDadeLog, hM, hbracket]

/-- Continuous paths of the martingale and bracket give a continuous
stochastic-exponential path. -/
theorem continuous_doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : Continuous (fun t => M t omega))
    (hbracket : Continuous (fun t => bracket t omega)) :
    Continuous (fun t => doleansDadeExponential M bracket t omega) := by
  exact Real.continuous_exp.comp
    (hM.sub (continuous_const.mul hbracket))

/-- Capping paired dyadic exits by larger continuous exits gives a
grid-independent `L²` bound for the resulting Doléans-transform error.  The
outer exponential exit turns every diagonal cap into the same bounded
before-exit coefficient. -/
theorem eLpNorm_pairedExit_sub_outerCappedDyadic_cappedDoleans_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T H K R K' R' : ℝ≥0) (hKK' : K ≤ K') (hRR' : R ≤ R')
    (m n : ℕ) (t : ℝ≥0) :
    let E := doleansDadeExponential M bracket
    let tau : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K omega)
        (continuousExitTime E H R omega)
    let theta : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K' omega)
        (continuousExitTime E H R' omega)
    let rho : W → WithTop ℝ≥0 := fun omega =>
      min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
    eLpNorm
      (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) tau t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) rho t) 2 P ≤
      R' * eLpNorm
        ((localizingStoppedProcess M tau - localizingStoppedProcess M rho) T -
          (localizingStoppedProcess M tau - localizingStoppedProcess M rho) 0)
        2 P := by
  dsimp only
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K' omega)
      (continuousExitTime E H R' omega)
  let rho : W → WithTop ℝ≥0 := fun omega =>
    min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
  let Hn := cappedDoleansDadeExponential M bracket (n + 1)
  let Hkill := beforeContinuousExitProcessOf E Hn H R'
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have hMtau : Martingale (localizingStoppedProcess M tau) 𝒱 P :=
    martingale_localizingStoppedProcess_min_continuousExitTime
      hM hMcont hM.stronglyAdapted hEadapt H K R
  have hMrho : Martingale (localizingStoppedProcess M rho) 𝒱 P :=
    martingale_localizingStoppedProcess_pairedDyadic_min_outerContinuousExit
      hM hMcont hM.stronglyAdapted hEadapt H K R K' R' m
  have htauM (omega : W) : tau omega ≤
      continuousExitTime M H K' omega :=
    (min_le_left _ _).trans
      (continuousExitTime_mono_radius M H K K' hKK' omega)
  have hrhoM (omega : W) : rho omega ≤
      continuousExitTime M H K' omega :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htauE (omega : W) : tau omega ≤
      continuousExitTime E H R' omega :=
    (min_le_right _ _).trans
      (continuousExitTime_mono_radius E H R R' hRR' omega)
  have hrhoE (omega : W) : rho omega ≤
      continuousExitTime E H R' omega :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMtauT : MemLp (localizingStoppedProcess M tau T) 2 P := by
    apply MemLp.of_bound
      ((hMtau.stronglyAdapted T).mono (𝒱.le T)).aestronglyMeasurable K'
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_of_le_continuousExitTime
        hMcont H K' htauM T omega
  have hMrhoT : MemLp (localizingStoppedProcess M rho T) 2 P := by
    apply MemLp.of_bound
      ((hMrho.stronglyAdapted T).mono (𝒱.le T)).aestronglyMeasurable K'
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_of_le_continuousExitTime
        hMcont H K' hrhoM T omega
  have hNT : MemLp
      ((localizingStoppedProcess M tau -
        localizingStoppedProcess M rho) T) 2 P :=
    hMtauT.sub hMrhoT
  have hHkill : StronglyAdapted 𝒱 Hkill :=
    stronglyAdapted_beforeContinuousExitProcessOf hEadapt
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) H R'
  have hcap : ∀ (s : ℝ≥0) omega,
      (s : WithTop ℝ≥0) < continuousExitTime E H R' omega →
        ‖Hn s omega‖ ≤ R' := by
    intro s omega hs
    have hER := norm_le_of_lt_continuousExitTime hEcont H R' s omega hs
    rw [abs_of_pos (doleansDadeExponential_pos M bracket s omega)] at hER
    dsimp only [Hn, cappedDoleansDadeExponential]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (min_le_left _ _).trans hER
    · exact le_min (doleansDadeExponential_pos M bracket s omega).le
        (NNReal.coe_nonneg _)
  have hHkillBound : ∀ s omega, ‖Hkill s omega‖ ≤ R' :=
    norm_beforeContinuousExitProcessOf_le H R' R' hcap
  have hgeneric := eLpNorm_sub_localized_uniformAdapted_apply_le
    hMtau hMrho T hNT hHkill R' hHkillBound n t
  have hreplace := uniformAdapted_sub_localized_replace_beforeContinuousExit
    M E Hn T (n + 1) H R' htauE hrhoE
  have heqProcess :
      localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) rho =
      localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hkill T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hkill T (n + 1)) rho := by
    rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      uniformAdaptedMartingaleLeftSumProcess_sub, hreplace,
      ← uniformAdaptedMartingaleLeftSumProcess_sub,
      ← localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      ← localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  unfold cappedDoleansDadeLeftSumProcess
  change eLpNorm
    ((localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) rho) t)
      2 P ≤ _
  rw [congrFun heqProcess t]
  exact hgeneric

/-- The grid-independent outer-capped Doléans error bound tends to zero as
the inner dyadic exits converge to their continuous exits. -/
theorem tendsto_outerCappedDyadic_doleans_error_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (H K R K' R' T : ℝ≥0) (hKK' : K ≤ K') (hRR' : R ≤ R')
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    let E := doleansDadeExponential M bracket
    let tau : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K omega)
        (continuousExitTime E H R omega)
    let theta : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K' omega)
        (continuousExitTime E H R' omega)
    let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
      min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
    Tendsto
      (fun m => R' * eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) 0) 2 P)
      Filter.atTop (nhds 0) := by
  dsimp only
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K' omega)
      (continuousExitTime E H R' omega)
  let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
    min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have htau_rho (m : ℕ) (omega : W) : tau omega ≤ rho m omega := by
    have hMdyadic : continuousExitTime M H K omega ≤
        dyadicHittingTimeNNReal M H K m omega := by
      unfold continuousExitTime
      exact iInf_le _ m
    have hEdyadic : continuousExitTime E H R omega ≤
        dyadicHittingTimeNNReal E H R m omega := by
      unfold continuousExitTime
      exact iInf_le _ m
    have hsigma : tau omega ≤
        pairedDyadicHittingTimeNNReal M E H K R m omega := by
      exact min_le_min hMdyadic hEdyadic
    have htheta : tau omega ≤ theta omega :=
      min_le_min (continuousExitTime_mono_radius M H K K' hKK' omega)
        (continuousExitTime_mono_radius E H R R' hRR' omega)
    exact le_min hsigma htheta
  have hrhopos (m : ℕ) (omega : W) :
      (⊥ : WithTop ℝ≥0) < rho m omega :=
    (hpos omega).trans_le (htau_rho m omega)
  have hzero (m : ℕ) :
      (localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) 0 = fun _ => 0 := by
    funext omega
    simp only [Pi.sub_apply]
    rw [localizingStoppedProcess_zero_of_pos M tau omega (hpos omega),
      localizingStoppedProcess_zero_of_pos M (rho m) omega
        (hrhopos m omega), sub_self]
  have hraw :=
    tendsto_eLpNorm_two_localizingStoppedProcess_pairedDyadic_min_outerExit
      (P := P) hM hEadapt hMcont H K R K' R' hKK' hRR' hpos T
  have hterminal : Tendsto
      (fun m => eLpNorm
        ((localizingStoppedProcess M tau -
          localizingStoppedProcess M (rho m)) T) 2 P)
      Filter.atTop (nhds 0) := by
    simpa only [tau, rho, theta, Pi.sub_apply,
      eLpNorm_sub_comm] using hraw
  have hincrement : Tendsto
      (fun m => eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) 0) 2 P)
      Filter.atTop (nhds 0) := by
    apply hterminal.congr'
    exact Filter.Eventually.of_forall fun m => by
      change eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T) 2 P =
        eLpNorm
          ((localizingStoppedProcess M tau -
              localizingStoppedProcess M (rho m)) T -
            (localizingStoppedProcess M tau -
              localizingStoppedProcess M (rho m)) 0) 2 P
      rw [hzero m]
      change eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T) 2 P =
        eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T - 0) 2 P
      rw [sub_zero]
  have hmul := ENNReal.Tendsto.const_mul
    (a := (R' : ℝ≥0∞)) hincrement (Or.inr ENNReal.coe_ne_top)
  simpa only [tau, rho, theta, mul_zero] using hmul

/-- After stopping both the integrator and the stochastic exponential at
bounded continuous exits, the diagonal capped Doléans left sums have a
grid-independent terminal `L²` bound.  The exponential exit, rather than
the growing deterministic cap, supplies the uniform coefficient bound. -/
theorem
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R : ℝ≥0) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R) T) 2 P ≤
      R * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) 0)
          2 P := by
  let E := doleansDadeExponential M bracket
  have hEadapt : StronglyAdapted 𝓥 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have hcap : ∀ (t : ℝ≥0) omega,
      (t : WithTop ℝ≥0) < continuousExitTime E ET R omega →
        ‖cappedDoleansDadeExponential M bracket (n + 1) t omega‖ ≤ R := by
    intro t omega ht
    have hER := norm_le_of_lt_continuousExitTime hEcont ET R t omega ht
    rw [abs_of_pos (doleansDadeExponential_pos M bracket t omega)] at hER
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (min_le_left _ _).trans hER
    · exact le_min (doleansDadeExponential_pos M bracket t omega).le
        (NNReal.coe_nonneg _)
  unfold cappedDoleansDadeLeftSumProcess
  exact eLpNorm_doubleExit_localized_uniformAdaptedOf_le
    hM hMcont hEadapt
    (stronglyAdapted_cappedDoleansDadeExponential
      hM.stronglyAdapted hbracket (n + 1))
    T MT K ET R R hcap n

/-- The same two bounded continuous exits turn every diagonal capped
Doléans left-sum process into a genuine martingale. -/
theorem
    martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (T MT K ET R : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R))
      𝓥 P := by
  let tauM := continuousExitTime M MT K
  let E := doleansDadeExponential M bracket
  let X := cappedDoleansDadeLeftSumProcess M bracket T n
  let X1 := localizingStoppedProcess X tauM
  have hN1 : Martingale (localizingStoppedProcess M tauM) 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime hM hMcont MT K
  have hX1 : Martingale X1 𝓥 P := by
    exact martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
      hN1 hM.stronglyAdapted hbracket T n
  have hXcont : ∀ omega, Continuous (fun t => X t omega) := fun omega =>
    continuous_uniformAdaptedMartingaleLeftSumProcess hMcont
      T (n + 1) omega
  have hX1cont : ∀ omega, Continuous (fun t => X1 t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hXcont MT K
  have hEadapt : StronglyAdapted 𝓥 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  exact martingale_localizingStoppedProcess_continuousExitTime_of_adapted
    hX1 hX1cont hEadapt ET R

/-- On a probability space, the twice-exit-localized diagonal capped
Doléans left sums are uniformly integrable in `L¹`, uniformly over the
simultaneously growing grid and cap. -/
theorem
    uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R : ℝ≥0) :
    UniformIntegrable
      (fun n =>
        localizingStoppedProcess
          (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (continuousExitTime M MT K))
          (continuousExitTime (doleansDadeExponential M bracket) ET R) T)
      1 P := by
  let E := doleansDadeExponential M bracket
  let N := localizingStoppedProcess
    (localizingStoppedProcess M (continuousExitTime M MT K))
    (continuousExitTime E ET R)
  let C : ℝ≥0 := (R * eLpNorm (N T - N 0) 2 P).toNNReal
  have hNmart : Martingale N 𝓥 P := by
    have hN1 := martingale_localizingStoppedProcess_continuousExitTime
      hM hMcont MT K
    have hN1cont := continuous_localizingStoppedProcess_continuousExitTime
      (Z := M) hMcont MT K
    exact martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hN1 hN1cont
        (stronglyAdapted_doleansDadeExponential
          hM.stronglyAdapted hbracket) ET R
  have hNT : MemLp (N T) 2 P := by
    apply MemLp.of_bound
      ((hNmart.stronglyAdapted T).mono (𝓥.le T)).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_le K
        (norm_localizingStoppedProcess_continuousExitTime_le hMcont MT K)
        T omega
  have hN0 : MemLp (N 0) 2 P :=
    martingale_memLp_of_le hNmart bot_le one_le_two hNT
  have hfinite : R * eLpNorm (N T - N 0) 2 P ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hNT.sub hN0).2.ne
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C)
  · intro n
    exact (((martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket T MT K ET R n).stronglyAdapted T).mono
        (𝓥.le T)).aestronglyMeasurable
  · intro n
    rw [show (C : ℝ≥0∞) = R * eLpNorm (N T - N 0) 2 P by
      exact ENNReal.coe_toNNReal hfinite]
    exact eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_le
      hM hMcont hbracket hbracketCont T MT K ET R n

/-- The grid-independent `L²` bound for twice-exit-localized diagonal
Doléans sums holds at every observation time, not only at the terminal
horizon.  Before the horizon this is martingale contraction; afterwards it
uses eventual constancy of the coherent left-sum process. -/
theorem
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R t : ℝ≥0) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R) t) 2 P ≤
      R * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) 0)
          2 P := by
  let tauM := continuousExitTime M MT K
  let tauE := continuousExitTime (doleansDadeExponential M bracket) ET R
  let X := cappedDoleansDadeLeftSumProcess M bracket T n
  let X1 := localizingStoppedProcess X tauM
  let X2 := localizingStoppedProcess X1 tauE
  have hterminal :=
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_le
      hM hMcont hbracket hbracketCont T MT K ET R n
  rcases le_total t T with htT | hTt
  · exact (martingale_eLpNorm_le_of_le
      (martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
        hM hMcont hbracket T MT K ET R n) htT one_le_two).trans hterminal
  · have hXconst : ∀ s, T ≤ s → X s = X T := by
      intro s hTs
      exact uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n s hTs
    have hX1const : ∀ s, T ≤ s → X1 s = X1 T := by
      intro s hTs
      exact localizingStoppedProcess_eq_terminal_of_le
        X tauM T s hTs hXconst
    have hX2eq : X2 t = X2 T :=
      localizingStoppedProcess_eq_terminal_of_le
        X1 tauE T t hTt hX1const
    rw [show localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) tauM) tauE t =
        localizingStoppedProcess
          (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n) tauM) tauE T
      from hX2eq]
    exact hterminal

/-- The twice-exit-localized diagonal capped Doléans sums are uniformly
integrable at every observation time. -/
theorem
    uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R t : ℝ≥0) :
    UniformIntegrable
      (fun n =>
        localizingStoppedProcess
          (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (continuousExitTime M MT K))
          (continuousExitTime (doleansDadeExponential M bracket) ET R) t)
      1 P := by
  let E := doleansDadeExponential M bracket
  let N := localizingStoppedProcess
    (localizingStoppedProcess M (continuousExitTime M MT K))
    (continuousExitTime E ET R)
  let C : ℝ≥0 := (R * eLpNorm (N T - N 0) 2 P).toNNReal
  have hNmart : Martingale N 𝓥 P := by
    have hN1 := martingale_localizingStoppedProcess_continuousExitTime
      hM hMcont MT K
    have hN1cont := continuous_localizingStoppedProcess_continuousExitTime
      (Z := M) hMcont MT K
    exact martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hN1 hN1cont
        (stronglyAdapted_doleansDadeExponential
          hM.stronglyAdapted hbracket) ET R
  have hNT : MemLp (N T) 2 P := by
    apply MemLp.of_bound
      ((hNmart.stronglyAdapted T).mono (𝓥.le T)).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_le K
        (norm_localizingStoppedProcess_continuousExitTime_le hMcont MT K)
        T omega
  have hN0 : MemLp (N 0) 2 P :=
    martingale_memLp_of_le hNmart bot_le one_le_two hNT
  have hfinite : R * eLpNorm (N T - N 0) 2 P ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hNT.sub hN0).2.ne
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C)
  · intro n
    exact (((martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket T MT K ET R n).stronglyAdapted t).mono
        (𝓥.le t)).aestronglyMeasurable
  · intro n
    rw [show (C : ℝ≥0∞) = R * eLpNorm (N T - N 0) 2 P by
      exact ENNReal.coe_toNNReal hfinite]
    exact
      eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply_le
        hM hMcont hbracket hbracketCont T MT K ET R t n

/-- Each member of the common continuous-exit localizing sequence gives
uniform integrability of the localized diagonal capped Doléans sums at every
observation time. -/
theorem
    uniformIntegrable_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0) (k : ℕ) (t : ℝ≥0) :
    UniformIntegrable
      (fun n =>
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (pairedContinuousExitLocalizingSequence M
            (doleansDadeExponential M bracket) (T + 1) k) t)
      1 P := by
  let H : ℝ≥0 := T + 1
  let E := doleansDadeExponential M bracket
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hUI :=
    uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply
      hM hMcont hbracket hbracketCont T H (k + 1) H (k + 1) t
  apply hUI.ae_eq
  intro n
  have hXconst : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    have hTH : T ≤ H := by
      dsimp only [H]
      exact le_add_right le_rfl
    have hTs : T ≤ s := hTH.trans hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s hTs).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  have heq := localizingStoppedProcess_pairedContinuousExit_eq
    (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k hHpos hXconst
  exact Filter.Eventually.of_forall fun omega =>
    congrFun (congrFun heq.symm t) omega

/-- Localizing a diagonal capped Doléans sum by the common continuous-exit
exhaustion gives a genuine martingale. -/
theorem martingale_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (T : ℝ≥0) (k n : ℕ) :
    Martingale
      (localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (pairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k)) 𝓥 P := by
  let H : ℝ≥0 := T + 1
  let E := doleansDadeExponential M bracket
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hXconst : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    have hTH : T ≤ H := by
      dsimp only [H]
      exact le_add_right le_rfl
    have hTs : T ≤ s := hTH.trans hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s hTs).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  rw [localizingStoppedProcess_pairedContinuousExit_eq
    (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k hHpos hXconst]
  exact martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
    hM hMcont hbracket T H (k + 1) H (k + 1) n

/-- Fixed-horizon local Vitali closure with all localization and moment
conditions discharged.  The only remaining input is convergence in measure
after the explicit common continuous-exit stopping sequence. -/
theorem isLocalMartingale_doleansDadeIntegralCandidate_stop_of_pairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0)
    (hconv : ∀ k t, TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (pairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (pairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)) :
    IsLocalMartingale
      (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
      𝓥 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let tau := pairedContinuousExitLocalizingSequence M E H
  have hEadapt : StronglyAdapted 𝓥 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have htau : IsLocalizingSequence 𝓥 tau P :=
    isLocalizingSequence_pairedContinuousExit hM.stronglyAdapted hEadapt
      hMcont hEcont H
  apply isLocalMartingale_of_stopped_tendstoInMeasure_of_uniformIntegrable
    htau
  · intro n k
    exact martingale_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket T k n
  · intro k
    apply stronglyAdapted_localizingStoppedProcess
    · intro t
      exact (stronglyAdapted_doleansDadeIntegralCandidate
        hM.stronglyAdapted hbracket (min T t)).mono
          (𝓥.mono (min_le_right T t))
    · intro omega
      exact (continuous_doleansDadeIntegralCandidate M bracket omega
        (hMcont omega) (hbracketCont omega)).comp
          (continuous_const.min continuous_id)
    · exact htau.isStoppingTime k
  · intro k t
    exact uniformIntegrable_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket hbracketCont T k t
  · exact hconv

/-- Fixed-horizon continuous-local-martingale endpoint.  All optional
stopping and uniform-integrability obligations are internal; convergence in
measure under the explicit paired exit sequence is the sole analytic input. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_pairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0)
    (hconv : ∀ k t, TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (pairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (pairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝓥 P := by
  have hlocal := isLocalMartingale_doleansDadeIntegralCandidate_stop_of_pairedExit
    hM hMcont hbracket hbracketCont T hconv
  refine ⟨?_, Filter.Eventually.of_forall fun omega => ?_⟩
  · have hadd := hlocal.const_add 1
    convert hadd using 1
    funext s omega
    simp only [doleansDadeIntegralCandidate]
    ring
  · exact (continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)).comp
        (continuous_const.min continuous_id)

/-- The fixed-horizon local Vitali closure using the shifted radius-`n+2`
paired continuous-exit exhaustion. -/
theorem
    isLocalMartingale_doleansDadeIntegralCandidate_stop_of_shiftedPairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0)
    (hconv : ∀ k t, TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (shiftedPairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (shiftedPairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)) :
    IsLocalMartingale
      (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
      𝒱 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let tau := shiftedPairedContinuousExitLocalizingSequence M E H
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have htau : IsLocalizingSequence 𝒱 tau P :=
    isLocalizingSequence_shiftedPairedContinuousExit hM.stronglyAdapted
      hEadapt hMcont hEcont H
  apply isLocalMartingale_of_stopped_tendstoInMeasure_of_uniformIntegrable
    htau
  · intro n k
    exact martingale_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket T (k + 1) n
  · intro k
    apply stronglyAdapted_localizingStoppedProcess
    · intro t
      exact (stronglyAdapted_doleansDadeIntegralCandidate
        hM.stronglyAdapted hbracket (min T t)).mono
          (𝒱.mono (min_le_right T t))
    · intro omega
      exact (continuous_doleansDadeIntegralCandidate M bracket omega
        (hMcont omega) (hbracketCont omega)).comp
          (continuous_const.min continuous_id)
    · exact htau.isStoppingTime k
  · intro k t
    exact uniformIntegrable_pairedContinuousExit_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket hbracketCont T (k + 1) t
  · exact hconv

/-- Fixed-horizon continuous-local-martingale endpoint using the shifted
paired continuous-exit exhaustion. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_shiftedPairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0)
    (hconv : ∀ k t, TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (shiftedPairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (shiftedPairedContinuousExitLocalizingSequence M
          (doleansDadeExponential M bracket) (T + 1) k) t)) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  have hlocal :=
    isLocalMartingale_doleansDadeIntegralCandidate_stop_of_shiftedPairedExit
      hM hMcont hbracket hbracketCont T hconv
  refine ⟨?_, Filter.Eventually.of_forall fun omega => ?_⟩
  · have hadd := hlocal.const_add 1
    convert hadd using 1
    funext s omega
    simp only [doleansDadeIntegralCandidate]
    ring
  · exact (continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)).comp
        (continuous_const.min continuous_id)

/-- A uniform-on-bounded-time approximation estimate discharges the
random-stopping convergence required by the fixed-horizon Doléans endpoint.
The `k`-th error majorant only needs to control the deterministic interval
containing the `k`-th paired continuous-exit localizer. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_uniform_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T : ℝ≥0) (U : ℕ → ℕ → W → ℝ)
    (hU : ∀ k, TendstoInMeasure P (U k) Filter.atTop (fun _ => 0))
    (hbound : ∀ (k n : ℕ) (s : ℝ≥0) (omega : W),
      s ≤ (T + 1) + (k + 1) →
      |cappedDoleansDadeLeftSumProcess M bracket T n s omega -
        doleansDadeIntegralCandidate M bracket (min T s) omega| ≤
          |U k n omega|) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_pairedExit
      hM hMcont hbracket hbracketCont T
  intro k t
  exact tendstoInMeasure_localizingStoppedProcess_of_uniform_error
    ((T + 1) + (k + 1))
    (pairedContinuousExitLocalizingSequence_le M
      (doleansDadeExponential M bracket) (T + 1) k)
    (hbound k) (hU k) t

/-- Almost-everywhere continuous inputs give almost-everywhere continuous
stochastic-exponential paths. -/
theorem ae_continuous_doleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ)
    (hM : ∀ᵐ omega ∂P, Continuous (fun t => M t omega))
    (hbracket : ∀ᵐ omega ∂P, Continuous (fun t => bracket t omega)) :
    ∀ᵐ omega ∂P,
      Continuous (fun t => doleansDadeExponential M bracket t omega) := by
  filter_upwards [hM, hbracket] with omega hMomega hbracketOmega
  exact continuous_doleansDadeExponential M bracket omega
    hMomega hbracketOmega

/-- Under the before-stop quadratic-variation contract, the quadratic sums
weighted by one half of the Doléans--Dade exponential converge in measure to
the corresponding pathwise Stieltjes bracket integral.  This is the
second-order half of the drift cancellation for an arbitrary continuous
bracket. -/
theorem
    generalItoMixedQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoMixedQuadraticApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) M t (n + 1))
      Filter.atTop
      (stieltjesBracketIntegral
        (fun s omega ↦ (1 / 2 : ℝ) *
          doleansDadeExponential M bracket s omega)
        bracket t) := by
  have hsecond : Continuous (fun p : ℝ × ℝ ↦
      itoSpaceSecondDerivative (fun _ x ↦ Real.exp x) p.1 p.2) := by
    simp only [itoSpaceSecondDerivative, Real.deriv_exp]
    fun_prop
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝓥.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝓥.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hweightMeas : ∀ s, AEStronglyMeasurable
      (fun omega ↦ (1 / 2 : ℝ) *
        doleansDadeExponential M bracket s omega) P := by
    intro s
    exact aestronglyMeasurable_const.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s))
  have hweightCont : ∀ᵐ omega ∂P, Continuous (fun s ↦
      (1 / 2 : ℝ) * doleansDadeExponential M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact continuous_const.mul
      (continuous_doleansDadeExponential M bracket omega
        hMomega hbracketOmega.1)
  have hG := bracketWeightedLeftSum_tendstoInMeasure
    (fun s omega ↦ (1 / 2 : ℝ) *
      doleansDadeExponential M bracket s omega)
    bracket hweightMeas hbracketMeas hweightCont hbracketPath t
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_generalItoMixedQuadraticApprox
        (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket) M
        hlogMeas hMmeas 0 (n + 1)
    · filter_upwards with omega
      simp [generalItoMixedQuadraticApprox, stieltjesBracketIntegral,
        uniformPartitionTime]
  · apply generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
      (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket) M
      hlogMeas hMmeas t ht bracket
        (stieltjesBracketIntegral
          (fun s omega ↦ (1 / 2 : ℝ) *
            doleansDadeExponential M bracket s omega) bracket t)
      (Y := doleansDadeLog M bracket)
    · intro a ha
      simpa only [min_eq_right ha] using hbefore t a
    · simp only [itoSpaceSecondDerivative, Real.deriv_exp]
      change TendstoInMeasure P
        (fun k ↦ bracketWeightedLeftSum
          (fun s omega ↦ (1 / 2 : ℝ) *
            Real.exp (doleansDadeLog M bracket s omega))
          bracket t (k + 1)) Filter.atTop
        (stieltjesBracketIntegral
          (fun s omega ↦ (1 / 2 : ℝ) *
            doleansDadeExponential M bracket s omega) bracket t)
      simpa only [doleansDadeExponential] using hG
    · refine ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, ?_⟩
      filter_upwards [hMcont, hbracketPath]
        with omega hMomega hbracketOmega
      exact hMomega.sub (continuous_const.mul hbracketOmega.1)

/-- The compensated logarithm `M - (1/2) bracket` has the same fixed-time
quadratic variation as `M`: the continuous monotone bracket term has zero
quadratic variation and hence may be removed. -/
theorem hasQuadraticVariationInProbabilityAt_doleansDadeLog
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (doleansDadeLog M bracket) P t (bracket t) := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketZero : HasQuadraticVariationInProbabilityAt
      bracket P t (fun _ ↦ 0) :=
    quadraticVariation_continuous_monotone_inProbability_zero
      bracket hbracketMeas hbracketPath t
  have hdriftZero : HasQuadraticVariationInProbabilityAt
      (fun s omega ↦ (-1 / 2 : ℝ) * bracket s omega) P t (fun _ ↦ 0) := by
    simpa only [mul_zero] using hbracketZero.const_mul hbracketMeas (-1 / 2 : ℝ)
  have hsum := hdriftZero.add_of_left_zero_of_aestronglyMeasurable
    (hbefore.toProcess t)
    (fun s ↦ aestronglyMeasurable_const.mul (hbracketMeas s)) hMmeas
  apply hsum.congr
  · intro s
    filter_upwards with omega
    simp only [doleansDadeLog]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Taylor's second-order remainder for the exponential of the compensated
logarithm vanishes in probability.  The bracket limit required by Taylor's
theorem is supplied by `hasQuadraticVariationInProbabilityAt_doleansDadeLog`.
-/
theorem doleansDadeLog_exp_stateTaylorRemainder_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ itoStateTaylorRemainderApprox Real.exp
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hlogCont : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ doleansDadeLog M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact hMomega.sub (continuous_const.mul hbracketOmega.1)
  have hself : IsContinuousProcessModification
      (doleansDadeLog M bracket) (doleansDadeLog M bracket) P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hlogCont⟩
  exact hself.stateTaylorRemainder_tendstoInMeasure Real.exp
    Real.contDiff_exp t (bracket t) hlogMeas
    (hasQuadraticVariationInProbabilityAt_doleansDadeLog
      hM hbracket hbracketPath hbefore t)

/-- Once the local martingale and its selected quadratic variation have
continuous paths, continuity of the stochastic exponential is automatic. -/
theorem ae_continuous_doleansDadeExponential_of_continuousLocalMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket : ℝ≥0 → W → ℝ}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hM : IsContinuousLocalMartingale M 𝓕 P)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P) :
    ∀ᵐ omega ∂P,
      Continuous (fun t => doleansDadeExponential M bracket t omega) := by
  exact ae_continuous_doleansDadeExponential M bracket hM.2
    (hbracket.2.1.mono fun _ homega => homega.1)

/-- Structural assembly of the Doléans–Dade conclusion: under the continuous
input and bracket contracts, only local martingality of the exponential
remains to be proved. -/
theorem isContinuousLocalMartingale_doleansDadeExponential_of_isLocalMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket : ℝ≥0 → W → ℝ}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hM : IsContinuousLocalMartingale M 𝓕 P)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hexponential : IsLocalMartingale
      (doleansDadeExponential M bracket) 𝓕 P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓕 P :=
  ⟨hexponential,
    ae_continuous_doleansDadeExponential_of_continuousLocalMartingale
      hM hbracket⟩

/-- Process-level endpoint of the Itô argument.  Once the exponential has
been identified pointwise with one plus a local-martingale stochastic
integral, its local-martingale and continuity conclusions follow.  Thus the
remaining general-theory obligation is precisely to construct the integral
process and prove this identity. -/
theorem isContinuousLocalMartingale_doleansDadeExponential_of_integral_identity
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket integral : ℝ≥0 → W → ℝ}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hM : IsContinuousLocalMartingale M 𝓕 P)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hintegral : IsLocalMartingale integral 𝓕 P)
    (hidentity : doleansDadeExponential M bracket =
      fun t omega => 1 + integral t omega) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓕 P := by
  apply isContinuousLocalMartingale_doleansDadeExponential_of_isLocalMartingale
    hM hbracket
  rw [hidentity]
  exact hintegral.const_add 1

/-- Concrete process-level reduction of the arbitrary Doléans–Dade theorem.
The integral is approximated by the explicit diagonal sequence of bounded
capped-exponential uniform left sums.  Stopped `L¹` convergence makes that
integral a local martingale; the supplied Itô identity then yields the full
continuous-local-martingale conclusion. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_cappedLeftSumLimit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket integral : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketAdapt : StronglyAdapted 𝓥 bracket) (T : ℝ≥0)
    (hIadapt : ∀ k, StronglyAdapted 𝓥
      (localizingStoppedProcess integral (hM.1.localSeq k)))
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess integral (hM.1.localSeq k) t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (hM.1.localSeq k) t) 1 P) Filter.atTop (𝓝 0))
    (hidentity : doleansDadeExponential M bracket =
      fun t omega => 1 + integral t omega) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓥 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_integral_identity
      hM hbracket
  · exact hM.1.cappedDoleansDadeLeftSumProcess_limit
      hMadapt hbracketAdapt T hIadapt hconv
  · exact hidentity

/-- Direct Doléans--Dade endpoint for strongly progressive inputs.  The
adaptation and identity hypotheses of the general approximation theorem are
discharged internally.  It remains only to prove stopped `L¹`-norm
convergence of the explicit bounded diagonal left sums to
`doleansDadeExponential M bracket - 1`. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_progressive_cappedLeftSumLimit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝓥 P)
    (hMprog : IsStronglyProgressive 𝓥 M)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketProg : IsStronglyProgressive 𝓥 bracket)
    (T : ℝ≥0)
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
          (hM.1.localSeq k) t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (hM.1.localSeq k) t) 1 P) Filter.atTop (𝓝 0)) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓥 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_cappedLeftSumLimit
      hM hMprog.stronglyAdapted hbracket hbracketProg.stronglyAdapted T
  · intro k
    exact stronglyAdapted_localizingStoppedProcess_of_isStronglyProgressive
      (isStronglyProgressive_doleansDadeIntegralCandidate
        hMprog hbracketProg)
      (hM.1.isLocalizingSequence_localSeq.isStoppingTime k)
  · exact hconv
  · exact doleansDadeExponential_eq_one_add_integralCandidate M bracket

/-- Vitali-form direct endpoint for strongly progressive inputs.  Stopped
convergence in measure of the concrete capped sums, together with their
stopped uniform integrability, suffices for the full continuous-local-
martingale conclusion. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_progressive_cappedLeftSumLimit_inMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝓥 P)
    (hMprog : IsStronglyProgressive 𝓥 M)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketProg : IsStronglyProgressive 𝓥 bracket)
    (T : ℝ≥0)
    (hUI : ∀ k t, UniformIntegrable (fun n ↦
      localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (hM.1.localSeq k) t) 1 P)
    (hconv : ∀ k t, TendstoInMeasure P (fun n ↦
      localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (hM.1.localSeq k) t) Filter.atTop
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        (hM.1.localSeq k) t)) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓥 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_integral_identity
      hM hbracket
  · exact hM.1.cappedDoleansDadeLeftSumProcess_limit_inMeasure
      hMprog.stronglyAdapted hbracketProg.stronglyAdapted T
      (fun k ↦
        stronglyAdapted_localizingStoppedProcess_of_isStronglyProgressive
          (isStronglyProgressive_doleansDadeIntegralCandidate
            hMprog hbracketProg)
          (hM.1.isLocalizingSequence_localSeq.isStoppingTime k))
      hUI hconv
  · exact doleansDadeExponential_eq_one_add_integralCandidate M bracket

/-- Localized second-moment form of the direct Doléans--Dade endpoint.  A
uniform `L²` bound after each random localization supplies stopped `L¹`
uniform integrability; stopped convergence in measure is then the only other
limit hypothesis needed by the local Vitali closure. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_progressive_stopped_uniform_eLpNorm_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝓥 P)
    (hMprog : IsStronglyProgressive 𝓥 M)
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketProg : IsStronglyProgressive 𝓥 bracket)
    (T : ℝ≥0)
    (hL2 : ∀ k t, ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (hM.1.localSeq k) t) 2 P ≤ C)
    (hconv : ∀ k t, TendstoInMeasure P (fun n ↦
      localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (hM.1.localSeq k) t) Filter.atTop
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        (hM.1.localSeq k) t)) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓥 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_progressive_cappedLeftSumLimit_inMeasure
      hM hMprog hbracket hbracketProg T
  · intro k t
    obtain ⟨C, hC⟩ := hL2 k t
    apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C) _ hC
    intro n
    exact (((martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
      (hM.1.stoppedProcess_localSeq k) hMprog.stronglyAdapted
        hbracketProg.stronglyAdapted T n).stronglyMeasurable t).mono
          (𝓥.le t)).aestronglyMeasurable
  · exact hconv

/-- Direct Doléans--Dade endpoint for the canonical integral candidate under
all-path continuity.  This convenient corollary obtains strong progressive
measurability from the continuous adapted inputs. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_candidate_cappedLeftSumLimit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hMcont : ∀ omega, Continuous (fun t ↦ M t omega))
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketAdapt : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t ↦ bracket t omega))
    (T : ℝ≥0)
    (hconv : ∀ k t, Tendsto (fun n ↦ eLpNorm
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
          (hM.1.localSeq k) t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (hM.1.localSeq k) t) 1 P) Filter.atTop (𝓝 0)) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝓥 P := by
  exact
    isContinuousLocalMartingale_doleansDadeExponential_of_progressive_cappedLeftSumLimit
      hM (hMadapt.isStronglyProgressive_of_continuous hMcont) hbracket
      (hbracketAdapt.isStronglyProgressive_of_continuous hbracketCont)
      T hconv

/-- The exponential test function has zero time derivative. -/
theorem itoTimeDerivative_exp_state (s x : ℝ) :
    itoTimeDerivative (fun _ x => Real.exp x) s x = 0 := by
  simp [itoTimeDerivative]

/-- The first state derivative of the exponential test function is itself. -/
theorem itoSpaceDerivative_exp_state (s x : ℝ) :
    itoSpaceDerivative (fun _ x => Real.exp x) s x = Real.exp x := by
  simp [itoSpaceDerivative, Real.deriv_exp]

/-- The second state derivative of the exponential test function is itself. -/
theorem itoSpaceSecondDerivative_exp_state (s x : ℝ) :
    itoSpaceSecondDerivative (fun _ x => Real.exp x) s x = Real.exp x := by
  simp [itoSpaceSecondDerivative, Real.deriv_exp]

/-- The finite-variation compensation `-(1/2) d⟪M⟫` cancels the second-order
Itô correction of the exponential. -/
theorem doleansDade_drift_correction_cancel (x q : ℝ) :
    Real.exp x * (-(1 / 2 : ℝ) * q) +
        (1 / 2 : ℝ) * Real.exp x * q = 0 := by
  ring

/-- The full quadratic term in Taylor's formula for the compensated
logarithm converges to the bracket Stieltjes integral.  The proof combines
finite-variation removal with the martingale-only weighted-bracket theorem.
-/
theorem
    generalItoQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoQuadraticApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (stieltjesBracketIntegral
        (fun s omega ↦ (1 / 2 : ℝ) *
          doleansDadeExponential M bracket s omega)
        bracket t) := by
  let A : ℝ≥0 → W → ℝ :=
    fun s omega ↦ (-1 / 2 : ℝ) * bracket s omega
  have hsecond : Continuous (fun p : ℝ × ℝ ↦
      itoSpaceSecondDerivative (fun _ x ↦ Real.exp x) p.1 p.2) := by
    simp only [itoSpaceSecondDerivative_exp_state]
    fun_prop
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := fun s ↦
    aestronglyMeasurable_const.mul (hbracketMeas s)
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hAqv : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n ↦ quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0) := by
    filter_upwards [hbracketPath] with omega homega
    have hzero :=
      tendsto_quadraticVariationApprox_zero_of_continuous_monotone
        bracket t omega homega.1 homega.2
    simpa only [A, quadraticVariationApprox_const_mul, mul_zero] using
      hzero.const_mul ((-1 / 2 : ℝ) ^ 2)
  have hlogCont : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ doleansDadeLog M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact hMomega.sub (continuous_const.mul hbracketOmega.1)
  have hself : IsContinuousProcessModification
      (doleansDadeLog M bracket) (doleansDadeLog M bracket) P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hlogCont⟩
  have herror :=
    generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
      (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket)
      A M hlogMeas hAmeas hMmeas t (bracket t) hAqv
      (hbefore.toProcess t)
      (hself.uniformPartition_secondDerivative_bounded
        (fun _ x ↦ Real.exp x) hsecond t)
  have hsumEq : (fun s omega ↦ A s omega + M s omega) =
      doleansDadeLog M bracket := by
    funext s omega
    simp only [A, doleansDadeLog]
    ring
  rw [hsumEq] at herror
  have herrorActual : TendstoInMeasure P
      (fun n omega ↦
        generalItoQuadraticApprox (fun _ x ↦ Real.exp x)
            (doleansDadeLog M bracket) t (n + 1) omega -
          generalItoMixedQuadraticApprox (fun _ x ↦ Real.exp x)
            (doleansDadeLog M bracket) M t (n + 1) omega)
      Filter.atTop (fun _ ↦ 0) := by
    simpa only [generalItoQuadraticApprox,
      generalItoMixedQuadraticApprox] using herror
  have hmartingale :=
    generalItoMixedQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
      hM hbracket hMcont hbracketPath hbefore t
  have hsum := herrorActual.add_real_noMeas hmartingale
  apply hsum.congr
  · intro n
    filter_upwards with omega
    ring
  · filter_upwards with omega
    ring

/-- The first-order Taylor sum against the compensated logarithm converges
to the exponential endpoint increment minus its bracket correction. -/
theorem generalItoSpace_doleansDadeLog_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoSpaceApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (fun omega ↦
        doleansDadeExponential M bracket t omega -
          doleansDadeExponential M bracket 0 omega -
          stieltjesBracketIntegral
            (fun s omega ↦ (1 / 2 : ℝ) *
              doleansDadeExponential M bracket s omega)
            bracket t omega) := by
  let Q : W → ℝ := stieltjesBracketIntegral
    (fun s omega ↦ (1 / 2 : ℝ) *
      doleansDadeExponential M bracket s omega) bracket t
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hEmeas : ∀ s,
      AEStronglyMeasurable (doleansDadeExponential M bracket s) P :=
    fun s ↦ Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s)
  have hendpoint : AEStronglyMeasurable
      (fun omega ↦ Real.exp (doleansDadeLog M bracket t omega) -
        Real.exp (doleansDadeLog M bracket 0 omega)) P := by
    change AEStronglyMeasurable
      (doleansDadeExponential M bracket t -
        doleansDadeExponential M bracket 0) P
    exact (hEmeas t).sub (hEmeas 0)
  have htimeZero (n : ℕ) (omega : W) :
      generalItoTimeApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t n omega = 0 := by
    unfold generalItoTimeApprox
    simp only [itoTimeDerivative_exp_state, zero_mul, Finset.sum_const_zero]
  have htime : TendstoInMeasure P
      (fun n ↦ generalItoTimeApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_const.congr
        (Filter.Eventually.of_forall fun omega ↦ (htimeZero (n + 1) omega).symm)
    · filter_upwards with omega
      simpa only [htimeZero] using
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0))
  have hquadratic : TendstoInMeasure P
      (fun n ↦ generalItoQuadraticApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1)) Filter.atTop Q := by
    simpa only [Q] using
      generalItoQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
        hM hbracket hMcont hbracketPath hbefore t
  have hstate :=
    doleansDadeLog_exp_stateTaylorRemainder_tendstoInMeasure
      hM hbracket hMcont hbracketPath hbefore t
  have hremainderEq (n : ℕ) (omega : W) :
      generalItoRemainderApprox (fun _ x ↦ Real.exp x)
          (doleansDadeLog M bracket) t n omega =
        itoStateTaylorRemainderApprox Real.exp
          (doleansDadeLog M bracket) t n omega := by
    unfold generalItoRemainderApprox itoStateTaylorRemainderApprox
    apply Finset.sum_congr rfl
    intro i _hi
    unfold generalItoRemainderIncrement itoStateTaylorRemainder
    simp only [itoTimeDerivative_exp_state, itoSpaceDerivative_exp_state,
      itoSpaceSecondDerivative_exp_state, Real.deriv_exp, zero_mul, sub_zero]
  have hremainder : TendstoInMeasure P
      (fun n ↦ generalItoRemainderApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
    apply hstate.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega ↦
      (hremainderEq (n + 1) omega).symm
  apply (generalIto_formula_ae_iff_space_limit
    (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t
    (fun _ ↦ 0)
    (fun omega ↦
      doleansDadeExponential M bracket t omega -
        doleansDadeExponential M bracket 0 omega - Q omega)
    Q hendpoint htime hquadratic hremainder).2
  filter_upwards with omega
  simp only [doleansDadeExponential]
  ring

/-- The genuine uncapped Doléans left sums converge in probability to the
stochastic-exponential endpoint increment.  The bracket Stieltjes term from
Taylor's formula cancels exactly with the finite-variation part of the
compensated logarithm. -/
theorem doleansDadeLeftSumProcess_terminal_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket t n t)
      Filter.atTop
      (fun omega ↦ doleansDadeExponential M bracket t omega -
        doleansDadeExponential M bracket 0 omega) := by
  let H : ℝ≥0 → W → ℝ := fun s omega ↦
    (1 / 2 : ℝ) * doleansDadeExponential M bracket s omega
  let Q : W → ℝ := stieltjesBracketIntegral H bracket t
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hHmeas : ∀ s, AEStronglyMeasurable (H s) P := by
    intro s
    exact aestronglyMeasurable_const.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s))
  have hHcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ H s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact continuous_const.mul
      (continuous_doleansDadeExponential M bracket omega
        hMomega hbracketOmega.1)
  have hspace : TendstoInMeasure P
      (fun n ↦ generalItoSpaceApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (fun omega ↦
        doleansDadeExponential M bracket t omega -
          doleansDadeExponential M bracket 0 omega - Q omega) := by
    simpa only [Q, H] using
      generalItoSpace_doleansDadeLog_tendstoInMeasure
        hM hbracket hMcont hbracketPath hbefore t
  have hbracketSum : TendstoInMeasure P
      (fun n ↦ bracketWeightedLeftSum H bracket t (n + 1))
      Filter.atTop Q := by
    exact bracketWeightedLeftSum_tendstoInMeasure H bracket
      hHmeas hbracketMeas hHcont hbracketPath t
  have hsum := hspace.add_real_noMeas hbracketSum
  apply hsum.congr
  · intro n
    filter_upwards with omega
    rw [doleansDadeLeftSumProcess_terminal]
    unfold generalItoSpaceApprox bracketWeightedLeftSum H
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [itoSpaceDerivative_exp_state, doleansDadeExponential,
      doleansDadeLog]
    ring
  · filter_upwards with omega
    ring

/-- With the standard zero initial conditions, the terminal left sums
converge directly to the canonical integral candidate `ℰ(M) - 1`. -/
theorem
    doleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket t n t)
      Filter.atTop (doleansDadeIntegralCandidate M bracket t) := by
  have hterminal := doleansDadeLeftSumProcess_terminal_tendstoInMeasure
    hM hbracket hMcont hbracketPath hbefore t
  apply hterminal.congr_right
  filter_upwards [hMzero, hbracketZero]
    with omega hMzeroOmega hbracketZeroOmega
  rw [doleansDadeExponential_zero M bracket omega
    hMzeroOmega hbracketZeroOmega]
  rfl

/-- The bounded diagonal approximation has the same terminal
convergence-in-probability limit as the uncapped Doléans sums. -/
theorem
    cappedDoleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket t n t)
      Filter.atTop (doleansDadeIntegralCandidate M bracket t) := by
  apply tendstoInMeasure_cappedDoleansDadeLeftSumProcess_of_uncapped
    hM hbracket hMcont (hbracketPath.mono fun _ h ↦ h.1) t t
  exact
    doleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
      hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero t

/-- On one fixed horizon, the coherent uncapped left-sum processes converge
at every observation time to the canonical integral candidate stopped at
that horizon. -/
theorem doleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket T n t)
      Filter.atTop
      (doleansDadeIntegralCandidate M bracket (min T t)) := by
  let Ms : ℝ≥0 → W → ℝ := fun s omega ↦ M (min s t) omega
  let As : ℝ≥0 → W → ℝ :=
    fun s omega ↦ bracket (min s t) omega
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hMsadapt : StronglyAdapted 𝒱 Ms := by
    intro s
    exact (hM (min s t)).mono (𝒱.mono (min_le_left s t))
  have hAsadapt : StronglyAdapted 𝒱 As := by
    intro s
    exact (hbracket (min s t)).mono (𝒱.mono (min_le_left s t))
  have hMscont : ∀ᵐ omega ∂P, Continuous (fun s ↦ Ms s omega) := by
    filter_upwards [hMcont] with omega homega
    exact homega.comp (continuous_id.min continuous_const)
  have hAspath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ As s omega) ∧
        Monotone (fun s ↦ As s omega) := by
    filter_upwards [hbracketPath] with omega homega
    refine ⟨homega.1.comp (continuous_id.min continuous_const), ?_⟩
    exact homega.2.comp fun _ _ hab ↦ min_le_min hab le_rfl
  have hbeforeStop : HasQuadraticVariationBeforeStopProcessInProbability
      Ms As P := by
    simpa only [Ms, As] using hbefore.stop hMmeas hMcont t
  have hMsZero : Ms 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hMzero] with omega homega
    change M (min 0 t) omega = 0
    have hz : min (0 : ℝ≥0) t = 0 :=
      min_eq_left (show (0 : ℝ≥0) ≤ t by exact bot_le)
    rw [hz]
    exact homega
  have hAsZero : As 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hbracketZero] with omega homega
    change bracket (min 0 t) omega = 0
    have hz : min (0 : ℝ≥0) t = 0 :=
      min_eq_left (show (0 : ℝ≥0) ≤ t by exact bot_le)
    rw [hz]
    exact homega
  have hterminal :=
    doleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
      hMsadapt hAsadapt hMscont hAspath hbeforeStop hMsZero hAsZero T
  have hsource := hterminal.congr_left fun n ↦
    Filter.Eventually.of_forall fun omega ↦ by
      exact (doleansDadeLeftSumProcess_eq_stopped_terminal
        M bracket T n t omega).symm
  apply hsource.congr_right
  exact Filter.Eventually.of_forall fun omega ↦ rfl

/-- The bounded diagonal Doléans approximations inherit the coherent
common-horizon convergence of the uncapped left sums. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t)
      Filter.atTop
      (doleansDadeIntegralCandidate M bracket (min T t)) := by
  apply tendstoInMeasure_cappedDoleansDadeLeftSumProcess_of_uncapped
    hM hbracket hMcont (hbracketPath.mono fun _ h ↦ h.1) T t
  exact doleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero T t

/-- The coherent capped Doléans approximations may be evaluated at every
fixed paired dyadic exit.  This is the finite-range random-stopping form of
the general Itô convergence theorem. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedDyadicExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R : ℝ≥0) (m : ℕ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (pairedDyadicHittingTimeNNReal M
          (doleansDadeExponential M bracket) H K R m) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (pairedDyadicHittingTimeNNReal M
          (doleansDadeExponential M bracket) H K R m) t) := by
  apply tendstoInMeasure_localizingStoppedProcess_of_finiteRange
    ((Finset.range (2 ^ m + 1)).image
      (uniformPartitionTime H (2 ^ m)))
  · exact pairedDyadicHittingTimeNNReal_mem_rangeFinset M
      (doleansDadeExponential M bracket) H K R m
  · intro s
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
        hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero T s

/-- Uniform control of replacing a positive paired continuous exit by its
dyadic approximants upgrades the finite-range Itô limits to convergence at
the continuous exit.  All finite-grid and candidate-limit terms are
discharged internally; `happrox` is precisely the remaining uniform
martingale-modulus estimate. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_dyadic_error
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ omega,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega))
    (U : ℕ → W → ℝ)
    (hU : TendstoInMeasure P U Filter.atTop (fun _ => 0))
    (happrox : ∀ m n t omega,
      ‖localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (fun omega => min (continuousExitTime M H K omega)
            (continuousExitTime (doleansDadeExponential M bracket) H R omega))
          t omega -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (pairedDyadicHittingTimeNNReal M
            (doleansDadeExponential M bracket) H K R m) t omega‖ ≤
        ‖U m omega‖) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have hYadapt : StronglyAdapted 𝒱 Y := by
    intro s
    exact (stronglyAdapted_doleansDadeIntegralCandidate
      hM hbracket (min T s)).mono (𝒱.mono (min_le_right T s))
  have hYcont : ∀ omega, Continuous (fun s => Y s omega) := by
    intro omega
    exact (continuous_doleansDadeIntegralCandidate M bracket omega
      (hMcont omega) (hbracketPath omega).1).comp
        (continuous_const.min continuous_id)
  apply tendstoInMeasure_of_uniform_approximation
    (fm := fun m n => localizingStoppedProcess
      (cappedDoleansDadeLeftSumProcess M bracket T n)
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
    (gm := fun m => localizingStoppedProcess Y
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
    (U := U)
  · intro m n omega
    exact happrox m n t omega
  · exact hU
  · intro m
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedDyadicExit
        hM hbracket (Filter.Eventually.of_forall hMcont)
        (Filter.Eventually.of_forall hbracketPath) hbefore hMzero
        hbracketZero T H K R m t
  · exact tendstoInMeasure_localizingStoppedProcess_pairedDyadic_of_pos
      hYadapt hYcont hM hEadapt H K R hpos t

/-- Uniform-in-grid convergence in probability for replacing a paired
continuous exit by its dyadic approximants is sufficient for convergence at
the continuous exit.  This is the probability-estimate form of
`cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_dyadic_error`;
it avoids the stronger requirement of a pointwise error majorant. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ omega,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R t : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega))
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ N, ∀ m, N ≤ m → ∀ n,
          P {omega | epsilon ≤
            ‖localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (fun omega => min (continuousExitTime M H K omega)
                  (continuousExitTime
                    (doleansDadeExponential M bracket) H R omega))
                t omega -
              localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (pairedDyadicHittingTimeNNReal M
                  (doleansDadeExponential M bracket) H K R m)
                t omega‖} ≤ delta) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have hYadapt : StronglyAdapted 𝒱 Y := by
    intro s
    exact (stronglyAdapted_doleansDadeIntegralCandidate
      hM hbracket (min T s)).mono (𝒱.mono (min_le_right T s))
  have hYcont : ∀ omega, Continuous (fun s => Y s omega) := by
    intro omega
    exact (continuous_doleansDadeIntegralCandidate M bracket omega
      (hMcont omega) (hbracketPath omega).1).comp
        (continuous_const.min continuous_id)
  apply tendstoInMeasure_of_uniform_approximation_in_measure
    (fm := fun m n => localizingStoppedProcess
      (cappedDoleansDadeLeftSumProcess M bracket T n)
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
    (gm := fun m => localizingStoppedProcess Y
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
  · exact happrox
  · intro m
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedDyadicExit
        hM hbracket (Filter.Eventually.of_forall hMcont)
        (Filter.Eventually.of_forall hbracketPath) hbefore hMzero
        hbracketZero T H K R m t
  · exact tendstoInMeasure_localizingStoppedProcess_pairedDyadic_of_pos
      hYadapt hYcont hM hEadapt H K R hpos t

/-- A uniform `L²` modulus for dyadic exit replacement supplies the
uniform convergence-in-probability hypothesis at a paired continuous exit.
Measurability of the error is derived from adaptedness, path continuity, and
the stopping-time constructions. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_eLpNorm_error
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ omega,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R t : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega))
    (V : ℕ → ℝ≥0∞) (hV : Tendsto V Filter.atTop (nhds 0))
    (hbound : ∀ m n,
      eLpNorm
        (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (fun omega => min (continuousExitTime M H K omega)
              (continuousExitTime
                (doleansDadeExponential M bracket) H R omega)) t -
          localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (pairedDyadicHittingTimeNNReal M
              (doleansDadeExponential M bracket) H K R m) t)
        2 P ≤ V m) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let sigma : ℕ → W → WithTop ℝ≥0 :=
    pairedDyadicHittingTimeNNReal M E H K R
  let X : ℕ → ℝ≥0 → W → ℝ := fun n =>
    cappedDoleansDadeLeftSumProcess M bracket T n
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have htau : IsStoppingTime 𝒱 tau :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted hM H K).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hEadapt H R)
  have hsigma (m : ℕ) : IsStoppingTime 𝒱 (sigma m) :=
    isStoppingTime_pairedDyadicHittingTimeNNReal hM hEadapt H K R m
  have hXadapt (n : ℕ) : StronglyAdapted 𝒱 (X n) := by
    exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
      (stronglyAdapted_cappedDoleansDadeExponential hM hbracket (n + 1))
      T (n + 1)
  have hXcont (n : ℕ) : ∀ omega, Continuous (fun s => X n s omega) :=
    fun omega => continuous_uniformAdaptedMartingaleLeftSumProcess hMcont
      T (n + 1) omega
  have hmeas : ∀ m n, AEStronglyMeasurable
      (localizingStoppedProcess (X n) tau t -
        localizingStoppedProcess (X n) (sigma m) t) P := by
    intro m n
    exact (((stronglyAdapted_localizingStoppedProcess
      (hXadapt n) (hXcont n) htau t).mono
        (𝒱.le t)).aestronglyMeasurable).sub
      (((stronglyAdapted_localizingStoppedProcess
        (hXadapt n) (hXcont n) (hsigma m) t).mono
          (𝒱.le t)).aestronglyMeasurable)
  apply
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
      hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero
        T H K R t hpos
  exact uniform_approximation_in_measure_of_eLpNorm hmeas hV hbound

/-- For a continuous martingale, nested continuous exits discharge the
uniform dyadic-stop approximation estimate.  The inner-to-outer capped error
vanishes in `L²`, while the event on which removing the outer cap changes the
stop has probability tending to zero. -/
theorem cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ => 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ => 0)
    (T H K R t : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H (K + 1) omega)
      (continuousExitTime E H (R + 1) omega)
  let sigma : ℕ → W → WithTop ℝ≥0 :=
    pairedDyadicHittingTimeNNReal M E H K R
  let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
    min (sigma m omega) (theta omega)
  let X : ℕ → ℝ≥0 → W → ℝ := fun n =>
    cappedDoleansDadeLeftSumProcess M bracket T n
  let B : ℕ → ℝ≥0∞ := fun m => (R + 1) * eLpNorm
    ((localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) T -
      (localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) 0) 2 P
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have htau : IsStoppingTime 𝒱 tau :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted
      hM.stronglyAdapted H K).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hEadapt H R)
  have htheta : IsStoppingTime 𝒱 theta :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted
      hM.stronglyAdapted H (K + 1)).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted
        hEadapt H (R + 1))
  have hsigma (m : ℕ) : IsStoppingTime 𝒱 (sigma m) :=
    isStoppingTime_pairedDyadicHittingTimeNNReal
      hM.stronglyAdapted hEadapt H K R m
  have hrho (m : ℕ) : IsStoppingTime 𝒱 (rho m) :=
    (hsigma m).min htheta
  have hXadapt (n : ℕ) : StronglyAdapted 𝒱 (X n) :=
    stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess
      hM.stronglyAdapted
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) T (n + 1)
  have hXcont (n : ℕ) : ∀ omega, Continuous (fun s => X n s omega) :=
    fun omega => continuous_uniformAdaptedMartingaleLeftSumProcess
      hMcont T (n + 1) omega
  have hmeas : ∀ m n, AEStronglyMeasurable
      (localizingStoppedProcess (X n) tau t -
        localizingStoppedProcess (X n) (rho m) t) P := by
    intro m n
    exact (((stronglyAdapted_localizingStoppedProcess
      (hXadapt n) (hXcont n) htau t).mono
        (𝒱.le t)).aestronglyMeasurable).sub
      (((stronglyAdapted_localizingStoppedProcess
        (hXadapt n) (hXcont n) (hrho m) t).mono
          (𝒱.le t)).aestronglyMeasurable)
  have hBtend : Tendsto B Filter.atTop (nhds 0) := by
    dsimp only [B, tau, theta, rho, sigma, E]
    exact tendsto_outerCappedDyadic_doleans_error_bound
      (P := P) hM.stronglyAdapted hbracket hMcont
        (fun omega => (hbracketPath omega).1)
        H K R (K + 1) (R + 1) T
        (le_add_right le_rfl) (le_add_right le_rfl) hpos
  have hbound : ∀ m n,
      eLpNorm
        (localizingStoppedProcess (X n) tau t -
          localizingStoppedProcess (X n) (rho m) t) 2 P ≤ B m := by
    intro m n
    dsimp only [X, tau, rho, sigma, theta, B, E]
    exact eLpNorm_pairedExit_sub_outerCappedDyadic_cappedDoleans_le
      hM hMcont hbracket (fun omega => (hbracketPath omega).1)
        T H K R (K + 1) (R + 1)
        (le_add_right le_rfl) (le_add_right le_rfl) m n t
  have hcapApprox := uniform_approximation_in_measure_of_eLpNorm
    hmeas hBtend hbound
  have hexception := tendsto_measure_outerContinuousExit_lt_pairedDyadic
    (P := P) hM.stronglyAdapted hEadapt hMcont hEcont
      H K R (K + 1) (R + 1) hpos (lt_add_one K) (lt_add_one R)
  apply
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
      hM.stronglyAdapted hbracket hMcont hbracketPath hbefore hMzero
        hbracketZero T H K R t hpos
  intro epsilon hepsilon delta hdelta
  have hdeltaHalf : 0 < delta / 2 :=
    ENNReal.div_pos hdelta.ne' ENNReal.ofNat_ne_top
  obtain ⟨Ncap, hNcap⟩ :=
    hcapApprox epsilon hepsilon (delta / 2) hdeltaHalf
  rw [ENNReal.tendsto_atTop_zero] at hexception
  obtain ⟨Nexception, hNexception⟩ :=
    hexception (delta / 2) hdeltaHalf
  refine ⟨max Ncap Nexception, fun m hm n => ?_⟩
  have hcap := hNcap m (le_trans (le_max_left _ _) hm) n
  have hexc := hNexception m (le_trans (le_max_right _ _) hm)
  calc
    P {omega | epsilon ≤
        ‖localizingStoppedProcess (X n) tau t omega -
          localizingStoppedProcess (X n) (sigma m) t omega‖} ≤
      P ({omega | epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖} ∪
        {omega | theta omega < sigma m omega}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_contra hnot
      push Not at hnot
      have hstop : rho m omega = sigma m omega := by
        dsimp only [rho]
        rw [min_eq_left hnot.2]
      have hlocal := localizingStoppedProcess_congr_stop_at
        (X n) (rho m) (sigma m) t omega hstop
      have hlarge : epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖ := by
        rw [hlocal]
        exact homega
      exact (not_lt_of_ge hlarge) hnot.1
    _ ≤ P {omega | epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖} +
        P {omega | theta omega < sigma m omega} := measure_union_le _ _
    _ ≤ delta / 2 + delta / 2 := add_le_add hcap hexc
    _ = delta := ENNReal.add_halves delta

/-- Fixed-horizon Doléans theorem reduced to a uniform dyadic-stop
approximation estimate.  Finite-range stopping, general Itô convergence,
continuous-exit localization, martingality, and uniform integrability are all
discharged internally. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_dyadic_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ => 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ => 0)
    (T : ℝ≥0)
    (hpos : ∀ (k : ℕ) (omega : W), (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M (T + 1) ((k : ℝ≥0) + 1 + 1) omega)
        (continuousExitTime (doleansDadeExponential M bracket) (T + 1)
          ((k : ℝ≥0) + 1 + 1) omega))
    (U : ℕ → ℕ → W → ℝ)
    (hU : ∀ k, TendstoInMeasure P (U k) Filter.atTop (fun _ => 0))
    (happrox : ∀ (k m n : ℕ) (t : ℝ≥0) (omega : W),
      ‖localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (fun omega => min
            (continuousExitTime M (T + 1) ((k : ℝ≥0) + 1 + 1) omega)
            (continuousExitTime (doleansDadeExponential M bracket) (T + 1)
              ((k : ℝ≥0) + 1 + 1) omega)) t omega -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (pairedDyadicHittingTimeNNReal M
            (doleansDadeExponential M bracket) (T + 1)
              ((k : ℝ≥0) + 1 + 1) ((k : ℝ≥0) + 1 + 1) m)
          t omega‖ ≤ ‖U k m omega‖) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hTH : T ≤ H := by
    dsimp only [H]
    exact le_add_right le_rfl
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_shiftedPairedExit
      hM hMcont hbracket (fun omega => (hbracketPath omega).1) T
  intro k t
  let R : ℝ≥0 := (k : ℝ≥0) + 1 + 1
  have hraw :=
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_dyadic_error
      hM.stronglyAdapted hbracket hMcont hbracketPath hbefore hMzero
      hbracketZero T H R R (hpos k) (U k) (hU k)
        (fun m n t omega => happrox k m n t omega) t
  have hXconst (n : ℕ) : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s
        (hTH.trans hHs)).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  have hYconst : ∀ s, H ≤ s → Y s = Y H := by
    intro s hHs
    funext omega
    change doleansDadeIntegralCandidate M bracket (min T s) omega =
      doleansDadeIntegralCandidate M bracket (min T H) omega
    rw [min_eq_left (hTH.trans hHs), min_eq_left hTH]
  have heqX (n : ℕ) :=
    localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
      (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k
        hHpos (hXconst n)
  have heqY := localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
    Y M E H k hHpos hYconst
  apply hraw.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun (heqX n).symm t) omega
  · exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heqY.symm t) omega

/-- Normalized fixed-horizon form of the conditional Doléans theorem.
Pointwise normalization at time zero and path continuity automatically make
all shifted paired exit times positive, so the only remaining input is the
uniform dyadic-stop approximation estimate. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_normalized_dyadic_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (T : ℝ≥0)
    (U : ℕ → ℕ → W → ℝ)
    (hU : ∀ k, TendstoInMeasure P (U k) Filter.atTop (fun _ => 0))
    (happrox : ∀ (k m n : ℕ) (t : ℝ≥0) (omega : W),
      ‖localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (fun omega => min
            (continuousExitTime M (T + 1) ((k : ℝ≥0) + 1 + 1) omega)
            (continuousExitTime (doleansDadeExponential M bracket) (T + 1)
              ((k : ℝ≥0) + 1 + 1) omega)) t omega -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (pairedDyadicHittingTimeNNReal M
            (doleansDadeExponential M bracket) (T + 1)
              ((k : ℝ≥0) + 1 + 1) ((k : ℝ≥0) + 1 + 1) m)
          t omega‖ ≤ ‖U k m omega‖) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_dyadic_error
      hM hMcont hbracket hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero) T (U := U)
  · intro k omega
    apply min_continuousExitTime_pos_of_initial_lt
    · exact hMcont omega
    · exact continuous_doleansDadeExponential M bracket omega
        (hMcont omega) (hbracketPath omega).1
    · positivity
    · rw [hMzero omega]
      norm_num
      positivity
    · rw [doleansDadeExponential_zero M bracket omega
        (hMzero omega) (hbracketZero omega)]
      norm_num
      positivity
  · exact hU
  · exact happrox

/-- Fixed-horizon Doléans theorem under the natural uniform-in-grid
convergence-in-probability estimate for dyadic exit approximation. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_uniform_dyadic_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ => 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ => 0)
    (T : ℝ≥0)
    (hpos : ∀ (k : ℕ) (omega : W), (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M (T + 1) ((k : ℝ≥0) + 1 + 1) omega)
        (continuousExitTime (doleansDadeExponential M bracket) (T + 1)
          ((k : ℝ≥0) + 1 + 1) omega))
    (happrox : ∀ (k : ℕ) (t : ℝ≥0) (epsilon : ℝ), 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ N, ∀ m, N ≤ m → ∀ n,
          P {omega | epsilon ≤
            ‖localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (fun omega => min
                  (continuousExitTime M (T + 1)
                    ((k : ℝ≥0) + 1 + 1) omega)
                  (continuousExitTime (doleansDadeExponential M bracket)
                    (T + 1) ((k : ℝ≥0) + 1 + 1) omega)) t omega -
              localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (pairedDyadicHittingTimeNNReal M
                  (doleansDadeExponential M bracket) (T + 1)
                    ((k : ℝ≥0) + 1 + 1) ((k : ℝ≥0) + 1 + 1) m)
                t omega‖} ≤ delta) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hTH : T ≤ H := by
    dsimp only [H]
    exact le_add_right le_rfl
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_shiftedPairedExit
      hM hMcont hbracket (fun omega => (hbracketPath omega).1) T
  intro k t
  let R : ℝ≥0 := (k : ℝ≥0) + 1 + 1
  have hraw :=
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
      hM.stronglyAdapted hbracket hMcont hbracketPath hbefore hMzero
      hbracketZero T H R R t (hpos k) (happrox k t)
  have hXconst (n : ℕ) : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s
        (hTH.trans hHs)).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  have hYconst : ∀ s, H ≤ s → Y s = Y H := by
    intro s hHs
    funext omega
    change doleansDadeIntegralCandidate M bracket (min T s) omega =
      doleansDadeIntegralCandidate M bracket (min T H) omega
    rw [min_eq_left (hTH.trans hHs), min_eq_left hTH]
  have heqX (n : ℕ) :=
    localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
      (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k
        hHpos (hXconst n)
  have heqY := localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
    Y M E H k hHpos hYconst
  apply hraw.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun (heqX n).symm t) omega
  · exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heqY.symm t) omega

/-- In the normalized setting, the uniform convergence-in-probability
estimate is the sole remaining hypothesis in the fixed-horizon theorem. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_normalized_uniform_dyadic_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (T : ℝ≥0)
    (happrox : ∀ (k : ℕ) (t : ℝ≥0) (epsilon : ℝ), 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ N, ∀ m, N ≤ m → ∀ n,
          P {omega | epsilon ≤
            ‖localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (fun omega => min
                  (continuousExitTime M (T + 1)
                    ((k : ℝ≥0) + 1 + 1) omega)
                  (continuousExitTime (doleansDadeExponential M bracket)
                    (T + 1) ((k : ℝ≥0) + 1 + 1) omega)) t omega -
              localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (pairedDyadicHittingTimeNNReal M
                  (doleansDadeExponential M bracket) (T + 1)
                    ((k : ℝ≥0) + 1 + 1) ((k : ℝ≥0) + 1 + 1) m)
                t omega‖} ≤ delta) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_uniform_dyadic_error
      hM hMcont hbracket hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero) T
  · intro k omega
    apply min_continuousExitTime_pos_of_initial_lt
    · exact hMcont omega
    · exact continuous_doleansDadeExponential M bracket omega
        (hMcont omega) (hbracketPath omega).1
    · positivity
    · rw [hMzero omega]
      norm_num
      positivity
    · rw [doleansDadeExponential_zero M bracket omega
        (hMzero omega) (hbracketZero omega)]
      norm_num
      positivity
  · exact happrox

/-- Normalized fixed-horizon Doléans theorem reduced to a grid-uniform
`L²` modulus for replacing each paired continuous exit by its dyadic
approximants.  Chebyshev--Markov and all subsequent convergence, UI, and
localization steps are discharged internally. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_normalized_L2_exit_error
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (T : ℝ≥0)
    (V : ℕ → ℝ≥0 → ℕ → ℝ≥0∞)
    (hV : ∀ k t, Tendsto (V k t) Filter.atTop (nhds 0))
    (hbound : ∀ (k : ℕ) (t : ℝ≥0) (m n : ℕ),
      eLpNorm
        (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (fun omega => min
              (continuousExitTime M (T + 1)
                ((k : ℝ≥0) + 1 + 1) omega)
              (continuousExitTime (doleansDadeExponential M bracket)
                (T + 1) ((k : ℝ≥0) + 1 + 1) omega)) t -
          localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (pairedDyadicHittingTimeNNReal M
              (doleansDadeExponential M bracket) (T + 1)
                ((k : ℝ≥0) + 1 + 1) ((k : ℝ≥0) + 1 + 1) m)
            t)
        2 P ≤ V k t m) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hTH : T ≤ H := by
    dsimp only [H]
    exact le_add_right le_rfl
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_shiftedPairedExit
      hM hMcont hbracket (fun omega => (hbracketPath omega).1) T
  intro k t
  let R : ℝ≥0 := (k : ℝ≥0) + 1 + 1
  have hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H R omega)
        (continuousExitTime E H R omega) := by
    intro omega
    apply min_continuousExitTime_pos_of_initial_lt
    · exact hMcont omega
    · exact continuous_doleansDadeExponential M bracket omega
        (hMcont omega) (hbracketPath omega).1
    · dsimp only [H]
      positivity
    · rw [hMzero omega]
      dsimp only [R]
      norm_num
      positivity
    · dsimp only [E]
      rw [doleansDadeExponential_zero M bracket omega
        (hMzero omega) (hbracketZero omega)]
      dsimp only [R]
      norm_num
      positivity
  have hraw :=
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_eLpNorm_error
      hM.stronglyAdapted hbracket hMcont hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero)
        T H R R t hpos (V k t) (hV k t) (hbound k t)
  have hXconst (n : ℕ) : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s
        (hTH.trans hHs)).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  have hYconst : ∀ s, H ≤ s → Y s = Y H := by
    intro s hHs
    funext omega
    change doleansDadeIntegralCandidate M bracket (min T s) omega =
      doleansDadeIntegralCandidate M bracket (min T H) omega
    rw [min_eq_left (hTH.trans hHs), min_eq_left hTH]
  have heqX (n : ℕ) :=
    localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
      (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k
        hHpos (hXconst n)
  have heqY := localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
    Y M E H k hHpos hYconst
  apply hraw.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun (heqX n).symm t) omega
  · exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heqY.symm t) omega

/-- The normalized stochastic exponential of a continuous martingale is a
continuous local martingale on every deterministic horizon.  The proof uses
the general Itô approximation together with nested continuous-exit
localization. -/
theorem isContinuousLocalMartingale_doleansDadeExponential_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (T : ℝ≥0) :
    IsContinuousLocalMartingale
      (fun s omega => doleansDadeExponential M bracket (min T s) omega)
      𝒱 P := by
  let E := doleansDadeExponential M bracket
  let H : ℝ≥0 := T + 1
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hHpos : 0 < H := by
    dsimp only [H]
    positivity
  have hTH : T ≤ H := by
    dsimp only [H]
    exact le_add_right le_rfl
  apply
    isContinuousLocalMartingale_doleansDadeExponential_stop_of_shiftedPairedExit
      hM hMcont hbracket (fun omega => (hbracketPath omega).1) T
  intro k t
  let R : ℝ≥0 := (k : ℝ≥0) + 1 + 1
  have hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H R omega)
        (continuousExitTime E H R omega) := by
    intro omega
    apply min_continuousExitTime_pos_of_initial_lt
    · exact hMcont omega
    · exact continuous_doleansDadeExponential M bracket omega
        (hMcont omega) (hbracketPath omega).1
    · dsimp only [H]
      positivity
    · rw [hMzero omega]
      dsimp only [R]
      norm_num
      positivity
    · dsimp only [E]
      rw [doleansDadeExponential_zero M bracket omega
        (hMzero omega) (hbracketZero omega)]
      dsimp only [R]
      norm_num
      positivity
  have hraw :=
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit
      hM hMcont hbracket hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero)
        T H R R t hpos
  have hXconst (n : ℕ) : ∀ s, H ≤ s →
      cappedDoleansDadeLeftSumProcess M bracket T n s =
        cappedDoleansDadeLeftSumProcess M bracket T n H := by
    intro s hHs
    unfold cappedDoleansDadeLeftSumProcess
    exact (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
      M (cappedDoleansDadeExponential M bracket (n + 1)) T n s
        (hTH.trans hHs)).trans
      (uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n H hTH).symm
  have hYconst : ∀ s, H ≤ s → Y s = Y H := by
    intro s hHs
    funext omega
    change doleansDadeIntegralCandidate M bracket (min T s) omega =
      doleansDadeIntegralCandidate M bracket (min T H) omega
    rw [min_eq_left (hTH.trans hHs), min_eq_left hTH]
  have heqX (n : ℕ) :=
    localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
      (cappedDoleansDadeLeftSumProcess M bracket T n) M E H k
        hHpos (hXconst n)
  have heqY := localizingStoppedProcess_shiftedPairedContinuousExit_eq_min
    Y M E H k hHpos hYconst
  apply hraw.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun (heqX n).symm t) omega
  · exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heqY.symm t) omega

/-- If a positive stopping rule is bounded by `H`, localizing a process
capped at `H` gives the same result as localizing the original process. -/
theorem localizingStoppedProcess_min_horizon_eq_of_le
    {W : Type*} (X : ℝ≥0 → W → ℝ) (H : ℝ≥0)
    (tau : W → WithTop ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega)
    (hle : ∀ omega, tau omega ≤ (H : WithTop ℝ≥0)) :
    localizingStoppedProcess (fun s omega => X (min H s) omega) tau =
      localizingStoppedProcess X tau := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
    hpos omega
  let sTop := min (t : WithTop ℝ≥0) (tau omega)
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X (min H sTop.untopA)) omega =
    {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X sTop.untopA) omega
  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  have hs_ne : sTop ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hscoe : ((sTop.untopA : ℝ≥0) : WithTop ℝ≥0) = sTop := by
    rw [WithTop.untopA_eq_untop hs_ne]
    exact WithTop.coe_untop sTop hs_ne
  have hsH : sTop.untopA ≤ H := by
    apply WithTop.coe_le_coe.mp
    rw [hscoe]
    exact (min_le_right _ _).trans (hle omega)
  change X (min H sTop.untopA) omega = X sTop.untopA omega
  rw [min_eq_right hsH]

/-- At a positive pair of bounded continuous exits, the normalized
Doleans integral candidate is a genuine martingale.  Nested exit estimates
provide convergence of the capped left sums, and their uniform `L²` bound
provides the Vitali closure. -/
theorem martingale_doleansDadeIntegralCandidate_pairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (H K R : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    Martingale
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega))) 𝒱 P := by
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let X : ℕ → ℝ≥0 → W → ℝ := fun n =>
    cappedDoleansDadeLeftSumProcess M bracket H n
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have htau : IsStoppingTime 𝒱 tau :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted
      hM.stronglyAdapted H K).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hEadapt H R)
  have hXmart (n : ℕ) : Martingale (X n) 𝒱 P := by
    dsimp only [X, cappedDoleansDadeLeftSumProcess]
    exact martingale_uniformAdaptedMartingaleLeftSumProcess hM
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) (n + 1)
      (norm_cappedDoleansDadeExponential_le M bracket (n + 1)) H (n + 1)
  have hXcont (n : ℕ) : ∀ omega, Continuous (fun t => X n t omega) :=
    fun omega => continuous_uniformAdaptedMartingaleLeftSumProcess
      hMcont H (n + 1) omega
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable
    (X := fun n => localizingStoppedProcess (X n) tau)
  · intro n
    exact martingale_localizingStoppedProcess_min_continuousExitTime
      (hXmart n) (hXcont n) hM.stronglyAdapted hEadapt H K R
  · exact stronglyAdapted_localizingStoppedProcess
      (stronglyAdapted_doleansDadeIntegralCandidate
        hM.stronglyAdapted hbracket)
      (fun omega => continuous_doleansDadeIntegralCandidate M bracket omega
        (hMcont omega) (hbracketPath omega).1)
      htau
  · intro t
    have hUI :=
      uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply
        hM hMcont hbracket (fun omega => (hbracketPath omega).1)
          H H K H R t
    apply hUI.ae_eq
    intro n
    have heq := localizingStoppedProcess_localizingStoppedProcess (X n)
      (continuousExitTime M H K) (continuousExitTime E H R)
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heq t) omega
  · intro t
    have hraw := cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit
      hM hMcont hbracket hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero)
        H H K R t hpos
    have hle : ∀ omega, tau omega ≤ (H : WithTop ℝ≥0) := by
      intro omega
      exact (min_le_left _ _).trans (continuousExitTime_le M H K omega)
    have heq := localizingStoppedProcess_min_horizon_eq_of_le
      (doleansDadeIntegralCandidate M bracket) H tau hpos hle
    exact hraw.congr (fun n => Filter.EventuallyEq.rfl)
      (Filter.Eventually.of_forall fun omega =>
        congrFun (congrFun heq t) omega)

/-- Localizing a Doléans exponential is the exponential of the two localized
inputs on the event where the stopping rule is positive, and zero elsewhere.
This records exactly the exceptional-set convention in Mathlib's `Locally`
predicate. -/
theorem localizingStoppedProcess_doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess (doleansDadeExponential M bracket) tau =
      fun t => {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (doleansDadeExponential
          (localizingStoppedProcess M tau)
          (localizingStoppedProcess bracket tau) t) := by
  funext t omega
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    simp only [Set.indicator_of_mem hmem]
    unfold doleansDadeExponential doleansDadeLog
    simp only [Set.indicator_of_mem hmem]
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    simp only [Set.indicator_of_notMem hmem]

/-- Localization commutes with multiplication by a fixed event indicator. -/
theorem localizingStoppedProcess_indicator
    {W : Type*} (X : ℝ≥0 → W → ℝ) (A : Set W)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess (fun t => A.indicator (X t)) tau =
      fun t => A.indicator (localizingStoppedProcess X tau t) := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  by_cases hA : omega ∈ A <;>
    by_cases htau : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} <;>
    simp [Set.indicator_apply, hA]

/-- Localizing `1 + X` at an everywhere-positive stopping rule is one plus
the localization of `X`. -/
theorem localizingStoppedProcess_one_add_of_pos
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega) :
    localizingStoppedProcess (fun t omega => 1 + X t omega) tau =
      fun t omega => 1 + localizingStoppedProcess X tau t omega := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
    hpos omega
  let sTop := min (t : WithTop ℝ≥0) (tau omega)
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (fun omega => 1 + X sTop.untopA omega) omega =
    1 + {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X sTop.untopA) omega
  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]

/-- The stochastic exponential itself, rather than only its integral
candidate, is a genuine martingale after a positive pair of bounded exits. -/
theorem martingale_doleansDadeExponential_pairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (H K R : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    Martingale
      (localizingStoppedProcess (doleansDadeExponential M bracket)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega))) 𝒱 P := by
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime (doleansDadeExponential M bracket) H R omega)
  have hI := martingale_doleansDadeIntegralCandidate_pairedContinuousExit
    hM hMcont hbracket hbracketPath hbefore hMzero hbracketZero
      H K R hpos
  have hone : Martingale (fun _ : ℝ≥0 => fun _ : W => (1 : ℝ)) 𝒱 P :=
    martingale_const_fun 𝒱 P stronglyMeasurable_const (integrable_const 1)
  have hadd := hone.add hI
  change Martingale ((fun _ : ℝ≥0 => fun _ : W => (1 : ℝ)) +
    localizingStoppedProcess (doleansDadeIntegralCandidate M bracket) tau) 𝒱 P
      at hadd
  have hadd' : Martingale (fun t omega =>
      1 + localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        tau t omega) 𝒱 P := by
    convert hadd using 1; rfl
  have heq := localizingStoppedProcess_one_add_of_pos
    (doleansDadeIntegralCandidate M bracket) tau hpos
  rw [← heq] at hadd'
  change Martingale (localizingStoppedProcess
    (doleansDadeExponential M bracket) tau) 𝒱 P
  have hEeq : doleansDadeExponential M bracket =
      fun t omega => 1 + doleansDadeIntegralCandidate M bracket t omega := by
    funext t omega
    simp only [doleansDadeIntegralCandidate]
    ring
  rw [hEeq]
  exact hadd'

/-- The normalized stochastic exponential of a continuous genuine
martingale is a continuous local martingale on the whole time axis.  The
localizing sequence simultaneously bounds the integrator and exponential,
with exponentially growing horizons and linearly growing radii. -/
theorem isContinuousLocalMartingale_doleansDadeExponential_of_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  let E := doleansDadeExponential M bracket
  let tau := globalPairedContinuousExitSequence M E
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have htau : IsLocalizingSequence 𝒱 tau P :=
    isLocalizingSequence_globalPairedContinuousExit
      hM.stronglyAdapted hEadapt hMcont hEcont
  have hintegral : IsLocalMartingale
      (doleansDadeIntegralCandidate M bracket) 𝒱 P := by
    refine ⟨tau, htau, fun k => ?_⟩
    let H : ℝ≥0 := 2 ^ k
    let R : ℝ≥0 := (k : ℝ≥0) + 2
    have hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
        min (continuousExitTime M H R omega)
          (continuousExitTime E H R omega) := by
      intro omega
      apply min_continuousExitTime_pos_of_initial_lt
      · exact hMcont omega
      · exact hEcont omega
      · dsimp only [H]
        positivity
      · rw [hMzero omega]
        dsimp only [R]
        norm_num only [abs_zero]
        exact_mod_cast (show 0 < k + 2 by omega)
      · dsimp only [E]
        rw [doleansDadeExponential_zero M bracket omega
          (hMzero omega) (hbracketZero omega)]
        dsimp only [R]
        exact_mod_cast (show 1 < k + 2 by omega)
    have hmart :=
      martingale_doleansDadeIntegralCandidate_pairedContinuousExit
        hM hMcont hbracket hbracketPath hbefore hMzero hbracketZero
          H R R hpos
    change Martingale
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        (fun omega => min
          (continuousExitTime M (2 ^ k) ((k : ℝ≥0) + 2) omega)
          (continuousExitTime (doleansDadeExponential M bracket)
            (2 ^ k) ((k : ℝ≥0) + 2) omega))) 𝒱 P
    simpa only [H, R, E] using hmart
  refine ⟨?_, Filter.Eventually.of_forall hEcont⟩
  have hadd := hintegral.const_add 1
  convert hadd using 1
  funext t omega
  simp only [doleansDadeIntegralCandidate]
  ring

/-- The global martingale theorem stated with the standard deterministic-
stopping quadratic-variation contract. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_martingale_stoppedQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hstopped : HasStoppedQuadraticVariationProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s =>
    ((hM.stronglyAdapted s).mono (𝒱.le s)).aestronglyMeasurable
  exact isContinuousLocalMartingale_doleansDadeExponential_of_martingale
    hM hMcont hbracket hbracketPath
      (hstopped.toBeforeStop hMmeas
        (Filter.Eventually.of_forall hMcont))
      hMzero hbracketZero

/-- The Doléans--Dade theorem from a common martingale/bracket localizing
sequence and the localization-stable quadratic-variation contract used by
the proof.

Along the supplied sequence, each stopped bracket must be the robust
quadratic variation of the corresponding stopped martingale.  The proof puts
a second, bounded paired-exit sequence around each stopped martingale, applies
the genuine-martingale exponential theorem there, and then diagonalizes the
two localization layers. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_common_localizedQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (tau : ℕ → W → WithTop ℝ≥0)
    (htau : IsLocalizingSequence 𝒱 tau P)
    (hMmart : ∀ k, Martingale
      (localizingStoppedProcess M (tau k)) 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (hlocalQV : ∀ k,
      HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  let N : ℕ → ℝ≥0 → W → ℝ := fun k =>
    localizingStoppedProcess M (tau k)
  let Q : ℕ → ℝ≥0 → W → ℝ := fun k =>
    localizingStoppedProcess bracket (tau k)
  let E := doleansDadeExponential M bracket
  let Ek : ℕ → ℝ≥0 → W → ℝ := fun k =>
    doleansDadeExponential (N k) (Q k)
  let sigma : ℕ → ℕ → W → WithTop ℝ≥0 := fun k =>
    globalPairedContinuousExitSequence (N k) (Ek k)
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hNmart (k : ℕ) : Martingale (N k) 𝒱 P := by
    exact hMmart k
  have hNcont (k : ℕ) (omega : W) :
      Continuous (fun t => N k t omega) := by
    exact continuous_localizingStoppedProcess hMcont (tau k) omega
  have hQadapt (k : ℕ) : StronglyAdapted 𝒱 (Q k) := by
    exact stronglyAdapted_localizingStoppedProcess hbracket
      (fun omega => (hbracketPath omega).1) (htau.isStoppingTime k)
  have hQcont (k : ℕ) (omega : W) :
      Continuous (fun t => Q k t omega) := by
    exact continuous_localizingStoppedProcess
      (fun omega => (hbracketPath omega).1) (tau k) omega
  have hQmono (k : ℕ) (omega : W) :
      Monotone (fun t => Q k t omega) := by
    exact monotone_localizingStoppedProcess
      (fun omega => (hbracketPath omega).2) (tau k) omega
  have hNzero (k : ℕ) (omega : W) : N k 0 omega = 0 := by
    simp [N, localizingStoppedProcess, stoppedProcess,
      Set.indicator_apply, hMzero]
  have hQzero (k : ℕ) (omega : W) : Q k 0 omega = 0 := by
    simp [Q, localizingStoppedProcess, stoppedProcess,
      Set.indicator_apply, hbracketZero]
  have hEkadapt (k : ℕ) : StronglyAdapted 𝒱 (Ek k) := by
    exact stronglyAdapted_doleansDadeExponential
      (hNmart k).stronglyAdapted (hQadapt k)
  have hEkcont (k : ℕ) (omega : W) :
      Continuous (fun t => Ek k t omega) := by
    exact continuous_doleansDadeExponential (N k) (Q k) omega
      (hNcont k omega) (hQcont k omega)
  have hsigma (k : ℕ) : IsLocalizingSequence 𝒱 (sigma k) P := by
    exact isLocalizingSequence_globalPairedContinuousExit
      (hNmart k).stronglyAdapted (hEkadapt k) (hNcont k) (hEkcont k)
  have hsigmaBound (k j : ℕ) : ∃ T : ℝ≥0, ∀ omega,
      sigma k j omega ≤ (T : WithTop ℝ≥0) := by
    refine ⟨2 ^ j, fun omega => ?_⟩
    exact (min_le_left _ _).trans
      (continuousExitTime_le (N k) (2 ^ j) (j + 2) omega)
  have hmart (k j : ℕ) : Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess E (tau k)) (sigma k j)) 𝒱 P := by
    let H : ℝ≥0 := 2 ^ j
    let R : ℝ≥0 := (j : ℝ≥0) + 2
    have hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
        min (continuousExitTime (N k) H R omega)
          (continuousExitTime (Ek k) H R omega) := by
      intro omega
      apply min_continuousExitTime_pos_of_initial_lt
      · exact hNcont k omega
      · exact hEkcont k omega
      · dsimp only [H]
        positivity
      · rw [hNzero k omega]
        dsimp only [R]
        norm_num only [abs_zero]
        exact_mod_cast (show 0 < j + 2 by omega)
      · dsimp only [Ek]
        rw [doleansDadeExponential_zero (N k) (Q k) omega
          (hNzero k omega) (hQzero k omega)]
        dsimp only [R]
        exact_mod_cast (show 1 < j + 2 by omega)
    have hinner := martingale_doleansDadeExponential_pairedContinuousExit
      (hNmart k) (hNcont k) (hQadapt k)
      (fun omega => ⟨hQcont k omega, hQmono k omega⟩)
      (hlocalQV k) (hNzero k) (hQzero k) H R R hpos
    have hinner' : Martingale
        (localizingStoppedProcess (Ek k) (sigma k j)) 𝒱 P := by
      change Martingale (localizingStoppedProcess (Ek k)
        (fun omega => min (continuousExitTime (N k) H R omega)
          (continuousExitTime (Ek k) H R omega))) 𝒱 P at hinner
      change Martingale (localizingStoppedProcess (Ek k)
        (fun omega => min (continuousExitTime (N k) (2 ^ j) (j + 2) omega)
          (continuousExitTime (Ek k) (2 ^ j) (j + 2) omega))) 𝒱 P
      simpa only [H, R] using hinner
    let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau k omega}
    have hA : MeasurableSet[𝒱 0] A := by
      change MeasurableSet[𝒱 0]
        {omega | (⊥ : WithTop ℝ≥0) < tau k omega}
      rw [show (⊥ : WithTop ℝ≥0) =
        ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
      exact (htau.isStoppingTime k).measurableSet_gt 0
    have hindicator := StochasticCalculus.Martingale.indicator_zero hinner' hA
    have houter := localizingStoppedProcess_doleansDadeExponential
      M bracket (tau k)
    have hdouble := localizingStoppedProcess_indicator
      (Ek k) A (sigma k j)
    rw [houter, hdouble]
    exact hindicator
  have hlocal : IsLocalMartingale E 𝒱 P :=
    isLocalMartingale_of_bounded_double_localization hEcont tau htau
      sigma hsigma hsigmaBound hmart
  exact ⟨hlocal, Filter.Eventually.of_forall hEcont⟩

/-- The proof-independent local-bracket formulation of the Doléans--Dade
theorem.  A pathwise-continuous process with an adapted continuous monotone
local quadratic variation has a continuous-local-martingale stochastic
exponential. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability
      M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  obtain ⟨tau, htau, hMmart, hQV⟩ := hlocalQV
  exact
    isContinuousLocalMartingale_doleansDadeExponential_of_common_localizedQV
      tau htau hMmart hMcont hbracket hbracketPath hMzero hbracketZero hQV

/-- Every deterministic scaling of a process carrying the robust local
quadratic-variation contract has its corresponding scaled Doléans exponential
as a continuous local martingale. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_const_mul_of_localQuadraticVariation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability
      M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (c : ℝ) :
    IsContinuousLocalMartingale
      (doleansDadeExponential
        (fun t omega => c * M t omega)
        (fun t omega => c ^ 2 * bracket t omega)) 𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
      (hlocalQV.const_mul c)
  · intro omega
    exact continuous_const.mul (hMcont omega)
  · intro t
    exact stronglyMeasurable_const.mul (hbracket t)
  · intro omega
    refine ⟨continuous_const.mul (hbracketPath omega).1, ?_⟩
    intro s t hst
    exact mul_le_mul_of_nonneg_left ((hbracketPath omega).2 hst) (sq_nonneg c)
  · intro omega
    simp only [hMzero omega, mul_zero]
  · intro omega
    simp only [hbracketZero omega, mul_zero]

/-- A convenient specialization of the common-localizer Doléans theorem to
the localizing sequence selected by an existing local-martingale proof. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_localizedQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : IsContinuousLocalMartingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (hlocalQV : ∀ k,
      HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (hM.1.localSeq k))
        (localizingStoppedProcess bracket (hM.1.localSeq k)) P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  exact
    isContinuousLocalMartingale_doleansDadeExponential_of_common_localizedQV
      hM.1.localSeq hM.1.isLocalizingSequence_localSeq
      hM.1.stoppedProcess_localSeq hMcont hbracket hbracketPath
      hMzero hbracketZero hlocalQV

/-- Uniform integrability upgrades the coherent capped Doléans approximation
from convergence in probability to convergence in `L¹`.  This isolates the
remaining probabilistic estimate in the general Doléans--Dade argument: once
uniform integrability of the explicit bounded left sums is available, their
canonical integral candidate is also their `L¹` limit. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendsto_eLpNorm_one_integralCandidate_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T t : ℝ≥0)
    (hUI : UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P) :
    Tendsto
      (fun n ↦ eLpNorm
        (cappedDoleansDadeLeftSumProcess M bracket T n t -
          doleansDadeIntegralCandidate M bracket (min T t)) 1 P)
      Filter.atTop (𝓝 0) := by
  have hconv :=
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
      hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero T t
  have hlimitMem : MemLp
      (doleansDadeIntegralCandidate M bracket (min T t)) 1 P :=
    hUI.memLp_of_tendstoInMeasure hconv
  exact tendsto_Lp_finite_of_tendstoInMeasure (by simp) (by simp)
    (fun n ↦ (hUI.1 n)) hlimitMem hUI.unifIntegrable hconv

/-- For a genuine martingale integrator, uniform integrability of the
bounded diagonal approximations upgrades coherent convergence in probability
to a martingale theorem for the deterministically stopped integral candidate.
-/
theorem martingale_doleansDadeIntegralCandidate_stop_of_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝒱 P)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T : ℝ≥0)
    (hUI : ∀ t, UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P) :
    Martingale
      (fun t ↦ doleansDadeIntegralCandidate M bracket (min T t)) 𝒱 P := by
  have hcandidate : StronglyAdapted 𝒱
      (doleansDadeIntegralCandidate M bracket) :=
    stronglyAdapted_doleansDadeIntegralCandidate hM.stronglyAdapted hbracket
  have hYadapt : StronglyAdapted 𝒱
      (fun t ↦ doleansDadeIntegralCandidate M bracket (min T t)) := by
    intro t
    exact (hcandidate (min T t)).mono (𝒱.mono (min_le_right T t))
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable
    (Y := fun t ↦ doleansDadeIntegralCandidate M bracket (min T t))
    (X := fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n)
  · intro n
    unfold cappedDoleansDadeLeftSumProcess
    exact martingale_uniformAdaptedMartingaleLeftSumProcess hM
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) (n + 1)
      (norm_cappedDoleansDadeExponential_le M bracket (n + 1)) T (n + 1)
  · exact hYadapt
  · exact hUI
  · intro t
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
        hM.stronglyAdapted hbracket hMcont hbracketPath hbefore
          hMzero hbracketZero T t

/-- For a martingale integrator, uniform integrability of the capped
approximations on every deterministic horizon makes the canonical integral
candidate a local martingale.  Deterministic horizons `n + 1` provide the
localizing sequence. -/
theorem
    isLocalMartingale_doleansDadeIntegralCandidate_of_martingale_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝒱 P)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (hUI : ∀ T t, UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P) :
    IsLocalMartingale (doleansDadeIntegralCandidate M bracket) 𝒱 P := by
  let tau : ℕ → W → WithTop ℝ≥0 := fun n _ ↦ ((n + 1 : ℕ) : ℝ≥0)
  have htau : IsLocalizingSequence 𝒱 tau P := by
    refine {
      isStoppingTime := fun n ↦
        isStoppingTime_const 𝒱 ((n + 1 : ℕ) : ℝ≥0)
      mono := ?_
      tendsto_top := ?_ }
    · filter_upwards with omega
      have hnat : Filter.Tendsto (fun n : ℕ ↦ n + 1)
          Filter.atTop Filter.atTop := tendsto_add_atTop_nat 1
      have hnn : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0))
          Filter.atTop Filter.atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ≥0)).comp hnat
      exact WithTop.tendsto_coe_atTop.comp hnn
    · filter_upwards with omega
      intro i j hij
      dsimp only [tau]
      exact_mod_cast Nat.add_le_add_right hij 1
  refine ⟨tau, htau, fun n ↦ ?_⟩
  let T : ℝ≥0 := (n + 1 : ℕ)
  have hstopped :=
    martingale_doleansDadeIntegralCandidate_stop_of_uniformIntegrable
      hM hbracket hMcont hbracketPath hbefore hMzero
        hbracketZero T (hUI T)
  have heq : localizingStoppedProcess
      (doleansDadeIntegralCandidate M bracket) (tau n) =
      fun t ↦ doleansDadeIntegralCandidate M bracket (min T t) := by
    funext t omega
    unfold localizingStoppedProcess stoppedProcess
    have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau n omega} := by
      change (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0)
      rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
      exact WithTop.coe_lt_coe.mpr (by
        dsimp only [T]
        exact_mod_cast Nat.zero_lt_succ n)
    change {omega | (⊥ : WithTop ℝ≥0) < tau n omega}.indicator
        (doleansDadeIntegralCandidate M bracket
          (min (t : WithTop ℝ≥0) (tau n omega)).untopA) omega =
      doleansDadeIntegralCandidate M bracket (min T t) omega
    rw [Set.indicator_of_mem hmem]
    change doleansDadeIntegralCandidate M bracket
        (min (t : WithTop ℝ≥0) (T : WithTop ℝ≥0)).untopA omega =
      doleansDadeIntegralCandidate M bracket (min T t) omega
    rcases le_total t T with htT | hTt
    · rw [min_eq_left (WithTop.coe_le_coe.mpr htT),
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
        min_eq_right htT]
    · rw [min_eq_right (WithTop.coe_le_coe.mpr hTt),
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
        min_eq_left hTt]
  change Martingale
    (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
      (tau n)) 𝒱 P
  rw [heq]
  exact hstopped

/-- Conditional end-to-end Doléans--Dade theorem for a true continuous
martingale: the robust bracket contract supplies the Itô limit, and uniform
integrability of the capped approximations supplies the final Vitali closure.
-/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_martingale_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝒱 P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketAdapt : StronglyAdapted 𝒱 bracket)
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hUI : ∀ T t, UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  have hMlocal : IsContinuousLocalMartingale M 𝒱 P :=
    isContinuousLocalMartingale_of_martingale hM hMcont
  have hintegral : IsLocalMartingale
      (doleansDadeIntegralCandidate M bracket) 𝒱 P :=
    isLocalMartingale_doleansDadeIntegralCandidate_of_martingale_uniformIntegrable
      hM hbracketAdapt hMcont hbracket.2.1 hbefore hMzero
        hbracket.2.2 hUI
  exact isContinuousLocalMartingale_doleansDadeExponential_of_integral_identity
    hMlocal hbracket hintegral
      (doleansDadeExponential_eq_one_add_integralCandidate M bracket)

/-- The preceding conditional endpoint stated with the standard
deterministically-stopped quadratic-variation contract. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_stoppedQV_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝒱 P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketAdapt : StronglyAdapted 𝒱 bracket)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hUI : ∀ T t, UniformIntegrable
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t) 1 P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM.stronglyAdapted s).mono (𝒱.le s)).aestronglyMeasurable
  exact
    isContinuousLocalMartingale_doleansDadeExponential_of_martingale_uniformIntegrable
      hM hMcont hbracket hbracketAdapt
        (hstopped.toBeforeStop hMmeas hMcont) hMzero hUI

/-- A concrete second-moment version of the conditional end-to-end theorem.
On a probability space, a uniform `L²` bound on the explicit capped
martingale transforms supplies the `L¹` uniform integrability used by the
Vitali closure. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_stoppedQV_uniform_eLpNorm_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝒱 P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracket : IsContinuousQuadraticVariationProcess M bracket P)
    (hbracketAdapt : StronglyAdapted 𝒱 bracket)
    (hstopped : HasStoppedQuadraticVariationProcessInProbability M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hL2 : ∀ T t, ∃ C : ℝ≥0, ∀ n,
      eLpNorm (cappedDoleansDadeLeftSumProcess M bracket T n t) 2 P ≤ C) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_stoppedQV_uniformIntegrable
      hM hMcont hbracket hbracketAdapt hstopped hMzero
  intro T t
  obtain ⟨C, hC⟩ := hL2 T t
  exact
    uniformIntegrable_cappedDoleansDadeLeftSumProcess_of_uniform_eLpNorm_two
      hM.stronglyAdapted hbracketAdapt T t C hC

/-! ## Centered Gaussian normalization -/

/-- The exponentially normalized value of a centered Gaussian random
variable is integrable. -/
theorem integrable_gaussianNormalizedExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : W → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    Integrable (fun omega =>
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))) P := by
  have hexp : Integrable (fun x : ℝ => Real.exp (1 * x))
      (gaussianReal 0 v) := integrable_exp_mul_gaussianReal 1
  rw [← hX.map_eq] at hexp
  have hcomp := hexp.comp_aemeasurable hX.aemeasurable
  have hraw : Integrable (fun omega => Real.exp (X omega)) P := by
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => by simp)
  have hscaled := hraw.const_mul (Real.exp (-(1 / 2 : ℝ) * (v : ℝ)))
  exact hscaled.congr (Filter.Eventually.of_forall fun omega => by
    change Real.exp (-(1 / 2 : ℝ) * (v : ℝ)) * Real.exp (X omega) =
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))
    rw [← Real.exp_add]
    congr 1
    ring)

/-- The exponential normalizer of a centered Gaussian random variable has
expectation one. -/
theorem integral_gaussianNormalizedExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : W → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ omega, Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ)) ∂P = 1 := by
  have hmgf : ∫ omega, Real.exp (X omega) ∂P =
      Real.exp ((v : ℝ) / 2) := by
    have h := mgf_gaussianReal hX.map_eq 1
    simpa [mgf] using h
  have heq : (fun omega =>
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))) =
      fun omega => Real.exp (-(1 / 2 : ℝ) * (v : ℝ)) *
        Real.exp (X omega) := by
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hmgf, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring_nf

/-- A centered Gaussian process with independent increments relative to a
filtration and deterministic nondecreasing variance clock. -/
structure IsCenteredGaussianIndependentIncrements
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (variance : ℝ≥0 → ℝ≥0) (P : Measure W) : Prop where
  stronglyAdapted : StronglyAdapted 𝓕 M
  variance_mono : Monotone variance
  hasLaw_eval (t : ℝ≥0) : HasLaw (M t) (gaussianReal 0 (variance t)) P
  hasLaw_increment {a b : ℝ≥0} (hab : a ≤ b) :
    HasLaw (fun omega => M b omega - M a omega)
      (gaussianReal 0 (variance b - variance a)) P
  indep_increment {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap (fun omega => M b omega - M a omega)
        inferInstance)
      (𝓕 a) P

/-- A real square bundled as a nonnegative real variance. -/
def realSquareNNReal (c : ℝ) : ℝ≥0 :=
  ⟨c ^ 2, sq_nonneg c⟩

@[simp]
theorem coe_realSquareNNReal (c : ℝ) :
    (realSquareNNReal c : ℝ) = c ^ 2 :=
  rfl

/-- Centered Gaussian independent-increment processes are closed under
deterministic scalar multiplication; their variance clock scales by `c²`. -/
theorem IsCenteredGaussianIndependentIncrements.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P) (c : ℝ) :
    IsCenteredGaussianIndependentIncrements
      (fun t omega => c * M t omega) 𝓕
      (fun t => realSquareNNReal c * variance t) P where
  stronglyAdapted := by
    change StronglyAdapted 𝓕 (c • M)
    exact hM.stronglyAdapted.smul c
  variance_mono := by
    intro a b hab
    simpa only [mul_comm] using
      mul_le_mul_left (hM.variance_mono hab) (realSquareNNReal c)
  hasLaw_eval := by
    intro t
    have hsquare : NNReal.mk (c ^ 2) (sq_nonneg c) = realSquareNNReal c := by
      apply NNReal.eq
      rfl
    rw [← hsquare]
    simpa only [mul_zero] using gaussianReal_const_mul (hM.hasLaw_eval t) c
  hasLaw_increment := by
    intro a b hab
    have hsquare : NNReal.mk (c ^ 2) (sq_nonneg c) = realSquareNNReal c := by
      apply NNReal.eq
      rfl
    have hLaw := gaussianReal_const_mul (hM.hasLaw_increment hab) c
    change HasLaw (fun omega => c * M b omega - c * M a omega)
      (gaussianReal 0
        (realSquareNNReal c * variance b -
          realSquareNNReal c * variance a)) P
    rw [← mul_tsub]
    rw [← hsquare]
    apply HasLaw.congr
    · simpa only [mul_zero] using hLaw
    filter_upwards with omega
    ring
  indep_increment := by
    intro a b hab
    let increment : W → ℝ := fun omega => M b omega - M a omega
    have hraw : Indep (MeasurableSpace.comap increment inferInstance)
        (𝓕 a) P := hM.indep_increment hab
    have hincMeas : @Measurable W ℝ
        (MeasurableSpace.comap increment inferInstance) inferInstance increment :=
      measurable_iff_comap_le.mpr le_rfl
    have hscaledMeas : @Measurable W ℝ
        (MeasurableSpace.comap increment inferInstance) inferInstance
        (fun omega => c * M b omega - c * M a omega) := by
      have hcomp : @Measurable W ℝ
          (MeasurableSpace.comap increment inferInstance) inferInstance
          (fun omega => c * increment omega) := by
        fun_prop
      convert hcomp using 1
      funext omega
      dsimp only [increment]
      ring
    exact indep_of_indep_of_le_left hraw hscaledMeas.comap_le

/-- The stochastic exponential associated to a centered Gaussian process and
its deterministic variance clock. -/
def centeredGaussianDoleansDadeExponential
    {W : Type*} (M : ℝ≥0 → W → ℝ) (variance : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential M (fun s _ => (variance s : ℝ)) t omega

/-- The normalized exponential of one increment of a centered Gaussian
process with deterministic variance clock. -/
def centeredGaussianDoleansDadeIncrement
    {W : Type*} (M : ℝ≥0 → W → ℝ) (variance : ℝ≥0 → ℝ≥0)
    (a b : ℝ≥0) (omega : W) : ℝ :=
  Real.exp ((M b omega - M a omega) -
    (1 / 2 : ℝ) * ((variance b - variance a : ℝ≥0) : ℝ))

/-- Every fixed-time centered Gaussian stochastic exponential is
integrable. -/
theorem IsCenteredGaussianIndependentIncrements.integrable_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) :
    Integrable (centeredGaussianDoleansDadeExponential M variance t) P := by
  exact integrable_gaussianNormalizedExponential (hM.hasLaw_eval t)

/-- The deterministic variance compensation normalizes every fixed-time
centered Gaussian exponential to have expectation one. -/
theorem IsCenteredGaussianIndependentIncrements.integral_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) :
    ∫ omega, centeredGaussianDoleansDadeExponential M variance t omega ∂P = 1 :=
  integral_gaussianNormalizedExponential (hM.hasLaw_eval t)

/-- If the variance clock starts at zero, the centered Gaussian process
itself starts at zero almost surely. -/
theorem IsCenteredGaussianIndependentIncrements.ae_eq_zero_at_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (hvariance : variance 0 = 0) :
    M 0 =ᵐ[P] fun _ => 0 := by
  have hLaw := hM.hasLaw_eval 0
  rw [hvariance, gaussianReal_zero_var] at hLaw
  exact hLaw.ae_eq_of_dirac

/-- A centered Gaussian stochastic exponential with zero initial variance
starts at one almost surely. -/
theorem IsCenteredGaussianIndependentIncrements.exponential_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (hvariance : variance 0 = 0) :
    centeredGaussianDoleansDadeExponential M variance 0 =ᵐ[P] fun _ => 1 := by
  filter_upwards [hM.ae_eq_zero_at_zero hvariance] with omega hzero
  exact doleansDadeExponential_zero M (fun s _ => (variance s : ℝ)) omega
    hzero (by simp only [hvariance, NNReal.coe_zero])

/-- Squaring a centered Gaussian stochastic exponential produces the
twice-scaled exponential and its deterministic second-moment factor. -/
theorem sq_centeredGaussianDoleansDadeExponential
    {W : Type*} (M : ℝ≥0 → W → ℝ) (variance : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) (omega : W) :
    centeredGaussianDoleansDadeExponential M variance t omega ^ 2 =
      Real.exp (variance t : ℝ) *
        centeredGaussianDoleansDadeExponential
          (fun s omega => 2 * M s omega)
          (fun s => realSquareNNReal 2 * variance s) t omega := by
  unfold centeredGaussianDoleansDadeExponential doleansDadeExponential
    doleansDadeLog
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  simp only [coe_realSquareNNReal, NNReal.coe_mul]
  congr 1
  ring

/-- The exact second moment of a centered Gaussian stochastic exponential
is the exponential of its variance clock. -/
theorem IsCenteredGaussianIndependentIncrements.integral_sq_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) :
    ∫ omega,
        centeredGaussianDoleansDadeExponential M variance t omega ^ 2 ∂P =
      Real.exp (variance t : ℝ) := by
  have heq : (fun omega =>
      centeredGaussianDoleansDadeExponential M variance t omega ^ 2) =
      fun omega => Real.exp (variance t : ℝ) *
        centeredGaussianDoleansDadeExponential
          (fun s omega => 2 * M s omega)
          (fun s => realSquareNNReal 2 * variance s) t omega := by
    funext omega
    exact sq_centeredGaussianDoleansDadeExponential M variance t omega
  rw [heq, integral_const_mul, (hM.const_mul 2).integral_exponential, mul_one]

/-- Every fixed-time centered Gaussian stochastic exponential belongs to
`L²(P)`. -/
theorem IsCenteredGaussianIndependentIncrements.memLp_two_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) :
    MemLp (centeredGaussianDoleansDadeExponential M variance t) 2 P := by
  have hmeas := (hM.integrable_exponential t).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have htwice := (hM.const_mul 2).integrable_exponential t
  have hscaled := htwice.const_mul (Real.exp (variance t : ℝ))
  exact hscaled.congr (Filter.Eventually.of_forall fun omega =>
    (sq_centeredGaussianDoleansDadeExponential M variance t omega).symm)

/-- The exact second moments are uniformly bounded on deterministic compact
time intervals. -/
theorem IsCenteredGaussianIndependentIncrements.integral_sq_exponential_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {t T : ℝ≥0} (ht : t ≤ T) :
    ∫ omega,
        centeredGaussianDoleansDadeExponential M variance t omega ^ 2 ∂P ≤
      Real.exp (variance T : ℝ) := by
  rw [hM.integral_sq_exponential]
  exact Real.exp_le_exp.mpr (mod_cast hM.variance_mono ht)

/-- The normalized exponential of a centered Gaussian increment is
integrable. -/
theorem IsCenteredGaussianIndependentIncrements.integrable_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Integrable (centeredGaussianDoleansDadeIncrement M variance a b) P :=
  integrable_gaussianNormalizedExponential (hM.hasLaw_increment hab)

/-- The normalized exponential of a centered Gaussian increment has mean
one. -/
theorem IsCenteredGaussianIndependentIncrements.integral_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    (∫ omega,
      centeredGaussianDoleansDadeIncrement M variance a b omega ∂P) = 1 :=
  integral_gaussianNormalizedExponential (hM.hasLaw_increment hab)

/-- The centered Gaussian stochastic exponential factors into its current
value and the normalized future increment. -/
theorem IsCenteredGaussianIndependentIncrements.exponential_factor
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    centeredGaussianDoleansDadeExponential M variance b =
      centeredGaussianDoleansDadeExponential M variance a *
        centeredGaussianDoleansDadeIncrement M variance a b := by
  funext omega
  unfold centeredGaussianDoleansDadeExponential
    centeredGaussianDoleansDadeIncrement doleansDadeExponential doleansDadeLog
  simp only [Pi.mul_apply]
  rw [← Real.exp_add, NNReal.coe_sub (hM.variance_mono hab)]
  congr 1
  ring

/-- A normalized future Gaussian exponential increment is independent of
the filtration at the left endpoint. -/
theorem IsCenteredGaussianIndependentIncrements.indep_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap
        (centeredGaussianDoleansDadeIncrement M variance a b) inferInstance)
      (𝓕 a) P := by
  have hincMeas : @Measurable W ℝ
      (MeasurableSpace.comap (fun omega => M b omega - M a omega)
        inferInstance) inferInstance
      (fun omega => M b omega - M a omega) :=
    measurable_iff_comap_le.mpr le_rfl
  apply indep_of_indep_of_le_left (hM.indep_increment hab)
  apply Measurable.comap_le
  exact (show Measurable (fun x : ℝ => Real.exp
    (x - (1 / 2 : ℝ) * ((variance b - variance a : ℝ≥0) : ℝ))) by
      fun_prop).comp hincMeas

/-- Every coordinate of a centered Gaussian independent-increment process is
integrable. -/
theorem IsCenteredGaussianIndependentIncrements.integrable_eval
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) : Integrable (M t) P :=
  (hM.hasLaw_eval t).hasGaussianLaw.integrable

/-- A strongly adapted centered Gaussian process whose future increments are
independent of the past is itself a martingale. -/
theorem IsCenteredGaussianIndependentIncrements.martingale_process
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P) :
    Martingale M 𝓕 P := by
  let _ : IsProbabilityMeasure P := (hM.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨hM.stronglyAdapted, fun a b hab => ?_⟩
  let increment : W → ℝ := fun omega => M b omega - M a omega
  have hincMeas : StronglyMeasurable increment :=
    ((hM.stronglyAdapted b).mono (𝓕.le b)).sub
      ((hM.stronglyAdapted a).mono (𝓕.le a))
  have hcondInc : P[increment | 𝓕 a] =ᵐ[P]
      fun _ => ∫ omega, increment omega ∂P := by
    exact condExp_indep_eq hincMeas.measurable.comap_le (𝓕.le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl))
      (hM.indep_increment hab)
  have hmean : (∫ omega, increment omega ∂P) = 0 := by
    change (∫ omega, M b omega - M a omega ∂P) = 0
    rw [(hM.hasLaw_increment hab).integral_eq, integral_id_gaussianReal]
  have hcurrent : StronglyMeasurable[𝓕 a] (M a) :=
    hM.stronglyAdapted a
  have hsplit : M b = increment + M a := by
    funext omega
    change M b omega = (M b omega - M a omega) + M a omega
    ring
  calc
    P[M b | 𝓕 a] = P[increment + M a | 𝓕 a] := by rw [← hsplit]
    _ =ᵐ[P] P[increment | 𝓕 a] + P[M a | 𝓕 a] :=
      condExp_add
        ((hM.integrable_eval b).sub (hM.integrable_eval a))
        (hM.integrable_eval a) _
    _ =ᵐ[P] (fun _ => (0 : ℝ)) + M a := by
      refine Filter.EventuallyEq.add (hcondInc.trans ?_) ?_
      · filter_upwards with omega
        simp only [hmean]
      · exact Filter.EventuallyEq.of_eq <|
          condExp_of_stronglyMeasurable (𝓕.le a) hcurrent
            (hM.integrable_eval a)
    _ =ᵐ[P] M a := by
      filter_upwards with omega
      simp

/-- With continuous sample paths, a centered Gaussian
independent-increment process is a continuous local martingale. -/
theorem IsCenteredGaussianIndependentIncrements.isContinuousLocalMartingale_process
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun t => M t omega)) :
    IsContinuousLocalMartingale M 𝓕 P :=
  isContinuousLocalMartingale_of_martingale hM.martingale_process hcontinuous

/-- A centered Gaussian independent-increment process has a martingale
stochastic exponential. -/
theorem IsCenteredGaussianIndependentIncrements.martingale_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P) :
    Martingale (centeredGaussianDoleansDadeExponential M variance) 𝓕 P := by
  let _ : IsProbabilityMeasure P := (hM.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun t => ?_, fun a b hab => ?_⟩
  · change StronglyMeasurable[𝓕 t] (fun omega =>
      Real.exp (M t omega - (1 / 2 : ℝ) * (variance t : ℝ)))
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hM.stronglyAdapted t).sub stronglyMeasurable_const)
  · let future : W → ℝ :=
      centeredGaussianDoleansDadeIncrement M variance a b
    have hfutureInt : Integrable future P :=
      hM.integrable_increment_exponential hab
    have hcurrentMeas : StronglyMeasurable[𝓕 a]
        (centeredGaussianDoleansDadeExponential M variance a) := by
      change StronglyMeasurable[𝓕 a] (fun omega =>
        Real.exp (M a omega - (1 / 2 : ℝ) * (variance a : ℝ)))
      exact Real.continuous_exp.comp_stronglyMeasurable
        ((hM.stronglyAdapted a).sub stronglyMeasurable_const)
    have hind : Indep (MeasurableSpace.comap future inferInstance) (𝓕 a) P :=
      hM.indep_increment_exponential hab
    have hfutureMeas : StronglyMeasurable future := by
      have hb := (hM.stronglyAdapted b).mono (𝓕.le b)
      have ha := (hM.stronglyAdapted a).mono (𝓕.le a)
      exact Real.continuous_exp.comp_stronglyMeasurable
        ((hb.sub ha).sub stronglyMeasurable_const)
    have hcondFuture : P[future | 𝓕 a] =ᵐ[P]
        fun _ => ∫ omega, future omega ∂P := by
      exact condExp_indep_eq hfutureMeas.measurable.comap_le (𝓕.le a)
        (Measurable.stronglyMeasurable
          (measurable_iff_comap_le.mpr le_rfl)) hind
    have hfactor : centeredGaussianDoleansDadeExponential M variance b =
        centeredGaussianDoleansDadeExponential M variance a * future :=
      hM.exponential_factor hab
    have hproductInt : Integrable
        (centeredGaussianDoleansDadeExponential M variance a * future) P := by
      rw [← hfactor]
      exact hM.integrable_exponential b
    calc
      P[centeredGaussianDoleansDadeExponential M variance b | 𝓕 a] =
          P[centeredGaussianDoleansDadeExponential M variance a * future |
            𝓕 a] := by rw [hfactor]
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a *
          P[future | 𝓕 a] :=
        condExp_mul_of_stronglyMeasurable_left hcurrentMeas
          hproductInt hfutureInt
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a *
          (fun _ => ∫ omega, future omega ∂P) :=
        Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a := by
        have hmean : (∫ omega, future omega ∂P) = 1 :=
          hM.integral_increment_exponential hab
        filter_upwards with omega
        simp only [Pi.mul_apply, hmean, mul_one]

/-- With continuous sample paths and a continuous variance clock, the
centered Gaussian stochastic exponential is a continuous local martingale. -/
theorem IsCenteredGaussianIndependentIncrements.isContinuousLocalMartingale_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun t => M t omega))
    (hvariance : Continuous (fun t => (variance t : ℝ))) :
    IsContinuousLocalMartingale
      (centeredGaussianDoleansDadeExponential M variance) 𝓕 P := by
  apply isContinuousLocalMartingale_of_martingale hM.martingale_exponential
  filter_upwards [hcontinuous] with omega hpath
  exact continuous_doleansDadeExponential M
    (fun t _ => (variance t : ℝ)) omega hpath hvariance

/-- The Gaussian contract projection exposes both the input continuous local
martingale and its stochastic-exponential conclusion. -/
theorem IsCenteredGaussianIndependentIncrements.continuousLocalMartingale_case
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun t => M t omega))
    (hvariance : Continuous (fun t => (variance t : ℝ))) :
    IsContinuousLocalMartingale M 𝓕 P ∧
      IsContinuousLocalMartingale
        (centeredGaussianDoleansDadeExponential M variance) 𝓕 P :=
  ⟨hM.isContinuousLocalMartingale_process hcontinuous,
    hM.isContinuousLocalMartingale_exponential hcontinuous hvariance⟩

/-! ## Brownian specialization -/

/-- The Doléans–Dade exponential of Brownian motion, whose bracket is time. -/
def brownianDoleansDadeExponential
    {W : Type*} (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential B (fun s _ => (s : ℝ)) t omega

@[simp]
theorem brownianDoleansDadeExponential_apply
    {W : Type*} (B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    brownianDoleansDadeExponential B t omega =
      Real.exp (B t omega - (1 / 2 : ℝ) * (t : ℝ)) :=
  rfl

/-- Brownian continuity gives continuous paths for its stochastic
exponential. -/
theorem ae_continuous_brownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ omega ∂P,
      Continuous (fun t => brownianDoleansDadeExponential B t omega) := by
  filter_upwards [hB.cont] with omega hcontinuous
  exact continuous_doleansDadeExponential B (fun s _ => (s : ℝ)) omega
    hcontinuous (by fun_prop)

/-- The Brownian stochastic exponential starts at one almost surely. -/
theorem brownianDoleansDadeExponential_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) :
    brownianDoleansDadeExponential B 0 =ᵐ[P] fun _ => 1 := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with omega hzero
  exact doleansDadeExponential_zero B (fun s _ => (s : ℝ)) omega hzero (by simp)

/-- Every fixed-time Brownian stochastic exponential is integrable. -/
theorem integrable_brownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Integrable (brownianDoleansDadeExponential B t) P := by
  have hexp : Integrable (fun x : ℝ => Real.exp (1 * x))
      (gaussianReal 0 t) := integrable_exp_mul_gaussianReal 1
  rw [← (hB.hasLaw_eval t).map_eq] at hexp
  have hcomp := hexp.comp_aemeasurable (hB.aemeasurable t)
  have hBt : Integrable (fun omega => Real.exp (B t omega)) P := by
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => by simp)
  have hconst : Integrable
      (fun omega => Real.exp (-(1 / 2 : ℝ) * (t : ℝ)) *
        Real.exp (B t omega)) P :=
    hBt.const_mul _
  refine hconst.congr (Filter.Eventually.of_forall fun omega => ?_)
  change Real.exp (-(1 / 2 : ℝ) * (t : ℝ)) * Real.exp (B t omega) =
    brownianDoleansDadeExponential B t omega
  rw [brownianDoleansDadeExponential_apply, ← Real.exp_add]
  congr 1
  ring

/-- The Gaussian normalizer makes the expectation of the Brownian
stochastic exponential equal to one. -/
theorem integral_brownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∫ omega, brownianDoleansDadeExponential B t omega ∂P = 1 := by
  have hmgf : ∫ omega, Real.exp (B t omega) ∂P =
      Real.exp ((t : ℝ) / 2) := by
    have h := mgf_gaussianReal (hB.hasLaw_eval t).map_eq 1
    simpa [mgf] using h
  have heq : (fun omega => brownianDoleansDadeExponential B t omega) =
      fun omega => Real.exp (-(1 / 2 : ℝ) * (t : ℝ)) *
        Real.exp (B t omega) := by
    funext omega
    rw [brownianDoleansDadeExponential_apply, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hmgf, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring_nf

/-- The normalized exponential of a Brownian increment. -/
def brownianDoleansDadeIncrement
    {W : Type*} (B : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (omega : W) : ℝ :=
  Real.exp ((B b omega - B a omega) -
    (1 / 2 : ℝ) * ((b : ℝ) - (a : ℝ)))

/-- A normalized increment is the stochastic exponential of the shifted
Brownian motion. -/
theorem brownianDoleansDadeIncrement_eq_shift
    {W : Type*} (B : ℝ≥0 → W → ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    brownianDoleansDadeIncrement B a b =
      brownianDoleansDadeExponential
        (fun s omega => B (a + s) omega - B a omega) (b - a) := by
  funext omega
  rw [brownianDoleansDadeExponential_apply]
  simp only [brownianDoleansDadeIncrement]
  congr 2
  · rw [add_comm, tsub_add_cancel_of_le hab]
  · norm_cast

/-- A normalized future Brownian increment is integrable. -/
theorem integrable_brownianDoleansDadeIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Integrable (brownianDoleansDadeIncrement B a b) P := by
  rw [brownianDoleansDadeIncrement_eq_shift B hab]
  exact integrable_brownianDoleansDadeExponential
    (hB.shift a) (b - a)

/-- A normalized future Brownian increment has expectation one. -/
theorem integral_brownianDoleansDadeIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ omega, brownianDoleansDadeIncrement B a b omega ∂P = 1 := by
  rw [brownianDoleansDadeIncrement_eq_shift B hab]
  exact integral_brownianDoleansDadeExponential
    (hB.shift a) (b - a)

/-- The Brownian stochastic exponential factors into its present value and
an independent normalized future increment. -/
theorem brownianDoleansDadeExponential_factor
    {W : Type*} (B : ℝ≥0 → W → ℝ) (a b : ℝ≥0) :
    brownianDoleansDadeExponential B b =
      brownianDoleansDadeExponential B a *
        brownianDoleansDadeIncrement B a b := by
  funext omega
  simp only [Pi.mul_apply, brownianDoleansDadeExponential_apply,
    brownianDoleansDadeIncrement]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Brownian stochastic exponential is measurable at each time in the
natural filtration. -/
theorem stronglyMeasurable_brownianDoleansDadeExponential_natural
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (t : ℝ≥0) :
    StronglyMeasurable[Filtration.natural B hsm t]
      (brownianDoleansDadeExponential B t) := by
  have hBt : StronglyMeasurable[Filtration.natural B hsm t] (B t) :=
    Filtration.stronglyAdapted_natural hsm t
  change StronglyMeasurable[Filtration.natural B hsm t]
    (fun omega => Real.exp (B t omega - (1 / 2 : ℝ) * (t : ℝ)))
  exact Real.continuous_exp.comp_stronglyMeasurable
    (hBt.sub stronglyMeasurable_const)

/-- A normalized future Brownian exponential is independent of the natural
filtration at the left endpoint. -/
theorem indep_brownianDoleansDadeIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap (brownianDoleansDadeIncrement B a b) inferInstance)
      (Filtration.natural B hsm a) P := by
  have hshift := hB.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ => x (b - a)) :=
    measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hnormalizedPast : IndepFun (brownianDoleansDadeIncrement B a b)
      (fun omega (t : Set.Iic a) => B t omega) P := by
    have h := hfuturePast.comp
      (show Measurable (fun x : ℝ =>
        Real.exp (x - (1 / 2 : ℝ) * ((b : ℝ) - (a : ℝ)))) by fun_prop)
      measurable_id
    convert h using 1
    · funext omega
      simp only [Function.comp_apply, brownianDoleansDadeIncrement]
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hnormalizedPast
  have hnat : Filtration.natural B hsm a =
      MeasurableSpace.comap (fun omega (t : Set.Iic a) => B t omega)
        inferInstance := by
    rw [Filtration.natural_eq_comap]
  rw [hnat]
  exact hind

/-- A future Brownian increment is independent of the natural filtration at
its left endpoint. -/
theorem indep_brownianIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap (fun omega => B b omega - B a omega)
        inferInstance)
      (Filtration.natural B hsm a) P := by
  have hshift := hB.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ => x (b - a)) :=
    measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hincPast : IndepFun (fun omega => B b omega - B a omega)
      (fun omega (t : Set.Iic a) => B t omega) P := by
    convert hfuturePast using 1
    · funext omega
      change B b omega - B a omega = B (a + (b - a)) omega - B a omega
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hincPast
  have hnat : Filtration.natural B hsm a =
      MeasurableSpace.comap (fun omega (t : Set.Iic a) => B t omega)
        inferInstance := by
    rw [Filtration.natural_eq_comap]
  rw [hnat]
  exact hind

/-- Brownian motion is a centered Gaussian independent-increment process
with variance clock `t`. -/
theorem isCenteredGaussianIndependentIncrements_brownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    IsCenteredGaussianIndependentIncrements B
      (Filtration.natural B hsm) (fun t => t) P where
  stronglyAdapted := Filtration.stronglyAdapted_natural hsm
  variance_mono := fun _ _ hab => hab
  hasLaw_eval := hB.hasLaw_eval
  hasLaw_increment := by
    intro a b hab
    refine ((hB.shift a).hasLaw_eval (b - a)).congr ?_
    filter_upwards with omega
    rw [add_comm, tsub_add_cancel_of_le hab]
  indep_increment := indep_brownianIncrement_natural hB hsm

/-- Pull a filtration back along a deterministic nondecreasing time change. -/
def timeChangeFiltration
    {W : Type*} [MeasurableSpace W]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock) :
    Filtration ℝ≥0 ‹MeasurableSpace W› where
  seq t := 𝓕 (clock t)
  mono' _ _ hab := 𝓕.mono (hclock hab)
  le' t := 𝓕.le (clock t)

/-- Brownian motion under a deterministic nondecreasing time change is a
centered Gaussian independent-increment process with that clock as variance. -/
theorem isCenteredGaussianIndependentIncrements_brownian_timeChange
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock) :
    IsCenteredGaussianIndependentIncrements
      (fun t omega => B (clock t) omega)
      (timeChangeFiltration (Filtration.natural B hsm) clock hclock)
      clock P where
  stronglyAdapted := fun t =>
    Filtration.stronglyAdapted_natural hsm (clock t)
  variance_mono := hclock
  hasLaw_eval := fun t => hB.hasLaw_eval (clock t)
  hasLaw_increment := by
    intro a b hab
    refine ((hB.shift (clock a)).hasLaw_eval (clock b - clock a)).congr ?_
    filter_upwards with omega
    rw [add_comm, tsub_add_cancel_of_le (hclock hab)]
  indep_increment := by
    intro a b hab
    exact indep_brownianIncrement_natural hB hsm (hclock hab)

/-- A continuous deterministic time change of Brownian motion has a
continuous-local-martingale stochastic exponential. -/
theorem isContinuousLocalMartingale_brownianTimeChange_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock)
    (hclockContinuous : Continuous clock) :
    IsContinuousLocalMartingale
      (centeredGaussianDoleansDadeExponential
        (fun t omega => B (clock t) omega) clock)
      (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P := by
  apply (isCenteredGaussianIndependentIncrements_brownian_timeChange
    hB.toIsPreBrownianReal hsm clock hclock).isContinuousLocalMartingale_exponential
  · filter_upwards [hB.cont] with omega hcontinuous
    exact hcontinuous.comp hclockContinuous
  · exact continuous_subtype_val.comp hclockContinuous

/-- A scaled deterministic Brownian time change has a martingale stochastic
exponential with variance clock `c² clock`. -/
theorem martingale_scaledBrownianTimeChange_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock) (c : ℝ) :
    Martingale
      (centeredGaussianDoleansDadeExponential
        (fun t omega => c * B (clock t) omega)
        (fun t => realSquareNNReal c * clock t))
      (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P :=
  ((isCenteredGaussianIndependentIncrements_brownian_timeChange
    hB hsm clock hclock).const_mul c).martingale_exponential

/-- With a continuous clock, the scaled time-changed Brownian exponential is
a continuous local martingale. -/
theorem isContinuousLocalMartingale_scaledBrownianTimeChange_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock)
    (hclockContinuous : Continuous clock) (c : ℝ) :
    IsContinuousLocalMartingale
      (centeredGaussianDoleansDadeExponential
        (fun t omega => c * B (clock t) omega)
        (fun t => realSquareNNReal c * clock t))
      (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P := by
  apply ((isCenteredGaussianIndependentIncrements_brownian_timeChange
    hB.toIsPreBrownianReal hsm clock hclock).const_mul c
      ).isContinuousLocalMartingale_exponential
  · filter_upwards [hB.cont] with omega hcontinuous
    exact continuous_const.mul (hcontinuous.comp hclockContinuous)
  · change Continuous (fun t : ℝ≥0 => c ^ 2 * (clock t : ℝ))
    exact continuous_const.mul (continuous_subtype_val.comp hclockContinuous)

/-- Contract projection with premise and conclusion together for every scaled
continuous deterministic Brownian time change. -/
theorem scaledBrownianTimeChange_doleansDade_case
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclock : Monotone clock)
    (hclockContinuous : Continuous clock) (c : ℝ) :
    IsContinuousLocalMartingale
        (fun t omega => c * B (clock t) omega)
        (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P ∧
      IsContinuousLocalMartingale
        (centeredGaussianDoleansDadeExponential
          (fun t omega => c * B (clock t) omega)
          (fun t => realSquareNNReal c * clock t))
        (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P := by
  apply ((isCenteredGaussianIndependentIncrements_brownian_timeChange
    hB.toIsPreBrownianReal hsm clock hclock).const_mul c
      ).continuousLocalMartingale_case
  · filter_upwards [hB.cont] with omega hcontinuous
    exact continuous_const.mul (hcontinuous.comp hclockContinuous)
  · change Continuous (fun t : ℝ≥0 => c ^ 2 * (clock t : ℝ))
    exact continuous_const.mul (continuous_subtype_val.comp hclockContinuous)

/-- A Brownian motion on a continuous monotone clock has that clock as its
process-valued quadratic variation. -/
theorem hasQuadraticVariationProcess_timeChangedBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (clock : ℝ≥0 → ℝ≥0)
    (hclockZero : clock 0 = 0) (hclockContinuous : Continuous clock)
    (hclock : Monotone clock) :
    HasQuadraticVariationProcessInProbability
      (fun t omega => B (clock t) omega)
      (fun t _ => (clock t : ℝ)) P := by
  intro t
  exact quadraticVariation_timeChanged_brownian_inProbability
    hB clock hclockZero hclockContinuous hclock t

/-- The deterministic clock bracket of time-changed Brownian motion is a
continuous quadratic-variation process. -/
theorem isContinuousQuadraticVariationProcess_timeChangedBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (clock : ℝ≥0 → ℝ≥0)
    (hclockZero : clock 0 = 0) (hclockContinuous : Continuous clock)
    (hclock : Monotone clock) :
    IsContinuousQuadraticVariationProcess
      (fun t omega => B (clock t) omega)
      (fun t _ => (clock t : ℝ)) P := by
  refine ⟨hasQuadraticVariationProcess_timeChangedBrownian hB clock
      hclockZero hclockContinuous hclock,
    Filter.Eventually.of_forall fun omega => ⟨?_, ?_⟩,
    Filter.Eventually.of_forall fun omega => ?_⟩
  · exact NNReal.continuous_coe.comp hclockContinuous
  · intro a b hab
    exact_mod_cast hclock hab
  · simp only [hclockZero, NNReal.coe_zero]

/-- Scaled time-changed Brownian motion has bracket `c² clock`. -/
theorem isContinuousQuadraticVariationProcess_scaledTimeChangedBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (clock : ℝ≥0 → ℝ≥0)
    (hclockZero : clock 0 = 0) (hclockContinuous : Continuous clock)
    (hclock : Monotone clock) (c : ℝ) :
    IsContinuousQuadraticVariationProcess
      (fun t omega => c * B (clock t) omega)
      (fun t _ => c ^ 2 * (clock t : ℝ)) P := by
  exact (isContinuousQuadraticVariationProcess_timeChangedBrownian
    hB clock hclockZero hclockContinuous hclock).const_mul
      (fun t =>
        (hB.toIsPreBrownianReal.aemeasurable (clock t)).aestronglyMeasurable) c

/-- Bracket-complete Doléans–Dade projection for every scaled continuous
deterministic Brownian time change. -/
theorem scaledBrownianTimeChange_doleansDade_with_bracket_case
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (clock : ℝ≥0 → ℝ≥0) (hclockZero : clock 0 = 0)
    (hclockContinuous : Continuous clock) (hclock : Monotone clock) (c : ℝ) :
    IsContinuousLocalMartingale
        (fun t omega => c * B (clock t) omega)
        (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P ∧
      IsContinuousQuadraticVariationProcess
        (fun t omega => c * B (clock t) omega)
        (fun t _ => c ^ 2 * (clock t : ℝ)) P ∧
      IsContinuousLocalMartingale
        (doleansDadeExponential
          (fun t omega => c * B (clock t) omega)
          (fun t _ => c ^ 2 * (clock t : ℝ)))
        (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P := by
  refine ⟨(scaledBrownianTimeChange_doleansDade_case hB hsm clock hclock
      hclockContinuous c).1,
    isContinuousQuadraticVariationProcess_scaledTimeChangedBrownian
      hB clock hclockZero hclockContinuous hclock c, ?_⟩
  change IsContinuousLocalMartingale
    (centeredGaussianDoleansDadeExponential
      (fun t omega => c * B (clock t) omega)
      (fun t => realSquareNNReal c * clock t))
    (timeChangeFiltration (Filtration.natural B hsm) clock hclock) P
  exact (scaledBrownianTimeChange_doleansDade_case hB hsm clock hclock
    hclockContinuous c).2

/-- A constant multiple of Brownian motion is a centered Gaussian
independent-increment process with variance clock `c²t`. -/
theorem isCenteredGaussianIndependentIncrements_scaledBrownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsCenteredGaussianIndependentIncrements
      (fun t omega => c * B t omega) (Filtration.natural B hsm)
      (fun t => realSquareNNReal c * t) P :=
  (isCenteredGaussianIndependentIncrements_brownian_natural hB hsm).const_mul c

/-- The Brownian stochastic-exponential martingale theorem as a direct
instance of the centered Gaussian independent-increment theorem. -/
theorem martingale_brownianDoleansDadeExponential_via_gaussianIncrements
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale (brownianDoleansDadeExponential B)
      (Filtration.natural B hsm) P := by
  change Martingale
    (centeredGaussianDoleansDadeExponential B (fun t => t))
      (Filtration.natural B hsm) P
  exact (isCenteredGaussianIndependentIncrements_brownian_natural
    hB hsm).martingale_exponential

/-- A pre-Brownian process with strongly measurable coordinates is a
martingale in its natural filtration. -/
theorem martingale_brownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale B (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨Filtration.stronglyAdapted_natural hsm, fun a b hab => ?_⟩
  have hincMeas : StronglyMeasurable (fun omega => B b omega - B a omega) :=
    (hsm b).sub (hsm a)
  have hind := indep_brownianIncrement_natural hB hsm hab
  have hcondInc : P[(fun omega => B b omega - B a omega) |
      Filtration.natural B hsm a] =ᵐ[P]
      fun _ => ∫ omega, B b omega - B a omega ∂P := by
    exact condExp_indep_eq hincMeas.measurable.comap_le
      ((Filtration.natural B hsm).le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl)) hind
  have hmean : (∫ omega, B b omega - B a omega ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
      hB.integral_eval b, hB.integral_eval a, sub_zero]
  have hcurrent : StronglyMeasurable[Filtration.natural B hsm a] (B a) :=
    Filtration.stronglyAdapted_natural hsm a
  have hsplit : B b = (fun omega => B b omega - B a omega) + B a := by
    funext omega
    change B b omega = (B b omega - B a omega) + B a omega
    ring
  calc
    P[B b | Filtration.natural B hsm a] =
        P[(fun omega => B b omega - B a omega) + B a |
          Filtration.natural B hsm a] := by rw [← hsplit]
    _ =ᵐ[P] P[(fun omega => B b omega - B a omega) |
          Filtration.natural B hsm a] +
        P[B a | Filtration.natural B hsm a] :=
      condExp_add
        ((hB.integrable_eval b).sub (hB.integrable_eval a))
        (hB.integrable_eval a) _
    _ =ᵐ[P] (fun _ => (0 : ℝ)) + B a := by
      refine Filter.EventuallyEq.add (hcondInc.trans ?_) ?_
      · filter_upwards with omega
        simp only [hmean]
      · exact Filter.EventuallyEq.of_eq <|
          condExp_of_stronglyMeasurable
            ((Filtration.natural B hsm).le a) hcurrent
            (hB.integrable_eval a)
    _ =ᵐ[P] B a := by
      filter_upwards with omega
      simp

/-- A Brownian motion is a continuous local martingale in its natural
filtration. -/
theorem isContinuousLocalMartingale_brownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    IsContinuousLocalMartingale B (Filtration.natural B hsm) P :=
  isContinuousLocalMartingale_of_martingale
    (martingale_brownian_natural hB.toIsPreBrownianReal hsm) hB.cont

/-- The stochastic exponential of Brownian motion is a martingale in its
natural filtration. -/
theorem martingale_brownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale (brownianDoleansDadeExponential B)
      (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t =>
    stronglyMeasurable_brownianDoleansDadeExponential_natural hsm t,
    fun a b hab => ?_⟩
  let future := brownianDoleansDadeIncrement B a b
  have hfutureMeas : StronglyMeasurable future := by
    change StronglyMeasurable (fun omega =>
      Real.exp ((B b omega - B a omega) -
        (1 / 2 : ℝ) * ((b : ℝ) - (a : ℝ))))
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hsm b).sub (hsm a) |>.sub stronglyMeasurable_const)
  have hfutureInt : Integrable future P :=
    integrable_brownianDoleansDadeIncrement hB hab
  have hcurrentMeas :
      StronglyMeasurable[Filtration.natural B hsm a]
        (brownianDoleansDadeExponential B a) :=
    stronglyMeasurable_brownianDoleansDadeExponential_natural hsm a
  have hind : Indep (MeasurableSpace.comap future inferInstance)
      (Filtration.natural B hsm a) P :=
    indep_brownianDoleansDadeIncrement_natural hB hsm hab
  have hcondFuture : P[future | Filtration.natural B hsm a] =ᵐ[P]
      fun _ => ∫ omega, future omega ∂P := by
    exact condExp_indep_eq
      hfutureMeas.measurable.comap_le
      ((Filtration.natural B hsm).le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl)) hind
  have hproductInt : Integrable
      (brownianDoleansDadeExponential B a * future) P := by
    rw [← brownianDoleansDadeExponential_factor B a b]
    exact integrable_brownianDoleansDadeExponential hB b
  calc
    P[brownianDoleansDadeExponential B b |
        Filtration.natural B hsm a] =
        P[brownianDoleansDadeExponential B a * future |
          Filtration.natural B hsm a] := by
      rw [brownianDoleansDadeExponential_factor B a b]
    _ =ᵐ[P] brownianDoleansDadeExponential B a *
        P[future | Filtration.natural B hsm a] :=
      condExp_mul_of_stronglyMeasurable_left hcurrentMeas
        hproductInt hfutureInt
    _ =ᵐ[P] brownianDoleansDadeExponential B a *
        (fun _ => ∫ omega, future omega ∂P) :=
      Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
    _ =ᵐ[P] brownianDoleansDadeExponential B a := by
      have hmean : (∫ omega, future omega ∂P) = 1 :=
        integral_brownianDoleansDadeIncrement hB hab
      filter_upwards with omega
      simp only [Pi.mul_apply, hmean, mul_one]

/-- The Brownian stochastic exponential is a continuous local martingale in
its natural filtration. -/
theorem isContinuousLocalMartingale_brownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    IsContinuousLocalMartingale (brownianDoleansDadeExponential B)
      (Filtration.natural B hsm) P :=
  isContinuousLocalMartingale_of_martingale
    (martingale_brownianDoleansDadeExponential hB.toIsPreBrownianReal hsm)
    (ae_continuous_brownianDoleansDadeExponential hB)

/-! ## Constant multiples of Brownian motion -/

/-- The time-state function used to apply Itô's formula to `c B`. -/
def scaledBrownianDoleansDadeFunction (c s x : ℝ) : ℝ :=
  Real.exp (c * x - (1 / 2 : ℝ) * (c ^ 2 * s))

/-- The time derivative in the scaled Brownian exponential formula. -/
theorem itoTimeDerivative_scaledBrownianDoleansDadeFunction
    (c s x : ℝ) :
    itoTimeDerivative (scaledBrownianDoleansDadeFunction c) s x =
      (-(1 / 2 : ℝ) * c ^ 2) *
        scaledBrownianDoleansDadeFunction c s x := by
  have hinner := (hasDerivAt_const (x := s) (c := c * x)).sub
    (((hasDerivAt_id s).const_mul (c ^ 2)).const_mul (1 / 2 : ℝ))
  have h := hinner.exp.deriv
  unfold itoTimeDerivative scaledBrownianDoleansDadeFunction
  convert h using 1 <;> simp only [id_eq, Pi.sub_apply]
  all_goals ring

/-- The first state derivative in the scaled Brownian exponential formula. -/
theorem itoSpaceDerivative_scaledBrownianDoleansDadeFunction
    (c s x : ℝ) :
    itoSpaceDerivative (scaledBrownianDoleansDadeFunction c) s x =
      c * scaledBrownianDoleansDadeFunction c s x := by
  have hinner := ((hasDerivAt_id x).const_mul c).sub_const
    ((1 / 2 : ℝ) * (c ^ 2 * s))
  have h := hinner.exp.deriv
  unfold itoSpaceDerivative scaledBrownianDoleansDadeFunction
  convert h using 1 <;> simp only [id_eq]
  all_goals ring

/-- The second state derivative in the scaled Brownian exponential
formula. -/
theorem itoSpaceSecondDerivative_scaledBrownianDoleansDadeFunction
    (c s x : ℝ) :
    itoSpaceSecondDerivative (scaledBrownianDoleansDadeFunction c) s x =
      c ^ 2 * scaledBrownianDoleansDadeFunction c s x := by
  have hfirst : deriv (scaledBrownianDoleansDadeFunction c s) =
      fun y => c * scaledBrownianDoleansDadeFunction c s y := by
    funext y
    exact itoSpaceDerivative_scaledBrownianDoleansDadeFunction c s y
  rw [itoSpaceSecondDerivative, hfirst]
  have hinner := ((hasDerivAt_id x).const_mul c).sub_const
    ((1 / 2 : ℝ) * (c ^ 2 * s))
  have h := hinner.exp.const_mul c |>.deriv
  unfold scaledBrownianDoleansDadeFunction
  convert h using 1 <;> simp only [id_eq]
  all_goals ring

/-- The time drift and the second-order correction cancel exactly for the
scaled Brownian stochastic exponential. -/
theorem scaledBrownianDoleansDade_ito_drift_cancel (c s x : ℝ) :
    itoTimeDerivative (scaledBrownianDoleansDadeFunction c) s x +
        (1 / 2 : ℝ) *
          itoSpaceSecondDerivative
            (scaledBrownianDoleansDadeFunction c) s x = 0 := by
  rw [itoTimeDerivative_scaledBrownianDoleansDadeFunction,
    itoSpaceSecondDerivative_scaledBrownianDoleansDadeFunction]
  ring

/-- The Doléans–Dade exponential associated to `c B`, whose bracket is
`c² t`. -/
def scaledBrownianDoleansDadeExponential
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential
    (fun s omega => c * B s omega)
    (fun s _ => c ^ 2 * (s : ℝ)) t omega

/-- The generic Gaussian exponential specializes definitionally to the
scaled Brownian exponential. -/
theorem centeredGaussianDoleansDadeExponential_scaledBrownian
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ) :
    centeredGaussianDoleansDadeExponential
        (fun t omega => c * B t omega)
        (fun t => realSquareNNReal c * t) =
      scaledBrownianDoleansDadeExponential c B := by
  rfl

/-- The scaled Brownian stochastic exponential is a martingale by the
generic centered Gaussian independent-increment theorem. -/
theorem martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    Martingale (scaledBrownianDoleansDadeExponential c B)
      (Filtration.natural B hsm) P := by
  rw [← centeredGaussianDoleansDadeExponential_scaledBrownian]
  exact (isCenteredGaussianIndependentIncrements_scaledBrownian_natural
    hB hsm c).martingale_exponential

/-- Path continuity and the generic Gaussian theorem also recover the
continuous-local-martingale conclusion for scaled Brownian exponentials. -/
theorem
    isContinuousLocalMartingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale (scaledBrownianDoleansDadeExponential c B)
      (Filtration.natural B hsm) P := by
  rw [← centeredGaussianDoleansDadeExponential_scaledBrownian]
  apply (isCenteredGaussianIndependentIncrements_scaledBrownian_natural
    hB.toIsPreBrownianReal hsm c).isContinuousLocalMartingale_exponential
  · filter_upwards [hB.cont] with omega hcontinuous
    exact continuous_const.mul hcontinuous
  · change Continuous (fun t : ℝ≥0 => c ^ 2 * (t : ℝ))
    fun_prop

@[simp]
theorem scaledBrownianDoleansDadeExponential_apply
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    scaledBrownianDoleansDadeExponential c B t omega =
      Real.exp (c * B t omega - (1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))) :=
  rfl

/-- Every fixed-time scaled Brownian stochastic exponential is integrable. -/
theorem integrable_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    Integrable (scaledBrownianDoleansDadeExponential c B t) P := by
  have hexp : Integrable (fun x : ℝ => Real.exp (c * x))
      (gaussianReal 0 t) := integrable_exp_mul_gaussianReal c
  rw [← (hB.hasLaw_eval t).map_eq] at hexp
  have hcomp := hexp.comp_aemeasurable (hB.aemeasurable t)
  have hBt : Integrable (fun omega => Real.exp (c * B t omega)) P := by
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => by simp)
  have hconst : Integrable
      (fun omega => Real.exp (-(1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))) *
        Real.exp (c * B t omega)) P :=
    hBt.const_mul _
  refine hconst.congr (Filter.Eventually.of_forall fun omega => ?_)
  change Real.exp (-(1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))) *
      Real.exp (c * B t omega) =
    scaledBrownianDoleansDadeExponential c B t omega
  rw [scaledBrownianDoleansDadeExponential_apply, ← Real.exp_add]
  congr 1
  ring

/-- The Gaussian normalizer makes every scaled Brownian stochastic
exponential have expectation one. -/
theorem integral_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    ∫ omega, scaledBrownianDoleansDadeExponential c B t omega ∂P = 1 := by
  have hmgf : ∫ omega, Real.exp (c * B t omega) ∂P =
      Real.exp ((t : ℝ) * c ^ 2 / 2) := by
    have h := mgf_gaussianReal (hB.hasLaw_eval t).map_eq c
    simpa [mgf] using h
  have heq : (fun omega =>
      scaledBrownianDoleansDadeExponential c B t omega) =
      fun omega => Real.exp (-(1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))) *
        Real.exp (c * B t omega) := by
    funext omega
    rw [scaledBrownianDoleansDadeExponential_apply, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hmgf, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring_nf

/-- Squaring a scaled Brownian stochastic exponential produces the
twice-scaled exponential times its deterministic second-moment factor. -/
theorem sq_scaledBrownianDoleansDadeExponential
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    scaledBrownianDoleansDadeExponential c B t omega ^ 2 =
      Real.exp (c ^ 2 * (t : ℝ)) *
        scaledBrownianDoleansDadeExponential (2 * c) B t omega := by
  rw [pow_two, scaledBrownianDoleansDadeExponential_apply,
    scaledBrownianDoleansDadeExponential_apply, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- The second moment of the scaled Brownian stochastic exponential is
`exp(c² t)`. -/
theorem integral_sq_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    ∫ omega, scaledBrownianDoleansDadeExponential c B t omega ^ 2 ∂P =
      Real.exp (c ^ 2 * (t : ℝ)) := by
  have heq : (fun omega =>
      scaledBrownianDoleansDadeExponential c B t omega ^ 2) =
      fun omega => Real.exp (c ^ 2 * (t : ℝ)) *
        scaledBrownianDoleansDadeExponential (2 * c) B t omega := by
    funext omega
    exact sq_scaledBrownianDoleansDadeExponential c B t omega
  rw [heq, integral_const_mul,
    integral_scaledBrownianDoleansDadeExponential hB, mul_one]

/-- Every fixed-time scaled Brownian stochastic exponential belongs to
`L²(P)`. -/
theorem memLp_two_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    MemLp (scaledBrownianDoleansDadeExponential c B t) 2 P := by
  have hmeas : AEStronglyMeasurable
      (scaledBrownianDoleansDadeExponential c B t) P := by
    change AEStronglyMeasurable (fun omega =>
      Real.exp (c * B t omega -
        (1 / 2 : ℝ) * (c ^ 2 * (t : ℝ)))) P
    exact Real.continuous_exp.comp_aestronglyMeasurable
      ((aestronglyMeasurable_const.mul
        (hB.aemeasurable t).aestronglyMeasurable).sub
          aestronglyMeasurable_const)
  rw [memLp_two_iff_integrable_sq hmeas]
  have htwice := integrable_scaledBrownianDoleansDadeExponential
    hB (2 * c) t
  have hscaled := htwice.const_mul (Real.exp (c ^ 2 * (t : ℝ)))
  exact hscaled.congr (Filter.Eventually.of_forall fun omega =>
    (sq_scaledBrownianDoleansDadeExponential c B t omega).symm)

/-- The second moments are uniformly bounded on every deterministic compact
time interval. -/
theorem integral_sq_scaledBrownianDoleansDadeExponential_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) {t T : ℝ≥0} (ht : t ≤ T) :
    ∫ omega, scaledBrownianDoleansDadeExponential c B t omega ^ 2 ∂P ≤
      Real.exp (c ^ 2 * (T : ℝ)) := by
  rw [integral_sq_scaledBrownianDoleansDadeExponential hB]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (mod_cast ht) (sq_nonneg c))

/-- A scaled Brownian stochastic exponential starts at one almost surely. -/
theorem scaledBrownianDoleansDadeExponential_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (c : ℝ) :
    scaledBrownianDoleansDadeExponential c B 0 =ᵐ[P] fun _ => 1 := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with omega hzero
  simp [hzero]

/-- Brownian continuity gives continuous paths for every scaled stochastic
exponential. -/
theorem ae_continuous_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P) (c : ℝ) :
    ∀ᵐ omega ∂P,
      Continuous (fun t =>
        scaledBrownianDoleansDadeExponential c B t omega) := by
  filter_upwards [hB.cont] with omega hcontinuous
  exact continuous_doleansDadeExponential
    (fun s omega => c * B s omega)
    (fun s _ => c ^ 2 * (s : ℝ)) omega
    (continuous_const.mul hcontinuous) (by fun_prop)

/-- The normalized exponential increment associated to `c B`. -/
def scaledBrownianDoleansDadeIncrement
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (a b : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (c * (B b omega - B a omega) -
    (1 / 2 : ℝ) * (c ^ 2 * ((b : ℝ) - (a : ℝ))))

/-- A scaled normalized increment is the stochastic exponential of the
corresponding shifted Brownian motion. -/
theorem scaledBrownianDoleansDadeIncrement_eq_shift
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) :
    scaledBrownianDoleansDadeIncrement c B a b =
      scaledBrownianDoleansDadeExponential c
        (fun s omega => B (a + s) omega - B a omega) (b - a) := by
  funext omega
  rw [scaledBrownianDoleansDadeExponential_apply]
  simp only [scaledBrownianDoleansDadeIncrement]
  congr 2
  · rw [add_comm, tsub_add_cancel_of_le hab]
  · norm_cast

/-- A normalized scaled Brownian increment is integrable. -/
theorem integrable_scaledBrownianDoleansDadeIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    Integrable (scaledBrownianDoleansDadeIncrement c B a b) P := by
  rw [scaledBrownianDoleansDadeIncrement_eq_shift c B hab]
  exact integrable_scaledBrownianDoleansDadeExponential
    (hB.shift a) c (b - a)

/-- A normalized scaled Brownian increment has expectation one. -/
theorem integral_scaledBrownianDoleansDadeIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ omega, scaledBrownianDoleansDadeIncrement c B a b omega ∂P = 1 := by
  rw [scaledBrownianDoleansDadeIncrement_eq_shift c B hab]
  exact integral_scaledBrownianDoleansDadeExponential
    (hB.shift a) c (b - a)

/-- The scaled Brownian stochastic exponential factors across two times. -/
theorem scaledBrownianDoleansDadeExponential_factor
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ) (a b : ℝ≥0) :
    scaledBrownianDoleansDadeExponential c B b =
      scaledBrownianDoleansDadeExponential c B a *
        scaledBrownianDoleansDadeIncrement c B a b := by
  funext omega
  simp only [Pi.mul_apply, scaledBrownianDoleansDadeExponential_apply,
    scaledBrownianDoleansDadeIncrement]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The scaled Brownian stochastic exponential is measurable in the natural
filtration. -/
theorem stronglyMeasurable_scaledBrownianDoleansDadeExponential_natural
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (t : ℝ≥0) :
    StronglyMeasurable[Filtration.natural B hsm t]
      (scaledBrownianDoleansDadeExponential c B t) := by
  have hBt : StronglyMeasurable[Filtration.natural B hsm t] (B t) :=
    Filtration.stronglyAdapted_natural hsm t
  change StronglyMeasurable[Filtration.natural B hsm t]
    (fun omega => Real.exp
      (c * B t omega - (1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))))
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((stronglyMeasurable_const.mul hBt).sub stronglyMeasurable_const)

/-- A normalized future scaled Brownian exponential is independent of the
natural filtration at the left endpoint. -/
theorem indep_scaledBrownianDoleansDadeIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap
        (scaledBrownianDoleansDadeIncrement c B a b) inferInstance)
      (Filtration.natural B hsm a) P := by
  have hshift := hB.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ => x (b - a)) :=
    measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hnormalizedPast :
      IndepFun (scaledBrownianDoleansDadeIncrement c B a b)
        (fun omega (t : Set.Iic a) => B t omega) P := by
    have h := hfuturePast.comp
      (show Measurable (fun x : ℝ =>
        Real.exp (c * x -
          (1 / 2 : ℝ) * (c ^ 2 * ((b : ℝ) - (a : ℝ))))) by fun_prop)
      measurable_id
    convert h using 1
    · funext omega
      simp only [Function.comp_apply, scaledBrownianDoleansDadeIncrement]
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hnormalizedPast
  have hnat : Filtration.natural B hsm a =
      MeasurableSpace.comap (fun omega (t : Set.Iic a) => B t omega)
        inferInstance := by
    rw [Filtration.natural_eq_comap]
  rw [hnat]
  exact hind

/-- For every real constant `c`, the stochastic exponential of `c B` is a
martingale in the natural Brownian filtration. -/
theorem martingale_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    Martingale (scaledBrownianDoleansDadeExponential c B)
      (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t =>
    stronglyMeasurable_scaledBrownianDoleansDadeExponential_natural hsm c t,
    fun a b hab => ?_⟩
  let future := scaledBrownianDoleansDadeIncrement c B a b
  have hfutureMeas : StronglyMeasurable future := by
    change StronglyMeasurable (fun omega =>
      Real.exp (c * (B b omega - B a omega) -
        (1 / 2 : ℝ) * (c ^ 2 * ((b : ℝ) - (a : ℝ)))))
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_const.mul ((hsm b).sub (hsm a))).sub
        stronglyMeasurable_const)
  have hfutureInt : Integrable future P :=
    integrable_scaledBrownianDoleansDadeIncrement hB c hab
  have hcurrentMeas :
      StronglyMeasurable[Filtration.natural B hsm a]
        (scaledBrownianDoleansDadeExponential c B a) :=
    stronglyMeasurable_scaledBrownianDoleansDadeExponential_natural hsm c a
  have hind : Indep (MeasurableSpace.comap future inferInstance)
      (Filtration.natural B hsm a) P :=
    indep_scaledBrownianDoleansDadeIncrement_natural hB hsm c hab
  have hcondFuture : P[future | Filtration.natural B hsm a] =ᵐ[P]
      fun _ => ∫ omega, future omega ∂P := by
    exact condExp_indep_eq
      hfutureMeas.measurable.comap_le
      ((Filtration.natural B hsm).le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl)) hind
  have hproductInt : Integrable
      (scaledBrownianDoleansDadeExponential c B a * future) P := by
    rw [← scaledBrownianDoleansDadeExponential_factor c B a b]
    exact integrable_scaledBrownianDoleansDadeExponential hB c b
  calc
    P[scaledBrownianDoleansDadeExponential c B b |
        Filtration.natural B hsm a] =
        P[scaledBrownianDoleansDadeExponential c B a * future |
          Filtration.natural B hsm a] := by
      rw [scaledBrownianDoleansDadeExponential_factor c B a b]
    _ =ᵐ[P] scaledBrownianDoleansDadeExponential c B a *
        P[future | Filtration.natural B hsm a] :=
      condExp_mul_of_stronglyMeasurable_left hcurrentMeas
        hproductInt hfutureInt
    _ =ᵐ[P] scaledBrownianDoleansDadeExponential c B a *
        (fun _ => ∫ omega, future omega ∂P) :=
      Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
    _ =ᵐ[P] scaledBrownianDoleansDadeExponential c B a := by
      have hmean : (∫ omega, future omega ∂P) = 1 :=
        integral_scaledBrownianDoleansDadeIncrement hB c hab
      filter_upwards with omega
      simp only [Pi.mul_apply, hmean, mul_one]

/-- For every real constant `c`, the stochastic exponential of `c B` is a
continuous local martingale. -/
theorem isContinuousLocalMartingale_scaledBrownianDoleansDadeExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale
      (scaledBrownianDoleansDadeExponential c B)
      (Filtration.natural B hsm) P :=
  isContinuousLocalMartingale_of_martingale
    (martingale_scaledBrownianDoleansDadeExponential
      hB.toIsPreBrownianReal hsm c)
    (ae_continuous_scaledBrownianDoleansDadeExponential hB c)

/-- Every constant multiple of Brownian motion is a martingale in the same
natural filtration. -/
theorem martingale_scaledBrownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    Martingale (fun t omega => c * B t omega)
      (Filtration.natural B hsm) P := by
  change Martingale (c • B) (Filtration.natural B hsm) P
  exact (martingale_brownian_natural hB hsm).smul c

/-- Every constant multiple of Brownian motion is a continuous local
martingale. -/
theorem isContinuousLocalMartingale_scaledBrownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale (fun t omega => c * B t omega)
      (Filtration.natural B hsm) P := by
  apply isContinuousLocalMartingale_of_martingale
    (martingale_scaledBrownian_natural hB.toIsPreBrownianReal hsm c)
  filter_upwards [hB.cont] with omega hcontinuous
  exact continuous_const.mul hcontinuous

/-- A fully discharged Doléans–Dade theorem for the continuous local
martingale `c B` and its bracket `c² t`.  This is the constant-integrand
projection of the general theorem. -/
theorem scaledBrownian_doleansDade_case
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale (fun t omega => c * B t omega)
        (Filtration.natural B hsm) P ∧
      IsContinuousLocalMartingale
        (doleansDadeExponential
          (fun t omega => c * B t omega)
          (fun t _ => c ^ 2 * (t : ℝ)))
        (Filtration.natural B hsm) P := by
  exact ⟨isContinuousLocalMartingale_scaledBrownian_natural hB hsm c,
    isContinuousLocalMartingale_scaledBrownianDoleansDadeExponential
      hB hsm c⟩

/-- The process `c B` has the bracket process `c² t`. -/
theorem hasQuadraticVariationProcess_scaledBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (c : ℝ) :
    HasQuadraticVariationProcessInProbability
      (fun t omega => c * B t omega)
      (fun t _ => c ^ 2 * (t : ℝ)) P := by
  intro t
  exact quadraticVariation_const_mul_brownian_inProbability hB c t

/-- The bracket `c² t` of `c B` is continuous, nondecreasing, and starts at
zero. -/
theorem isContinuousQuadraticVariationProcess_scaledBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (c : ℝ) :
    IsContinuousQuadraticVariationProcess
      (fun t omega => c * B t omega)
      (fun t _ => c ^ 2 * (t : ℝ)) P := by
  refine ⟨hasQuadraticVariationProcess_scaledBrownian hB c,
    Filter.Eventually.of_forall fun omega => ⟨by fun_prop, ?_⟩,
    Filter.Eventually.of_forall fun omega => by simp⟩
  intro a b hab
  exact mul_le_mul_of_nonneg_left (mod_cast hab) (sq_nonneg c)

/-- The constant-integrand projection with all three contracts visible: the
input is a continuous local martingale, `c² t` is its quadratic variation,
and its Doléans–Dade exponential is a continuous local martingale. -/
theorem scaledBrownian_doleansDade_with_bracket_case
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale (fun t omega => c * B t omega)
        (Filtration.natural B hsm) P ∧
      HasQuadraticVariationProcessInProbability
        (fun t omega => c * B t omega)
        (fun t _ => c ^ 2 * (t : ℝ)) P ∧
      IsContinuousLocalMartingale
        (doleansDadeExponential
          (fun t omega => c * B t omega)
          (fun t _ => c ^ 2 * (t : ℝ)))
        (Filtration.natural B hsm) P := by
  exact ⟨isContinuousLocalMartingale_scaledBrownian_natural hB hsm c,
    hasQuadraticVariationProcess_scaledBrownian hB c,
    isContinuousLocalMartingale_scaledBrownianDoleansDadeExponential
      hB hsm c⟩

/-- The strengthened constant-integrand projection using the continuous
quadratic-variation contract required for the general theorem. -/
theorem scaledBrownian_doleansDade_continuousBracket_case
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsContinuousLocalMartingale (fun t omega => c * B t omega)
        (Filtration.natural B hsm) P ∧
      IsContinuousQuadraticVariationProcess
        (fun t omega => c * B t omega)
        (fun t _ => c ^ 2 * (t : ℝ)) P ∧
      IsContinuousLocalMartingale
        (doleansDadeExponential
          (fun t omega => c * B t omega)
          (fun t _ => c ^ 2 * (t : ℝ)))
        (Filtration.natural B hsm) P := by
  exact ⟨isContinuousLocalMartingale_scaledBrownian_natural hB hsm c,
    isContinuousQuadraticVariationProcess_scaledBrownian hB c,
    isContinuousLocalMartingale_scaledBrownianDoleansDadeExponential
      hB hsm c⟩

end StochasticCalculus
