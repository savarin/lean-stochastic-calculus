/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.WeightedBracketRiemann
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Local martingales and quadratic-variation contracts

Continuous local martingales through Mathlib's `Locally` predicate, the
quadratic-variation contracts in probability at fixed times, before a
deterministic stop, and stopped, their instances for pre-Brownian motion,
and the `Lᵖ` and stopping facts about martingales that the later layers use.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- A real process is a local martingale when its indicated stopped processes
are martingales along a Mathlib localizing sequence. -/
@[expose] def IsLocalMartingale
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) : Prop :=
  Locally (fun N => Martingale N 𝓕 P) 𝓕 M P

/-- A continuous local martingale has a local-martingale localization and
almost-everywhere continuous sample paths. -/
@[expose] def IsContinuousLocalMartingale
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) : Prop :=
  IsLocalMartingale M 𝓕 P ∧
    ∀ᵐ omega ∂P, Continuous (fun t => M t omega)

/-- A process-valued quadratic variation: at every fixed time, the uniform
partition squared-increment sums converge in probability to the selected
bracket value. -/
@[expose] def HasQuadraticVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ t, HasQuadraticVariationInProbabilityAt M P t (bracket t)

/-- A process-level quadratic-variation contract robust under truncating a
fine uniform grid at any earlier deterministic time.  This is strictly the
interface needed by two-scale weighted-bracket arguments; fixed-time uniform
partitions alone do not provide it. -/
@[expose] def HasQuadraticVariationBeforeStopProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (M bracket : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ T a, TendstoInMeasure P
    (fun n ↦ quadraticVariationBeforeStopApprox M T (n + 1) a)
    Filter.atTop (bracket (min T a))

/-- Completed-cell covariation before a deterministic cutoff on a fixed
uniform horizon. -/
@[expose] noncomputable def quadraticCovariationBeforeStopApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (a : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    if uniformPartitionTime T n (i + 1) ≤ a then
      (X (uniformPartitionTime T n (i + 1)) omega -
        X (uniformPartitionTime T n i) omega) *
      (Y (uniformPartitionTime T n (i + 1)) omega -
        Y (uniformPartitionTime T n i) omega)
    else 0

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
@[expose] def HasStoppedQuadraticVariationProcessInProbability
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

end StochasticCalculus
