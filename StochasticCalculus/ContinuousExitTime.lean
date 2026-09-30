/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.LocalMartingaleContract

/-!
# Continuous exit times

Uniform-partition sampling and hitting times, dyadic hitting times of the
complement of a closed ball, the continuous exit time as their limit with
its stopping-time property and bounds, and the global exit sequences that
localize a continuous process.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Sample a continuous-time process on a deterministic uniform grid. -/
@[expose] def uniformPartitionSample
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
@[expose] noncomputable def uniformPartitionHittingTimeNNReal
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

/-- The closed complement of the real ball of radius `R`. -/
def outsideClosedBall (R : ℝ≥0) : Set ℝ := {x | (R : ℝ) ≤ |x|}

/-- First visit to the complement of the radius-`R` ball on the dyadic grid
of level `n`, mapped back to continuous nonnegative time. -/
@[expose] noncomputable def dyadicHittingTimeNNReal
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T R : ℝ≥0) (n : ℕ) :
    W → WithTop ℝ≥0 :=
  uniformPartitionHittingTimeNNReal M T (2 ^ n) (outsideClosedBall R)

/-- The pointwise minimum of two dyadic-grid exit rules on the same grid. -/
@[expose] noncomputable def pairedDyadicHittingTimeNNReal
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
          simp only [hn, hittingBtwn, ite_eq_right hex]
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
@[expose] noncomputable def continuousExitTime
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
      rw [ite_eq_right hnone]]
    change (uniformPartitionTime T (2 ^ n) (2 ^ n) : WithTop ℝ≥0) = T
    apply WithTop.coe_eq_coe.mpr
    unfold uniformPartitionTime
    apply mul_div_cancel_right₀
    exact_mod_cast (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  unfold continuousExitTime
  simp_rw [hdyadic]
  exact iInf_const

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
@[expose] noncomputable def globalContinuousExitSequence
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
@[expose] noncomputable def globalPairedContinuousExitSequence
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
@[expose] def beforeContinuousExitProcessOf
    {W : Type*} (Z H : ℝ≥0 → W → ℝ) (T R : ℝ≥0) :
    ℝ≥0 → W → ℝ :=
  fun t => {omega | (t : WithTop ℝ≥0) < continuousExitTime Z T R omega}.indicator
    (H t)

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

end StochasticCalculus
