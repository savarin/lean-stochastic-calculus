/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.LocalizingStoppedProcess

/-!
# Partition-valued stopping times

The first uniform-partition index at or after a bounded stopping rule,
martingality of bounded stopped processes and of localizations at
continuous exit times, adaptedness of localizations, and convergence in
measure through uniform approximations.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

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
an approximation whose error tends to zero in measure uniformly in the
outer index.  This version asks directly for the uniform probability estimate and
therefore does not require a pointwise random majorant. -/
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

end StochasticCalculus
