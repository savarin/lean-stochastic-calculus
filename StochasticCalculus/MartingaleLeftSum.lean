/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.PartitionStoppingTime

/-!
# Left sums against a martingale

Finite elementary stochastic integrals and the uniformly adapted left-sum
process, their martingale property, terminal `L²` bounds, double
localization at continuous exits, and the `L²` control of localized
differences.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

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
    rw [ite_eq_left htauMem, ite_eq_left hsigmaMem, ite_eq_left hminMem]
  · have htauMem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hsigmaMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < sigma omega} :=
      hsigma
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_right ((⊥ : WithTop ℝ≥0) < tau omega) hsigma)
    rw [ite_eq_left htauMem, ite_eq_right hsigmaMem, ite_eq_right hminMem]
  · have htauMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_left ((⊥ : WithTop ℝ≥0) < sigma omega) htau)
    rw [ite_eq_right htauMem, ite_eq_right hminMem]
  · have htauMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := htau
    have hminMem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) <
        min (tau omega) (sigma omega)} := by
      simpa only [Set.mem_ofPred_eq, lt_min_iff] using
        (not_and_of_not_left ((⊥ : WithTop ℝ≥0) < sigma omega) htau)
    rw [ite_eq_right htauMem, ite_eq_right hminMem]

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
      exact ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul hDelta.aestronglyMeasurable
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
      ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul (hd2 i).aestronglyMeasurable
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
      ((hH _).mono (𝓥.le _)).aestronglyMeasurable.mul hDelta.aestronglyMeasurable
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
  rw [← ENNReal.toReal_le_toReal hprocess2.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hdelta2.eLpNorm_ne_top)]
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

end StochasticCalculus
