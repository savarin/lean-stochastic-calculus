/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovCrossVariation

/-!
# Mixed variation under continuous stopping

The second process remains evaluated on deterministic grids. Only the first
process is stopped, so no continuity of the second process is needed.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Stopping the first process within one grid cell changes its mixed sum
from the completed upper prefix by exactly one cell contribution. -/
theorem quadraticCovariationApprox_stop_sub_grid
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (tau : W → ℝ≥0) (omega : W) {i : ℕ} (hi : i < n)
    (hleft : uniformPartitionTime T n i ≤ tau omega)
    (hright : tau omega ≤ uniformPartitionTime T n (i + 1)) :
    quadraticCovariationApprox (fun t omega ↦ X (min t (tau omega)) omega)
        Y T n omega -
      uniformStoppedCovariationApprox X Y T n
        (uniformPartitionTime T n (i + 1)) omega =
    (X (tau omega) omega - X (uniformPartitionTime T n (i + 1)) omega) *
      (Y (uniformPartitionTime T n (i + 1)) omega -
        Y (uniformPartitionTime T n i) omega) := by
  classical
  have htime := monotone_uniformPartitionTime_general T n
  have hilr := htime (Nat.le_succ i)
  unfold quadraticCovariationApprox uniformStoppedCovariationApprox
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [min_eq_right hright, min_eq_left hleft, min_self, min_eq_right hilr]
    ring
  · intro k hk hki
    rcases lt_or_gt_of_ne hki with hki | hik
    · have hkr : uniformPartitionTime T n (k + 1) ≤ tau omega :=
        (htime (Nat.succ_le_of_lt hki)).trans hleft
      have hkl : uniformPartitionTime T n k ≤ tau omega :=
        (htime (Nat.le_succ k)).trans hkr
      have hkr' : uniformPartitionTime T n (k + 1) ≤
          uniformPartitionTime T n (i + 1) := hkr.trans hright
      have hkl' : uniformPartitionTime T n k ≤
          uniformPartitionTime T n (i + 1) := hkl.trans hright
      simp only [min_eq_left hkr, min_eq_left hkl, min_eq_right hkr', min_eq_right hkl',
        sub_self]
    · have hrk : uniformPartitionTime T n (i + 1) ≤ uniformPartitionTime T n k :=
        htime (Nat.succ_le_of_lt hik)
      have hrk' : uniformPartitionTime T n (i + 1) ≤ uniformPartitionTime T n (k + 1) :=
        hrk.trans (htime (Nat.le_succ k))
      simp only [min_eq_right (hright.trans hrk), min_eq_right (hright.trans hrk'),
        min_eq_left hrk, min_eq_left hrk', sub_self, zero_mul]
  · intro hin
    exact False.elim (hin (Finset.mem_range.mpr hi))

/-- The ceiling-prefix comparison is bounded by a continuous-process
oscillation times the second process's full-grid increment maximum. -/
theorem norm_quadraticCovariationApprox_stop_sub_ceil_le
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ)
    (tau : W → ℝ≥0) (hbound : ∀ omega, tau omega ≤ T) (omega : W) :
    let hb : ∀ omega, (tau omega : WithTop ℝ≥0) ≤ T :=
      fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)
    let j := uniformPartitionCeilIndex (fun omega ↦ (tau omega : WithTop ℝ≥0))
      T (n + 1) (Nat.zero_lt_succ n) hb omega
    let r := uniformPartitionTime T (n + 1) j
    ‖quadraticCovariationApprox (fun t omega ↦ X (min t (tau omega)) omega)
        Y T (n + 1) omega - uniformStoppedCovariationApprox X Y T (n + 1) r omega‖ ≤
      ‖X (tau omega) omega - X r omega‖ * uniformPartitionMaxAbsIncrement Y T n omega := by
  intro hb j r
  have htaur : tau omega ≤ r := WithTop.coe_le_coe.mp
    (uniformPartitionCeilIndex_spec (fun omega ↦ (tau omega : WithTop ℝ≥0))
      T (n + 1) (Nat.zero_lt_succ n) hb omega)
  have hjle : j ≤ n + 1 := uniformPartitionCeilIndex_le
    (fun omega ↦ (tau omega : WithTop ℝ≥0)) T (n + 1) (Nat.zero_lt_succ n) hb omega
  by_cases hj0 : j = 0
  · have hr0 : r = 0 := by simp [r, hj0, uniformPartitionTime]
    have htau0 : tau omega = 0 := le_antisymm (hr0 ▸ htaur) bot_le
    simp only [quadraticCovariationApprox, uniformStoppedCovariationApprox,
      htau0, hr0, min_zero, zero_min, sub_self, zero_mul, Finset.sum_const_zero,
      norm_zero]
    exact le_rfl
  · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hleft : uniformPartitionTime T (n + 1) i ≤ tau omega := by
      have hnot : ¬ (tau omega : WithTop ℝ≥0) ≤
          (uniformPartitionTime T (n + 1) i : WithTop ℝ≥0) := by
        apply Nat.find_min (exists_uniformPartitionTime_ge
          (fun omega ↦ (tau omega : WithTop ℝ≥0)) T (n + 1)
          (Nat.zero_lt_succ n) hb omega)
        change i < j
        omega
      exact WithTop.coe_le_coe.mp (le_of_lt (lt_of_not_ge hnot))
    have hile : i < n + 1 := by omega
    have heq := quadraticCovariationApprox_stop_sub_grid X Y T (n + 1) tau omega
      hile hleft (by simpa only [r, hi] using htaur)
    change ‖_ - uniformStoppedCovariationApprox X Y T (n + 1) r omega‖ ≤ _
    have hr : r = uniformPartitionTime T (n + 1) (i + 1) := by dsimp only [r]; rw [hi]
    rw [hr, heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using
        abs_uniformPartition_increment_le_max Y T n omega (Finset.mem_range.mpr hile))
      (norm_nonneg _)

/-- A bounded nonnegative time rounded upwards to a uniform grid point. -/
noncomputable def uniformPartitionCeilTime
    {W : Type*} (tau : W → ℝ≥0) (T : ℝ≥0) (n : ℕ)
    (hbound : ∀ omega, tau omega ≤ T) (omega : W) : ℝ≥0 :=
  uniformPartitionTime T (n + 1)
    (uniformPartitionCeilIndex (fun omega ↦ (tau omega : WithTop ℝ≥0))
      T (n + 1) (Nat.zero_lt_succ n)
      (fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)) omega)

/-- The rounded time converges pointwise to the original time. -/
theorem tendsto_uniformPartitionCeilTime
    {W : Type*} (tau : W → ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ omega, tau omega ≤ T) (omega : W) :
    Tendsto (fun n ↦ uniformPartitionCeilTime tau T n hbound omega)
      atTop (nhds (tau omega)) := by
  apply WithTop.isEmbedding_coe.tendsto_nhds_iff.mpr
  exact tendsto_uniformPartitionCeilStoppingTime
    (fun omega ↦ (tau omega : WithTop ℝ≥0)) T
    (fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)) omega

/-- Rounding a bounded stopping time gives a measurable nonnegative time. -/
theorem measurable_uniformPartitionCeilTime
    {W : Type*} [MeasurableSpace W] {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0)))
    (T : ℝ≥0) (n : ℕ) (hbound : ∀ omega, tau omega ≤ T) :
    Measurable (uniformPartitionCeilTime tau T n hbound) := by
  let hb := fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)
  have hstop := isStoppingTime_uniformPartitionCeilStoppingTime htau T (n + 1)
    (Nat.zero_lt_succ n) hb
  have hmeas := (hstop.measurable_of_le (uniformPartitionCeilStoppingTime_le
    (fun omega ↦ (tau omega : WithTop ℝ≥0)) T (n + 1)
    (Nat.zero_lt_succ n) hb)).mono (V.le T) le_rfl
  exact hmeas.untopA

/-- Continuous processes with measurable sections can be evaluated at a
measurable random time. No adaptation of the process is required. -/
theorem stronglyMeasurable_continuous_random_eval
    {W : Type*} [MeasurableSpace W] {X : ℝ≥0 → W → ℝ}
    (hXcont : ∀ omega, Continuous fun t ↦ X t omega)
    (hXmeas : ∀ t, StronglyMeasurable (X t))
    {tau : W → ℝ≥0} (htau : Measurable tau) :
    StronglyMeasurable (fun omega ↦ X (tau omega) omega) :=
  (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hXcont hXmeas).comp_measurable
    (htau.prodMk measurable_id)

set_option linter.style.longLine false in
/-- The crossing-cell error vanishes when the first process is continuous
and the second has the Brownian deterministic-grid increment estimate. -/
theorem tendstoInMeasure_quadraticCovariation_stop_sub_ceil
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X B : ℝ≥0 → W → ℝ}
    (hXcont : ∀ omega, Continuous fun t ↦ X t omega)
    (hXmeas : ∀ t, StronglyMeasurable (X t)) (hB : IsPreBrownianReal B P)
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P (fun n omega ↦
      quadraticCovariationApprox (fun t omega ↦ X (min t (tau omega)) omega)
          B T (n + 1) omega -
        uniformStoppedCovariationApprox X B T (n + 1)
          (uniformPartitionCeilTime tau T n hbound omega) omega) atTop (fun _ ↦ 0) := by
  have htauMeas : Measurable tau :=
    ((htau.measurable_of_le (fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega))).mono
      (V.le T) le_rfl).untopA
  have hXa := stronglyMeasurable_continuous_random_eval hXcont hXmeas htauMeas
  have hXr (n : ℕ) := stronglyMeasurable_continuous_random_eval hXcont hXmeas
    (measurable_uniformPartitionCeilTime htau T n hbound)
  have hosc : TendstoInMeasure P (fun n omega ↦ X (tau omega) omega -
      X (uniformPartitionCeilTime tau T n hbound omega) omega) atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (hXa.sub (hXr n)).aestronglyMeasurable)
    filter_upwards with omega
    simpa only [Function.comp_apply, Pi.sub_apply, sub_self] using
      (tendsto_const_nhds (x := X (tau omega) omega)).sub
      ((hXcont omega).tendsto (tau omega) |>.comp
        (tendsto_uniformPartitionCeilTime tau T hbound omega))
  apply TendstoInMeasure.of_norm_sub_le_mul_of_eventually_tight hosc
    (fun n omega ↦ uniformPartitionMaxAbsIncrement_nonneg B T n omega)
    ((uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero hB
    T).eventually_tight_of_limit_tails
        (StronglyMeasurable.exists_measureReal_ge_lt_finite
          (show StronglyMeasurable (fun _ : W ↦ (0 : ℝ)) from stronglyMeasurable_const)))
  intro n omega
  simpa only [sub_zero, uniformPartitionCeilTime] using
    norm_quadraticCovariationApprox_stop_sub_ceil_le X B T n tau hbound omega

/-- Mixed variation survives bounded stopping of its continuous first
process. The compensator may be represented by a timewise-a.e. continuous
version, even when that version is not itself adapted. -/
theorem tendstoInMeasure_quadraticCovariation_stop_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X B C D : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : ∀ U, U ≤ T → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X B U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hBmart : Martingale B V P)
    (hB : IsPreBrownianReal B P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hB4 : ∀ t, MemLp (B t) 4 P)
    (hXcont : ∀ omega, Continuous fun t ↦ X t omega)
    (hDcont : ∀ omega, Continuous fun t ↦ D t omega)
    (hDmeas : ∀ t, StronglyMeasurable (D t)) (hCD : ∀ t, C t =ᵐ[P] D t)
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0)))
    (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P (fun n ↦
      quadraticCovariationApprox (fun t omega ↦ X (min t (tau omega)) omega)
        B T (n + 1)) atTop (fun omega ↦ D (tau omega) omega) := by
  let hb := fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)
  let j := fun n ↦ uniformPartitionCeilIndex (fun omega ↦ (tau omega : WithTop ℝ≥0))
    T (n + 1) (Nat.zero_lt_succ n) hb
  have hj (n : ℕ) (omega : W) : j n omega ≤ n + 1 :=
    uniformPartitionCeilIndex_le (fun omega ↦ (tau omega : WithTop ℝ≥0))
      T (n + 1) (Nat.zero_lt_succ n) hb omega
  let r := fun n ↦ uniformPartitionCeilTime tau T n hbound
  have hp := tendstoInMeasure_uniformStoppedCovariation_random_grid_error
    h hX hBmart hC hCzero hX4 hB4 j hj
  have hpD : TendstoInMeasure P (fun n omega ↦
      uniformStoppedCovariationApprox X B T (n + 1) (r n omega) omega -
        D (r n omega) omega) atTop (fun _ ↦ 0) := by
    apply hp.congr_left
    intro n
    filter_upwards [ae_all_iff.mpr (fun i : ℕ ↦ hCD (uniformPartitionTime T (n + 1) i))]
      with omega homega
    change _ - C (r n omega) omega = _ - D (r n omega) omega
    rw [show C (r n omega) omega = D (r n omega) omega from homega (j n omega)]
    rfl
  have htauMeas : Measurable tau :=
    ((htau.measurable_of_le hb).mono (V.le T) le_rfl).untopA
  have hDa := stronglyMeasurable_continuous_random_eval hDcont hDmeas htauMeas
  have hDr (n : ℕ) := stronglyMeasurable_continuous_random_eval hDcont hDmeas
    (measurable_uniformPartitionCeilTime htau T n hbound)
  have hDosc : TendstoInMeasure P (fun n omega ↦ D (r n omega) omega -
      D (tau omega) omega) atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hDr n).sub hDa).aestronglyMeasurable)
    filter_upwards with omega
    simpa only [Function.comp_apply, Pi.sub_apply, sub_self] using
      (((hDcont omega).tendsto (tau omega)).comp
        (tendsto_uniformPartitionCeilTime tau T hbound omega)).sub
        (tendsto_const_nhds (x := D (tau omega) omega))
  have hcrossing := tendstoInMeasure_quadraticCovariation_stop_sub_ceil hXcont
    (fun t ↦ (hX.stronglyAdapted t).mono (V.le t)) hB htau T hbound
  have hprefix := TendstoInMeasure.sub_chain_normed_noMeas hcrossing hpD
  have hfinal := TendstoInMeasure.sub_chain_normed_noMeas hprefix hDosc
  rw [tendstoInMeasure_iff_norm] at hfinal ⊢
  simpa only [sub_zero] using hfinal

/-- A deterministic horizon truncation of the stopping rule has no effect
on mixed sums sampled below that horizon. -/
theorem quadraticCovariationApprox_stop_min_horizon
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (tau : W → ℝ≥0) :
    quadraticCovariationApprox (fun t omega ↦ X (min t (min T (tau omega))) omega)
      Y T (n + 1) =
    quadraticCovariationApprox (fun t omega ↦ X (min t (tau omega)) omega) Y T (n + 1) := by
  funext omega
  unfold quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hl := (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
    ((Nat.le_succ i).trans hi1)).2
  have hr := (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hi1).2
  dsimp only
  rw [← min_assoc, ← min_assoc, min_eq_left hr, min_eq_left hl]

/-- Cross variation is stable under stopping its continuous L4 martingale
argument, while the pre-Brownian argument remains unstopped. -/
theorem HasCrossVariationProcessInProbability.stop_left_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X B C D : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X B C P)
    (hX : Martingale X V P) (hBmart : Martingale B V P)
    (hB : IsPreBrownianReal B P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hB4 : ∀ t, MemLp (B t) 4 P)
    (hXcont : ∀ omega, Continuous fun t ↦ X t omega)
    (hDcont : ∀ omega, Continuous fun t ↦ D t omega)
    (hDmeas : ∀ t, StronglyMeasurable (D t)) (hCD : ∀ t, C t =ᵐ[P] D t)
    {tau : W → ℝ≥0} (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0))) :
    HasCrossVariationProcessInProbability (fun t omega ↦ X (min t (tau omega)) omega)
      B (fun t omega ↦ D (min t (tau omega)) omega) P := by
  intro T
  have htau' : IsStoppingTime V
      (fun omega ↦ ((min T (tau omega)) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const V T).min htau
  have hlimit := tendstoInMeasure_quadraticCovariation_stop_of_memLp_four
    (fun U _ ↦ h U) hX hBmart hB hC hCzero hX4 hB4 hXcont hDcont hDmeas hCD
    htau' (fun omega ↦ min_le_left T (tau omega))
  simpa only [quadraticCovariationApprox_stop_min_horizon] using hlimit

end StochasticCalculus
