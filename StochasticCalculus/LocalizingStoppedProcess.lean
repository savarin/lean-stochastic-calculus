/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.ElementaryMartingaleIntegral

/-!
# Localized stopped processes

The stopped-and-indicated process behind Mathlib's local properties, the
local quadratic-variation contract with an explicit common localizer, and
the continuity, monotonicity and norm bounds of localizations at continuous
exit times.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

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

end StochasticCalculus
