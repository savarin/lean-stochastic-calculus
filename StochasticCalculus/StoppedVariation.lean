/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.Girsanov
import StochasticCalculus.GirsanovMoments

/-!
# Random cutoffs of variation approximations

Monotone completed-cell sums admit a finite-grid sandwich. A continuous
monotone limit then permits evaluation at an arbitrary bounded random
cutoff, without assuming sample-path regularity of an unrelated integrator.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- A fixed-coarse error vanishing with the fine mesh, plus a coarse error
vanishing with the coarse mesh, proves convergence in probability. -/
theorem TendstoInMeasure.of_two_scale_error_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {f : ℕ → W → ℝ} {g : W → ℝ}
    {R : ℕ → ℕ → W → ℝ} {H : ℕ → W → ℝ}
    (hR : ∀ k, TendstoInMeasure P (R k) atTop (fun _ ↦ 0))
    (hH : TendstoInMeasure P H atTop (fun _ ↦ 0))
    (hbound : ∀ k n omega, ‖f n omega - g omega‖ ≤
      ‖R k n omega‖ + ‖H k omega‖) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hHprob := (tendstoInMeasure_iff_measureReal_norm.mp hH)
    (epsilon / 2) (half_pos hepsilon)
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hHprob) (delta / 2) (half_pos hdelta)
  have hHsmall : P.real {omega | epsilon / 2 ≤ ‖H k omega‖} < delta / 2 := by
    simpa only [sub_zero, Real.dist_eq, abs_of_nonneg measureReal_nonneg] using hk k le_rfl
  have hRprob := (tendstoInMeasure_iff_measureReal_norm.mp (hR k))
    (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hRprob) (delta / 2) (half_pos hdelta)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hRsmall : P.real {omega | epsilon / 2 ≤ ‖R k n omega‖} < delta / 2 := by
    simpa only [sub_zero, Real.dist_eq, abs_of_nonneg measureReal_nonneg] using hN n hn
  have hsubset : {omega | epsilon ≤ ‖f n omega - g omega‖} ⊆
      {omega | epsilon / 2 ≤ ‖R k n omega‖} ∪
        {omega | epsilon / 2 ≤ ‖H k omega‖} := by
    intro omega homega
    change epsilon ≤ ‖f n omega - g omega‖ at homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have h := hbound k n omega
    linarith
  have hsmall : P.real {omega | epsilon ≤ ‖f n omega - g omega‖} < delta := by
    calc
      _ ≤ P.real ({omega | epsilon / 2 ≤ ‖R k n omega‖} ∪
          {omega | epsilon / 2 ≤ ‖H k omega‖}) := measureReal_mono hsubset
      _ ≤ P.real {omega | epsilon / 2 ≤ ‖R k n omega‖} +
          P.real {omega | epsilon / 2 ≤ ‖H k omega‖} := measureReal_union_le _ _
      _ < delta / 2 + delta / 2 := add_lt_add hRsmall hHsmall
      _ = delta := by ring
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hsmall

/-- A monotone function is controlled at every point by its values on a
finite grid and the largest grid increment of a monotone comparison. -/
theorem norm_monotone_sub_le_uniformPartition_error
    {W : Type*} (F G : ℝ≥0 → W → ℝ) (T : ℝ≥0) (k : ℕ) (omega : W)
    (hF : Monotone fun t ↦ F t omega) (hG : Monotone fun t ↦ G t omega)
    {a : ℝ≥0} (haT : a ≤ T) :
    ‖F a omega - G a omega‖ ≤
      (∑ i ∈ Finset.range (k + 2),
        ‖F (uniformPartitionTime T (k + 1) i) omega -
          G (uniformPartitionTime T (k + 1) i) omega‖) +
        uniformPartitionMaxAbsIncrement G T k omega := by
  classical
  let tau : Unit → WithTop ℝ≥0 := fun _ ↦ (a : WithTop ℝ≥0)
  have hbound : ∀ x, tau x ≤ (T : WithTop ℝ≥0) :=
    fun _ ↦ WithTop.coe_le_coe.mpr haT
  let j := uniformPartitionCeilIndex tau T (k + 1) (Nat.zero_lt_succ k) hbound ()
  let S := ∑ i ∈ Finset.range (k + 2),
    ‖F (uniformPartitionTime T (k + 1) i) omega -
      G (uniformPartitionTime T (k + 1) i) omega‖
  have herr (i : ℕ) (hi : i ≤ k + 1) :
      ‖F (uniformPartitionTime T (k + 1) i) omega -
        G (uniformPartitionTime T (k + 1) i) omega‖ ≤ S := by
    exact Finset.single_le_sum (s := Finset.range (k + 2)) (a := i)
      (f := fun i ↦ ‖F (uniformPartitionTime T (k + 1) i) omega -
        G (uniformPartitionTime T (k + 1) i) omega‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hj : j ≤ k + 1 :=
    uniformPartitionCeilIndex_le tau T (k + 1) (Nat.zero_lt_succ k) hbound ()
  have hau : a ≤ uniformPartitionTime T (k + 1) j :=
    WithTop.coe_le_coe.mp
      (uniformPartitionCeilIndex_spec tau T (k + 1) (Nat.zero_lt_succ k) hbound ())
  by_cases hj0 : j = 0
  · have ha0 : a = 0 := by
      simpa only [hj0, uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        nonpos_iff_eq_zero] using hau
    have he := herr 0 (by omega)
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div] at he
    rw [ha0]
    exact he.trans (le_add_of_nonneg_right
      (uniformPartitionMaxAbsIncrement_nonneg G T k omega))
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hla : uniformPartitionTime T (k + 1) i ≤ a := by
    have hnot : ¬ tau () ≤ (uniformPartitionTime T (k + 1) i : WithTop ℝ≥0) := by
      apply Nat.find_min (exists_uniformPartitionTime_ge tau T (k + 1)
        (Nat.zero_lt_succ k) hbound ())
      change i < j
      omega
    exact (WithTop.coe_le_coe.mp (le_of_lt (lt_of_not_ge hnot)))
  have huerr := herr j hj
  have hlerr := herr i (by omega)
  have hgap : G (uniformPartitionTime T (k + 1) j) omega -
      G (uniformPartitionTime T (k + 1) i) omega ≤
        uniformPartitionMaxAbsIncrement G T k omega := by
    rw [hi]
    exact (le_abs_self _).trans (abs_uniformPartition_increment_le_max G T k omega
      (Finset.mem_range.mpr (by omega)))
  have hFl := hF hla
  have hFu := hF hau
  have hGl := hG hla
  have hGu := hG hau
  rw [Real.norm_eq_abs, abs_le] at hlerr huerr ⊢
  change -S ≤ _ ∧ _ ≤ S at hlerr huerr
  change -(S + _) ≤ _ ∧ _ ≤ S + _
  constructor <;> linarith [hlerr.1, huerr.2]

/-- Finitely many errors vanishing in probability have a vanishing sum of
norms, with no extra measurability premise. -/
theorem TendstoInMeasure.finset_sum_norm_sub
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (S : Finset I) {F : I → ℕ → W → ℝ} {G : I → W → ℝ}
    (h : ∀ i ∈ S, TendstoInMeasure P (F i) atTop (G i)) :
    TendstoInMeasure P (fun n omega ↦ ∑ i ∈ S, ‖F i n omega - G i omega‖)
      atTop (fun _ ↦ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      exact Filter.Eventually.of_forall fun _ ↦ tendsto_const_nhds
  | @insert i S hi hind =>
      have hhead := h i (Finset.mem_insert_self i S)
      have hnorm : TendstoInMeasure P
          (fun n omega ↦ ‖F i n omega - G i omega‖) atTop (fun _ ↦ 0) := by
        rw [tendstoInMeasure_iff_norm] at hhead ⊢
        simpa only [sub_zero, Real.norm_eq_abs, abs_abs] using hhead
      have htail := hind (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi, zero_add] using hnorm.add_real_noMeas htail

/-- Pointwise convergence in probability of monotone processes to a
continuous monotone limit can be evaluated at any bounded random cutoff.
The finite-grid bound is uniform in the cutoff, so the cutoff itself need
not be measurable for this convergence-in-outer-measure conclusion. -/
theorem tendstoInMeasure_monotone_random_cutoff
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {F : ℕ → ℝ≥0 → W → ℝ} {G : ℝ≥0 → W → ℝ}
    (hF : ∀ n omega, Monotone fun t ↦ F n t omega)
    (hG : ∀ omega, Monotone fun t ↦ G t omega)
    (hGmeas : ∀ t, StronglyMeasurable (G t))
    (hGcont : ∀ omega, Continuous fun t ↦ G t omega)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ F n t) atTop (G t))
    (T : ℝ≥0) (tau : W → ℝ≥0) (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P (fun n omega ↦ F n (tau omega) omega)
      atTop (fun omega ↦ G (tau omega) omega) := by
  let R : ℕ → ℕ → W → ℝ := fun k n omega ↦
    ∑ i ∈ Finset.range (k + 2),
      ‖F n (uniformPartitionTime T (k + 1) i) omega -
        G (uniformPartitionTime T (k + 1) i) omega‖
  have hR (k : ℕ) : TendstoInMeasure P (R k) atTop (fun _ ↦ 0) :=
    TendstoInMeasure.finset_sum_norm_sub (Finset.range (k + 2))
      (fun i _ ↦ hconv (uniformPartitionTime T (k + 1) i))
  have hRnonneg (k n : ℕ) (omega : W) : 0 ≤ R k n omega :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hH := uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous (P := P)
    hGmeas hGcont T
  apply TendstoInMeasure.of_two_scale_error_bound hR hH
  intro k n omega
  rw [Real.norm_of_nonneg (hRnonneg k n omega),
    Real.norm_of_nonneg (uniformPartitionMaxAbsIncrement_nonneg G T k omega)]
  exact norm_monotone_sub_le_uniformPartition_error
    (F n) G T k omega (hF n omega) (hG omega) (hbound omega)

/-- Completed-cell scalar quadratic sums are monotone in their cutoff. -/
theorem monotone_quadraticVariationBeforeStopApprox
    {W : Type*} (M : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W) :
    Monotone fun a ↦ quadraticVariationBeforeStopApprox M T n a omega := by
  intro a b hab
  unfold quadraticVariationBeforeStopApprox
  apply Finset.sum_le_sum
  intro i _hi
  by_cases ha : uniformPartitionTime T n (i + 1) ≤ a
  · simp only [ha, ha.trans hab, ↓reduceIte, le_refl]
  · by_cases hb : uniformPartitionTime T n (i + 1) ≤ b
    · simp only [ha, hb, ↓reduceIte]
      exact sq_nonneg _
    · simp only [ha, hb, ↓reduceIte, le_refl]

/-- A robust scalar bracket remains the limit when the completed-cell
cutoff is selected separately on every sample. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.random_cutoff
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P)
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hcont : ∀ omega, Continuous fun t ↦ bracket t omega)
    (hmono : ∀ omega, Monotone fun t ↦ bracket t omega)
    (T : ℝ≥0) (tau : W → ℝ≥0) (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P
      (fun n omega ↦ quadraticVariationBeforeStopApprox M T (n + 1) (tau omega) omega)
      atTop (fun omega ↦ bracket (tau omega) omega) := by
  have hraw := tendstoInMeasure_monotone_random_cutoff
    (fun n omega ↦ monotone_quadraticVariationBeforeStopApprox M T (n + 1) omega)
    (fun omega ↦ (hmono omega).comp (monotone_const.min monotone_id))
    (fun a ↦ hbracket (min T a))
    (fun omega ↦ (hcont omega).comp (continuous_const.min continuous_id))
    (h T) T tau hbound
  apply hraw.congr_right
  exact Filter.Eventually.of_forall fun omega ↦ by
    change bracket (min T (tau omega)) omega = bracket (tau omega) omega
    rw [min_eq_right (hbound omega)]

/-- The partial-cell square at a measurable random cutoff is measurable
when the integrator has measurable sections and continuous paths. -/
theorem stronglyMeasurable_quadraticVariationCrossingStop_random
    {W : Type*} [MeasurableSpace W] {M : ℝ≥0 → W → ℝ}
    (hM : ∀ t, StronglyMeasurable (M t))
    (hcont : ∀ omega, Continuous fun t ↦ M t omega)
    (T : ℝ≥0) (n : ℕ) {tau : W → ℝ≥0} (htau : Measurable tau) :
    StronglyMeasurable
      (fun omega ↦ quadraticVariationCrossingStopApprox M T n (tau omega) omega) := by
  classical
  have hMtau : StronglyMeasurable (fun omega ↦ M (tau omega) omega) :=
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hM).comp_measurable
      (htau.prodMk measurable_id)
  unfold quadraticVariationCrossingStopApprox uniformPartitionCrossingCells
  simp only [Finset.sum_filter]
  apply Finset.stronglyMeasurable_fun_sum
  intro i _hi
  apply StronglyMeasurable.ite
    ((measurableSet_le measurable_const htau).inter
      (measurableSet_le measurable_const htau).compl)
  · exact (hMtau.sub (hM _)).pow 2
  · exact stronglyMeasurable_const

/-- Continuity removes the unique partial cell at any measurable random
cutoff bounded by the grid horizon. -/
theorem tendstoInMeasure_quadraticVariationCrossingStop_random
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M : ℝ≥0 → W → ℝ}
    (hM : ∀ t, StronglyMeasurable (M t))
    (hcont : ∀ omega, Continuous fun t ↦ M t omega)
    (T : ℝ≥0) {tau : W → ℝ≥0} (htau : Measurable tau)
    (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P
      (fun n omega ↦ quadraticVariationCrossingStopApprox M T (n + 1) (tau omega) omega)
      atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (stronglyMeasurable_quadraticVariationCrossingStop_random
      hM hcont T (n + 1) htau).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      quadraticVariationCrossingStopApprox_tendsto_zero_of_continuousOn
        M T (tau omega) omega ⟨bot_le, hbound omega⟩ (hcont omega).continuousOn

/-- A continuous process with a robust bracket retains its ordinary
quadratic variation after a measurable random stop bounded by the horizon. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.quadraticVariation_random_stop_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P)
    (hM : ∀ t, StronglyMeasurable (M t))
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega)
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hcont : ∀ omega, Continuous fun t ↦ bracket t omega)
    (hmono : ∀ omega, Monotone fun t ↦ bracket t omega)
    (T : ℝ≥0) {tau : W → ℝ≥0} (htau : Measurable tau)
    (hbound : ∀ omega, tau omega ≤ T) :
    TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox (fun t omega ↦ M (min t (tau omega)) omega)
        T (n + 1)) atTop (fun omega ↦ bracket (tau omega) omega) := by
  have hb := h.random_cutoff hbracket hcont hmono T tau hbound
  have hc := tendstoInMeasure_quadraticVariationCrossingStop_random
    (P := P) hM hMcont T htau hbound
  have hsum := hb.add_real_noMeas hc
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      simpa only [quadraticVariationApprox] using
        (quadraticVariationApprox_stop_eq_before_add_crossing M T (n + 1)
          (tau omega) omega).symm
  · exact Filter.Eventually.of_forall fun _ ↦ add_zero _

/-- The random stop need not be bounded by the observation horizon: its
minimum with that horizon selects the same stopped grid values. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.quadraticVariation_random_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P)
    (hM : ∀ t, StronglyMeasurable (M t))
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega)
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hcont : ∀ omega, Continuous fun t ↦ bracket t omega)
    (hmono : ∀ omega, Monotone fun t ↦ bracket t omega)
    (T : ℝ≥0) {tau : W → ℝ≥0} (htau : Measurable tau) :
    TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox (fun t omega ↦ M (min t (tau omega)) omega)
        T (n + 1)) atTop (fun omega ↦ bracket (min T (tau omega)) omega) := by
  have hraw := h.quadraticVariation_random_stop_le hM hMcont hbracket hcont hmono T
    (measurable_const.min htau) (fun omega ↦ min_le_left T (tau omega))
  apply hraw.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    simpa only [quadraticVariationApprox] using
      (quadraticVariationApprox_stop_eq_min_horizon M T (tau omega) (n + 1) omega).symm

/-- Robust quadratic variation is stable under measurable random stopping
of a continuous real process with a continuous increasing bracket. -/
theorem HasQuadraticVariationBeforeStopProcessInProbability.random_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationBeforeStopProcessInProbability M bracket P)
    (hM : ∀ t, StronglyMeasurable (M t))
    (hMcont : ∀ omega, Continuous fun t ↦ M t omega)
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hcont : ∀ omega, Continuous fun t ↦ bracket t omega)
    (hmono : ∀ omega, Monotone fun t ↦ bracket t omega)
    {tau : W → ℝ≥0} (htau : Measurable tau) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun t omega ↦ M (min t (tau omega)) omega)
      (fun t omega ↦ bracket (min t (tau omega)) omega) P := by
  have hstopped : HasStoppedQuadraticVariationProcessInProbability
      (fun t omega ↦ M (min t (tau omega)) omega)
      (fun t omega ↦ bracket (min t (tau omega)) omega) P := by
    intro T a
    have hraw := h.quadraticVariation_random_stop hM hMcont hbracket hcont hmono T
      (measurable_const.min htau : Measurable fun omega ↦ min a (tau omega))
    simpa only [min_assoc] using hraw
  apply hstopped.toBeforeStop
  · intro t
    exact ((stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      hMcont hM).comp_measurable
        ((measurable_const.min htau).prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      (hMcont omega).comp (continuous_id.min continuous_const)

/-- The bounded real-valued stopping convention is the literal minimum of
the observation time and the random cutoff. -/
theorem stoppedProcess_coe_nnreal
    {W E : Type*} (M : ℝ≥0 → W → E) (tau : W → ℝ≥0) :
    stoppedProcess M (fun omega ↦ (tau omega : WithTop ℝ≥0)) =
      fun t omega ↦ M (min t (tau omega)) omega := by
  funext t omega
  simp only [stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

/-- Stopping before the Novikov horizon preserves the full common-localizer
density contract. The stopped real integrator is already a true martingale,
so the constant infinite localizer realizes its robust bracket. -/
theorem GirsanovDensityData.stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) {tau : W → ℝ≥0}
    (htau : IsStoppingTime V (fun omega ↦ (tau omega : WithTop ℝ≥0)))
    (hbound : ∀ omega, tau omega ≤ T) :
    GirsanovDensityData P V
      (fun t omega ↦ M (min t (tau omega)) omega)
      (fun t omega ↦ bracket (min t (tau omega)) omega) T := by
  let N : ℝ≥0 → W → ℝ := fun t ↦ M (min t T)
  let S : ℝ≥0 → W → ℝ := fun t omega ↦ M (min t (tau omega)) omega
  let A : ℝ≥0 → W → ℝ := fun t omega ↦ bracket (min t (tau omega)) omega
  have hbound' : ∀ omega, (tau omega : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) :=
    fun omega ↦ WithTop.coe_le_coe.mpr (hbound omega)
  have htauMeas : Measurable tau :=
    ((htau.measurable_of_le hbound').untopA).mono (V.le T) le_rfl
  have hN : Martingale N V P := h.martingale_stopAt_martingale
  have hNcont (omega : W) : Continuous fun t ↦ N t omega :=
    (h.continuous_martingale_path omega).comp (continuous_id.min continuous_const)
  have hS : Martingale S V P := by
    have hstop := martingale_stoppedProcess_of_bounded hN hNcont htau T hbound'
    have heq : stoppedProcess N (fun omega ↦ (tau omega : WithTop ℝ≥0)) = S := by
      rw [stoppedProcess_coe_nnreal]
      funext t omega
      dsimp only [N, S]
      rw [min_eq_left ((min_le_right t (tau omega)).trans (hbound omega))]
    rwa [heq] at hstop
  have hAadapt : StronglyAdapted V A := by
    simpa only [stoppedProcess_coe_nnreal, A] using
      ((h.adapted_bracket.isStronglyProgressive_of_continuous
        (fun omega ↦ (h.continuous_monotone_bracket omega).1)).stronglyAdapted_stoppedProcess
          htau)
  have hQV : HasQuadraticVariationBeforeStopProcessInProbability S A P :=
    h.localQuadraticVariation.toBeforeStop.random_stop
      (fun t ↦ (h.adapted_martingale t).mono (V.le t))
      h.continuous_martingale_path
      (fun t ↦ (h.adapted_bracket t).mono (V.le t))
      (fun omega ↦ (h.continuous_monotone_bracket omega).1)
      (fun omega ↦ (h.continuous_monotone_bracket omega).2) htauMeas
  have hlocal : HasLocalQuadraticVariationProcessInProbability S A V P := by
    have hSloc : localizingStoppedProcess S (fun _ ↦ ⊤) = S := by
      funext t omega
      simp [localizingStoppedProcess]
    have hAloc : localizingStoppedProcess A (fun _ ↦ ⊤) = A := by
      funext t omega
      simp [localizingStoppedProcess]
    refine ⟨fun _ _ ↦ ⊤, isLocalizingSequence_const_top V P, ?_, ?_⟩
    · intro n
      simpa only [hSloc] using hS
    · intro n
      simpa only [hSloc, hAloc] using hQV
  refine
    { novikov := ?_
      localQuadraticVariation := hlocal
      continuous_martingale_path := fun omega ↦
        (h.continuous_martingale_path omega).comp (continuous_id.min continuous_const)
      adapted_martingale := hS.stronglyAdapted
      adapted_bracket := hAadapt
      continuous_monotone_bracket := fun omega ↦
        ⟨(h.continuous_monotone_bracket omega).1.comp (continuous_id.min continuous_const),
          (h.continuous_monotone_bracket omega).2.comp (monotone_id.min monotone_const)⟩
      martingale_zero := fun omega ↦ by
        rw [zero_min]
        exact h.martingale_zero omega
      bracket_zero := fun omega ↦ by
        rw [zero_min]
        exact h.bracket_zero omega }
  apply h.novikov.mono
  · have hAmeas : AEStronglyMeasurable (A T) P :=
      ((hAadapt T).mono (V.le T)).aestronglyMeasurable
    change AEStronglyMeasurable (fun omega ↦ Real.exp (A T omega / 2)) P
    simpa only [div_eq_mul_inv] using Real.continuous_exp.comp_aestronglyMeasurable
      (hAmeas.mul_const (2 : ℝ)⁻¹)
  · filter_upwards with omega
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      ((h.continuous_monotone_bracket omega).2 (min_le_left T (tau omega))) (by norm_num)

end StochasticCalculus
