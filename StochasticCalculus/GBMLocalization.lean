/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GBMGronwall

/-!
# Localization of the linear SDE

Dyadic sampled exits approximate the bounded path-exit coefficient. These
lemmas retain the original probability measure and the adapted coefficients.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace StochasticCalculus

/-- A left dyadic sample never lies after the time being approximated. -/
theorem gbm_uniformPartitionTime_dyadicApproxIndex_le
    (s t : ℝ≥0) (n : ℕ) :
    uniformPartitionTime t (2 ^ n) (dyadicApproxIndex s t n) ≤ s := by
  by_cases ht : t = 0
  · simp [ht, uniformPartitionTime]
  have htpos : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hfloor := Nat.floor_le (show 0 ≤ (s : ℝ) / t * (2 : ℝ) ^ n by positivity)
  change (t * (dyadicApproxIndex s t n : ℝ≥0) / (2 ^ n : ℕ) : ℝ≥0) ≤ s
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).2
  have h := mul_le_mul_of_nonneg_left hfloor htpos.le
  dsimp [dyadicApproxIndex]
  convert h using 1; field_simp

/-- The left dyadic index is monotone in the time being approximated. -/
theorem dyadicApproxIndex_mono_time {s u : ℝ≥0} (hsu : s ≤ u)
    (t : ℝ≥0) (n : ℕ) : dyadicApproxIndex s t n ≤ dyadicApproxIndex u t n := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by exact_mod_cast hsu) (NNReal.coe_nonneg t))
    (by positivity)

/-- On a continuous path, the sampled stay decision through the left dyadic
approximation of `s` eventually equals the full path-stay decision at `s`. -/
theorem eventually_uniformGridStaySet_dyadic_iff
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) (omega : W)
    (hcont : Continuous (fun u ↦ X u omega)) :
    ∀ᶠ n : ℕ in atTop,
      (omega ∈ uniformGridStaySet R X t (2 ^ n) (dyadicApproxIndex s t n) ↔
        omega ∈ uniformGridPathStaySet R X s) := by
  classical
  by_cases hstay : omega ∈ uniformGridPathStaySet R X s
  · apply Filter.Eventually.of_forall
    intro n
    simp only [hstay, iff_true]
    have hb := (mem_uniformGridPathStaySet_iff_of_continuous R X s omega hcont).1 hstay
    simp only [uniformGridStaySet, Set.mem_iInter, Set.mem_ofPred_eq]
    intro j hj
    apply hb _ ⟨bot_le, ?_⟩
    have hjle : j ≤ dyadicApproxIndex s t n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (monotone_uniformPartitionTime_general t (2 ^ n) hjle).trans
      (gbm_uniformPartitionTime_dyadicApproxIndex_le s t n)
  · have hex : ∃ u ∈ Icc (0 : ℝ≥0) s, (R : ℝ) < |X u omega| := by
      have hn := hstay
      rw [mem_uniformGridPathStaySet_iff_of_continuous R X s omega hcont] at hn
      push Not at hn
      exact hn
    obtain ⟨u, hu, hlarge⟩ := hex
    have hlim := (hcont.abs.tendsto u).comp
      (tendsto_uniformPartitionTime_dyadicApproxIndex (hu.2.trans hst))
    have hevent := hlim.eventually (eventually_gt_nhds hlarge)
    filter_upwards [hevent] with n hn
    simp only [hstay, iff_false]
    intro hgrid
    have hsmall := Set.mem_iInter₂.mp hgrid (dyadicApproxIndex u t n)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadicApproxIndex_mono_time hu.2 t n)))
    exact (not_lt_of_ge hsmall) hn

/-- Sampled exit coefficients converge pathwise to the path-exit coefficient
at each time, with no moment assumption on the continuous path. -/
theorem tendsto_uniformGridExitCoefficient_dyadic
    {W : Type*} (volatility : ℝ) (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) (omega : W)
    (hcont : Continuous (fun u ↦ X u omega)) :
    Tendsto (fun n ↦ uniformGridExitCoefficient volatility R X t (2 ^ n)
      (dyadicApproxIndex s t n) omega) atTop
      (nhds (volatility * pathExitCoefficient R X s omega)) := by
  classical
  have heq := eventually_uniformGridStaySet_dyadic_iff R X hst omega hcont
  by_cases hstay : omega ∈ uniformGridPathStaySet R X s
  · rw [pathExitCoefficient, Set.indicator_of_mem hstay]
    apply Tendsto.congr' _ ((hcont.tendsto s).comp
      (tendsto_uniformPartitionTime_dyadicApproxIndex hst) |>.const_mul volatility)
    filter_upwards [heq] with n hn
    simp only [uniformGridExitCoefficient, Set.indicator_of_mem (hn.mpr hstay)]
    rfl
  · rw [pathExitCoefficient, Set.indicator_of_notMem hstay, mul_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with n hn
    simp only [uniformGridExitCoefficient, Set.indicator_of_notMem (mt hn.mp hstay)]

/-- Bounded dyadic exit coefficients have convergent second moments even
when the unlocalized process has no finite moment. -/
theorem tendsto_integral_sq_uniformGridExitCoefficient_dyadic
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (volatility : ℝ) (R : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n ↦ ∫ omega,
      (uniformGridExitCoefficient volatility R X t (2 ^ n)
        (dyadicApproxIndex s t n) omega) ^ 2 ∂P) atTop
      (nhds (∫ omega, (volatility * pathExitCoefficient R X s omega) ^ 2 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (|volatility| * (R : ℝ)) ^ 2)
  · intro n
    exact (((stronglyMeasurable_uniformGridExitCoefficient hX volatility R t
      (2 ^ n) (dyadicApproxIndex s t n)).mono (V.le _)).aestronglyMeasurable.pow 2)
  · exact integrable_const _
  · intro n
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_uniformGridExitCoefficient_le volatility R X t (2 ^ n)
      (dyadicApproxIndex s t n) omega
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  · filter_upwards [hcont] with omega homega
    exact (tendsto_uniformGridExitCoefficient_dyadic volatility R X hst omega homega).pow 2

/-- The finite step function attached to a uniform partition. -/
def uniformLeftStep (t : ℝ≥0) (n : ℕ) (C : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (Ico (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)).indicator (fun _ ↦ C i) s

/-- Membership in a dyadic cell is exactly the left-floor index. -/
theorem mem_uniformPartition_Ico_iff_dyadicApproxIndex
    {s t : ℝ≥0} (ht : 0 < t) (n i : ℕ) :
    (s : ℝ) ∈ Ico (uniformPartitionTime t (2 ^ n) i : ℝ)
      (uniformPartitionTime t (2 ^ n) (i + 1) : ℝ) ↔
      dyadicApproxIndex s t n = i := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicApproxIndex, Nat.floor_eq_iff (by positivity)]
  simp only [Set.mem_Ico, uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [div_mul_eq_mul_div]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ htR).2
      have h := (div_le_iff₀ hp).1 hlo
      convert h using 1; ring
    · apply (div_lt_iff₀ htR).2
      have h := (lt_div_iff₀ hp).1 hhi
      convert h using 1; ring
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_le_iff₀ hp).2
      have h : (i : ℝ) * t ≤ (s : ℝ) * 2 ^ n := by
        apply (le_div_iff₀ htR).1
        exact hlo
      nlinarith
    · apply (lt_div_iff₀ hp).2
      have h : (s : ℝ) * 2 ^ n < ((i : ℝ) + 1) * t := by
        apply (div_lt_iff₀ htR).1
        exact hhi
      nlinarith

/-- On the half-open horizon a dyadic step is its unique sampled value. -/
theorem uniformLeftStep_dyadic_eq
    {s t : ℝ≥0} (hst : s < t) (n : ℕ) (C : ℕ → ℝ) :
    uniformLeftStep t (2 ^ n) C s = C (dyadicApproxIndex s t n) := by
  classical
  have ht : 0 < t := lt_of_le_of_lt bot_le hst
  have hi : dyadicApproxIndex s t n < 2 ^ n := by
    unfold dyadicApproxIndex
    apply (Nat.floor_lt (by positivity)).2
    change (s : ℝ) / t * (2 : ℝ) ^ n < ((2 ^ n : ℕ) : ℝ)
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    calc
      (s : ℝ) / t * (2 : ℝ) ^ n < 1 * (2 : ℝ) ^ n :=
        mul_lt_mul_of_pos_right ((div_lt_one htR).2 (by exact_mod_cast hst))
          (by positivity)
      _ = _ := one_mul _
  unfold uniformLeftStep
  rw [Finset.sum_eq_single (dyadicApproxIndex s t n)]
  · exact Set.indicator_of_mem
      ((mem_uniformPartition_Ico_iff_dyadicApproxIndex ht n _).2 rfl) _
  · intro i hi hne
    apply Set.indicator_of_notMem
    intro hmem
    exact hne ((mem_uniformPartition_Ico_iff_dyadicApproxIndex ht n i).1 hmem).symm
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

/-- A uniform step is zero outside its half-open horizon. -/
theorem uniformLeftStep_eq_zero_of_notMem
    (t : ℝ≥0) (n : ℕ) (C : ℕ → ℝ) {s : ℝ}
    (hs : s ∉ Ico (0 : ℝ) t) : uniformLeftStep t n C s = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  apply Set.indicator_of_notMem
  intro hmem
  apply hs
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i) (Finset.mem_range.mp hi)
  have hend : uniformPartitionTime t n n = t := by
    simp [uniformPartitionTime, ne_of_gt hn]
  have hle := monotone_uniformPartitionTime_general t n
    (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  rw [hend] at hle
  exact ⟨le_trans (NNReal.coe_nonneg _) hmem.1,
    lt_of_lt_of_le hmem.2 (by exact_mod_cast hle)⟩

/-- Uniform step functions are integrable. -/
theorem integrable_uniformLeftStep (t : ℝ≥0) (n : ℕ) (C : ℕ → ℝ) :
    Integrable (uniformLeftStep t n C) := by
  apply integrable_finsetSum
  intro i hi
  exact (integrable_indicator_iff measurableSet_Ico).2
    (integrableOn_const (by simp [Real.volume_Ico]))

/-- The integral of a uniform step is its exact finite Riemann sum. -/
theorem integral_uniformLeftStep (t : ℝ≥0) (n : ℕ) (C : ℕ → ℝ) :
    ∫ s, uniformLeftStep t n C s =
      ∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) * C i := by
  unfold uniformLeftStep
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator measurableSet_Ico, setIntegral_const]
    simp only [Measure.real, Real.volume_Ico, smul_eq_mul]
    rw [ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr (by exact_mod_cast
      monotone_uniformPartitionTime_general t n (Nat.le_succ i))
  · intro i hi
    exact (integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by simp [Real.volume_Ico]))

/-- The expected energies of the sampled exit coefficients converge after
integration in time. No continuity of the localized moment profile is needed. -/
theorem tendsto_sum_integral_sq_uniformGridExitCoefficient_dyadic
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range (2 ^ n),
      ((uniformPartitionTime t (2 ^ n) (i + 1) : ℝ) -
        (uniformPartitionTime t (2 ^ n) i : ℝ)) *
      ∫ omega, (uniformGridExitCoefficient volatility R X t (2 ^ n) i omega) ^ 2 ∂P)
      atTop (nhds (∫ s in Icc (0 : ℝ) t,
        ∫ omega, (volatility * pathExitCoefficient R X s.toNNReal omega) ^ 2 ∂P)) := by
  classical
  let C : ℕ → ℕ → ℝ := fun n i ↦
    ∫ omega, (uniformGridExitCoefficient volatility R X t (2 ^ n) i omega) ^ 2 ∂P
  let g : ℝ → ℝ := fun s ↦
    ∫ omega, (volatility * pathExitCoefficient R X s.toNNReal omega) ^ 2 ∂P
  let K : ℝ := (|volatility| * (R : ℝ)) ^ 2
  have hC (n i : ℕ) : ‖C n i‖ ≤ K := by
    have hnonneg : 0 ≤ C n i := integral_nonneg fun _ ↦ sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      C n i ≤ ∫ _ : W, K ∂P := by
        apply integral_mono
          ((memLp_two_iff_integrable_sq
            (memLp_two_uniformGridExitCoefficient hX volatility R t (2 ^ n) i
              (P := P)).aestronglyMeasurable).1
                (memLp_two_uniformGridExitCoefficient hX volatility R t (2 ^ n) i))
          (integrable_const K)
        intro omega
        have hb := norm_uniformGridExitCoefficient_le volatility R X t (2 ^ n) i omega
        rw [Real.norm_eq_abs] at hb
        simpa only [sq_abs, K] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = K := by simp
  have hDCT := tendsto_integral_of_dominated_convergence
    ((Ico (0 : ℝ) t).indicator (fun _ ↦ K))
    (fun n ↦ (integrable_uniformLeftStep t (2 ^ n) (C n)).aestronglyMeasurable)
    ((integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by simp [Real.volume_Ico])))
    (f := (Ico (0 : ℝ) t).indicator g)
    (fun n ↦ Filter.Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ico (0 : ℝ) t
      · have hsNN : s.toNNReal < t := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal s hs.1]
          exact hs.2
        rw [Set.indicator_of_mem hs]
        rw [← Real.coe_toNNReal s hs.1, uniformLeftStep_dyadic_eq hsNN]
        exact hC n _
      · rw [uniformLeftStep_eq_zero_of_notMem t (2 ^ n) (C n) hs,
          Set.indicator_of_notMem hs, norm_zero])
    (Filter.Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ico (0 : ℝ) t
      · have hsNN : s.toNNReal < t := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal s hs.1]
          exact hs.2
        rw [Set.indicator_of_mem hs]
        have hh := tendsto_integral_sq_uniformGridExitCoefficient_dyadic
          hX hcont volatility R hsNN.le
        apply hh.congr'
        apply Filter.Eventually.of_forall
        intro n
        change C n (dyadicApproxIndex s.toNNReal t n) = uniformLeftStep t (2 ^ n) (C n) s
        rw [← Real.coe_toNNReal s hs.1, uniformLeftStep_dyadic_eq hsNN]
        simp only [Real.toNNReal_coe]
      · rw [Set.indicator_of_notMem hs]
        apply tendsto_const_nhds.congr'
        exact Filter.Eventually.of_forall fun n ↦
          (uniformLeftStep_eq_zero_of_notMem t (2 ^ n) (C n) hs).symm)
  simpa only [integral_uniformLeftStep, integral_indicator measurableSet_Ico,
    ← integral_Icc_eq_integral_Ico, C, g] using hDCT

/-- The exact exit-gated discrete Itô isometries converge to the localized
coefficient energy. -/
theorem tendsto_integral_sq_gridExitLinearSDESpaceApprox_dyadic
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) :
    Tendsto (fun n ↦ ∫ omega,
      (gridExitLinearSDESpaceApprox volatility R X B t (2 ^ n) omega) ^ 2 ∂P)
      atTop (nhds (∫ s in Icc (0 : ℝ) t,
        ∫ omega, (volatility * pathExitCoefficient R X s.toNNReal omega) ^ 2 ∂P)) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hh := tendsto_sum_integral_sq_uniformGridExitCoefficient_dyadic
    hX hcont volatility R t
  convert hh using 1
  funext n
  exact integral_sq_uniformBrownianLeftSum hB hsm
    (fun i ↦ (stronglyMeasurable_uniformGridExitCoefficient
      hX volatility R t (2 ^ n) i).aestronglyMeasurable)
    (fun i ↦ memLp_two_uniformGridExitCoefficient hX volatility R t (2 ^ n) i)


/-- Lower semicontinuity on an event only needs convergence of the original
second moments, not convergence of the unrestricted random variables. -/
theorem integral_sq_indicator_limit_le_of_second_moment
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {S : ℕ → W → ℝ} (hSmem : ∀ n, MemLp (S n) 2 P)
    {A : Set W} (hA : MeasurableSet A) {I : W → ℝ} {L : ℝ}
    (hI : TendstoInMeasure P (fun n ↦ A.indicator (S n)) atTop I)
    (hsecond : Tendsto (fun n ↦ ∫ omega, (S n omega) ^ 2 ∂P) atTop (nhds L)) :
    MemLp I 2 P ∧ ∫ omega, I omega ^ 2 ∂P ≤ L := by
  have hLnonneg : 0 ≤ L := by
    exact ge_of_tendsto hsecond (Filter.Eventually.of_forall fun n ↦
      integral_nonneg fun omega ↦ sq_nonneg (S n omega))
  obtain ⟨ns, hns, hnsae⟩ := hI.exists_seq_tendsto_ae'
  have hsquare : Tendsto
      (fun n ↦ (eLpNorm (S (ns n)) 2 P).toReal ^ 2)
      Filter.atTop (nhds L) := by
    convert hsecond.comp hns using 1
    funext n
    exact (integral_sq_eq_eLpNorm_two_toReal_sq (hSmem (ns n))).symm
  have hrealnorm : Tendsto
      (fun n ↦ (eLpNorm (S (ns n)) 2 P).toReal)
      Filter.atTop (nhds (Real.sqrt L)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    convert hsqrt using 1
    funext n
    simp [Function.comp_apply]
  have hennnorm : Tendsto (fun n ↦ eLpNorm (S (ns n)) 2 P)
      Filter.atTop (nhds (ENNReal.ofReal (Real.sqrt L))) := by
    convert ENNReal.tendsto_ofReal hrealnorm using 1
    funext n
    exact (ENNReal.ofReal_toReal (hSmem (ns n)).eLpNorm_ne_top).symm
  have hImeas : AEStronglyMeasurable I P :=
    hI.aestronglyMeasurable (fun n ↦ ((hSmem n).indicator hA).aestronglyMeasurable)
  have hInorm : eLpNorm I 2 P ≤ ENNReal.ofReal (Real.sqrt L) := by
    have hlower := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (2 : ℝ≥0∞))
      (fun n ↦ ((hSmem (ns n)).indicator hA).aestronglyMeasurable) I hnsae
    have hupper := Filter.liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall
      fun n ↦ eLpNorm_indicator_le (μ := P) (p := (2 : ℝ≥0∞)) (S (ns n)) (s := A))
    exact hlower.trans (hupper.trans_eq hennnorm.liminf_eq)
  have hImem : MemLp I 2 P :=
    ⟨hImeas, hInorm.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hImem, ?_⟩
  rw [integral_sq_eq_eLpNorm_two_toReal_sq hImem]
  have hreal : (eLpNorm I 2 P).toReal ≤ Real.sqrt L := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hInorm
    simpa [ENNReal.toReal_ofReal (Real.sqrt_nonneg L)] using this
  calc
    (eLpNorm I 2 P).toReal ^ 2 ≤ (Real.sqrt L) ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg L)).mpr hreal
    _ = L := Real.sq_sqrt hLnonneg

/-- The residual localized to a path-stay event satisfies the sharp integral
bound, with no global moment condition and without constructing a stopped
integral process. -/
theorem integral_sq_indicator_linearSDESpaceApprox_limit_le_integral
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1)) atTop I) :
    let A := uniformGridPathStaySet R X t
    MemLp (A.indicator I) 2 P ∧
      ∫ omega, (A.indicator I omega) ^ 2 ∂P ≤
        ∫ s in Icc (0 : ℝ) t,
          ∫ omega, (volatility * pathExitCoefficient R X s.toNNReal omega) ^ 2 ∂P := by
  classical
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let A := uniformGridPathStaySet R X t
  have hA : MeasurableSet A := (Filtration.natural B hsm).le t A
    (measurableSet_uniformGridPathStaySet hX R t)
  have hsub : Tendsto (fun n : ℕ ↦ 2 ^ n - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlimit : TendstoInMeasure P
      (fun n ↦ A.indicator (gridExitLinearSDESpaceApprox volatility R X B t (2 ^ n)))
      atTop (A.indicator I) := by
    apply ((hI.comp hsub).indicator A).congr_left
    intro n
    have hpow : 2 ^ n - 1 + 1 = (2 ^ n : ℕ) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num)))
    filter_upwards with omega
    by_cases hstay : omega ∈ A
    · simp only [Set.indicator_of_mem hstay]
      have heq := gridExitLinearSDESpaceApprox_eq_of_mem_pathStaySet
        volatility R X B t (2 ^ n - 1) omega hstay
      simpa only [Function.comp_apply, hpow] using heq.symm
    · simp only [Set.indicator_of_notMem hstay]
  exact integral_sq_indicator_limit_le_of_second_moment
    (fun n ↦ memLp_two_gridExitLinearSDESpaceApprox hB hsm hX volatility R t (2 ^ n))
    hA hlimit
    (tendsto_integral_sq_gridExitLinearSDESpaceApprox_dyadic hB hsm hX hcont volatility R t)

/-- The bounded path-exit coefficient is jointly measurable up to completion
on each finite time horizon. Dyadic step approximation avoids requiring a
measurable set of everywhere-continuous paths. -/
theorem aestronglyMeasurable_pathExitCoefficient_uncurry
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (R : ℝ≥0) (t : ℝ≥0) :
    AEStronglyMeasurable
      (fun p : ℝ × W ↦ pathExitCoefficient R X p.1.toNNReal p.2)
      ((volume.restrict (Icc (0 : ℝ) t)).prod P) := by
  classical
  rw [← restrict_Ico_eq_restrict_Icc]
  let mu : Measure ℝ := volume.restrict (Ico (0 : ℝ) t)
  let F : ℕ → ℝ × W → ℝ := fun n p ↦ uniformLeftStep t (2 ^ n)
    (fun i ↦ uniformGridExitCoefficient 1 R X t (2 ^ n) i p.2) p.1
  have hF (n : ℕ) : AEStronglyMeasurable (F n) (mu.prod P) := by
    apply StronglyMeasurable.aestronglyMeasurable
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have hm := ((stronglyMeasurable_uniformGridExitCoefficient hX 1 R t
      (2 ^ n) i).mono (V.le _)).comp_measurable
        (measurable_snd : Measurable (fun p : ℝ × W ↦ p.2))
    have hh := hm.indicator ((measurableSet_Ico (a :=
      (uniformPartitionTime t (2 ^ n) i : ℝ)) (b :=
      (uniformPartitionTime t (2 ^ n) (i + 1) : ℝ))).preimage measurable_fst)
    exact hh
  have hlim : ∀ᵐ p : ℝ × W ∂mu.prod P,
      Tendsto (fun n ↦ F n p) atTop
        (nhds (pathExitCoefficient R X p.1.toNNReal p.2)) := by
    have ha : ∀ᵐ p : ℝ × W ∂mu.prod P, p.1 ∈ Ico (0 : ℝ) t :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)
    have hc : ∀ᵐ p : ℝ × W ∂mu.prod P, Continuous (fun u ↦ X u p.2) :=
      Measure.quasiMeasurePreserving_snd.ae hcont
    filter_upwards [ha, hc] with p hp hcp
    have hpt : p.1.toNNReal < t := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal p.1 hp.1]
      exact hp.2
    have hh := tendsto_uniformGridExitCoefficient_dyadic 1 R X hpt.le p.2 hcp
    simp only [one_mul] at hh
    apply hh.congr'
    apply Filter.Eventually.of_forall
    intro n
    dsimp only [F]
    rw [← Real.coe_toNNReal p.1 hp.1, uniformLeftStep_dyadic_eq hpt]
    simp only [Real.toNNReal_coe]
  exact (tendstoInMeasure_of_tendsto_ae hF hlim).aestronglyMeasurable hF

/-- The localized squared coefficient is integrable on the product space. -/
theorem integrable_sq_pathExitCoefficient_uncurry
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) :
    Integrable (fun p : ℝ × W ↦ (c * pathExitCoefficient R X p.1.toNNReal p.2) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) t)).prod P) := by
  apply (integrable_const ((|c| * (R : ℝ)) ^ 2)).mono'
    (((aestronglyMeasurable_pathExitCoefficient_uncurry hX hcont R t).const_mul c).pow 2)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb : |c * pathExitCoefficient R X p.1.toNNReal p.2| ≤ |c| * (R : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_pathExitCoefficient_le R X p.1.toNNReal p.2) (abs_nonneg c)
  simpa only [sq_abs, Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) hb 2

/-- The localized second-moment profile is integrable in time. -/
theorem integrableOn_integral_sq_pathExitCoefficient
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ ↦
      ∫ omega, (c * pathExitCoefficient R X s.toNNReal omega) ^ 2 ∂P)
      (Icc (0 : ℝ) t) :=
  (integrable_sq_pathExitCoefficient_uncurry hX hcont c R t).integral_prod_left

/-- On a continuous path, a stay event at a later horizon implies every
earlier stay event. -/
theorem mem_uniformGridPathStaySet_of_le_of_continuous
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) (omega : W)
    (hcont : Continuous (fun u ↦ X u omega))
    (hstay : omega ∈ uniformGridPathStaySet R X t) :
    omega ∈ uniformGridPathStaySet R X s := by
  apply (mem_uniformGridPathStaySet_iff_of_continuous R X s omega hcont).2
  intro u hu
  exact (mem_uniformGridPathStaySet_iff_of_continuous R X t omega hcont).1
    hstay u ⟨hu.1, hu.2.trans hst⟩

/-- On the terminal stay event, localization does not alter the drift
integral over any earlier time. -/
theorem indicator_integral_eq_indicator_integral_pathExitCoefficient
    {W : Type*} (c : ℝ) (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) (hcont : Continuous (fun u ↦ X u omega)) :
    (uniformGridPathStaySet R X t).indicator
      (fun omega ↦ ∫ s in Icc (0 : ℝ) t, c * X s.toNNReal omega) omega =
    (uniformGridPathStaySet R X t).indicator
      (fun omega ↦ ∫ s in Icc (0 : ℝ) t,
        c * pathExitCoefficient R X s.toNNReal omega) omega := by
  classical
  by_cases hstay : omega ∈ uniformGridPathStaySet R X t
  · simp only [Set.indicator_of_mem hstay]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    have hst : s.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs.1]
      exact hs.2
    change c * X s.toNNReal omega = c * pathExitCoefficient R X s.toNNReal omega
    rw [pathExitCoefficient, Set.indicator_of_mem
      (mem_uniformGridPathStaySet_of_le_of_continuous R X hst omega hcont hstay)]
  · simp only [Set.indicator_of_notMem hstay]

/-- The time integral of a bounded path-exit coefficient is square integrable. -/
theorem memLp_two_integral_pathExitCoefficient
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (hcont : ∀ᵐ omega ∂P, Continuous (fun u ↦ X u omega))
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) :
    MemLp (fun omega ↦ ∫ s in Icc (0 : ℝ) t,
      c * pathExitCoefficient R X s.toNNReal omega) 2 P := by
  have hm := (aestronglyMeasurable_pathExitCoefficient_uncurry hX hcont R t).const_mul c
  apply MemLp.of_bound hm.prod_swap.integral_prod_right' (|c| * (R : ℝ) * t)
  filter_upwards with omega
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0 : ℝ) t))
    (f := fun s : ℝ ↦ c * pathExitCoefficient R X s.toNNReal omega)
    (Filter.Eventually.of_forall fun s ↦ by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_pathExitCoefficient_le R X s.toNNReal omega) (abs_nonneg c))
  simpa [Measure.real, NNReal.coe_nonneg] using hb

/-- The localized moment inequality for any zero-initial strong solution.
All expectations are taken under the original Brownian probability measure. -/
theorem IsStrongLinearSDESolution.integral_sq_pathExitCoefficient_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B Z : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)} {drift volatility : ℝ}
    (hZ : IsStrongLinearSDESolution Z B P hsm 0 drift volatility)
    (R : ℝ≥0) (t : ℝ≥0) :
    (∫ omega, (pathExitCoefficient R Z t omega) ^ 2 ∂P) ≤
      (2 * (t : ℝ) * drift ^ 2 + 2 * volatility ^ 2) *
        ∫ s in Icc (0 : ℝ) t,
          ∫ omega, (pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P := by
  classical
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let A := uniformGridPathStaySet R Z t
  let D : W → ℝ := fun omega ↦ ∫ s in Icc (0 : ℝ) t,
    drift * pathExitCoefficient R Z s.toNNReal omega
  let J := A.indicator (linearSDEResidual drift Z 0 t)
  have hA : MeasurableSet A := (Filtration.natural B hsm).le t A
    (measurableSet_uniformGridPathStaySet hZ.adapted R t)
  have hDmem : MemLp D 2 P := memLp_two_integral_pathExitCoefficient
    hZ.adapted hZ.continuous_paths drift R t
  obtain ⟨hJmem, hJbound⟩ := integral_sq_indicator_linearSDESpaceApprox_limit_le_integral
    hB hsm hZ.adapted hZ.continuous_paths volatility R t (hZ.integral_equation t)
  have hZeq : pathExitCoefficient R Z t =ᵐ[P] A.indicator D + J := by
    filter_upwards [hZ.continuous_paths] with omega homega
    have hdeq := indicator_integral_eq_indicator_integral_pathExitCoefficient
      drift R Z t omega homega
    change A.indicator (fun omega ↦ ∫ s in Icc (0 : ℝ) t,
      drift * Z s.toNNReal omega) omega = A.indicator D omega at hdeq
    change A.indicator (Z t) omega = A.indicator D omega +
      A.indicator (linearSDEResidual drift Z 0 t) omega
    by_cases ha : omega ∈ A
    · simp only [Set.indicator_of_mem ha] at hdeq ⊢
      simp only [linearSDEResidual, sub_zero]
      rw [hdeq]
      ring
    · simp only [Set.indicator_of_notMem ha, zero_add]
  have hsum := integral_sq_add_le_two (hDmem.indicator hA) hJmem
  have hDineq : (∫ omega, (A.indicator D omega) ^ 2 ∂P) ≤ ∫ omega, (D omega) ^ 2 ∂P := by
    apply integral_mono
      ((memLp_two_iff_integrable_sq (hDmem.indicator hA).aestronglyMeasurable).1
        (hDmem.indicator hA))
      ((memLp_two_iff_integrable_sq hDmem.aestronglyMeasurable).1 hDmem)
    intro omega
    by_cases ha : omega ∈ A
    · simp only [Set.indicator_of_mem ha, le_refl]
    · simp only [Set.indicator_of_notMem ha, zero_pow (by norm_num : 2 ≠ 0)]
      exact sq_nonneg _
  have hDbound := integral_sq_setIntegral_Icc_le (P := P)
    (f := fun s omega ↦ drift * pathExitCoefficient R Z s.toNNReal omega) t
    ((aestronglyMeasurable_pathExitCoefficient_uncurry
      hZ.adapted hZ.continuous_paths R t).const_mul drift)
    (integrable_sq_pathExitCoefficient_uncurry hZ.adapted hZ.continuous_paths drift R t)
  have hcoeff (c : ℝ) : (∫ s in Icc (0 : ℝ) t,
      ∫ omega, (c * pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P) =
      c ^ 2 * ∫ s in Icc (0 : ℝ) t,
        ∫ omega, (pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P := by
    simp only [mul_pow, integral_const_mul]
  calc
    (∫ omega, (pathExitCoefficient R Z t omega) ^ 2 ∂P) =
        ∫ omega, (A.indicator D omega + J omega) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hZeq] with omega homega
      rw [homega]
      rfl
    _ ≤ 2 * ∫ omega, (A.indicator D omega) ^ 2 ∂P +
        2 * ∫ omega, (J omega) ^ 2 ∂P := hsum
    _ ≤ 2 * ((t : ℝ) * ∫ s in Icc (0 : ℝ) t,
        ∫ omega, (drift * pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P) +
        2 * (∫ s in Icc (0 : ℝ) t,
          ∫ omega, (volatility * pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P) := by
      have hd := hDineq.trans hDbound
      linarith [hJbound]
    _ = _ := by rw [hcoeff drift, hcoeff volatility]; ring

/-- Every zero-initial continuous strong solution of the linear SDE vanishes.
Exit localization removes all global moment assumptions. -/
theorem IsStrongLinearSDESolution.ae_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B Z : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)} {drift volatility : ℝ}
    (hZ : IsStrongLinearSDESolution Z B P hsm 0 drift volatility) :
    ∀ t, Z t =ᵐ[P] fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlocal (R : ℝ≥0) (T : ℝ≥0) : pathExitCoefficient R Z T =ᵐ[P] fun _ ↦ 0 := by
    let u : ℝ → ℝ := fun s ↦ ∫ omega, (pathExitCoefficient R Z s.toNNReal omega) ^ 2 ∂P
    have hnonneg : ∀ s, 0 ≤ u s := fun s ↦ integral_nonneg fun _ ↦ sq_nonneg _
    have hu : IntegrableOn u (Icc (0 : ℝ) T) := by
      simpa only [one_mul] using integrableOn_integral_sq_pathExitCoefficient
        hZ.adapted hZ.continuous_paths 1 R T
    let K : ℝ := 2 * (T : ℝ) * drift ^ 2 + 2 * volatility ^ 2
    have hzero := eq_zero_of_nonneg_le_mul_setIntegral hu hnonneg (K := K)
      (fun s hs ↦ by
        have hh := hZ.integral_sq_pathExitCoefficient_le hB R s.toNNReal
        rw [Real.coe_toNNReal s hs.1] at hh
        have hK : 2 * s * drift ^ 2 + 2 * volatility ^ 2 ≤ K := by
          dsimp only [K]
          nlinarith [mul_le_mul_of_nonneg_right hs.2 (sq_nonneg drift)]
        exact hh.trans (mul_le_mul_of_nonneg_right hK
          (integral_nonneg fun r ↦ hnonneg r)))
    have hintzero : ∫ omega, (pathExitCoefficient R Z T omega) ^ 2 ∂P = 0 := by
      simpa only [u, Real.toNNReal_coe] using hzero T ⟨NNReal.coe_nonneg T, le_rfl⟩
    have hmem := memLp_two_pathExitCoefficient (P := P) hZ.adapted R T
    have hsqint := (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
    have hsqzero := (integral_eq_zero_iff_of_nonneg
      (fun omega ↦ sq_nonneg (pathExitCoefficient R Z T omega)) hsqint).1 hintzero
    filter_upwards [hsqzero] with omega homega
    exact sq_eq_zero_iff.mp homega
  intro t
  have hall : ∀ᵐ omega ∂P, ∀ R : ℕ, pathExitCoefficient (R : ℝ≥0) Z t omega = 0 :=
    ae_all_iff.mpr fun R ↦ hlocal R t
  filter_upwards [hall, ae_mem_iUnion_uniformGridPathStaySet hZ.continuous_paths t]
    with omega homega hstay
  obtain ⟨R, hR⟩ := Set.mem_iUnion.mp hstay
  have hh := homega R
  rwa [pathExitCoefficient, Set.indicator_of_mem hR] at hh

/-- Indistinguishable uniqueness among all adapted continuous strong
solutions of the scalar linear Brownian SDE. -/
theorem IsStrongLinearSDESolution.indistinguishable
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X Y : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)} {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hY : IsStrongLinearSDESolution Y B P hsm spot drift volatility) :
    ∀ᵐ omega ∂P, ∀ t, X t omega = Y t omega := by
  have hzero := (hX.sub hY).ae_eq_zero hB
  apply ae_all_eq_of_continuous_processes hX.continuous_paths hY.continuous_paths
  intro t
  filter_upwards [hzero t] with omega homega
  exact sub_eq_zero.mp homega

/-- Geometric Brownian motion is the unique strong solution of its linear
SDE, without any additional moment or stopping assumptions on competitors. -/
theorem geometricBrownianMotion_unique_strong_solution
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (spot drift volatility : ℝ) :
    IsStrongLinearSDESolution (geometricBrownianMotion spot drift volatility B)
      B P hsm spot drift volatility ∧
      ∀ X, IsStrongLinearSDESolution X B P hsm spot drift volatility →
        ∀ᵐ omega ∂P, ∀ t,
          X t omega = geometricBrownianMotion spot drift volatility B t omega := by
  have hGBM := geometricBrownianMotion_isStrongLinearSDESolution hB hsm spot drift volatility
  exact ⟨hGBM, fun X hX ↦ hX.indistinguishable hB.toIsPreBrownianReal hGBM⟩

end StochasticCalculus
