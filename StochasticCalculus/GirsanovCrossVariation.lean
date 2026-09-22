/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.MartingaleFourthMoment
import StochasticCalculus.GirsanovBounded
import StochasticCalculus.StoppedVariation

/-!
# Stopping mixed variation without stopping the Brownian version

L4 martingale estimates upgrade deterministic mixed sums to L1 and identify
the product compensator. This provides maximal control of grid prefixes.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Square-integrable integrators and coefficients give true elementary
martingale transforms without pathwise coefficient bounds. -/
theorem martingale_uniformAdaptedMartingaleSmulProcess_of_memLp_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M H : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) (hH : StronglyAdapted V H)
    (hM2 : ∀ t, MemLp (M t) 2 P) (hH2 : ∀ t, MemLp (H t) 2 P)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformAdaptedMartingaleSmulProcess M H T n) V P := by
  classical
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  have hterm (i : ℕ) : Martingale
      (elementaryMartingaleSmulProcess M (uniformPartitionTime T n i)
        (uniformPartitionTime T n (i + 1)) (H (uniformPartitionTime T n i))) V P := by
    apply martingale_elementaryMartingaleSmulProcess_of_integrable hM
      (monotone_uniformPartitionTime_general T n (Nat.le_succ i)) (hH _)
    intro t
    exact ((hM2 _).sub (hM2 _)).integrable_mul (hH2 _)
  have hsum (S : Finset ℕ) : Martingale
      (∑ i ∈ S, elementaryMartingaleSmulProcess M (uniformPartitionTime T n i)
        (uniformPartitionTime T n (i + 1)) (H (uniformPartitionTime T n i))) V P := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using martingale_zero ℝ V P
    | @insert i S hi ih => simpa only [Finset.sum_insert hi] using (hterm i).add ih
  exact hsum _

/-- The rational common-refinement bridge also converges in `L¹` for
L4 martingales.  Thus the coherent stopped-grid product decomposition
has the correct compensator at every positive rational sub-horizon. -/
theorem
    HasCrossVariationProcessInProbability.tendsto_eLpNorm_one_uniformStopped_rational_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ} {Horizon : ℝ≥0}
    (h : ∀ U, U ≤ Horizon → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X Y U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P)
    (T : ℝ≥0) (hTH : T ≤ Horizon) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) :
    Tendsto (fun n ↦ eLpNorm
      (uniformStoppedCovariationApprox X Y T (k * (n + 1))
        (T * (j : ℝ≥0) / (k : ℝ≥0)) -
        C (T * (j : ℝ≥0) / (k : ℝ≥0))) 1 P)
      atTop (nhds 0) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have haT : a ≤ T := by
    dsimp only [a]
    calc
      T * (j : ℝ≥0) / (k : ℝ≥0) ≤ T * (k : ℝ≥0) / (k : ℝ≥0) := by gcongr
      _ = T := mul_div_cancel_right₀ T (by exact_mod_cast hk.ne')
  have hLp := (tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    (uniformIntegrable_quadraticCovariationApprox_of_memLp_four hX hY hX4 hY4 a)
    (h a (haT.trans hTH))).comp hns.tendsto_atTop
  apply (tendsto_congr' ?_).2 hLp
  filter_upwards with n
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change eLpNorm
      (uniformStoppedCovariationApprox X Y T (k * (n + 1)) a - C a) 1 P =
    eLpNorm (quadraticCovariationApprox X Y a (ns n + 1) - C a) 1 P
  rw [hcount]
  apply congrArg (fun f : W → ℝ ↦ eLpNorm (f - C a) 1 P)
  funext omega
  exact uniformStoppedCovariationApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) hjk omega

/-- Stochastic integration by parts on rational times.  For two L4
martingales, the compensated product has equal past-event integrals between a
positive rational sub-horizon and the terminal horizon. -/
theorem
    HasCrossVariationProcessInProbability.setIntegral_stoppedProduct_sub_eq_rational_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ} {Horizon : ℝ≥0}
    (h : ∀ U, U ≤ Horizon → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X Y U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P)
    (T : ℝ≥0) (hTH : T ≤ Horizon) {k j : ℕ} (hk : 0 < k) (hjk : j ≤ k)
    {Aset : Set W}
    (hAset : MeasurableSet[V (T * (j : ℝ≥0) / (k : ℝ≥0))] Aset) :
    (∫ omega in Aset,
      X (T * (j : ℝ≥0) / (k : ℝ≥0)) omega *
          Y (T * (j : ℝ≥0) / (k : ℝ≥0)) omega -
        X 0 omega * Y 0 omega -
        C (T * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
      ∫ omega in Aset,
        X T omega * Y T omega - X 0 omega * Y 0 omega - C T omega ∂P := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  have hka0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have haT : a ≤ T := by
    dsimp only [a]
    calc
      T * (j : ℝ≥0) / (k : ℝ≥0) ≤
          T * (k : ℝ≥0) / (k : ℝ≥0) := by gcongr
      _ = T := mul_div_cancel_right₀ T hka0
  let S : ℕ → ℝ≥0 → W → ℝ := fun n ↦
    uniformAdaptedMartingaleSmulProcess Y X T (k * (n + 1)) +
      uniformAdaptedMartingaleSmulProcess X Y T (k * (n + 1))
  let F : ℝ≥0 → W → ℝ := fun t omega ↦
    X (min t T) omega * Y (min t T) omega -
      X 0 omega * Y 0 omega - C t omega
  have hS (n : ℕ) : Martingale (S n) V P := by
    apply Martingale.add
    · exact martingale_uniformAdaptedMartingaleSmulProcess_of_memLp_two
        hY hX.stronglyAdapted (fun t ↦ (hY4 t).mono_exponent (by norm_num))
        (fun t ↦ (hX4 t).mono_exponent (by norm_num)) T (k * (n + 1))
    · exact martingale_uniformAdaptedMartingaleSmulProcess_of_memLp_two
        hX hY.stronglyAdapted (fun t ↦ (hX4 t).mono_exponent (by norm_num))
        (fun t ↦ (hY4 t).mono_exponent (by norm_num)) T (k * (n + 1))
  have hFmeas (t : ℝ≥0) : AEStronglyMeasurable (F t) P := by
    have hXt : AEStronglyMeasurable (X (min t T)) P :=
      (((hX.stronglyMeasurable (min t T)).mono
        (V.mono (min_le_left _ _))).mono (V.le t)).aestronglyMeasurable
    have hYt : AEStronglyMeasurable (Y (min t T)) P :=
      (((hY.stronglyMeasurable (min t T)).mono
        (V.mono (min_le_left _ _))).mono (V.le t)).aestronglyMeasurable
    have hX0 : AEStronglyMeasurable (X 0) P :=
      (((hX.stronglyMeasurable 0).mono
        (V.mono bot_le)).mono (V.le t)).aestronglyMeasurable
    have hY0 : AEStronglyMeasurable (Y 0) P :=
      (((hY.stronglyMeasurable 0).mono
        (V.mono bot_le)).mono (V.le t)).aestronglyMeasurable
    exact ((hXt.mul hYt).sub (hX0.mul hY0)).sub
      ((hC t).mono (V.le t)).aestronglyMeasurable
  have hconvF (r : ℝ≥0) (hrT : r ≤ T)
      (hcov : Tendsto (fun n ↦ eLpNorm
        (uniformStoppedCovariationApprox X Y T (k * (n + 1)) r - C r) 1 P)
        atTop (nhds 0)) :
      Tendsto (fun n ↦ eLpNorm (S n r - F r) 1 P) atTop (nhds 0) := by
    apply (tendsto_congr' ?_).2 hcov
    filter_upwards with n
    apply eLpNorm_congr_norm_ae
    filter_upwards with omega
    have hnpos : 0 < k * (n + 1) := Nat.mul_pos hk (Nat.zero_lt_succ n)
    have hprod := uniformStopped_product_decomposition_pos
      X Y T (k * (n + 1)) hnpos r omega
    change ‖S n r omega - F r omega‖ =
      ‖uniformStoppedCovariationApprox X Y T (k * (n + 1)) r omega -
        C r omega‖
    have heq : S n r omega - F r omega =
        C r omega -
          uniformStoppedCovariationApprox X Y T (k * (n + 1)) r omega := by
      dsimp only [S, F]
      simp only [Pi.add_apply]
      rw [min_eq_left hrT] at hprod
      rw [min_eq_left hrT]
      linarith
    rw [heq, norm_sub_rev]
  have hconvA : Tendsto (fun n ↦ eLpNorm (S n a - F a) 1 P)
      atTop (nhds 0) := by
    apply hconvF a haT
    by_cases hj : 0 < j
    · exact tendsto_eLpNorm_one_uniformStopped_rational_of_memLp_four h
        hX hY hX4 hY4 T hTH hk hj hjk
    · have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
      have ha0 : a = 0 := by simp [a, hj0]
      rw [ha0, hCzero]
      have hz (n : ℕ) : uniformStoppedCovariationApprox X Y T (k * (n + 1)) 0 = 0 := by
        funext omega
        simp only [uniformStoppedCovariationApprox, zero_min, sub_self, mul_zero,
          Finset.sum_const_zero, Pi.zero_apply]
      simpa only [hz, sub_self, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0))
  have hcovT0 :=
    tendsto_eLpNorm_one_uniformStopped_rational_of_memLp_four h
    hX hY hX4 hY4 T hTH hk hk le_rfl
  have hTk : T * (k : ℝ≥0) / (k : ℝ≥0) = T :=
    mul_div_cancel_right₀ T hka0
  have hconvT : Tendsto (fun n ↦ eLpNorm (S n T - F T) 1 P)
      atTop (nhds 0) := by
    apply hconvF T le_rfl
    simpa only [hTk] using hcovT0
  have hIntA := tendsto_setIntegral_of_L1' (F a) (hFmeas a)
    (Filter.Eventually.of_forall fun n ↦ (hS n).integrable a) hconvA Aset
  have hIntT := tendsto_setIntegral_of_L1' (F T) (hFmeas T)
    (Filter.Eventually.of_forall fun n ↦ (hS n).integrable T) hconvT Aset
  have hseq : (fun n ↦ ∫ omega in Aset, S n a omega ∂P) =
      fun n ↦ ∫ omega in Aset, S n T omega ∂P := by
    funext n
    exact (hS n).setIntegral_eq haT (by simpa only [a] using hAset)
  rw [hseq] at hIntA
  have hlimit := tendsto_nhds_unique hIntA hIntT
  simpa only [F, a, min_eq_left haT, min_self] using hlimit

/-- L4 mixed variation identifies the compensated product as a martingale
on each finite uniform grid. Only limits through the given horizon are used. -/
theorem martingale_uniformGrid_product_compensator_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : ∀ U, U ≤ T → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X Y U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P)
    (n : ℕ) :
    let u := fun i ↦ uniformPartitionTime T (n + 1) (min i (n + 1))
    let hu : Monotone u := (monotone_uniformPartitionTime_general T (n + 1)).comp
      (monotone_id.min monotone_const)
    Martingale (fun i omega ↦ X (u i) omega * Y (u i) omega -
      X 0 omega * Y 0 omega - C (u i) omega)
      (monotoneReindexFiltration V u hu) P := by
  intro u hu
  have huT (i : ℕ) : u i ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) (min_le_right _ _)).2
  have hCint (i : ℕ) : Integrable (C (u i)) P :=
    UniformIntegrable.integrable_of_tendstoInMeasure
      (uniformIntegrable_quadraticCovariationApprox_of_memLp_four
        hX hY hX4 hY4 (u i)) (h (u i) (huT i))
  have hprodInt (t : ℝ≥0) : Integrable (fun omega ↦ X t omega * Y t omega) P :=
    ((hX4 t).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_mul
      ((hY4 t).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))
  apply martingale_of_setIntegral_eq_succ
  · intro i
    exact (((hX.stronglyAdapted (u i)).mul (hY.stronglyAdapted (u i))).sub
      (((hX.stronglyAdapted 0).mono (V.mono bot_le)).mul
        ((hY.stronglyAdapted 0).mono (V.mono bot_le)))).sub (hC (u i))
  · intro i
    exact ((hprodInt (u i)).sub (hprodInt 0)).sub (hCint i)
  · intro i A hA
    have hk : 0 < min (i + 1) (n + 1) := lt_min (Nat.zero_lt_succ i) (Nat.zero_lt_succ n)
    have hjk : min i (n + 1) ≤ min (i + 1) (n + 1) :=
      min_le_min_right _ (Nat.le_succ i)
    have htime : u (i + 1) * (min i (n + 1) : ℕ) /
        (min (i + 1) (n + 1) : ℕ) = u i := by
      dsimp only [u, uniformPartitionTime]
      have hk0 : ((min (i + 1) (n + 1) : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hk.ne'
      have hn0 : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
      field_simp
    have hrat :=
      HasCrossVariationProcessInProbability.setIntegral_stoppedProduct_sub_eq_rational_of_memLp_four
        h hX hY hC hCzero hX4 hY4 (u (i + 1)) (huT (i + 1)) hk hjk
        (Aset := A) (by rw [htime]; exact hA)
    simpa only [htime] using hrat

/-- The mixed-variation error on a finite uniform grid is a martingale. -/
theorem martingale_uniformGrid_covariation_error_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : ∀ U, U ≤ T → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X Y U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P)
    (n : ℕ) :
    let u := fun i ↦ uniformPartitionTime T (n + 1) (min i (n + 1))
    let hu : Monotone u := (monotone_uniformPartitionTime_general T (n + 1)).comp
      (monotone_id.min monotone_const)
    Martingale (fun i omega ↦
      uniformStoppedCovariationApprox X Y T (n + 1) (u i) omega - C (u i) omega)
      (monotoneReindexFiltration V u hu) P := by
  intro u hu
  have hF := martingale_uniformGrid_product_compensator_of_memLp_four
    h hX hY hC hCzero hX4 hY4 n
  let S := uniformAdaptedMartingaleSmulProcess Y X T (n + 1) +
    uniformAdaptedMartingaleSmulProcess X Y T (n + 1)
  have hS : Martingale S V P :=
    (martingale_uniformAdaptedMartingaleSmulProcess_of_memLp_two hY hX.stronglyAdapted
      (fun t ↦ (hY4 t).mono_exponent (by norm_num))
      (fun t ↦ (hX4 t).mono_exponent (by norm_num)) T (n + 1)).add
    (martingale_uniformAdaptedMartingaleSmulProcess_of_memLp_two hX hY.stronglyAdapted
      (fun t ↦ (hX4 t).mono_exponent (by norm_num))
      (fun t ↦ (hY4 t).mono_exponent (by norm_num)) T (n + 1))
  have hD := hF.sub (martingale_comp_monotone hS u hu)
  convert hD using 1
  funext i omega
  have hui : u i ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) (min_le_right _ _)).2
  have hp := uniformStopped_product_decomposition_pos X Y T (n + 1)
    (Nat.zero_lt_succ n) (u i) omega
  rw [min_eq_left hui] at hp
  change _ = X (u i) omega * Y (u i) omega - X 0 omega * Y 0 omega -
    C (u i) omega - S (u i) omega
  dsimp only [S, Pi.add_apply]
  linarith

/-- The norm of a real martingale is a submartingale. -/
theorem Martingale.norm_submartingale
    {W I : Type*} [MeasurableSpace W] [Preorder I]
    {P : Measure W} {V : Filtration I ‹MeasurableSpace W›}
    {M : I → W → ℝ} (hM : Martingale M V P) :
    Submartingale (fun i omega ↦ ‖M i omega‖) V P := by
  have hsup := hM.submartingale.sup hM.neg.submartingale
  change Submartingale (fun i omega ↦ max (M i omega) (-M i omega)) V P at hsup
  simpa only [← abs_eq_max_neg, ← Real.norm_eq_abs] using hsup

/-- A terminal L1 bound controls a martingale at any random index before
that terminal index; the index need not be a stopping time. -/
theorem Martingale.measure_random_index_norm_ge_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℕ ‹MeasurableSpace W›}
    {M : ℕ → W → ℝ} (hM : Martingale M V P)
    (N : ℕ) (j : W → ℕ) (hj : ∀ omega, j omega ≤ N)
    {epsilon : ℝ≥0} (hepsilon : 0 < epsilon) :
    P {omega | (epsilon : ℝ) ≤ ‖M (j omega) omega‖} ≤
      eLpNorm (M N) 1 P / (epsilon : ℝ≥0∞) := by
  have hsub := Martingale.norm_submartingale hM
  have hmax := maximal_ineq hsub (fun i omega ↦ norm_nonneg (M i omega))
    (ε := epsilon) N
  have hbound : (epsilon : ℝ≥0∞) *
      P {omega | (epsilon : ℝ) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun i ↦ ‖M i omega‖)} ≤ eLpNorm (M N) 1 P := by
    refine hmax.trans ?_
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hM.integrable N)]
    exact ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hM.integrable N).norm
      (Filter.Eventually.of_forall fun omega ↦ norm_nonneg (M N omega)))
  have hsubset : {omega | (epsilon : ℝ) ≤ ‖M (j omega) omega‖} ⊆
      {omega | (epsilon : ℝ) ≤
        (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun i ↦ ‖M i omega‖)} := by
    intro omega homega
    exact homega.trans (Finset.le_sup' (fun i ↦ ‖M i omega‖)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hj omega))))
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hepsilon.ne'))
    (Or.inl (by finiteness))).mpr
  rw [mul_comm]
  exact (mul_le_mul le_rfl (measure_mono hsubset) bot_le bot_le).trans hbound

/-- Terminal L1 convergence of a family of martingales gives convergence
in probability at arbitrary bounded random grid indices. -/
theorem tendstoInMeasure_martingale_random_index_of_terminal_L1
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : ℕ → Filtration ℕ ‹MeasurableSpace W›} {M : ℕ → ℕ → W → ℝ}
    (hM : ∀ n, Martingale (M n) (V n) P) (N : ℕ → ℕ)
    (j : ℕ → W → ℕ) (hj : ∀ n omega, j n omega ≤ N n)
    (hL1 : Tendsto (fun n ↦ eLpNorm (M n (N n)) 1 P) atTop (nhds 0)) :
    TendstoInMeasure P (fun n omega ↦ M n (j n omega) omega) atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  let e : ℝ≥0 := ⟨epsilon, hepsilon.le⟩
  have he : 0 < e := hepsilon
  have hlim : Tendsto (fun n ↦ eLpNorm (M n (N n)) 1 P / (e : ℝ≥0∞))
      atTop (nhds 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hL1
      (Or.inr (by exact_mod_cast he.ne'))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n ↦ bot_le)
  intro n
  simp only [sub_zero]
  change P {omega | (e : ℝ) ≤ ‖M n (j n omega) omega‖} ≤
    eLpNorm (M n (N n)) 1 P / (e : ℝ≥0∞)
  exact Martingale.measure_random_index_norm_ge_le (hM n) (N n) (j n) (hj n) he

/-- L4 cross-variation errors vanish at any random endpoint of the grid. -/
theorem tendstoInMeasure_uniformStoppedCovariation_random_grid_error
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : ∀ U, U ≤ T → TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X Y U (n + 1)) atTop (C U))
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hC : StronglyAdapted V C) (hCzero : C 0 = 0)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P)
    (j : ℕ → W → ℕ) (hj : ∀ n omega, j n omega ≤ n + 1) :
    TendstoInMeasure P (fun n omega ↦
      uniformStoppedCovariationApprox X Y T (n + 1)
        (uniformPartitionTime T (n + 1) (j n omega)) omega -
      C (uniformPartitionTime T (n + 1) (j n omega)) omega) atTop (fun _ ↦ 0) := by
  let u := fun n i ↦ uniformPartitionTime T (n + 1) (min i (n + 1))
  have hu (n : ℕ) : Monotone (u n) :=
    (monotone_uniformPartitionTime_general T (n + 1)).comp
      (monotone_id.min monotone_const)
  let D := fun n i omega ↦
    uniformStoppedCovariationApprox X Y T (n + 1) (u n i) omega - C (u n i) omega
  have hD (n : ℕ) : Martingale (D n) (monotoneReindexFiltration V (u n) (hu n)) P :=
    martingale_uniformGrid_covariation_error_of_memLp_four h hX hY hC hCzero hX4 hY4 n
  have hterminal (n : ℕ) : D n (n + 1) =
      quadraticCovariationApprox X Y T (n + 1) - C T := by
    have hut : u n (n + 1) = T := by
      simp only [u, min_self, uniformPartitionTime]
      exact mul_div_cancel_right₀ T (by positivity)
    funext omega
    simp only [D, hut, uniformStoppedCovariationApprox_terminal, Pi.sub_apply]
  have hL1 : Tendsto (fun n ↦ eLpNorm (D n (n + 1)) 1 P) atTop (nhds 0) := by
    simp only [hterminal]
    exact tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (uniformIntegrable_quadraticCovariationApprox_of_memLp_four hX hY hX4 hY4 T)
      (h T le_rfl)
  have hconv := tendstoInMeasure_martingale_random_index_of_terminal_L1 hD
    (fun n ↦ n + 1) j hj hL1
  simpa only [D, u, min_eq_left (hj _ _)] using hconv

end StochasticCalculus
