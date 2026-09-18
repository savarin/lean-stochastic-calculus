/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.ItoFormulaGeneral

/-!
# Weighted bracket Riemann sums

Uniform half-open partitions integrate continuous random weights against the
absolutely continuous bracket of a natural Itô process.  Combined with the
two-scale completed-cell comparison, this closes diffusion-weighted
quadratic variation for the natural stochastic-integral component.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace StochasticCalculus

/-- The cubic test function has second state derivative `2x`; its Itô
quadratic coefficient is therefore exactly `x`. -/
@[simp]
theorem itoSpaceSecondDerivative_cubicThird (s x : ℝ) :
    itoSpaceSecondDerivative (fun _ y : ℝ ↦ y ^ 3 / 3) s x = 2 * x := by
  unfold itoSpaceSecondDerivative
  have hfirst : deriv (fun y : ℝ ↦ y ^ 3 / 3) = fun y ↦ y ^ 2 := by
    funext y
    rw [deriv_div_const, deriv_fun_pow]
    · norm_num
    · fun_prop
  rw [hfirst, deriv_fun_pow]
  · norm_num
  · fun_prop

/-- A left-weighted quadratic-variation sum. -/
noncomputable def weightedQuadraticVariationApprox
    {W : Type*} (H M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n, H (uniformPartitionTime t n i) omega *
    (M (uniformPartitionTime t n (i + 1)) omega -
      M (uniformPartitionTime t n i) omega) ^ 2

/-- The completed coarse-step counterpart of a left-weighted quadratic
variation. -/
noncomputable def weightedQuadraticVariationCompletedStepApprox
    {W : Type*} (H M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n k : ℕ) (omega : W) : ℝ :=
  ∑ j ∈ Finset.range k, H (uniformPartitionTime t k j) omega *
    (quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k (j + 1)) omega -
      quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k j) omega)

/-- A left-weighted quadratic covariation. -/
noncomputable def weightedQuadraticCovariationApprox
    {W : Type*} (H X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n, H (uniformPartitionTime t n i) omega *
    (X (uniformPartitionTime t n (i + 1)) omega -
      X (uniformPartitionTime t n i) omega) *
    (Y (uniformPartitionTime t n (i + 1)) omega -
      Y (uniformPartitionTime t n i) omega)

/-- Polarization identifies twice a weighted covariation with three weighted
quadratic variations on the same grid. -/
theorem two_mul_weightedQuadraticCovariationApprox
    {W : Type*} (H X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    2 * weightedQuadraticCovariationApprox H X Y t n omega =
      weightedQuadraticVariationApprox H (X + Y) t n omega -
        weightedQuadraticVariationApprox H X t n omega -
          weightedQuadraticVariationApprox H Y t n omega := by
  unfold weightedQuadraticCovariationApprox weightedQuadraticVariationApprox
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.add_apply]
  ring

/-- The Taylor remainder left after replacing an increment of `f(Y)` by its
left derivative times the increment of `Y`, weighted by an increment of
`X`. -/
noncomputable def covariationTaylorRemainderApprox
    {W : Type*} (f : ℝ → ℝ) (X Y : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (X (uniformPartitionTime t n (i + 1)) omega -
      X (uniformPartitionTime t n i) omega) *
    (f (Y (uniformPartitionTime t n (i + 1)) omega) -
      f (Y (uniformPartitionTime t n i) omega) -
      deriv f (Y (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega))

/-- Exact first-order Taylor decomposition of a covariation with a
state-function transform. -/
theorem quadraticCovariationApprox_comp_eq_weighted_add_remainder
    {W : Type*} (f : ℝ → ℝ) (X Y : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationApprox X (fun s w ↦ f (Y s w)) t n omega =
      weightedQuadraticCovariationApprox
          (fun s w ↦ deriv f (Y s w)) X Y t n omega +
        covariationTaylorRemainderApprox f X Y t n omega := by
  unfold quadraticCovariationApprox weightedQuadraticCovariationApprox
    covariationTaylorRemainderApprox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- On a compact interval, the first-order Taylor remainder of a `C¹`
function is uniformly small relative to the increment. -/
theorem uniform_firstTaylorRemainder_bound_on_Icc
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ x₀ ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, |x - x₀| < delta →
        |f x - f x₀ - deriv f x₀ * (x - x₀)| ≤
          epsilon * |x - x₀| := by
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have huc : UniformContinuousOn (deriv f) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hfirst.continuousOn
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro x₀ hx₀ x hx hxx₀
  rcases eq_or_ne x₀ x with rfl | hne
  · simp only [sub_self, mul_zero, abs_zero, le_refl]
  obtain ⟨y, hy, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 0) hne
      (hf.contDiffOn (s := Set.uIcc x₀ x))
  have hyab : y ∈ Set.Icc a b := by
    rcases hx₀ with ⟨hax₀, hx₀b⟩
    rcases hx with ⟨hax, hxb⟩
    grind [Set.uIoo, Set.uIcc]
  have hydist : dist y x₀ < delta := by
    calc
      dist y x₀ = dist x₀ y := dist_comm _ _
      _ ≤ dist x₀ x :=
        Real.dist_left_le_of_mem_uIcc (Set.uIoo_subset_uIcc_self hy)
      _ = |x - x₀| := by rw [Real.dist_eq, abs_sub_comm]
      _ < delta := hxx₀
  have hmod' := hmod y hyab x₀ hx₀ hydist
  rw [Real.dist_eq] at hmod'
  have hTaylor' : f x - f x₀ = deriv f y * (x - x₀) := by
    rw [taylor_within_zero_eval] at hTaylor
    norm_num [show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]] at hTaylor ⊢
    exact hTaylor
  rw [show f x - f x₀ - deriv f x₀ * (x - x₀) =
      (f x - f x₀) - deriv f x₀ * (x - x₀) by ring,
    hTaylor']
  rw [show deriv f y * (x - x₀) - deriv f x₀ * (x - x₀) =
    (deriv f y - deriv f x₀) * (x - x₀) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hmod'.le (abs_nonneg _)

/-- A global bound on the second derivative gives a quadratic bound for the
first-order Taylor remainder. -/
theorem firstTaylorRemainder_le_of_secondDeriv_bound
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K) (x0 x : ℝ) :
    |f x - f x0 - deriv f x0 * (x - x0)| ≤
      (K / 2) * (x - x0) ^ 2 := by
  rcases eq_or_ne x0 x with rfl | hne
  · simp
  obtain ⟨y, _hy, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne
      (hf.contDiffOn (s := Set.uIcc x0 x))
  have hu : UniqueDiffOn ℝ (Set.uIcc x0 x) := uniqueDiffOn_uIcc hne
  have hx0u : x0 ∈ Set.uIcc x0 x := Set.left_mem_uIcc
  have hfirst : iteratedDerivWithin 1 f (Set.uIcc x0 x) x0 = deriv f x0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
      (hf.contDiffAt.of_le (by norm_num)) hx0u]
    rw [show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
  have hTaylor' :
      f x - (f x0 + deriv f x0 * (x - x0)) =
        deriv (deriv f) y * (x - x0) ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, hfirst] at hTaylor
    rw [show iteratedDeriv 2 f = deriv (deriv f) by
      rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
        show iteratedDeriv 1 f = deriv f by
          rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
          simp only [iteratedDeriv_zero]]] at hTaylor
    norm_num at hTaylor ⊢
    simpa [smul_eq_mul, mul_comm] using hTaylor
  rw [show f x - f x0 - deriv f x0 * (x - x0) =
    f x - (f x0 + deriv f x0 * (x - x0)) by ring, hTaylor']
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg (x - x0))]
  calc
    |deriv (deriv f) y| * (x - x0) ^ 2 / 2 ≤
        K * (x - x0) ^ 2 / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hsecond y) (sq_nonneg _)) (by norm_num)
    _ = (K / 2) * (x - x0) ^ 2 := by ring

/-- A bounded second derivative controls an accumulated covariation Taylor
remainder by the geometric mean of the first process's quadratic variation
and the second process's fourth variation. -/
theorem abs_covariationTaylorRemainderApprox_le_sqrt_fourthVariation
    {W : Type*} (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    |covariationTaylorRemainderApprox f X Y t n omega| ≤
      (K / 2) * √(quadraticVariationApprox X t n omega *
        fourthVariationApprox Y t n omega) := by
  have hK : 0 ≤ K := (abs_nonneg (deriv (deriv f) 0)).trans (hsecond 0)
  have hsum : |covariationTaylorRemainderApprox f X Y t n omega| ≤
      (K / 2) * (∑ i ∈ Finset.range n,
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) ^ 2) := by
    unfold covariationTaylorRemainderApprox
    calc
      |∑ i ∈ Finset.range n, _| ≤ ∑ i ∈ Finset.range n, |_| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (K / 2) *
          (|X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega| *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul]
        have htaylor := firstTaylorRemainder_le_of_secondDeriv_bound
          f hf K hsecond
          (Y (uniformPartitionTime t n i) omega)
          (Y (uniformPartitionTime t n (i + 1)) omega)
        exact (mul_le_mul_of_nonneg_left htaylor (abs_nonneg _)).trans_eq (by ring)
      _ = (K / 2) * (∑ i ∈ Finset.range n,
          |X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega| *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) ^ 2) := by
        rw [Finset.mul_sum]
  have hcs : (∑ i ∈ Finset.range n,
      |X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega| *
      (Y (uniformPartitionTime t n (i + 1)) omega -
        Y (uniformPartitionTime t n i) omega) ^ 2) ≤
      √(quadraticVariationApprox X t n omega *
        fourthVariationApprox Y t n omega) := by
    apply Real.le_sqrt_of_sq_le
    unfold quadraticVariationApprox fourthVariationApprox
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (fun i => |X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega|)
      (fun i => (Y (uniformPartitionTime t n (i + 1)) omega -
        Y (uniformPartitionTime t n i) omega) ^ 2)
    rw [show (∑ i ∈ Finset.range n,
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) ^ 4) =
        ∑ i ∈ Finset.range n,
          ((Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) ^ 2) ^ 2 by
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    simpa only [sq_abs] using hraw
  exact hsum.trans
    (mul_le_mul_of_nonneg_left hcs (div_nonneg hK (by norm_num)))

/-- A continuous modification supplies the pathwise uniform first-order
Taylor estimate along all uniform grids. -/
theorem IsContinuousProcessModification.covariationTaylor_eventually_small
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {Y Ycont : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification Y Ycont P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ i ∈ Finset.range (n + 1),
        |f (Y (uniformPartitionTime t (n + 1) (i + 1)) omega) -
            f (Y (uniformPartitionTime t (n + 1) i) omega) -
          deriv f (Y (uniformPartitionTime t (n + 1) i) omega) *
            (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime t (n + 1) i) omega)| ≤
          epsilon *
            |Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime t (n + 1) i) omega| := by
  filter_upwards [hmod.uniformPartition_bounded t,
    hmod.uniformPartition_increments_tendsto t] with omega hbounded hincrements
  obtain ⟨R, hR⟩ := hbounded
  have hRnonneg : 0 ≤ R := by
    exact (abs_nonneg (Y (uniformPartitionTime t 1 0) omega)).trans
      (hR 0 0 (by omega))
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hTaylor⟩ :=
    uniform_firstTaylorRemainder_bound_on_Icc hf (-R) R epsilon hepsilon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hincrements delta hdelta)
  refine ⟨N, fun n hn i hi ↦ ?_⟩
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_add_right i 1).trans hi1
  have hYi : Y (uniformPartitionTime t (n + 1) i) omega ∈
      Set.Icc (-R) R := abs_le.mp (hR n i hi0)
  have hYi1 : Y (uniformPartitionTime t (n + 1) (i + 1)) omega ∈
      Set.Icc (-R) R := abs_le.mp (hR n (i + 1) hi1)
  exact hTaylor _ hYi _ hYi1 (hN n hn i hi)

/-- Convergence of the derivative-weighted covariation and disappearance of
the Taylor remainder imply the covariation chain rule in probability. -/
theorem tendstoInMeasure_quadraticCovariation_comp_of_weighted
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℝ → ℝ) (X Y : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (C : W → ℝ)
    (hweighted : TendstoInMeasure P
      (fun n ↦ weightedQuadraticCovariationApprox
        (fun s w ↦ deriv f (Y s w)) X Y t (n + 1))
      Filter.atTop C)
    (hremainder : TendstoInMeasure P
      (fun n ↦ covariationTaylorRemainderApprox f X Y t (n + 1))
      Filter.atTop (fun _ ↦ 0)) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationApprox X (fun s w ↦ f (Y s w))
        t (n + 1)) Filter.atTop C := by
  have hsum := hweighted.add_real_noMeas hremainder
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦
      (quadraticCovariationApprox_comp_eq_weighted_add_remainder
        f X Y t (n + 1) omega).symm
  · exact Filter.Eventually.of_forall fun omega ↦ by simp

/-- Measurability of the first-order covariation Taylor remainder. -/
theorem aestronglyMeasurable_covariationTaylorRemainderApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℝ → ℝ) (hf : Continuous f) (hderiv : Continuous (deriv f))
    (X Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (covariationTaylorRemainderApprox f X Y t n) P := by
  unfold covariationTaylorRemainderApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range n)
    (fun i _hi ↦
      ((hXmeas (uniformPartitionTime t n (i + 1))).sub
        (hXmeas (uniformPartitionTime t n i))).mul
      (((hf.comp_aestronglyMeasurable
          (hYmeas (uniformPartitionTime t n (i + 1)))).sub
        (hf.comp_aestronglyMeasurable
          (hYmeas (uniformPartitionTime t n i)))).sub
        ((hderiv.comp_aestronglyMeasurable
          (hYmeas (uniformPartitionTime t n i))).mul
          ((hYmeas (uniformPartitionTime t n (i + 1))).sub
            (hYmeas (uniformPartitionTime t n i))))))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

/-- A uniform little-o estimate for the one-step Taylor remainders makes
their accumulated covariation vanish in probability.  Convergent quadratic
variations of the two factors provide the tight random control through
Cauchy--Schwarz. -/
theorem covariationTaylorRemainder_tendstoInMeasure_zero_of_eventually_small
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ) (hf : Continuous f) (hderiv : Continuous (deriv f))
    (X Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (t : ℝ≥0) (QX QY : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox X t (n + 1)) Filter.atTop QX)
    (hQY : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox Y t (n + 1)) Filter.atTop QY)
    (hsmall : ∀ᵐ omega ∂P, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ i ∈ Finset.range (n + 1),
        |f (Y (uniformPartitionTime t (n + 1) (i + 1)) omega) -
            f (Y (uniformPartitionTime t (n + 1) i) omega) -
          deriv f (Y (uniformPartitionTime t (n + 1) i) omega) *
            (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime t (n + 1) i) omega)| ≤
          epsilon *
            |Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime t (n + 1) i) omega|) :
    TendstoInMeasure P
      (fun n ↦ covariationTaylorRemainderApprox f X Y t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun n omega ↦
    quadraticVariationApprox X t (n + 1) omega +
      quadraticVariationApprox Y t (n + 1) omega
  have hq : TendstoInMeasure P q Filter.atTop
      (fun omega ↦ QX omega + QY omega) := hQX.add_real_noMeas hQY
  apply TendstoInMeasure.of_ae_two_scale_uniform_control
    (P := P)
    (f := fun n ↦ covariationTaylorRemainderApprox f X Y t (n + 1))
    (q := q) (F := fun _ _ _ ↦ 0) (G := fun _ _ ↦ 0)
    (g := fun _ ↦ 0) (qlim := fun omega ↦ QX omega + QY omega)
  · intro n
    exact aestronglyMeasurable_covariationTaylorRemainderApprox
      f hf hderiv X Y hXmeas hYmeas t (n + 1)
  · intro k
    exact tendstoInMeasure_of_tendsto_ae
      (fun _ ↦ aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  · exact tendstoInMeasure_of_tendsto_ae
      (fun _ ↦ aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ ↦ tendsto_const_nhds)
  · exact hq
  · intro n omega
    exact add_nonneg
      (quadraticVariationApprox_nonneg X t (n + 1) omega)
      (quadraticVariationApprox_nonneg Y t (n + 1) omega)
  · filter_upwards [hsmall] with omega homega
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := homega epsilon hepsilon
    refine ⟨N, fun _k n _hk hn ↦ ?_⟩
    have hsum : abs (covariationTaylorRemainderApprox f X Y t (n + 1) omega) ≤
        epsilon * (∑ i ∈ Finset.range (n + 1),
          abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
            X (uniformPartitionTime t (n + 1) i) omega) *
          abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
            Y (uniformPartitionTime t (n + 1) i) omega)) := by
      unfold covariationTaylorRemainderApprox
      calc
        abs (∑ i ∈ Finset.range (n + 1), _) ≤
            ∑ i ∈ Finset.range (n + 1), abs _ :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (n + 1), epsilon *
            (abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
                X (uniformPartitionTime t (n + 1) i) omega) *
              abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
                Y (uniformPartitionTime t (n + 1) i) omega)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          calc
            _ ≤ abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
                  X (uniformPartitionTime t (n + 1) i) omega) *
                (epsilon * abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
                  Y (uniformPartitionTime t (n + 1) i) omega)) :=
              mul_le_mul_of_nonneg_left (hN n hn i hi) (abs_nonneg _)
            _ = _ := by ring
        _ = epsilon * (∑ i ∈ Finset.range (n + 1),
            abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
              X (uniformPartitionTime t (n + 1) i) omega) *
            abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
              Y (uniformPartitionTime t (n + 1) i) omega)) := by
          rw [Finset.mul_sum]
    have hcs : (∑ i ∈ Finset.range (n + 1),
        abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) *
        abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
          Y (uniformPartitionTime t (n + 1) i) omega)) ≤
        √(quadraticVariationApprox X t (n + 1) omega *
          quadraticVariationApprox Y t (n + 1) omega) := by
      apply Real.le_sqrt_of_sq_le
      unfold quadraticVariationApprox
      simpa only [sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
          (fun i ↦ abs (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
            X (uniformPartitionTime t (n + 1) i) omega))
          (fun i ↦ abs (Y (uniformPartitionTime t (n + 1) (i + 1)) omega -
            Y (uniformPartitionTime t (n + 1) i) omega)))
    let a := quadraticVariationApprox X t (n + 1) omega
    let b := quadraticVariationApprox Y t (n + 1) omega
    have ha : 0 ≤ a := quadraticVariationApprox_nonneg X t (n + 1) omega
    have hb : 0 ≤ b := quadraticVariationApprox_nonneg Y t (n + 1) omega
    have hsqrt : √(a * b) ≤ a + b := by
      have hs0 := Real.sqrt_nonneg (a * b)
      have hs2 := Real.sq_sqrt (mul_nonneg ha hb)
      nlinarith [sq_nonneg (a - b)]
    have htotal := hsum.trans (mul_le_mul_of_nonneg_left
      (hcs.trans hsqrt) hepsilon.le)
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, q, a, b] using htotal

/-- Continuous-path regularity discharges the uniform Taylor premise in the
previous theorem. -/
theorem
    covariationTaylorRemainder_tendstoInMeasure_zero_of_continuousModification
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (X Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (t : ℝ≥0) (QX QY : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox X t (n + 1)) Filter.atTop QX)
    (hQY : TendstoInMeasure P
      (fun n ↦ quadraticVariationApprox Y t (n + 1)) Filter.atTop QY)
    (Ycont : ℝ≥0 → W → ℝ)
    (hYmod : IsContinuousProcessModification Y Ycont P) :
    TendstoInMeasure P
      (fun n ↦ covariationTaylorRemainderApprox f X Y t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
  have hderiv : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  exact covariationTaylorRemainder_tendstoInMeasure_zero_of_eventually_small
    f hf.continuous hderiv X Y hXmeas hYmeas t QX QY hQX hQY
      (hYmod.covariationTaylor_eventually_small f hf t)

/-- When the transformed process is pre-Brownian, a global second-derivative
bound replaces path continuity in the covariation Taylor argument.  The
remainder is controlled by the geometric mean of the other process's
quadratic variation and Brownian fourth variation. -/
theorem
    covariationTaylorRemainder_tendstoInMeasure_zero_of_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ}
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    (hB : IsPreBrownianReal B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (QX : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop QX) :
    TendstoInMeasure P
      (fun n => covariationTaylorRemainderApprox f X B t (n + 1))
      Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hderiv : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have hmeas : ∀ n, AEStronglyMeasurable
      (covariationTaylorRemainderApprox f X B t (n + 1)) P := fun n =>
    aestronglyMeasurable_covariationTaylorRemainderApprox
      f hf.continuous hderiv X B hXmeas
        (fun s => (hB.aemeasurable s).aestronglyMeasurable) t (n + 1)
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ms, hms, hQXae⟩ :=
    (hQX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hfourth :=
    fourthVariationApprox_preBrownianReal_tendstoInMeasure_zero hB t
  have hindices : StrictMono (ns ∘ ms) := hns.comp hms
  have hfourthSub : TendstoInMeasure P
      (fun i => fourthVariationApprox B t (ns (ms i) + 1))
      Filter.atTop (fun _ => 0) := by
    change TendstoInMeasure P
      ((fun n => fourthVariationApprox B t (n + 1)) ∘ (ns ∘ ms))
      Filter.atTop (fun _ => 0)
    exact hfourth.comp hindices.tendsto_atTop
  obtain ⟨ls, hls, hfourthAE⟩ := hfourthSub.exists_seq_tendsto_ae
  refine ⟨ms ∘ ls, hms.comp hls, ?_⟩
  filter_upwards [hQXae, hfourthAE] with omega hqv hfourthOmega
  have hqv' : Filter.Tendsto
      (fun i => quadraticVariationApprox X t (ns (ms (ls i)) + 1) omega)
      Filter.atTop (nhds (QX omega)) := hqv.comp hls.tendsto_atTop
  have hproduct : Filter.Tendsto
      (fun i => quadraticVariationApprox X t (ns (ms (ls i)) + 1) omega *
        fourthVariationApprox B t (ns (ms (ls i)) + 1) omega)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hqv'.mul hfourthOmega
  have hsqrt : Filter.Tendsto
      (fun i => √(quadraticVariationApprox X t (ns (ms (ls i)) + 1) omega *
        fourthVariationApprox B t (ns (ms (ls i)) + 1) omega))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (Real.sqrt ∘ fun i =>
        quadraticVariationApprox X t (ns (ms (ls i)) + 1) omega *
          fourthVariationApprox B t (ns (ms (ls i)) + 1) omega)
      Filter.atTop (nhds 0)
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hproduct
  have hupper : Filter.Tendsto
      (fun i => (K / 2) *
        √(quadraticVariationApprox X t (ns (ms (ls i)) + 1) omega *
          fourthVariationApprox B t (ns (ms (ls i)) + 1) omega))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hsqrt.const_mul (K / 2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
  · exact Filter.Eventually.of_forall fun i =>
      abs_covariationTaylorRemainderApprox_le_sqrt_fourthVariation
        f hf K hsecond X B t (ns (ms (ls i)) + 1) omega
  · exact hupper

/-- A derivative-weighted covariation limit gives the covariation chain
rule against a pre-Brownian process.  Unlike the continuous-modification
variant, the nonlinear Taylor error is discharged directly by the Gaussian
fourth-variation estimate. -/
theorem tendstoInMeasure_quadraticCovariation_comp_of_weighted_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ}
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K : ℝ)
    (hsecond : ∀ y, |deriv (deriv f) y| ≤ K)
    (hB : IsPreBrownianReal B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (QX C : W → ℝ)
    (hQX : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop QX)
    (hweighted : TendstoInMeasure P
      (fun n => weightedQuadraticCovariationApprox
        (fun s w => deriv f (B s w)) X B t (n + 1))
      Filter.atTop C) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox X (fun s w => f (B s w))
        t (n + 1)) Filter.atTop C := by
  apply tendstoInMeasure_quadraticCovariation_comp_of_weighted
    f X B t C hweighted
  exact covariationTaylorRemainder_tendstoInMeasure_zero_of_preBrownian
    f hf K hsecond hB hXmeas t QX hQX

/-- A quadratic partition sum whose state-dependent weight is sampled from
`Z`, while the squared increments are sampled from `M`.  This separates the
state process from its stochastic-integral component during drift removal. -/
noncomputable def generalItoMixedQuadraticApprox
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / 2 : ℝ) *
      itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega) *
      (M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega) ^ 2

/-- The coarse-step counterpart of `generalItoMixedQuadraticApprox`. -/
noncomputable def generalItoMixedQuadraticCompletedStepApprox
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n k : ℕ) (omega : W) : ℝ :=
  ∑ j ∈ Finset.range k,
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t k j : ℝ)
      (Z (uniformPartitionTime t k j) omega)) *
    (quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k (j + 1)) omega -
      quadraticVariationBeforeStopApprox M t n
        (uniformPartitionTime t k j) omega)

theorem aestronglyMeasurable_generalItoMixedQuadraticApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoMixedQuadraticApprox f Z M t n) P := by
  unfold generalItoMixedQuadraticApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega) *
        (M (uniformPartitionTime t n (i + 1)) omega -
          M (uniformPartitionTime t n i) omega) ^ 2) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    have hpair : AEStronglyMeasurable
        (fun omega => ((uniformPartitionTime t n i : ℝ),
          Z (uniformPartitionTime t n i) omega)) P :=
      aestronglyMeasurable_const.prodMk
        (hZmeas (uniformPartitionTime t n i))
    have hweight : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) P :=
      hsecond.comp_aestronglyMeasurable hpair
    have hincrement : AEStronglyMeasurable
        (fun omega => M (uniformPartitionTime t n (i + 1)) omega -
          M (uniformPartitionTime t n i) omega) P :=
      (hMmeas (uniformPartitionTime t n (i + 1))).sub
        (hMmeas (uniformPartitionTime t n i))
    exact (aestronglyMeasurable_const.mul hweight).mul
      (hincrement.pow 2)
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

theorem abs_generalItoMixedQuadraticApprox_sub_completedStep_le_of_blockWeight
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (ht : 0 < t) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (K : ℝ)
    (omega : W)
    (hweight : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < uniformPartitionTime t n (i + 1) ∧
        uniformPartitionTime t n (i + 1) ≤
          uniformPartitionTime t k (j + 1) →
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega) -
        itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
          (Z (uniformPartitionTime t k j) omega)| ≤ K) :
    |generalItoMixedQuadraticApprox f Z M t n omega -
      generalItoMixedQuadraticCompletedStepApprox f Z M t n k omega| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox M t n omega := by
  unfold generalItoMixedQuadraticApprox
  unfold generalItoMixedQuadraticCompletedStepApprox
  apply abs_weightedQuadraticVariation_sub_completedBlocks_le
    M t n k
      (fun i omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega))
      (fun j omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (Z (uniformPartitionTime t k j) omega))
      ((1 / 2 : ℝ) * K) omega
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hr0 : 0 < uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    positivity
  have hrt : uniformPartitionTime t n (i + 1) ≤ t :=
    (uniformPartitionTime_mem_Icc_of_le t hn hi1).2
  have hstep := abs_sub_uniformPartition_rightEndpoint_step_sum_le
    t (uniformPartitionTime t n (i + 1)) k hk hr0 hrt
      (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega))
      (fun j => itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (Z (uniformPartitionTime t k j) omega)) K
      (fun j hj hactive => hweight i hi j hj hactive)
  have hsum :
      (∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t k j : ℝ)
            (Z (uniformPartitionTime t k j) omega)
        else 0) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
            (Z (uniformPartitionTime t k j) omega)
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    split_ifs <;> simp
  rw [hsum, ← mul_sub, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left hstep (by norm_num)

theorem generalItoMixedQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z M : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (ht : 0 < t) (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => Z s omega) (Set.Icc 0 t)) :
    ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
      |generalItoMixedQuadraticApprox f Z M t (n + 1) omega -
        generalItoMixedQuadraticCompletedStepApprox
          f Z M t (n + 1) (k + 1) omega| ≤
        (1 / 2 : ℝ) * K *
          quadraticVariationApprox M t (n + 1) omega := by
  intro K hK
  obtain ⟨N, hN⟩ := generalItoSecondDerivative_activeBlockWeight_eventually_small
    f Z t omega hsecond hpath K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  apply abs_generalItoMixedQuadraticApprox_sub_completedStep_le_of_blockWeight
    f Z M t ht (n + 1) (k + 1) (Nat.zero_lt_succ n)
      (Nat.zero_lt_succ k) K omega
  intro i hi j hj hactive
  exact (hN k n hk hn i hi j hj hactive).le

theorem
    IsContinuousProcessModification.generalItoMixedQuadraticApprox_sub_completedStep_eventually_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {Z Y M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification Z Y P)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2)) :
    ∀ᵐ omega ∂P, ∀ K : ℝ, 0 < K → ∃ N : ℕ,
      ∀ k n, N ≤ k → N ≤ n →
        |generalItoMixedQuadraticApprox f Z M t (n + 1) omega -
          generalItoMixedQuadraticCompletedStepApprox
            f Z M t (n + 1) (k + 1) omega| ≤
          (1 / 2 : ℝ) * K *
            quadraticVariationApprox M t (n + 1) omega := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid]
    with omega hcontinuous hagree
  intro K hK
  obtain ⟨N, hbound⟩ :=
    generalItoMixedQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
      f Y M t ht omega hsecond hcontinuous.continuousOn K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  have hfine : generalItoMixedQuadraticApprox f Z M t (n + 1) omega =
      generalItoMixedQuadraticApprox f Y M t (n + 1) omega := by
    unfold generalItoMixedQuadraticApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hagree n i]
  have hcoarse :
      generalItoMixedQuadraticCompletedStepApprox
          f Z M t (n + 1) (k + 1) omega =
        generalItoMixedQuadraticCompletedStepApprox
          f Y M t (n + 1) (k + 1) omega := by
    unfold generalItoMixedQuadraticCompletedStepApprox
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hagree k j]
  rw [hfine, hcoarse]
  exact hbound k n hk hn

theorem sum_abs_uniformPartition_increment_mul_le_sqrt
    {W : Type*} [MeasurableSpace W]
    (A M : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      |A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega| *
      |M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega|) ≤
      √(quadraticVariationApprox A t n omega *
        quadraticVariationApprox M t n omega) := by
  apply Real.le_sqrt_of_sq_le
  unfold quadraticVariationApprox
  simpa only [sq_abs] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (fun i => |A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega|)
      (fun i => |M (uniformPartitionTime t n (i + 1)) omega -
        M (uniformPartitionTime t n i) omega|))

theorem abs_generalItoMixedQuadraticApprox_add_sub_le
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Z A M : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) (K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ i ∈ Finset.range n,
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (Z (uniformPartitionTime t n i) omega)| ≤ K) :
    |generalItoMixedQuadraticApprox f Z
        (fun s omega => A s omega + M s omega) t n omega -
      generalItoMixedQuadraticApprox f Z M t n omega| ≤
      (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t n omega +
          2 * √(quadraticVariationApprox A t n omega *
            quadraticVariationApprox M t n omega)) := by
  have hdiff :
      generalItoMixedQuadraticApprox f Z
          (fun s omega => A s omega + M s omega) t n omega -
        generalItoMixedQuadraticApprox f Z M t n omega =
      ∑ i ∈ Finset.range n,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) *
        ((A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) ^ 2 +
          2 * (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) *
            (M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega)) := by
    unfold generalItoMixedQuadraticApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (Z (uniformPartitionTime t n i) omega)) *
        ((A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) ^ 2 +
          2 * (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega) *
            (M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) * K *
          ((A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega) ^ 2 +
            2 * |A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega| *
              |M (uniformPartitionTime t n (i + 1)) omega -
                M (uniformPartitionTime t n i) omega|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        (1 / 2 : ℝ) *
            |itoSpaceSecondDerivative f
              (uniformPartitionTime t n i : ℝ)
              (Z (uniformPartitionTime t n i) omega)| *
            |(A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2 +
              2 * (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) *
                (M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega)| ≤
          (1 / 2 : ℝ) * K *
            (|(A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2| +
              |2 * (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) *
                (M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega)|) := by
            gcongr
            · exact hweight i hi
            · exact abs_add_le _ _
        _ = _ := by
          rw [abs_sq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t n omega +
          2 * ∑ i ∈ Finset.range n,
            |A (uniformPartitionTime t n (i + 1)) omega -
              A (uniformPartitionTime t n i) omega| *
            |M (uniformPartitionTime t n (i + 1)) omega -
              M (uniformPartitionTime t n i) omega|) := by
      unfold quadraticVariationApprox
      calc
        _ = ∑ i ∈ Finset.range n,
            ((1 / 2 : ℝ) * K *
              (A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega) ^ 2 +
            (1 / 2 : ℝ) * K *
              (2 * |A (uniformPartitionTime t n (i + 1)) omega -
                A (uniformPartitionTime t n i) omega| *
                |M (uniformPartitionTime t n (i + 1)) omega -
                  M (uniformPartitionTime t n i) omega|)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
        _ = (∑ i ∈ Finset.range n,
              (1 / 2 : ℝ) * K *
                (A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega) ^ 2) +
            ∑ i ∈ Finset.range n,
              (1 / 2 : ℝ) * K *
                (2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) :=
              Finset.sum_add_distrib
        _ = (1 / 2 : ℝ) * K *
              (∑ i ∈ Finset.range n,
                (A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega) ^ 2) +
            (1 / 2 : ℝ) * K *
              (∑ i ∈ Finset.range n,
                2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) := by
              rw [Finset.mul_sum, Finset.mul_sum]
        _ = _ := by
          have hsum_two :
              (∑ i ∈ Finset.range n,
                2 * |A (uniformPartitionTime t n (i + 1)) omega -
                  A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega|) =
                2 * ∑ i ∈ Finset.range n,
                  |A (uniformPartitionTime t n (i + 1)) omega -
                    A (uniformPartitionTime t n i) omega| *
                  |M (uniformPartitionTime t n (i + 1)) omega -
                    M (uniformPartitionTime t n i) omega| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          rw [hsum_two]
          ring
    _ ≤ _ := by
      gcongr
      exact sum_abs_uniformPartition_increment_mul_le_sqrt A M t n omega

theorem generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z A M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hAmeas : ∀ s, AEStronglyMeasurable (A s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (q : W → ℝ)
    (hA : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n => quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0))
    (hM : TendstoInMeasure P
      (fun n => quadraticVariationApprox M t (n + 1))
      Filter.atTop q)
    (hweight : ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧
      ∀ n i : ℕ, i ≤ n + 1 →
        |itoSpaceSecondDerivative f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (Z (uniformPartitionTime t (n + 1) i) omega)| ≤ K) :
    TendstoInMeasure P
      (fun n omega =>
        generalItoMixedQuadraticApprox f Z
            (fun s omega => A s omega + M s omega) t (n + 1) omega -
          generalItoMixedQuadraticApprox f Z M t (n + 1) omega)
      Filter.atTop (fun _ => 0) := by
  have hdiffmeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        generalItoMixedQuadraticApprox f Z
            (fun s omega => A s omega + M s omega) t (n + 1) omega -
          generalItoMixedQuadraticApprox f Z M t (n + 1) omega) P := by
    intro n
    exact (aestronglyMeasurable_generalItoMixedQuadraticApprox
      f hsecond Z (fun s omega => A s omega + M s omega)
        hZmeas (fun s => (hAmeas s).add (hMmeas s)) t (n + 1)).sub
      (aestronglyMeasurable_generalItoMixedQuadraticApprox
        f hsecond Z M hZmeas hMmeas t (n + 1))
  rw [exists_seq_tendstoInMeasure_atTop_iff hdiffmeas]
  intro ns hns
  obtain ⟨r, hr, hMomega⟩ :=
    (hM.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨r, hr, ?_⟩
  filter_upwards [hA, hMomega, hweight]
    with omega hAomega hMlimit homega
  obtain ⟨K, hK, hKbound⟩ := homega
  have hindices : StrictMono (ns ∘ r) := hns.comp hr
  have hAfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox A t (ns (r i) + 1) omega)
      Filter.atTop (nhds 0) := by
    convert hAomega.comp hindices.tendsto_atTop using 1
    funext i
    rfl
  have hMfinal : Filter.Tendsto
      (fun i => quadraticVariationApprox M t (ns (r i) + 1) omega)
      Filter.atTop (nhds (q omega)) := by
    simpa only [Function.comp_apply] using hMlimit
  have hsqrt : Filter.Tendsto
      (fun i => √(quadraticVariationApprox A t (ns (r i) + 1) omega *
        quadraticVariationApprox M t (ns (r i) + 1) omega))
      Filter.atTop (nhds 0) := by
    have hraw := (hAfinal.mul hMfinal).sqrt
    simpa only [zero_mul, Real.sqrt_zero] using hraw
  have hupper : Filter.Tendsto
      (fun i => (1 / 2 : ℝ) * K *
        (quadraticVariationApprox A t (ns (r i) + 1) omega +
          2 * √(quadraticVariationApprox A t (ns (r i) + 1) omega *
            quadraticVariationApprox M t (ns (r i) + 1) omega)))
      Filter.atTop (nhds 0) := by
    have htwo : Filter.Tendsto (fun _ : ℕ => (2 : ℝ))
        Filter.atTop (nhds 2) := tendsto_const_nhds
    have hscale : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ) * K)
        Filter.atTop (nhds ((1 / 2 : ℝ) * K)) := tendsto_const_nhds
    have hinside := hAfinal.add (htwo.mul hsqrt)
    have hscaled := hscale.mul hinside
    simpa only [mul_zero, add_zero] using hscaled
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero (g := fun i => (1 / 2 : ℝ) * K *
      (quadraticVariationApprox A t (ns (r i) + 1) omega +
        2 * √(quadraticVariationApprox A t (ns (r i) + 1) omega *
          quadraticVariationApprox M t (ns (r i) + 1) omega)))
  · intro i
    exact abs_nonneg _
  · intro i
    apply abs_generalItoMixedQuadraticApprox_add_sub_le
      f Z A M t (ns (r i) + 1) omega K hK
    intro j hj
    apply hKbound (ns (r i)) j
    exact (Nat.le_add_right j 1).trans (Finset.mem_range.mp hj)
  · exact hupper

theorem integral_Ioc_sub_integral_Ioc_eq_integral_Ioc
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} {q : α → ℝ} {z a b t : α}
    (hza : z ≤ a) (hab : a ≤ b) (hbt : b ≤ t)
    (hq : IntegrableOn q (Ioc z t) μ) :
    (∫ s in Ioc z b, q s ∂μ) - (∫ s in Ioc z a, q s ∂μ) =
      ∫ s in Ioc a b, q s ∂μ := by
  have hsmall : Ioc z b ⊆ Ioc z t := Ioc_subset_Ioc_right hbt
  have hsub : Ioc z a ⊆ Ioc z b := Ioc_subset_Ioc_right hab
  have hdiff : Ioc z b \ Ioc z a = Ioc a b := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_Ioc]
    grind
  rw [← hdiff]
  exact (setIntegral_sdiff measurableSet_Ioc (hq.mono_set hsmall) hsub).symm

theorem biUnion_Ioc_succ_eq_Ioc
    {α : Type*} [LinearOrder α] (a : ℕ → α) (ha : Monotone a) (N : ℕ) :
    (⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1))) = Ioc (a 0) (a N) := by
  apply Subset.antisymm
  · rw [iUnion_subset_iff]
    intro i
    rw [iUnion_subset_iff]
    intro hi
    have hiN : i < N := Finset.mem_range.mp hi
    exact Ioc_subset_Ioc (ha (Nat.zero_le i)) (ha (Nat.succ_le_iff.mpr hiN))
  · exact Ioc_subset_biUnion_Ioc N a

theorem pairwise_disjoint_Ioc_succ
    {α : Type*} [LinearOrder α] (a : ℕ → α) (ha : Monotone a) (N : ℕ) :
    Set.Pairwise (↑(Finset.range N))
      (fun i j => Disjoint (Ioc (a i) (a (i + 1)))
        (Ioc (a j) (a (j + 1)))) := by
  intro i hi j hj hij
  exact ha.pairwise_disjoint_on_Ioc_succ hij

theorem abs_uniformPartition_weighted_integral_sub_le
    {μ : Measure ℝ≥0} (q w : ℝ≥0 → ℝ) (t : ℝ≥0) (k : ℕ) (hk : 0 < k)
    (hq : IntegrableOn q (Ioc 0 t) μ)
    (hwq : IntegrableOn (fun s => w s * q s) (Ioc 0 t) μ)
    (hq_nonneg : ∀ s, 0 ≤ q s) (K : ℝ) (_hK : 0 ≤ K)
    (hclose : ∀ i ∈ Finset.range k, ∀ s ∈
      Ioc (uniformPartitionTime t k i) (uniformPartitionTime t k (i + 1)),
      |w (uniformPartitionTime t k i) - w s| ≤ K) :
    |(∑ i ∈ Finset.range k, w (uniformPartitionTime t k i) *
        ((∫ s in Ioc 0 (uniformPartitionTime t k (i + 1)), q s ∂μ) -
          ∫ s in Ioc 0 (uniformPartitionTime t k i), q s ∂μ)) -
      ∫ s in Ioc 0 t, w s * q s ∂μ| ≤
        K * ∫ s in Ioc 0 t, q s ∂μ := by
  let a : ℕ → ℝ≥0 := uniformPartitionTime t k
  have ha : Monotone a := monotone_uniformPartitionTime_general t k
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have ha0 : a 0 = 0 := by
    simp only [a, uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  have hak : a k = t := by
    dsimp only [a]
    unfold uniformPartitionTime
    exact mul_div_cancel_right₀ t hk0
  have hcell_subset : ∀ i ∈ Finset.range k,
      Ioc (a i) (a (i + 1)) ⊆ Ioc 0 t := by
    intro i hi
    have hiN : i < k := Finset.mem_range.mp hi
    exact Ioc_subset_Ioc (ha0.ge.trans (ha (Nat.zero_le i)))
      ((ha (Nat.succ_le_iff.mpr hiN)).trans hak.le)
  have hcells : (⋃ i ∈ Finset.range k, Ioc (a i) (a (i + 1))) =
      Ioc 0 t := by
    rw [biUnion_Ioc_succ_eq_Ioc a ha k, ha0, hak]
  have hpair := pairwise_disjoint_Ioc_succ a ha k
  have hq_partition :
      (∫ s in Ioc 0 t, q s ∂μ) =
        ∑ i ∈ Finset.range k, ∫ s in Ioc (a i) (a (i + 1)), q s ∂μ := by
    rw [← hcells]
    exact integral_biUnion_finset (Finset.range k)
      (fun _ _ => measurableSet_Ioc) hpair
      (fun i hi => hq.mono_set (hcell_subset i hi))
  have hwq_partition :
      (∫ s in Ioc 0 t, w s * q s ∂μ) =
        ∑ i ∈ Finset.range k,
          ∫ s in Ioc (a i) (a (i + 1)), w s * q s ∂μ := by
    rw [← hcells]
    exact integral_biUnion_finset (Finset.range k)
      (fun _ _ => measurableSet_Ioc) hpair
      (fun i hi => hwq.mono_set (hcell_subset i hi))
  have hKq : IntegrableOn (fun s => K * q s) (Ioc 0 t) μ := hq.const_mul K
  have hKq_partition :
      (∫ s in Ioc 0 t, K * q s ∂μ) =
        ∑ i ∈ Finset.range k,
          ∫ s in Ioc (a i) (a (i + 1)), K * q s ∂μ := by
    rw [← hcells]
    exact integral_biUnion_finset (Finset.range k)
      (fun _ _ => measurableSet_Ioc) hpair
      (fun i hi => hKq.mono_set (hcell_subset i hi))
  have hblock : ∀ i ∈ Finset.range k,
      (∫ s in Ioc 0 (a (i + 1)), q s ∂μ) -
          ∫ s in Ioc 0 (a i), q s ∂μ =
        ∫ s in Ioc (a i) (a (i + 1)), q s ∂μ := by
    intro i hi
    have hiN : i < k := Finset.mem_range.mp hi
    apply integral_Ioc_sub_integral_Ioc_eq_integral_Ioc
      (ha0.ge.trans (ha (Nat.zero_le i))) (ha (Nat.le_succ i))
      ((ha (Nat.succ_le_iff.mpr hiN)).trans hak.le) hq
  have hterm : ∀ i ∈ Finset.range k,
      |w (a i) * (∫ s in Ioc (a i) (a (i + 1)), q s ∂μ) -
          ∫ s in Ioc (a i) (a (i + 1)), w s * q s ∂μ| ≤
        ∫ s in Ioc (a i) (a (i + 1)), K * q s ∂μ := by
    intro i hi
    have hqi := hq.mono_set (hcell_subset i hi)
    have hwqi := hwq.mono_set (hcell_subset i hi)
    have hKqi := hKq.mono_set (hcell_subset i hi)
    rw [← integral_const_mul]
    rw [← integral_sub (hqi.const_mul _) hwqi]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hKqi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← sub_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hq_nonneg s)]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [a] using hclose i hi s hs) (hq_nonneg s)
  calc
    _ = |∑ i ∈ Finset.range k,
        (w (a i) * (∫ s in Ioc (a i) (a (i + 1)), q s ∂μ) -
          ∫ s in Ioc (a i) (a (i + 1)), w s * q s ∂μ)| := by
      rw [hwq_partition, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hblock i hi]
    _ ≤ ∑ i ∈ Finset.range k,
        |w (a i) * (∫ s in Ioc (a i) (a (i + 1)), q s ∂μ) -
          ∫ s in Ioc (a i) (a (i + 1)), w s * q s ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range k,
        ∫ s in Ioc (a i) (a (i + 1)), K * q s ∂μ := by
      exact Finset.sum_le_sum hterm
    _ = ∫ s in Ioc 0 t, K * q s ∂μ := hKq_partition.symm
    _ = K * ∫ s in Ioc 0 t, q s ∂μ := by rw [integral_const_mul]

theorem uniformPartition_weighted_integral_tendsto
    {μ : Measure ℝ≥0} (q w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hq : IntegrableOn q (Ioc 0 t) μ)
    (hwq : IntegrableOn (fun s => w s * q s) (Ioc 0 t) μ)
    (hq_nonneg : ∀ s, 0 ≤ q s)
    (hw : ContinuousOn w (Icc 0 t)) :
    Filter.Tendsto
      (fun k => ∑ i ∈ Finset.range (k + 1),
        w (uniformPartitionTime t (k + 1) i) *
          ((∫ s in Ioc 0 (uniformPartitionTime t (k + 1) (i + 1)),
              q s ∂μ) -
            ∫ s in Ioc 0 (uniformPartitionTime t (k + 1) i), q s ∂μ))
      Filter.atTop (nhds (∫ s in Ioc 0 t, w s * q s ∂μ)) := by
  have hQ : 0 ≤ ∫ s in Ioc 0 t, q s ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (hq_nonneg ·))
  have huc : UniformContinuousOn w (Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let K : ℝ := epsilon / ((∫ s in Ioc 0 t, q s ∂μ) + 1)
  have hQone : 0 < (∫ s in Ioc 0 t, q s ∂μ) + 1 := by linarith
  have hK : 0 < K := div_pos hepsilon hQone
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc K hK
  have hdivNN : Filter.Tendsto
      (fun k : ℕ => t / ((k + 1 : ℕ) : ℝ≥0)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun k : ℕ => ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun k : ℕ => t / ((k + 1 : ℕ) : ℝ≥0))
      Filter.atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv eta heta
  refine ⟨N, fun k hk => ?_⟩
  have hmesh : ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta := by
    have hnear := hN k hk
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  have herr := abs_uniformPartition_weighted_integral_sub_le
    q w t (k + 1) (Nat.zero_lt_succ k) hq hwq hq_nonneg K hK.le
      (fun i hi s hs => by
        have hiN : i < k + 1 := Finset.mem_range.mp hi
        have hleftMem := uniformPartitionTime_mem_Icc_of_le t
          (Nat.zero_lt_succ k) (Nat.le_of_lt hiN)
        have hrightMem := uniformPartitionTime_mem_Icc_of_le t
          (Nat.zero_lt_succ k) (Nat.succ_le_iff.mpr hiN)
        have hsMem : s ∈ Icc (0 : ℝ≥0) t :=
          ⟨hleftMem.1.trans hs.1.le, hs.2.trans hrightMem.2⟩
        have hdistLe : dist (uniformPartitionTime t (k + 1) i) s ≤
            dist (uniformPartitionTime t (k + 1) i)
              (uniformPartitionTime t (k + 1) (i + 1)) := by
          rw [dist_comm (uniformPartitionTime t (k + 1) i) s,
            dist_comm (uniformPartitionTime t (k + 1) i)
              (uniformPartitionTime t (k + 1) (i + 1)),
            NNReal.dist_eq, NNReal.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hs.1.le)),
            abs_of_nonneg (sub_nonneg.mpr (by
              norm_cast
              unfold uniformPartitionTime
              gcongr
              omega))]
          exact sub_le_sub_right (by exact_mod_cast hs.2) _
        have hdist : dist (uniformPartitionTime t (k + 1) i) s < eta :=
          hdistLe.trans_lt
            ((show dist (uniformPartitionTime t (k + 1) i)
                (uniformPartitionTime t (k + 1) (i + 1)) =
                  ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) by
              rw [dist_comm]
              exact dist_uniformPartitionTime_succ_eq t
                (Nat.zero_lt_succ k) i).trans_lt hmesh)
        have hout := hmod
          (uniformPartitionTime t (k + 1) i) hleftMem s hsMem hdist
        exact (by simpa only [Real.dist_eq] using hout.le))
  have hKQ : K * (∫ s in Ioc 0 t, q s ∂μ) < epsilon := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hQone).2
    nlinarith
  rw [Real.dist_eq]
  exact herr.trans_lt hKQ

theorem generalItoMixedQuadratic_completedStep_naturalItoProcess_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (t : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    TendstoInMeasure P
      (fun n => generalItoMixedQuadraticCompletedStepApprox f Z
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1) k)
      Filter.atTop (fun omega => ∑ i ∈ Finset.range k,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k i : ℝ)
          (Z (uniformPartitionTime t k i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t k (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t k i) omega)) := by
  unfold generalItoMixedQuadraticCompletedStepApprox
  apply quadraticVariation_completedStepWeight_naturalItoProcess
    hB hsm U t k hk
  intro i _hi
  have hpair : AEStronglyMeasurable
      (fun omega => ((uniformPartitionTime t k i : ℝ),
        Z (uniformPartitionTime t k i) omega)) P :=
    aestronglyMeasurable_const.prodMk
      (hZmeas (uniformPartitionTime t k i))
  exact aestronglyMeasurable_const.mul
    (hsecond.comp_aestronglyMeasurable hpair)

theorem generalItoMixedQuadratic_naturalItoProcess_tendstoInMeasure_of_bracketStep_limit
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (t : ℝ≥0) (ht : 0 < t) (G : W → ℝ)
    (hG : TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G)
    (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification Z Y P) :
    TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f Z
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1)) Filter.atTop G := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  let F : ℕ → ℕ → W → ℝ := fun k n =>
    generalItoMixedQuadraticCompletedStepApprox
      f Z M t (n + 1) (k + 1)
  let Gk : ℕ → W → ℝ := fun k omega => ∑ i ∈ Finset.range (k + 1),
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t (k + 1) i : ℝ)
      (Z (uniformPartitionTime t (k + 1) i) omega)) *
    (predictableQuadraticVariation hsm U
        (uniformPartitionTime t (k + 1) (i + 1)) omega -
      predictableQuadraticVariation hsm U
        (uniformPartitionTime t (k + 1) i) omega)
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U s).aestronglyMeasurable
  have hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (Gk k) := by
    intro k
    simpa only [F, Gk, M] using
      (generalItoMixedQuadratic_completedStep_naturalItoProcess_tendstoInMeasure
        hB hsm U f hsecond Z hZmeas t (k + 1) (Nat.zero_lt_succ k))
  apply TendstoInMeasure.of_ae_two_scale_uniform_control
    (P := P)
    (f := fun n => generalItoMixedQuadraticApprox f Z M t (n + 1))
    (q := fun n => quadraticVariationApprox M t (n + 1))
    (F := F) (G := Gk)
    (qlim := predictableQuadraticVariation hsm U t)
  · intro n
    exact aestronglyMeasurable_generalItoMixedQuadraticApprox
      f hsecond Z M hZmeas hMmeas t (n + 1)
  · exact hFG
  · simpa only [Gk] using hG
  · simpa only [HasQuadraticVariationInProbabilityAt, M] using
      (quadraticVariation_naturalItoProcessRepresentative hB hsm U t)
  · intro n omega
    exact quadraticVariationApprox_nonneg M t (n + 1) omega
  · have hbound :=
      hmod.generalItoMixedQuadraticApprox_sub_completedStep_eventually_le
        (M := M) f t ht hsecond
    filter_upwards [hbound] with omega homega
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := homega (2 * epsilon)
      (mul_pos (by norm_num) hepsilon)
    refine ⟨N, fun k n hk hn => ?_⟩
    have hraw := hN k n hk hn
    simpa only [F, Real.norm_eq_abs, mul_assoc,
      show (1 / 2 : ℝ) * (2 * epsilon) = epsilon by ring] using hraw

theorem generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z M : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (ht : 0 < t) (Q : ℝ≥0 → W → ℝ) (G : W → ℝ)
    (hbefore : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox M t (n + 1) a)
      Filter.atTop (Q a))
    (hG : TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G)
    (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification Z Y P) :
    TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f Z M t (n + 1))
      Filter.atTop G := by
  let F : ℕ → ℕ → W → ℝ := fun k n =>
    generalItoMixedQuadraticCompletedStepApprox
      f Z M t (n + 1) (k + 1)
  let Gk : ℕ → W → ℝ := fun k omega => ∑ i ∈ Finset.range (k + 1),
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t (k + 1) i : ℝ)
      (Z (uniformPartitionTime t (k + 1) i) omega)) *
    (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
      Q (uniformPartitionTime t (k + 1) i) omega)
  have hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (Gk k) := by
    intro k
    unfold F Gk generalItoMixedQuadraticCompletedStepApprox
    apply tendstoInMeasure_finset_sum_mul_fixed_real (Finset.range (k + 1))
      (fun i n omega =>
        quadraticVariationBeforeStopApprox M t (n + 1)
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          quadraticVariationBeforeStopApprox M t (n + 1)
            (uniformPartitionTime t (k + 1) i) omega)
      (fun i omega =>
        Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega)
      (fun i omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t (k + 1) i : ℝ)
        (Z (uniformPartitionTime t (k + 1) i) omega))
    · intro i hi
      have hi1 : i + 1 ≤ k + 1 := Finset.mem_range.mp hi
      have hi0 : i ≤ k + 1 := (Nat.le_add_right i 1).trans hi1
      exact (hbefore (uniformPartitionTime t (k + 1) (i + 1))
        (uniformPartitionTime_mem_Icc_of_le t
          (Nat.zero_lt_succ k) hi1).2).sub_real_noMeas
        (hbefore (uniformPartitionTime t (k + 1) i)
          (uniformPartitionTime_mem_Icc_of_le t
            (Nat.zero_lt_succ k) hi0).2)
    · intro i _hi n
      exact (aestronglyMeasurable_quadraticVariationBeforeStopApprox
        hMmeas t (n + 1)
          (uniformPartitionTime t (k + 1) (i + 1))).sub
        (aestronglyMeasurable_quadraticVariationBeforeStopApprox
          hMmeas t (n + 1) (uniformPartitionTime t (k + 1) i))
    · intro i _hi
      have hpair : AEStronglyMeasurable
          (fun omega => ((uniformPartitionTime t (k + 1) i : ℝ),
            Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.prodMk
          (hZmeas (uniformPartitionTime t (k + 1) i))
      exact aestronglyMeasurable_const.mul
        (hsecond.comp_aestronglyMeasurable hpair)
  have hq : TendstoInMeasure P
      (fun n => quadraticVariationApprox M t (n + 1))
      Filter.atTop (Q t) := by
    apply (hbefore t le_rfl).congr_left
    intro n
    filter_upwards with omega
    unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]
  apply TendstoInMeasure.of_ae_two_scale_uniform_control
    (P := P)
    (f := fun n => generalItoMixedQuadraticApprox f Z M t (n + 1))
    (q := fun n => quadraticVariationApprox M t (n + 1))
    (F := F) (G := Gk) (qlim := Q t)
  · intro n
    exact aestronglyMeasurable_generalItoMixedQuadraticApprox
      f hsecond Z M hZmeas hMmeas t (n + 1)
  · exact hFG
  · simpa only [Gk] using hG
  · exact hq
  · intro n omega
    exact quadraticVariationApprox_nonneg M t (n + 1) omega
  · have hbound :=
      hmod.generalItoMixedQuadraticApprox_sub_completedStep_eventually_le
        (M := M) f t ht hsecond
    filter_upwards [hbound] with omega homega
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := homega (2 * epsilon)
      (mul_pos (by norm_num) hepsilon)
    refine ⟨N, fun k n hk hn => ?_⟩
    have hraw := hN k n hk hn
    simpa only [F, Real.norm_eq_abs, mul_assoc,
      show (1 / 2 : ℝ) * (2 * epsilon) = epsilon by ring] using hraw

/-- A continuous random left weight can be integrated against any robust
quadratic-variation process.  This is the coefficient-level form of the
mixed Itô bracket theorem, obtained from the cubic test function whose Itô
quadratic coefficient is the identity. -/
theorem weightedQuadraticVariation_tendstoInMeasure_of_beforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (H M : ℝ≥0 → W → ℝ)
    (hHmeas : ∀ s, AEStronglyMeasurable (H s) P)
    (hMmeas : ∀ s, AEStronglyMeasurable (M s) P)
    (t : ℝ≥0) (ht : 0 < t) (Q : ℝ≥0 → W → ℝ) (G : W → ℝ)
    (hbefore : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n ↦ quadraticVariationBeforeStopApprox M t (n + 1) a)
      Filter.atTop (Q a))
    (hG : TendstoInMeasure P
      (fun k omega ↦ ∑ i ∈ Finset.range (k + 1),
        H (uniformPartitionTime t (k + 1) i) omega *
        (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G)
    (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification H Y P) :
    TendstoInMeasure P
      (fun n ↦ weightedQuadraticVariationApprox H M t (n + 1))
      Filter.atTop G := by
  let f : ℝ → ℝ → ℝ := fun _ x ↦ x ^ 3 / 3
  have hsecond : Continuous (fun p : ℝ × ℝ ↦
      itoSpaceSecondDerivative f p.1 p.2) := by
    simp only [f, itoSpaceSecondDerivative_cubicThird]
    fun_prop
  have hG' : TendstoInMeasure P
      (fun k omega ↦ ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (H (uniformPartitionTime t (k + 1) i) omega)) *
        (Q (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Q (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G := by
    apply hG.congr_left
    intro k
    exact Filter.Eventually.of_forall fun omega ↦ by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [f, itoSpaceSecondDerivative_cubicThird]
      ring
  have hraw := generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
    f hsecond H M hHmeas hMmeas t ht Q G hbefore hG' Y hmod
  apply hraw.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    unfold generalItoMixedQuadraticApprox weightedQuadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [f, itoSpaceSecondDerivative_cubicThird]
    ring

/-- Polarization integrates a continuous random left weight against the
covariation of two processes once robust brackets are known for `X`, `Y`,
and `X + Y`.  The conclusion is expressed through the three corresponding
bracket Riemann limits, so no pathwise finite-variation representation is
required. -/
theorem weightedQuadraticCovariation_tendstoInMeasure_of_beforeStop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (H X Y : ℝ≥0 → W → ℝ)
    (hHmeas : ∀ s, AEStronglyMeasurable (H s) P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (t : ℝ≥0) (ht : 0 < t)
    (QX QY Qadd : ℝ≥0 → W → ℝ) (GX GY Gadd : W → ℝ)
    (hbeforeX : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n ↦ quadraticVariationBeforeStopApprox X t (n + 1) a)
      Filter.atTop (QX a))
    (hbeforeY : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n ↦ quadraticVariationBeforeStopApprox Y t (n + 1) a)
      Filter.atTop (QY a))
    (hbeforeAdd : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n ↦ quadraticVariationBeforeStopApprox (X + Y) t (n + 1) a)
      Filter.atTop (Qadd a))
    (hGX : TendstoInMeasure P
      (fun k omega ↦ ∑ i ∈ Finset.range (k + 1),
        H (uniformPartitionTime t (k + 1) i) omega *
        (QX (uniformPartitionTime t (k + 1) (i + 1)) omega -
          QX (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop GX)
    (hGY : TendstoInMeasure P
      (fun k omega ↦ ∑ i ∈ Finset.range (k + 1),
        H (uniformPartitionTime t (k + 1) i) omega *
        (QY (uniformPartitionTime t (k + 1) (i + 1)) omega -
          QY (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop GY)
    (hGadd : TendstoInMeasure P
      (fun k omega ↦ ∑ i ∈ Finset.range (k + 1),
        H (uniformPartitionTime t (k + 1) i) omega *
        (Qadd (uniformPartitionTime t (k + 1) (i + 1)) omega -
          Qadd (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop Gadd)
    (Hcont : ℝ≥0 → W → ℝ)
    (hHmod : IsContinuousProcessModification H Hcont P) :
    TendstoInMeasure P
      (fun n ↦ weightedQuadraticCovariationApprox H X Y t (n + 1))
      Filter.atTop (fun omega ↦
        (1 / 2 : ℝ) * (Gadd omega - GX omega - GY omega)) := by
  have hX := weightedQuadraticVariation_tendstoInMeasure_of_beforeStop
    H X hHmeas hXmeas t ht QX GX hbeforeX hGX Hcont hHmod
  have hY := weightedQuadraticVariation_tendstoInMeasure_of_beforeStop
    H Y hHmeas hYmeas t ht QY GY hbeforeY hGY Hcont hHmod
  have hAdd := weightedQuadraticVariation_tendstoInMeasure_of_beforeStop
    H (X + Y) hHmeas (fun s ↦ (hXmeas s).add (hYmeas s))
      t ht Qadd Gadd hbeforeAdd hGadd Hcont hHmod
  have hcombined := ((hAdd.sub_real_noMeas hX).sub_real_noMeas hY)
    |>.const_mul_real_noMeas (1 / 2 : ℝ)
  apply hcombined.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    have hpolar := two_mul_weightedQuadraticCovariationApprox
      H X Y t (n + 1) omega
    linarith

theorem bracketStep_process_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z Y sigma : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hmod : IsContinuousProcessModification Z Y P)
    (t : ℝ≥0)
    (hQmeas : ∀ a : ℝ≥0, AEStronglyMeasurable
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) a,
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) P)
    (hσint : ∀ᵐ omega ∂P, IntegrableOn
      (fun s : ℝ≥0 => (sigma s omega) ^ 2) (Set.Ioc 0 t)
      nonnegativeLebesgueMeasure) :
    TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        ((∫ s in Set.Ioc (0 : ℝ≥0)
              (uniformPartitionTime t (k + 1) (i + 1)),
              (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) -
          ∫ s in Set.Ioc (0 : ℝ≥0)
              (uniformPartitionTime t (k + 1) i),
              (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
      Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) := by
  have happroxMeas : ∀ k, AEStronglyMeasurable
      (fun omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        ((∫ s in Set.Ioc (0 : ℝ≥0)
              (uniformPartitionTime t (k + 1) (i + 1)),
              (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) -
          ∫ s in Set.Ioc (0 : ℝ≥0)
              (uniformPartitionTime t (k + 1) i),
              (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure)) P := by
    intro k
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (k + 1), fun omega =>
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (Z (uniformPartitionTime t (k + 1) i) omega)) *
          ((∫ s in Set.Ioc (0 : ℝ≥0)
                (uniformPartitionTime t (k + 1) (i + 1)),
                (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) -
            ∫ s in Set.Ioc (0 : ℝ≥0)
                (uniformPartitionTime t (k + 1) i),
                (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure)) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i _hi
      have hpair : AEStronglyMeasurable
          (fun omega => ((uniformPartitionTime t (k + 1) i : ℝ),
            Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.prodMk
          (hZmeas (uniformPartitionTime t (k + 1) i))
      have hw : AEStronglyMeasurable (fun omega =>
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.mul
          (hsecond.comp_aestronglyMeasurable hpair)
      exact hw.mul
        ((hQmeas (uniformPartitionTime t (k + 1) (i + 1))).sub
          (hQmeas (uniformPartitionTime t (k + 1) i)))
    apply hs.congr
    filter_upwards with omega
    simp only [Finset.sum_apply]
  apply tendstoInMeasure_of_tendsto_ae
  · exact happroxMeas
  · have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    filter_upwards [hgrid, hmod.continuous_paths, hσint]
      with omega hgridOmega hcontinuous hq
    let q : ℝ≥0 → ℝ := fun s => (sigma s omega) ^ 2
    let w : ℝ≥0 → ℝ := fun s =>
      (1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)
    have hq_nonneg : ∀ s, 0 ≤ q s := fun s => sq_nonneg _
    have hw : ContinuousOn w (Set.Icc 0 t) := by
      have hpair : ContinuousOn
          (fun s : ℝ≥0 => ((s : ℝ), Y s omega)) (Set.Icc 0 t) :=
        NNReal.continuous_coe.continuousOn.prodMk hcontinuous.continuousOn
      exact continuousOn_const.mul (hsecond.comp_continuousOn hpair)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      ((isCompact_Icc.image_of_continuousOn hw).isBounded)
    have hwq : IntegrableOn (fun s => w s * q s) (Set.Ioc 0 t)
        nonnegativeLebesgueMeasure := by
      apply hq.bdd_mul
      · exact (hw.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hC (w s) ⟨s, Set.Ioc_subset_Icc_self hs, rfl⟩
    have hpath := uniformPartition_weighted_integral_tendsto
      (μ := nonnegativeLebesgueMeasure) q w t hq hwq hq_nonneg hw
    change Filter.Tendsto _ Filter.atTop
      (nhds (∫ s in Set.Ioc (0 : ℝ≥0) t, w s * q s
        ∂nonnegativeLebesgueMeasure))
    convert hpath using 1
    funext k
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hgridOmega k i]

theorem bracketStep_mixed_naturalItoProcess_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (_hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (Z Y : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (hmod : IsContinuousProcessModification Z Y P) :
    TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) := by
  have happroxMeas : ∀ k, AEStronglyMeasurable
      (fun omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (Z (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega)) P := by
    intro k
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (k + 1), fun omega =>
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (Z (uniformPartitionTime t (k + 1) i) omega)) *
          (predictableQuadraticVariation hsm U
              (uniformPartitionTime t (k + 1) (i + 1)) omega -
            predictableQuadraticVariation hsm U
              (uniformPartitionTime t (k + 1) i) omega)) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i _hi
      have hpair : AEStronglyMeasurable
          (fun omega => ((uniformPartitionTime t (k + 1) i : ℝ),
            Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.prodMk
          (hZmeas (uniformPartitionTime t (k + 1) i))
      have hw : AEStronglyMeasurable (fun omega =>
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (Z (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.mul
          (hsecond.comp_aestronglyMeasurable hpair)
      have hblock :=
        (integrable_predictableQuadraticVariation hsm U
          (uniformPartitionTime t (k + 1) (i + 1))).aestronglyMeasurable.sub
        (integrable_predictableQuadraticVariation hsm U
          (uniformPartitionTime t (k + 1) i)).aestronglyMeasurable
      exact hw.mul hblock
    apply hs.congr
    filter_upwards with omega
    simp only [Finset.sum_apply]
  apply tendstoInMeasure_of_tendsto_ae
  · exact happroxMeas
  · have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    have hsections :=
      (Lp.memLp (U : TimeProcessL2 P)).integrable_sq.prod_left_ae
    filter_upwards [hgrid, hmod.continuous_paths, hsections]
      with omega hgridOmega hcontinuous hqGlobal
    let q : ℝ≥0 → ℝ := fun s => ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
    let w : ℝ≥0 → ℝ := fun s =>
      (1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)
    have hq : IntegrableOn q (Set.Ioc 0 t) nonnegativeLebesgueMeasure := by
      exact hqGlobal.mono_measure Measure.restrict_le_self
    have hq_nonneg : ∀ s, 0 ≤ q s := fun s => sq_nonneg _
    have hw : ContinuousOn w (Set.Icc 0 t) := by
      have hpair : ContinuousOn
          (fun s : ℝ≥0 => ((s : ℝ), Y s omega)) (Set.Icc 0 t) :=
        NNReal.continuous_coe.continuousOn.prodMk hcontinuous.continuousOn
      exact continuousOn_const.mul (hsecond.comp_continuousOn hpair)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      ((isCompact_Icc.image_of_continuousOn hw).isBounded)
    have hwq : IntegrableOn (fun s => w s * q s) (Set.Ioc 0 t)
        nonnegativeLebesgueMeasure := by
      apply hq.bdd_mul
      · exact (hw.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hC (w s) ⟨s, Set.Ioc_subset_Icc_self hs, rfl⟩
    have hpath := uniformPartition_weighted_integral_tendsto
      (μ := nonnegativeLebesgueMeasure) q w t hq hwq hq_nonneg hw
    convert hpath using 1
    · funext k
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hgridOmega k i]
      rfl

theorem generalItoMixedQuadratic_naturalItoProcess_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (Z : ℝ≥0 → W → ℝ)
    (hZmeas : ∀ s, AEStronglyMeasurable (Z s) P)
    (t : ℝ≥0) (ht : 0 < t) (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification Z Y P) :
    TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f Z
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1)) Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) := by
  apply
    generalItoMixedQuadratic_naturalItoProcess_tendstoInMeasure_of_bracketStep_limit
      hB hsm U f hsecond Z hZmeas t ht (Y := Y) (hmod := hmod)
  exact bracketStep_mixed_naturalItoProcess_tendstoInMeasure
    hB hsm U f hsecond t Z Y hZmeas hmod

theorem IsItoProcess.generalItoQuadratic_tendstoInMeasure_bracketIntegral
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P]
    {B X mu sigma : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X mu sigma B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (ht : 0 < t) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ)
          (hX.continuousVersion s omega)) *
          ((hX.diffusion : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let A : ℝ≥0 → W → ℝ := integratedDrift mu
  let M : ℝ≥0 → W → ℝ := hX.integralProcess
  have hZmeas : ∀ s, AEStronglyMeasurable (X s) P :=
    hX.aestronglyMeasurable_of_initial hXzero
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := by
    intro s
    exact (stronglyMeasurable_integratedDrift
      hX.drift_measurable s).aestronglyMeasurable
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact aestronglyMeasurable_integralProcess hX s
  have hAqv : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n => quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0) := by
    filter_upwards with omega
    exact tendsto_quadraticVariationApprox_integratedDrift_zero
      mu t omega (hX.drift_integrable t omega)
  have hMqv : TendstoInMeasure P
      (fun n => quadraticVariationApprox M t (n + 1)) Filter.atTop
      (predictableQuadraticVariation
        hX.driver_stronglyMeasurable hX.diffusion t) := by
    simpa only [M, IsItoProcess.integralProcess,
      stochasticIntegralProcess, HasQuadraticVariationInProbabilityAt] using
      (quadraticVariation_naturalItoProcessRepresentative
        hX.driver_brownian hX.driver_stronglyMeasurable hX.diffusion t)
  have hweight :=
    hX.continuousVersion_spec.uniformPartition_secondDerivative_bounded
      f hsecond t
  have herror :=
    generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
      f hsecond X A M hZmeas hAmeas hMmeas t
      (predictableQuadraticVariation
        hX.driver_stronglyMeasurable hX.diffusion t)
      hAqv hMqv hweight
  have hdecomp : ∀ s : ℝ≥0, X s =ᵐ[P]
      (fun omega => X 0 omega + A s omega + M s omega) := by
    intro s
    filter_upwards [hX.integral_eq_integralProcess s] with omega homega
    simpa only [A, M, integratedDrift] using homega
  have hgrid := fixedTime_ae_eq_uniformPartitions hdecomp t
  have heq : ∀ n, generalItoQuadraticApprox f X t (n + 1) =ᵐ[P]
      generalItoMixedQuadraticApprox f X
        (fun s omega => A s omega + M s omega) t (n + 1) := by
    intro n
    filter_upwards [hgrid] with omega homega
    unfold generalItoQuadraticApprox generalItoMixedQuadraticApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [homega n i, homega n (i + 1)]
    ring
  have herrorActual : TendstoInMeasure P
      (fun n omega => generalItoQuadraticApprox f X t (n + 1) omega -
        generalItoMixedQuadraticApprox f X M t (n + 1) omega)
      Filter.atTop (fun _ => 0) :=
    herror.congr_left fun n => by
      filter_upwards [heq n] with omega homega
      rw [homega]
  have hmixed : TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f X M t (n + 1))
      Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ)
          (hX.continuousVersion s omega)) *
          ((hX.diffusion : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) := by
    simpa only [M, IsItoProcess.integralProcess,
      stochasticIntegralProcess] using
      (generalItoMixedQuadratic_naturalItoProcess_tendstoInMeasure
        hX.driver_brownian hX.driver_stronglyMeasurable hX.diffusion
        f hsecond X hZmeas t ht hX.continuousVersion
        hX.continuousVersion_spec)
  have hsum := herrorActual.add_real_noMeas hmixed
  apply hsum.congr
  · intro n
    filter_upwards with omega
    ring
  · filter_upwards with omega
    ring

theorem bracketStep_naturalItoProcess_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) Y P) :
    TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
            (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U s).aestronglyMeasurable
  have happroxMeas : ∀ k, AEStronglyMeasurable
      (fun omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (M (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega)) P := by
    intro k
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (k + 1), fun omega =>
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (M (uniformPartitionTime t (k + 1) i) omega)) *
          (predictableQuadraticVariation hsm U
              (uniformPartitionTime t (k + 1) (i + 1)) omega -
            predictableQuadraticVariation hsm U
              (uniformPartitionTime t (k + 1) i) omega)) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i _hi
      have hpair : AEStronglyMeasurable
          (fun omega => ((uniformPartitionTime t (k + 1) i : ℝ),
            M (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.prodMk
          (hMmeas (uniformPartitionTime t (k + 1) i))
      have hw : AEStronglyMeasurable (fun omega =>
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) i : ℝ)
            (M (uniformPartitionTime t (k + 1) i) omega)) P :=
        aestronglyMeasurable_const.mul
          (hsecond.comp_aestronglyMeasurable hpair)
      have hblock :=
        (integrable_predictableQuadraticVariation hsm U
          (uniformPartitionTime t (k + 1) (i + 1))).aestronglyMeasurable.sub
        (integrable_predictableQuadraticVariation hsm U
          (uniformPartitionTime t (k + 1) i)).aestronglyMeasurable
      exact hw.mul hblock
    apply hs.congr
    filter_upwards with omega
    simp only [Finset.sum_apply]
  apply tendstoInMeasure_of_tendsto_ae
  · simpa only [M] using happroxMeas
  · have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    have hsections :=
      (Lp.memLp (U : TimeProcessL2 P)).integrable_sq.prod_left_ae
    filter_upwards [hgrid, hmod.continuous_paths, hsections]
      with omega hgridOmega hcontinuous hqGlobal
    let q : ℝ≥0 → ℝ := fun s => ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
    let w : ℝ≥0 → ℝ := fun s =>
      (1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)
    have hq : IntegrableOn q (Set.Ioc 0 t) nonnegativeLebesgueMeasure := by
      exact hqGlobal.mono_measure Measure.restrict_le_self
    have hq_nonneg : ∀ s, 0 ≤ q s := fun s => sq_nonneg _
    have hw : ContinuousOn w (Set.Icc 0 t) := by
      have hpair : ContinuousOn
          (fun s : ℝ≥0 => ((s : ℝ), Y s omega)) (Set.Icc 0 t) :=
        NNReal.continuous_coe.continuousOn.prodMk hcontinuous.continuousOn
      exact continuousOn_const.mul (hsecond.comp_continuousOn hpair)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      ((isCompact_Icc.image_of_continuousOn hw).isBounded)
    have hwq : IntegrableOn (fun s => w s * q s) (Set.Ioc 0 t)
        nonnegativeLebesgueMeasure := by
      apply hq.bdd_mul
      · exact (hw.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hC (w s) ⟨s, Set.Ioc_subset_Icc_self hs, rfl⟩
    have hpath := uniformPartition_weighted_integral_tendsto
      (μ := nonnegativeLebesgueMeasure) q w t hq hwq hq_nonneg hw
    convert hpath using 1
    · funext k
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hgridOmega k i]
      rfl

/-- The pathwise continuous-weight integral against a selected nonnegative
bracket density on nonnegative time. -/
noncomputable def generalItoQuadraticBracketIntegral
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Y : ℝ≥0 → W → ℝ)
    (u : ℝ≥0 × W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) t,
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
      (u (s, omega)) ^ 2 ∂nonnegativeLebesgueMeasure

theorem generalItoQuadraticBracketIntegral_uncurry_eq
    {W : Type*} [MeasurableSpace W]
    (f : ℝ → ℝ → ℝ) (Y sigma : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    generalItoQuadraticBracketIntegral f Y (Function.uncurry sigma) t omega =
      generalItoQuadraticIntegral f Y sigma t omega := by
  unfold generalItoQuadraticBracketIntegral generalItoQuadraticIntegral
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,
      map_nonnegativeLebesgueMeasure_restrict_Ioc t⟩
  have hchange := hpres.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun r : ℝ =>
      ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r (Y r.toNNReal omega)) *
        (sigma r.toNNReal omega) ^ 2)
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) =
        ∫ r in Set.Ioc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 := by
      simpa [Function.uncurry] using hchange
    _ = ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 :=
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
    _ = (1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          itoSpaceSecondDerivative f r (Y r.toNNReal omega) *
            (sigma r.toNNReal omega) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext r
      ring

theorem generalItoQuadratic_tendstoInMeasure_of_characteristics_of_pos
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (X mu sigma J Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hJmeas : ∀ s, AEStronglyMeasurable (J s) P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ t omega, IntegrableOn
      (fun s : ℝ => mu s.toNNReal omega) (Set.Icc 0 (t : ℝ)))
    (hmod : IsContinuousProcessModification X Y P)
    (hdecomp : ∀ s, X s =ᵐ[P] fun omega =>
      X 0 omega + integratedDrift mu s omega + J s omega)
    (hbefore : ∀ T a, TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a)
      Filter.atTop (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
    (hσint : ∀ T, ∀ᵐ omega ∂P, IntegrableOn
      (fun s : ℝ≥0 => (sigma s omega) ^ 2) (Set.Ioc 0 T)
      nonnegativeLebesgueMeasure)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (ht : 0 < t) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop (generalItoQuadraticIntegral f Y sigma t) := by
  let A : ℝ≥0 → W → ℝ := integratedDrift mu
  let Q : ℝ≥0 → W → ℝ := fun a omega =>
    ∫ s in Set.Ioc (0 : ℝ≥0) a,
      (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure
  have hQmeas : ∀ a, AEStronglyMeasurable (Q a) P := by
    intro a
    have hraw := (hbefore a a).aestronglyMeasurable (fun n =>
      aestronglyMeasurable_quadraticVariationBeforeStopApprox
        hJmeas a (n + 1) a)
    simpa only [Q, min_self] using hraw
  have hbeforeFixed : ∀ a, a ≤ t → TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J t (n + 1) a)
      Filter.atTop (Q a) := by
    intro a ha
    simpa only [Q, min_eq_right ha] using hbefore t a
  have hG := bracketStep_process_tendstoInMeasure
    f hsecond X Y sigma hXmeas hmod t hQmeas (hσint t)
  have hmixed : TendstoInMeasure P
      (fun n => generalItoMixedQuadraticApprox f X J t (n + 1))
      Filter.atTop (generalItoQuadraticBracketIntegral f Y
        (Function.uncurry sigma) t) := by
    change TendstoInMeasure P _ Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure)
    apply generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
      f hsecond X J hXmeas hJmeas t ht Q _ hbeforeFixed
        hG Y hmod
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := by
    intro s
    exact (stronglyMeasurable_integratedDrift hmuMeas s).aestronglyMeasurable
  have hAqv : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n => quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0) := by
    filter_upwards with omega
    exact tendsto_quadraticVariationApprox_integratedDrift_zero
      mu t omega (hmuInt t omega)
  have hJqv : TendstoInMeasure P
      (fun n => quadraticVariationApprox J t (n + 1))
      Filter.atTop (Q t) := by
    apply (hbeforeFixed t le_rfl).congr_left
    intro n
    filter_upwards with omega
    unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]
  have hweight := hmod.uniformPartition_secondDerivative_bounded
    f hsecond t
  have herror :=
    generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
      f hsecond X A J hXmeas hAmeas hJmeas t (Q t)
        hAqv hJqv hweight
  have hgrid := fixedTime_ae_eq_uniformPartitions hdecomp t
  have heq : ∀ n, generalItoQuadraticApprox f X t (n + 1) =ᵐ[P]
      generalItoMixedQuadraticApprox f X
        (fun s omega => A s omega + J s omega) t (n + 1) := by
    intro n
    filter_upwards [hgrid] with omega homega
    unfold generalItoQuadraticApprox generalItoMixedQuadraticApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [homega n i, homega n (i + 1)]
    ring
  have herrorActual : TendstoInMeasure P
      (fun n omega => generalItoQuadraticApprox f X t (n + 1) omega -
        generalItoMixedQuadraticApprox f X J t (n + 1) omega)
      Filter.atTop (fun _ => 0) :=
    herror.congr_left fun n => by
      filter_upwards [heq n] with omega homega
      rw [homega]
  have hsum := herrorActual.add_real_noMeas hmixed
  have hraw : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop (generalItoQuadraticBracketIntegral f Y
        (Function.uncurry sigma) t) := by
    apply hsum.congr
    · intro n
      filter_upwards with omega
      ring
    · filter_upwards with omega
      ring
  apply hraw.congr_right
  filter_upwards with omega
  exact generalItoQuadraticBracketIntegral_uncurry_eq f Y sigma t omega

theorem generalItoQuadratic_tendstoInMeasure_of_characteristics
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (X mu sigma J Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hJmeas : ∀ s, AEStronglyMeasurable (J s) P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ t omega, IntegrableOn
      (fun s : ℝ => mu s.toNNReal omega) (Set.Icc 0 (t : ℝ)))
    (hmod : IsContinuousProcessModification X Y P)
    (hdecomp : ∀ s, X s =ᵐ[P] fun omega =>
      X 0 omega + integratedDrift mu s omega + J s omega)
    (hbefore : ∀ T a, TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a)
      Filter.atTop (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
    (hσint : ∀ T, ∀ᵐ omega ∂P, IntegrableOn
      (fun s : ℝ≥0 => (sigma s omega) ^ 2) (Set.Ioc 0 T)
      nonnegativeLebesgueMeasure)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop (generalItoQuadraticIntegral f Y sigma t) := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_generalItoQuadraticApprox
        f hsecond X hXmeas 0 (n + 1)
    · filter_upwards with omega
      have hsource :
          (fun n => generalItoQuadraticApprox f X 0 (n + 1) omega) =
            fun _ => 0 := by
        funext n
        unfold generalItoQuadraticApprox uniformPartitionTime
        simp
      have htarget : generalItoQuadraticIntegral f Y sigma 0 omega = 0 := by
        unfold generalItoQuadraticIntegral
        simp
      change Filter.Tendsto
        (fun n => generalItoQuadraticApprox f X (0 : ℝ≥0) (n + 1) omega)
        Filter.atTop
        (nhds (generalItoQuadraticIntegral f Y sigma (0 : ℝ≥0) omega))
      rw [hsource, htarget]
      exact tendsto_const_nhds
  · exact generalItoQuadratic_tendstoInMeasure_of_characteristics_of_pos
      X mu sigma J Y hXmeas hJmeas hmuMeas hmuInt hmod hdecomp
        hbefore hσint f hsecond t ht

theorem quadraticVariation_tendstoInMeasure_of_characteristics
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (X mu sigma J : ℝ≥0 → W → ℝ)
    (hJmeas : ∀ s, AEStronglyMeasurable (J s) P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ t omega, IntegrableOn
      (fun s : ℝ => mu s.toNNReal omega) (Set.Icc 0 (t : ℝ)))
    (hdecomp : ∀ s, X s =ᵐ[P] fun omega =>
      X 0 omega + integratedDrift mu s omega + J s omega)
    (hbefore : ∀ T a, TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a)
      Filter.atTop (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop
      (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) := by
  let A : ℝ≥0 → W → ℝ := integratedDrift mu
  let Q : W → ℝ := fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
    (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := by
    intro s
    exact (stronglyMeasurable_integratedDrift hmuMeas s).aestronglyMeasurable
  have hAqv : HasQuadraticVariationInProbabilityAt A P t (fun _ => 0) := by
    exact quadraticVariation_integratedDrift_inProbability
      hmuMeas t (hmuInt t)
  have hJqv : HasQuadraticVariationInProbabilityAt J P t Q := by
    unfold HasQuadraticVariationInProbabilityAt
    have hraw : TendstoInMeasure P
        (fun n => quadraticVariationBeforeStopApprox J t (n + 1) t)
        Filter.atTop Q := by
      simpa only [Q, min_self] using hbefore t t
    apply hraw.congr_left
    intro n
    filter_upwards with omega
    unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
    simp only [uniformPartitionTime_mem_Icc_of_le t
      (Nat.zero_lt_succ n) hi1 |>.2, ↓reduceIte]
  have hadd : HasQuadraticVariationInProbabilityAt
      (fun s omega => A s omega + J s omega) P t Q :=
    hAqv.add_of_left_zero_of_aestronglyMeasurable
      hJqv hAmeas hJmeas
  have hgrid := fixedTime_ae_eq_uniformPartitions hdecomp t
  have heq : ∀ n, quadraticVariationApprox X t (n + 1) =ᵐ[P]
      quadraticVariationApprox (fun s omega => A s omega + J s omega)
        t (n + 1) := by
    intro n
    filter_upwards [hgrid] with omega homega
    unfold quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [homega n i, homega n (i + 1)]
    ring
  unfold HasQuadraticVariationInProbabilityAt at hadd
  apply hadd.congr_left
  intro n
  exact (heq n).symm

theorem exists_ito_formula_of_characteristics
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (X mu sigma J Y : ℝ≥0 → W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hJmeas : ∀ s, AEStronglyMeasurable (J s) P)
    (hmuMeas : Measurable (Function.uncurry mu))
    (hmuInt : ∀ t omega, IntegrableOn
      (fun s : ℝ => mu s.toNNReal omega) (Set.Icc 0 (t : ℝ)))
    (hmod : IsContinuousProcessModification X Y P)
    (hdecomp : ∀ s, X s =ᵐ[P] fun omega =>
      X 0 omega + integratedDrift mu s omega + J s omega)
    (hbefore : ∀ T a, TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox J T (n + 1) a)
      Filter.atTop (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) (min T a),
        (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure))
    (hσint : ∀ T, ∀ᵐ omega ∂P, IntegrableOn
      (fun s : ℝ≥0 => (sigma s omega) ^ 2) (Set.Ioc 0 T)
      nonnegativeLebesgueMeasure)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ =>
      itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          generalItoTimeIntegral f Y t omega + I omega +
            generalItoQuadraticIntegral f Y sigma t omega := by
  have hvalueMeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (fun omega => f s (X s omega)) P := by
    intro s
    have hp : AEStronglyMeasurable
        (fun omega => ((s : ℝ), X s omega)) P :=
      aestronglyMeasurable_const.prodMk (hXmeas s)
    exact hf.comp_aestronglyMeasurable hp
  have hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  have hqv := quadraticVariation_tendstoInMeasure_of_characteristics
    X mu sigma J hJmeas hmuMeas hmuInt hdecomp hbefore t
  exact generalIto_exists_space_limit_and_formula f X t
    (generalItoTimeIntegral f Y t)
    (generalItoQuadraticIntegral f Y sigma t) hendpoint
    (hmod.timeApprox_tendstoInMeasure f hdt t hXmeas)
    (generalItoQuadratic_tendstoInMeasure_of_characteristics
      X mu sigma J Y hXmeas hJmeas hmuMeas hmuInt hmod hdecomp
        hbefore hσint f hsecond t)
    (hmod.generalRemainder_tendstoInMeasure
      f hf htdiff hslice hdt hdx hsecond t _ hXmeas hqv)

theorem IsItoProcess.generalItoQuadraticBracketIntegral_diffusion_ae
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P]
    {B X mu sigma : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X mu sigma B P)
    (f : ℝ → ℝ → ℝ) (Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) :
    generalItoQuadraticBracketIntegral f Y
        (hX.diffusion : ℝ≥0 × W → ℝ) t =ᵐ[P]
      generalItoQuadraticIntegral f Y sigma t := by
  have hswap := (Measure.measurePreserving_swap
    (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp
      hX.diffusion_ae_eq
  have hswap' :
      (fun p : W × ℝ≥0 =>
        (hX.diffusion : ℝ≥0 × W → ℝ) p.swap) =ᵐ[
          P.prod nonnegativeLebesgueMeasure]
        fun p => sigma p.2 p.1 := by
    filter_upwards [hswap] with p hp
    rcases p with ⟨omega, s⟩
    simpa [Function.comp_def, Function.uncurry] using hp
  have hsections := Measure.ae_ae_of_ae_prod hswap'
  filter_upwards [hsections] with omega homega
  unfold generalItoQuadraticBracketIntegral generalItoQuadraticIntegral
  have hrepresentative :
      (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          ((hX.diffusion : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
        ∂nonnegativeLebesgueMeasure) =
      ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae homega] with s hs
    have hs' : (hX.diffusion : ℝ≥0 × W → ℝ) (s, omega) =
        sigma s omega := by
      simpa only [Prod.swap_prod_mk] using hs
    rw [hs']
  rw [hrepresentative]
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,
      map_nonnegativeLebesgueMeasure_restrict_Ioc t⟩
  have hchange := hpres.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun r : ℝ =>
      ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r (Y r.toNNReal omega)) *
        (sigma r.toNNReal omega) ^ 2)
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
          (sigma s omega) ^ 2 ∂nonnegativeLebesgueMeasure) =
        ∫ r in Set.Ioc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 := by
      simpa using hchange
    _ = ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f r
            (Y r.toNNReal omega)) * (sigma r.toNNReal omega) ^ 2 :=
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
    _ = (1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) (t : ℝ),
          itoSpaceSecondDerivative f r (Y r.toNNReal omega) *
            (sigma r.toNNReal omega) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext r
      ring

theorem IsItoProcess.generalItoQuadratic_tendstoInMeasure_of_pos
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P]
    {B X mu sigma : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X mu sigma B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (ht : 0 < t) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop
      (generalItoQuadraticIntegral f hX.continuousVersion sigma t) := by
  apply (hX.generalItoQuadratic_tendstoInMeasure_bracketIntegral
    hXzero f hsecond t ht).congr_right
  exact hX.generalItoQuadraticBracketIntegral_diffusion_ae
    f hX.continuousVersion t

theorem IsItoProcess.generalItoQuadratic_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P]
    {B X mu sigma : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X mu sigma B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop
      (generalItoQuadraticIntegral f hX.continuousVersion sigma t) := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_generalItoQuadraticApprox f hsecond X
        (hX.aestronglyMeasurable_of_initial hXzero) 0 (n + 1)
    · filter_upwards with omega
      have hsource :
          (fun n => generalItoQuadraticApprox f X 0 (n + 1) omega) =
            fun _ => 0 := by
        funext n
        unfold generalItoQuadraticApprox uniformPartitionTime
        simp
      have htarget :
          generalItoQuadraticIntegral f hX.continuousVersion sigma 0 omega =
            0 := by
        unfold generalItoQuadraticIntegral
        simp
      change Filter.Tendsto
        (fun n => generalItoQuadraticApprox f X (0 : ℝ≥0) (n + 1) omega)
        Filter.atTop
        (nhds (generalItoQuadraticIntegral f hX.continuousVersion sigma
          (0 : ℝ≥0) omega))
      rw [hsource, htarget]
      exact tendsto_const_nhds
  · exact hX.generalItoQuadratic_tendstoInMeasure_of_pos
      hXzero f hsecond t ht

/-- General Itô formula for a `C¹`-in-time, `C²`-in-state test function and
an arbitrary bundled Itô process.  The first-order `dX` integral is pinned as
the probability limit of the concrete uniform left sums. -/
theorem exists_ito_formula_itoProcess
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P]
    {B X mu sigma : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X mu sigma B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ =>
      itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          generalItoTimeIntegral f hX.continuousVersion t omega + I omega +
            generalItoQuadraticIntegral
              f hX.continuousVersion sigma t omega := by
  exact exists_ito_formula_itoProcess_of_quadratic_limit
    hX hXzero f hf htdiff hslice hdt hdx hsecond t
      (hX.generalItoQuadratic_tendstoInMeasure hXzero f hsecond t)

/-- Diffusion-weighted quadratic variation for a natural Itô process.  The
actual fine-grid second-derivative sums converge in probability to the
continuous-weight integral against the predictable `L²` bracket density.

This combines the arbitrary-fine-grid completed-cell theorem, the uniform
two-mesh diagonal closure, and pathwise weighted bracket Riemann convergence.
-/
theorem generalItoQuadratic_naturalItoProcess_tendstoInMeasure
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (ht : 0 < t) (Y : ℝ≥0 → W → ℝ)
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) Y P) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1)) Filter.atTop
      (generalItoQuadraticBracketIntegral f Y
        (U : ℝ≥0 × W → ℝ) t) := by
  apply generalItoQuadratic_naturalItoProcess_tendstoInMeasure_of_bracketStep_limit
    hB hsm U f hsecond t ht
  change TendstoInMeasure P _ Filter.atTop
    (fun omega => ∫ s in Set.Ioc (0 : ℝ≥0) t,
      ((1 / 2 : ℝ) * itoSpaceSecondDerivative f (s : ℝ) (Y s omega)) *
        ((U : ℝ≥0 × W → ℝ) (s, omega)) ^ 2
      ∂nonnegativeLebesgueMeasure)
  exact bracketStep_naturalItoProcess_tendstoInMeasure
    hB hsm U f hsecond t Y hmod

end StochasticCalculus
