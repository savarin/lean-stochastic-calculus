/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.Girsanov

/-!
# Fourth-moment bounds for discrete martingale variation

An elementary quartic convexity inequality bounds the sum of fourth powers
of martingale increments. Discrete integration by parts then bounds the
second moment of the quadratic sum by the terminal fourth moment.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Products of two L4 real functions belong to L2. -/
theorem memLp_two_mul_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} {X Y : W → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P) :
    MemLp (fun omega ↦ X omega * Y omega) 2 P := by
  let _ : ENNReal.HolderTriple 4 4 2 := holderTriple_four_four_two
  exact hX.fun_mul hY

/-- A real L4 function has integrable fourth power. -/
theorem integrable_pow_four_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} {X : W → ℝ}
    (hX : MemLp X 4 P) : Integrable (fun omega ↦ X omega ^ 4) P := by
  simpa only [Real.norm_eq_abs, (show Even 4 from ⟨2, by norm_num⟩).pow_abs] using
    hX.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)

/-- A fourth-power integrability statement is also an L4 statement. -/
theorem memLp_four_iff_integrable_pow_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} {X : W → ℝ}
    (hX : AEStronglyMeasurable X P) :
    MemLp X 4 P ↔ Integrable (fun omega ↦ X omega ^ 4) P := by
  constructor
  · exact integrable_pow_four_of_memLp_four
  · intro h
    apply (integrable_norm_rpow_iff hX (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by finiteness)).mp
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
      (show Even 4 from ⟨2, by norm_num⟩).pow_abs] using h

/-- Four L4 factors have an integrable product. -/
theorem integrable_fourfold_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} {X Y Z D : W → ℝ}
    (hX : MemLp X 4 P) (hY : MemLp Y 4 P)
    (hZ : MemLp Z 4 P) (hD : MemLp D 4 P) :
    Integrable (fun omega ↦ X omega * Y omega * Z omega * D omega) P := by
  have hXY := memLp_two_mul_of_memLp_four hX hY
  have hZD := memLp_two_mul_of_memLp_four hZ hD
  have hprod : Integrable (fun omega ↦
      (X omega * Y omega) * (Z omega * D omega)) P := hXY.integrable_mul hZD
  simpa only [mul_assoc] using hprod

/-- Any integrable predictable weight times a martingale increment has
zero expectation; the weight need not be bounded. -/
theorem integral_weighted_martingale_increment_eq_zero
    {W I : Type*} [MeasurableSpace W] [Preorder I]
    {P : Measure W} {V : Filtration I ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : I → W → ℝ} (hM : Martingale M V P) {a b : I} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[V a] Z)
    (hprod : Integrable (fun omega ↦ Z omega * (M b omega - M a omega)) P) :
    (∫ omega, Z omega * (M b omega - M a omega) ∂P) = 0 := by
  have hdelta : P[M b - M a | V a] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable b) (hM.integrable a) (V a)
    have hpast := condExp_of_stronglyMeasurable (V.le a)
      (hM.stronglyAdapted a) (hM.integrable a)
    filter_upwards [hsub, hM.condExp_ae_eq hab] with omega hsub hfuture
    rw [hsub, Pi.sub_apply, hfuture, hpast, sub_self]
    rfl
  have hprod' : Integrable (Z * (M b - M a)) P := hprod
  have hpull := condExp_mul_of_stronglyMeasurable_left hZ hprod'
    ((hM.integrable b).sub (hM.integrable a))
  have hcond : P[Z * (M b - M a) | V a] =ᵐ[P] 0 := by
    filter_upwards [hpull, hdelta] with omega hp hd
    rw [hp, Pi.mul_apply, hd, Pi.zero_apply, mul_zero]
  calc
    _ = ∫ omega, P[Z * (M b - M a) | V a] omega ∂P :=
      (integral_condExp (V.le a)).symm
    _ = ∫ _ : W, (0 : ℝ) ∂P := integral_congr_ae hcond
    _ = 0 := integral_zero _ _

/-- Uniform convexity of the fourth power, with an explicit optimal
remainder constant for this elementary estimate. -/
theorem fourth_increment_le_three_taylor (x y : ℝ) :
    (y - x) ^ 4 ≤ 3 * (y ^ 4 - x ^ 4 - 4 * (x ^ 3 * (y - x))) := by
  nlinarith [mul_nonneg (sq_nonneg (y - x)) (sq_nonneg (2 * x + y))]

/-- One martingale increment's fourth moment is bounded by three times the
increase in the fourth moment of the martingale. -/
theorem Martingale.integral_fourth_increment_le
    {W I : Type*} [MeasurableSpace W] [Preorder I]
    {P : Measure W} {V : Filtration I ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : I → W → ℝ} (hM : Martingale M V P) {a b : I} (hab : a ≤ b)
    (hMa : MemLp (M a) 4 P) (hMb : MemLp (M b) 4 P) :
    (∫ omega, (M b omega - M a omega) ^ 4 ∂P) ≤
      3 * ((∫ omega, M b omega ^ 4 ∂P) - ∫ omega, M a omega ^ 4 ∂P) := by
  have ha4 := integrable_pow_four_of_memLp_four hMa
  have hb4 := integrable_pow_four_of_memLp_four hMb
  have hd4 := integrable_pow_four_of_memLp_four (hMb.sub hMa)
  have hprod : Integrable (fun omega ↦ M a omega ^ 3 *
      (M b omega - M a omega)) P := by
    simpa only [Pi.sub_apply, pow_succ, pow_zero, one_mul, mul_assoc] using
      integrable_fourfold_of_memLp_four hMa hMa hMa (hMb.sub hMa)
  have hzero := integral_weighted_martingale_increment_eq_zero hM hab
    (show StronglyMeasurable[V a] (fun omega ↦ M a omega ^ 3) from
      (hM.stronglyAdapted a).pow 3) hprod
  have hpoly : Integrable (fun omega ↦
      3 * (M b omega ^ 4 - M a omega ^ 4 -
        4 * (M a omega ^ 3 * (M b omega - M a omega)))) P :=
    ((hb4.sub ha4).sub (hprod.const_mul 4)).const_mul 3
  have hle := integral_mono hd4 hpoly (fun omega ↦
    fourth_increment_le_three_taylor (M a omega) (M b omega))
  have hdiff4 : Integrable (fun omega ↦ M b omega ^ 4 - M a omega ^ 4) P :=
    hb4.sub ha4
  rw [integral_const_mul, integral_sub hdiff4 (hprod.const_mul 4),
    integral_sub hb4 ha4, integral_const_mul, hzero, mul_zero, sub_zero] at hle
  exact hle

/-- The expected sum of fourth powers of discrete martingale increments
has a bound independent of the grid length. -/
theorem Martingale.sum_integral_fourth_increments_le
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} {V : Filtration ℕ ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℕ → W → ℝ} (hM : Martingale M V P)
    (hM4 : ∀ i, MemLp (M i) 4 P) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ omega, (M (i + 1) omega - M i omega) ^ 4 ∂P) ≤
      3 * ∫ omega, M n omega ^ 4 ∂P := by
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        3 * ((∫ omega, M (i + 1) omega ^ 4 ∂P) -
          ∫ omega, M i omega ^ 4 ∂P) :=
      Finset.sum_le_sum fun i _ ↦
        Martingale.integral_fourth_increment_le hM
          (Nat.le_succ i) (hM4 i) (hM4 (i + 1))
    _ = 3 * ((∫ omega, M n omega ^ 4 ∂P) - ∫ omega, M 0 omega ^ 4 ∂P) := by
      rw [← Finset.mul_sum,
        Finset.sum_range_sub (fun i : ℕ ↦ ∫ omega, M i omega ^ 4 ∂P) n]
    _ ≤ 3 * ∫ omega, M n omega ^ 4 ∂P := by
      have h0 : 0 ≤ ∫ omega, M 0 omega ^ 4 ∂P :=
        integral_nonneg fun omega ↦ (show Even 4 from ⟨2, by norm_num⟩).pow_nonneg _
      linarith

/-- The sum of squared increments of a real process on a finite discrete grid. -/
def discreteQuadraticSum {W : Type*} (M : ℕ → W → ℝ) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n, (M (i + 1) omega - M i omega) ^ 2

@[simp] theorem discreteQuadraticSum_zero {W : Type*} (M : ℕ → W → ℝ) (omega : W) :
    discreteQuadraticSum M 0 omega = 0 := by simp only [discreteQuadraticSum, Finset.sum_range_zero]

theorem discreteQuadraticSum_succ {W : Type*} (M : ℕ → W → ℝ) (n : ℕ) (omega : W) :
    discreteQuadraticSum M (n + 1) omega =
      discreteQuadraticSum M n omega + (M (n + 1) omega - M n omega) ^ 2 := by
  exact Finset.sum_range_succ _ n

/-- L4 time sections make every finite quadratic sum square integrable. -/
theorem memLp_two_discreteQuadraticSum
    {W : Type*} [MeasurableSpace W] {P : Measure W} {M : ℕ → W → ℝ}
    (hM4 : ∀ i, MemLp (M i) 4 P) (n : ℕ) :
    MemLp (discreteQuadraticSum M n) 2 P := by
  apply memLp_finsetSum
  intro i _hi
  have hd := (hM4 (i + 1)).sub (hM4 i)
  simpa only [Pi.sub_apply, pow_two] using memLp_two_mul_of_memLp_four hd hd

/-- The quadratic sum through a discrete time is measurable in its past. -/
theorem stronglyMeasurable_discreteQuadraticSum
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℕ ‹MeasurableSpace W›} {M : ℕ → W → ℝ}
    (hM : StronglyAdapted V M) (n : ℕ) :
    StronglyMeasurable[V n] (discreteQuadraticSum M n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  exact (((hM (i + 1)).mono (V.mono hi1)).sub
    ((hM i).mono (V.mono ((Nat.le_succ i).trans hi1)))).pow 2

/-- A one-step integration-by-parts bound for the square of a quadratic sum. -/
theorem Martingale.integral_sq_discreteQuadraticSum_step_le
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} {V : Filtration ℕ ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℕ → W → ℝ} (hM : Martingale M V P)
    (hM4 : ∀ i, MemLp (M i) 4 P) (i : ℕ) :
    ((∫ omega, discreteQuadraticSum M (i + 1) omega ^ 2 ∂P) -
      ∫ omega, discreteQuadraticSum M i omega ^ 2 ∂P) ≤
      (∫ omega, (M (i + 1) omega - M i omega) ^ 4 ∂P) +
        2 * ((∫ omega, discreteQuadraticSum M (i + 1) omega * M (i + 1) omega ^ 2 ∂P) -
          ∫ omega, discreteQuadraticSum M i omega * M i omega ^ 2 ∂P) := by
  let Q := discreteQuadraticSum M
  have hQ2 := memLp_two_discreteQuadraticSum hM4
  have hM2 (j : ℕ) : MemLp (fun omega ↦ M j omega ^ 2) 2 P := by
    simpa only [pow_two] using memLp_two_mul_of_memLp_four (hM4 j) (hM4 j)
  have hprod (j : ℕ) : Integrable (fun omega ↦ Q j omega * M j omega ^ 2) P :=
    (hQ2 j).integrable_mul (hM2 j)
  have hcross : Integrable (fun omega ↦ Q i omega * M i omega *
      (M (i + 1) omega - M i omega)) P := by
    have hMD := memLp_two_mul_of_memLp_four (hM4 i) ((hM4 (i + 1)).sub (hM4 i))
    have hraw : Integrable (fun omega ↦ Q i omega *
        (M i omega * (M (i + 1) omega - M i omega))) P := (hQ2 i).integrable_mul hMD
    simpa only [mul_assoc] using hraw
  have hzero := integral_weighted_martingale_increment_eq_zero hM (Nat.le_succ i)
    (show StronglyMeasurable[V i] (fun omega ↦ Q i omega * M i omega) from
      (stronglyMeasurable_discreteQuadraticSum hM.stronglyAdapted i).mul
        (hM.stronglyAdapted i)) hcross
  have hfourth : Integrable (fun omega ↦ (M (i + 1) omega - M i omega) ^ 4) P :=
    integrable_pow_four_of_memLp_four ((hM4 (i + 1)).sub (hM4 i))
  have hleft : Integrable (fun omega ↦ Q (i + 1) omega ^ 2 - Q i omega ^ 2) P :=
    (hQ2 (i + 1)).integrable_sq.sub (hQ2 i).integrable_sq
  have hprodDiff : Integrable (fun omega ↦
      Q (i + 1) omega * M (i + 1) omega ^ 2 - Q i omega * M i omega ^ 2) P :=
    (hprod (i + 1)).sub (hprod i)
  have hright : Integrable (fun omega ↦
      (M (i + 1) omega - M i omega) ^ 4 +
        2 * (Q (i + 1) omega * M (i + 1) omega ^ 2 - Q i omega * M i omega ^ 2) -
          4 * (Q i omega * M i omega * (M (i + 1) omega - M i omega))) P :=
    (hfourth.add (hprodDiff.const_mul 2)).sub (hcross.const_mul 4)
  have hpoint (omega : W) : Q (i + 1) omega ^ 2 - Q i omega ^ 2 ≤
      (M (i + 1) omega - M i omega) ^ 4 +
        2 * (Q (i + 1) omega * M (i + 1) omega ^ 2 - Q i omega * M i omega ^ 2) -
          4 * (Q i omega * M i omega * (M (i + 1) omega - M i omega)) := by
    dsimp only [Q]
    rw [discreteQuadraticSum_succ]
    nlinarith [sq_nonneg ((M (i + 1) omega - M i omega) * M (i + 1) omega)]
  have hle := integral_mono hleft hright hpoint
  have hplus : Integrable (fun omega ↦ (M (i + 1) omega - M i omega) ^ 4 +
      2 * (Q (i + 1) omega * M (i + 1) omega ^ 2 - Q i omega * M i omega ^ 2)) P :=
    hfourth.add (hprodDiff.const_mul 2)
  rw [integral_sub (hQ2 (i + 1)).integrable_sq (hQ2 i).integrable_sq,
    integral_sub hplus (hcross.const_mul 4),
    integral_add hfourth (hprodDiff.const_mul 2), integral_const_mul,
    integral_sub (hprod (i + 1)) (hprod i), integral_const_mul,
    hzero, mul_zero, sub_zero] at hle
  exact hle

/-- The second moment of a martingale's quadratic sum is bounded by ten
times its terminal fourth moment, independently of the grid length. -/
theorem Martingale.integral_sq_discreteQuadraticSum_le
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} {V : Filtration ℕ ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℕ → W → ℝ} (hM : Martingale M V P)
    (hM4 : ∀ i, MemLp (M i) 4 P) (n : ℕ) :
    (∫ omega, discreteQuadraticSum M n omega ^ 2 ∂P) ≤
      10 * ∫ omega, M n omega ^ 4 ∂P := by
  let Q := discreteQuadraticSum M
  have hsteps := Finset.sum_le_sum (s := Finset.range n) (fun i _ ↦
    Martingale.integral_sq_discreteQuadraticSum_step_le hM hM4 i)
  rw [Finset.sum_range_sub (fun i : ℕ ↦ ∫ omega, Q i omega ^ 2 ∂P) n,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (fun i : ℕ ↦ ∫ omega, Q i omega * M i omega ^ 2 ∂P) n] at hsteps
  simp only [Q, discreteQuadraticSum_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, integral_zero, sub_zero] at hsteps
  have hfourth := Martingale.sum_integral_fourth_increments_le hM hM4 n
  have hQ2 := memLp_two_discreteQuadraticSum hM4 n
  have hM2 : MemLp (fun omega ↦ M n omega ^ 2) 2 P := by
    simpa only [pow_two] using memLp_two_mul_of_memLp_four (hM4 n) (hM4 n)
  have hprod : Integrable (fun omega ↦ Q n omega * M n omega ^ 2) P :=
    hQ2.integrable_mul hM2
  have hMn4 := integrable_pow_four_of_memLp_four (hM4 n)
  have hright : Integrable (fun omega ↦
      (1 / 2 : ℝ) * Q n omega ^ 2 + 2 * M n omega ^ 4) P :=
    (hQ2.integrable_sq.const_mul (1 / 2)).add (hMn4.const_mul 2)
  have hpoint (omega : W) : 2 * (Q n omega * M n omega ^ 2) ≤
      (1 / 2 : ℝ) * Q n omega ^ 2 + 2 * M n omega ^ 4 := by
    nlinarith [sq_nonneg (Q n omega - 2 * M n omega ^ 2)]
  have hyoung := integral_mono (hprod.const_mul 2) hright hpoint
  rw [integral_const_mul,
    integral_add (hQ2.integrable_sq.const_mul (1 / 2)) (hMn4.const_mul 2),
    integral_const_mul, integral_const_mul] at hyoung
  change (∫ omega, Q n omega ^ 2 ∂P) ≤ _
  change (∫ omega, Q n omega ^ 2 ∂P) ≤ _ at hsteps
  linarith

/-- Uniform-grid quadratic variation has a grid-independent second moment
whenever the real martingale has fourth moments. -/
theorem Martingale.integral_sq_quadraticVariationApprox_le
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (hM4 : ∀ t, MemLp (M t) 4 P) (T : ℝ≥0) (n : ℕ) :
    (∫ omega, quadraticVariationApprox M T (n + 1) omega ^ 2 ∂P) ≤
      10 * ∫ omega, M T omega ^ 4 ∂P := by
  let u := uniformPartitionTime T (n + 1)
  have hsample := martingale_comp_monotone hM u
    (monotone_uniformPartitionTime_general T (n + 1))
  have hraw := Martingale.integral_sq_discreteQuadraticSum_le hsample
    (fun i ↦ hM4 (u i)) (n + 1)
  have hu : u (n + 1) = T :=
    mul_div_cancel_right₀ T (by exact_mod_cast (Nat.zero_lt_succ n).ne')
  simpa only [discreteQuadraticSum, hu, quadraticVariationApprox, u] using hraw

/-- Fourth moments make the quadratic sums uniformly integrable. -/
theorem Martingale.uniformIntegrable_quadraticVariationApprox_of_memLp_four
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (hM4 : ∀ t, MemLp (M t) 4 P) (T : ℝ≥0) :
    UniformIntegrable (fun n ↦ quadraticVariationApprox M T (n + 1)) 1 P := by
  refine uniformIntegrable_one_of_uniform_integral_rpow (2 : ℝ) (by norm_num)
    (fun n ↦ aestronglyMeasurable_quadraticVariationApprox
      (fun t ↦ (hM4 t).aestronglyMeasurable) T (n + 1))
    (fun n omega ↦ quadraticVariationApprox_nonneg M T (n + 1) omega) ?_
    (10 * ∫ omega, M T omega ^ 4 ∂P) ?_
  · intro n
    have hq := memLp_two_discreteQuadraticSum
      (fun i ↦ hM4 (uniformPartitionTime T (n + 1) i)) (n + 1)
    simpa only [discreteQuadraticSum, quadraticVariationApprox, Real.rpow_two] using
      hq.integrable_sq
  · intro n
    simpa only [Real.rpow_two] using
      Martingale.integral_sq_quadraticVariationApprox_le hM hM4 T n

/-- The absolute mixed quadratic sum is dominated by the sum of the two
nonnegative scalar quadratic sums. -/
theorem norm_quadraticCovariationApprox_le_add
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W) :
    ‖quadraticCovariationApprox X Y T n omega‖ ≤
      quadraticVariationApprox X T n omega + quadraticVariationApprox Y T n omega := by
  have hsq := quadraticCovariationApprox_sq_le X Y T n omega
  have hX := quadraticVariationApprox_nonneg X T n omega
  have hY := quadraticVariationApprox_nonneg Y T n omega
  rw [Real.norm_eq_abs]
  have habs := sq_abs (quadraticCovariationApprox X Y T n omega)
  nlinarith [sq_nonneg (quadraticVariationApprox X T n omega),
    sq_nonneg (quadraticVariationApprox Y T n omega),
    abs_nonneg (quadraticCovariationApprox X Y T n omega)]

/-- Mixed quadratic sums of L4 martingales are uniformly integrable, with
no pathwise bounds or continuity assumption on either martingale. -/
theorem uniformIntegrable_quadraticCovariationApprox_of_memLp_four
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℝ} (hX : Martingale X V P) (hY : Martingale Y V P)
    (hX4 : ∀ t, MemLp (X t) 4 P) (hY4 : ∀ t, MemLp (Y t) 4 P) (T : ℝ≥0) :
    UniformIntegrable (fun n ↦ quadraticCovariationApprox X Y T (n + 1)) 1 P := by
  have hUIX := Martingale.uniformIntegrable_quadraticVariationApprox_of_memLp_four hX hX4 T
  have hUIY := Martingale.uniformIntegrable_quadraticVariationApprox_of_memLp_four hY hY4 T
  have hUI := UniformIntegrable.add_banach hUIX hUIY le_rfl
  apply UniformIntegrable.mono_norm hUI
  · intro n
    exact aestronglyMeasurable_quadraticCovariationApprox
      (fun t ↦ (hX4 t).aestronglyMeasurable) (fun t ↦ (hY4 t).aestronglyMeasurable)
      T (n + 1)
  · intro n omega
    change ‖quadraticCovariationApprox X Y T (n + 1) omega‖ ≤
      ‖quadraticVariationApprox X T (n + 1) omega +
        quadraticVariationApprox Y T (n + 1) omega‖
    rw [Real.norm_of_nonneg (add_nonneg
      (quadraticVariationApprox_nonneg X T (n + 1) omega)
      (quadraticVariationApprox_nonneg Y T (n + 1) omega))]
    exact norm_quadraticCovariationApprox_le_add X Y T (n + 1) omega

end StochasticCalculus
