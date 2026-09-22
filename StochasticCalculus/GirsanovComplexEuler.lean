/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovFourierIncrement

/-!
# Capped complex Euler approximations

The capped complex Girsanov exponential and its Euler processes, the
second-order residual of an exponential increment with its bound, and the
weighted bracket, quadratic, cross and higher-order residual sums along
uniform partitions.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- Cap only the real Novikov-density factor of the complex Girsanov
exponential.  Its oscillatory factor is left unchanged, so the cap is
bounded without requiring path regularity of the pre-Brownian driver. -/
def cappedComplexDoleansDadeExponentialCombination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) (omega : W) : ℂ :=
  (cappedDoleansDadeExponential M bracket R t omega : ℂ) *
    Complex.exp
      (((c * (B t omega - C t omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))

/-- The capped complex Girsanov exponential has an exact deterministic
modulus bound on every finite time interval. -/
theorem norm_cappedComplexDoleansDadeExponentialCombination_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T t : ℝ≥0) (ht : t ≤ T) (omega : W) :
    ‖cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R t omega‖ ≤
        (R : ℝ) * Real.exp (c ^ 2 * (T : ℝ) / 2) := by
  unfold cappedComplexDoleansDadeExponentialCombination
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · rw [Complex.norm_exp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
      mul_one, neg_zero, zero_add]
    have hexp : Real.exp (c ^ 2 * (t : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      have ht' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg c]
    exact mul_le_mul (min_le_right _ _) hexp
      (Real.exp_pos _).le R.coe_nonneg
  · exact le_min (doleansDadeExponential_pos M bracket t omega).le
      R.coe_nonneg

/-- Adapted inputs make the density-capped complex exponential adapted. -/
theorem stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R : ℝ≥0) :
    StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) := by
  intro t
  apply (Complex.continuous_ofReal.comp_stronglyMeasurable
    (stronglyAdapted_cappedDoleansDadeExponential
      hM hbracket R t)).mul
  apply Complex.continuous_exp.comp_stronglyMeasurable
  exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
    ((hB t).sub (hC t) |>.const_mul c)).mul_const Complex.I).add
      stronglyMeasurable_const)

/-- Deterministic norm bound for the density-capped complex coefficient on
the Girsanov horizon. -/
def cappedComplexGirsanovCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  R * Real.toNNReal (Real.exp (c ^ 2 * (T : ℝ) / 2))

/-- Deterministic norm bound for the Brownian coefficient `i c H` in the
two-integrator complex Euler process. -/
def cappedComplexGirsanovBrownianCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal
    (|c| * (cappedComplexGirsanovCoefficientBound c R T : ℝ))

/-- The Euler martingale candidate for the complex Girsanov exponential.
The density factor in the coefficient is capped, while `N` is the chosen
martingale approximation to the local-martingale integrator `M`. -/
def cappedComplexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The uncapped complex Euler process on a uniform grid.  It is the exact
first-order sum whose stochastic Taylor error remains after the increasing
density caps have become inactive. -/
def complexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The canonical complex uniform-grid Doléans left sum, written directly
for a complex integrator and its algebraic complex bracket. -/
noncomputable def complexDoleansEulerProcess
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential X Q (min t U) omega
  fun t omega => H 0 omega +
    ∑ i ∈ Finset.range n,
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          H (uniformPartitionTime U n i) omega

/-- The exact one-step residual sum for the canonical complex Doléans Euler
process.  Its first two terms telescope; the third is the Euler increment. -/
noncomputable def complexDoleansEulerResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  let E := complexDoleansDadeExponential X Q
  ∑ i ∈ Finset.range n,
    ((E (min t (uniformPartitionTime U n (i + 1))) omega -
        E (min t (uniformPartitionTime U n i)) omega) -
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          E (min (uniformPartitionTime U n i) U) omega)

/-- Exact multiplicative form of one complex Doléans Euler residual.  This
isolates the analytic remainder `exp z - 1 - dX` before any probabilistic
estimate is applied. -/
theorem complexDoleansDadeExponential_increment_sub_linear
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (Complex.exp
          ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) -
            1 - (X b omega - X a omega)) := by
  unfold complexDoleansDadeExponential
  have hexp :
      Complex.exp (X b omega - Q b omega / 2) =
        Complex.exp (X a omega - Q a omega / 2) *
          Complex.exp
            ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- The higher-order remainder left after extracting the quadratic-variation
term from one complex Doléans Euler cell. -/
noncomputable def complexDoleansSecondOrderResidual
    (dX dQ : ℂ) : ℂ :=
  Complex.exp (dX - dQ / 2) - 1 - dX - (dX ^ 2 - dQ) / 2

/-- Quantitative higher-order bound for the extracted complex Doléans
remainder.  The first term is cubic in the compensated-log increment; the
second records the finite-variation correction caused by replacing that
increment's square with `dX²`. -/
theorem norm_complexDoleansSecondOrderResidual_le (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        ‖((dX - dQ / 2) ^ 2 - dX ^ 2) / 2‖ := by
  let z : ℂ := dX - dQ / 2
  have hexp :
      ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤
        ‖z‖ ^ 3 * Real.exp ‖z‖ := by
    convert Complex.norm_exp_sub_sum_le_norm_mul_exp z 3 using 1
    congr 1
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  calc
    ‖complexDoleansSecondOrderResidual dX dQ‖ =
        ‖(Complex.exp z - 1 - z - z ^ 2 / 2) +
          (z ^ 2 - dX ^ 2) / 2‖ := by
      congr 1
      unfold complexDoleansSecondOrderResidual z
      ring
    _ ≤ ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := add_le_add hexp le_rfl
    _ = _ := by rfl

/-- A cancellation-ready version of the one-cell remainder bound.  The
correction to the cubic term contains an explicit bracket increment, rather
than an opaque difference of squares. -/
theorem norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket
    (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2 := by
  let z : ℂ := dX - dQ / 2
  have hfactor : z ^ 2 - dX ^ 2 = (-dQ / 2) * (z + dX) := by
    dsimp only [z]
    ring
  apply (norm_complexDoleansSecondOrderResidual_le dX dQ).trans
  gcongr
  rw [hfactor]
  simp only [norm_div, norm_mul, norm_neg]
  have hnormtwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnormtwo]
  calc
    ‖dQ‖ / 2 * ‖z + dX‖ / 2 ≤
        ‖dQ‖ / 2 * (‖z‖ + ‖dX‖) / 2 := by
      gcongr
      exact norm_add_le z dX
    _ = _ := by rfl

/-- The nonnegative scalar majorant for one higher-order Doléans cell. -/
noncomputable def complexDoleansSecondOrderResidualBound
    (dX dQ : ℂ) : ℝ :=
  ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
    (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2

theorem complexDoleansSecondOrderResidualBound_nonneg (dX dQ : ℂ) :
    0 ≤ complexDoleansSecondOrderResidualBound dX dQ := by
  unfold complexDoleansSecondOrderResidualBound
  positivity

/-- The one-cell higher-order remainder is controlled by its explicit
nonnegative scalar majorant. -/
theorem norm_complexDoleansSecondOrderResidual_le_bound (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      complexDoleansSecondOrderResidualBound dX dQ := by
  exact norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket dX dQ

/-- One Doléans Euler cell splits exactly into a weighted bracket discrepancy
and the higher-order exponential remainder. -/
theorem complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (((X b omega - X a omega) ^ 2 -
              (Q b omega - Q a omega)) / 2 +
          complexDoleansSecondOrderResidual
            (X b omega - X a omega) (Q b omega - Q a omega)) := by
  rw [complexDoleansDadeExponential_increment_sub_linear]
  unfold complexDoleansSecondOrderResidual
  ring

/-- The stopped-grid weighted discrepancy between algebraic squared
increments and increments of the proposed complex bracket. -/
noncomputable def complexDoleansWeightedBracketResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      ((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) ^ 2 -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega))

/-- A complex-weighted real quadratic-variation discrepancy on a stopped
uniform grid.  The complex weight is kept explicit because the Fourier
Doléans exponential is not real-valued. -/
noncomputable def complexWeightedQuadraticResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      (((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ) ^ 2 -
        ((A (min t (uniformPartitionTime U n (i + 1))) omega -
          A (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- A complex-weighted real cross-variation discrepancy on a stopped uniform
grid. -/
noncomputable def complexWeightedCrossResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ)
    (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      ((((X (min t (uniformPartitionTime U n (i + 1))) omega -
            X (min t (uniformPartitionTime U n i)) omega) *
          (Y (min t (uniformPartitionTime U n (i + 1))) omega -
            Y (min t (uniformPartitionTime U n i)) omega) : ℝ) : ℂ) -
        ((C (min t (uniformPartitionTime U n (i + 1))) omega -
          C (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- A sum over a uniformly subdivided grid can be indexed by its coarse
block and its position inside that block. -/
theorem sum_range_mul_eq_sum_range_sum_range
    {E : Type*} [AddCommMonoid E] (k n : ℕ) (f : ℕ → E) :
    (∑ i ∈ Finset.range (k * n), f i) =
      ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
  calc
    _ = ∑ i : Fin (k * n), f i :=
      (Fin.sum_univ_eq_sum_range f (k * n)).symm
    _ = ∑ p : Fin k × Fin n, f (finProdFinEquiv p) :=
      (Equiv.sum_comp finProdFinEquiv
        (fun i : Fin (k * n) ↦ f i)).symm
    _ = ∑ j : Fin k, ∑ r : Fin n, f (r + n * j) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ j ∈ Finset.range k, ∑ r : Fin n,
        f (r + n * j) := by
      exact Fin.sum_univ_eq_sum_range
        (fun j ↦ ∑ r : Fin n, f (r + n * j)) k
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Fin.sum_univ_eq_sum_range (fun r ↦ f (r + n * j)) n

/-- Frozen complex coarse weights against exact finite-variation increments
are the active right-endpoint step weights against all fine increments. -/
theorem finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (A (uniformPartitionTime U k (j + 1)) omega -
        A (uniformPartitionTime U k j) omega : ℂ)) =
      ∑ i ∈ Finset.range (k * n), c (i / n) omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ) := by
  have hblock (j : ℕ) :
      (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ) =
        ∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
    have hleft : uniformPartitionTime U (k * n) (n * j) =
        uniformPartitionTime U k j := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn j 0).symm
    have hright : uniformPartitionTime U (k * n) (n * (j + 1)) =
        uniformPartitionTime U k (j + 1) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn (j + 1) 0).symm
    have htel := Finset.sum_range_sub (fun r ↦
      (A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) n
    have hindex : n + n * j = n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simp only [zero_add] at htel
    rw [hindex, hright, hleft] at htel
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htel.symm
  calc
    _ = ∑ j ∈ Finset.range k, c j omega *
        (∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hblock]
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        c j omega *
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [sum_range_mul_eq_sum_range_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < n := Finset.mem_range.mp hr
      rw [Nat.add_mul_div_left r j hn, Nat.div_eq_of_lt hrlt,
        zero_add]

/-- Freezing complex weights on completed coarse blocks costs at most the
weight error times the total variation of the real integrator. -/
theorem norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (weight c : ℕ → W → ℂ)
    (K : ℝ) (_hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range (k * n),
      ‖weight i omega - c (i / n) omega‖ ≤ K) :
    ‖(∑ i ∈ Finset.range (k * n), weight i omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ)‖ ≤
      K * totalVariationApprox A U (k * n) omega := by
  rw [finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    A U hk hn c omega, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range (k * n),
        (weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range (k * n),
        ‖(weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k * n), K *
        |A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      rw [show
        ((A (uniformPartitionTime U (k * n) (i + 1)) omega : ℂ) -
            (A (uniformPartitionTime U (k * n) i) omega : ℂ)) =
          ((A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℝ) : ℂ) by
            push_cast
            rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _)
    _ = K * totalVariationApprox A U (k * n) omega := by
      unfold totalVariationApprox
      rw [Finset.mul_sum]

/-- Outside the Brownian block-oscillation event, freezing the complex
Girsanov weight in a finite-variation sum costs its total variation times
the same coefficient-and-Fourier modulus used for covariations. -/
theorem
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
    {W : Type*} [MeasurableSpace W]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    {k n : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (alpha R : ℝ) (halpha : 0 ≤ alpha) (hR : 0 ≤ R)
    (delta : ℝ≥0) (hdelta : 0 < delta) {omega : W}
    (hAclose : ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
      uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T (k * n) i) omega -
        girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ∀ j ∈ Finset.range k,
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T k j) omega‖ ≤ R)
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r ↦
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ‖(∑ i ∈ Finset.range (k * n),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega *
          (A (uniformPartitionTime T (k * n) (i + 1)) omega -
            A (uniformPartitionTime T (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k j) omega *
          (A (uniformPartitionTime T k (j + 1)) omega -
            A (uniformPartitionTime T k j) omega : ℂ)‖ ≤
      (alpha + R * |c| * (delta : ℝ)) *
        totalVariationApprox A T (k * n) omega := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by
      exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hweight : ∀ i ∈ Finset.range (k * n),
      ‖complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega -
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k (i / n)) omega‖ ≤
        alpha + R * |c| * (delta : ℝ) := by
    intro i hi
    let j := i / n
    have hilt : i < k * n := Finset.mem_range.mp hi
    have hjlt : j < k := by
      exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hilt)
    have hj : j ∈ Finset.range k := Finset.mem_range.mpr hjlt
    have hleft : uniformPartitionTime T k j =
        uniformPartitionTime T (k * n) (n * j) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn j 0
    have hright : uniformPartitionTime T k (j + 1) =
        uniformPartitionTime T (k * n) (n * (j + 1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    have hjmul : n * j ≤ i := by
      simpa only [j, Nat.mul_comm] using Nat.div_mul_le_self i n
    have hmod : i % n < n := Nat.mod_lt i hn
    have hdecomp : n * j + i % n = i := by
      exact Nat.div_add_mod i n
    have hiRight : i + 1 ≤ n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hactive : uniformPartitionTime T k j <
          uniformPartitionTime T (k * n) (i + 1) ∧
        uniformPartitionTime T (k * n) (i + 1) ≤
          uniformPartitionTime T k (j + 1) := by
      rw [hleft, hright]
      exact ⟨hstrict (by omega), hstrict.monotone hiRight⟩
    obtain ⟨r, hr, htime⟩ :=
      uniformPartitionTime_active_block_common_refinement
        T hT hk hn hactive
    have hBclose := hosc j hj r hr
    rw [← htime] at hBclose
    rw [complexDoleansDadeExponential_combination_factor_continuous_brownian,
      complexDoleansDadeExponential_combination_factor_continuous_brownian]
    have hraw := norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
      (girsanovComplexDoleansContinuousCoefficient M bracket C c) B
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (lipschitzWith_complexFourierCharacter c) T omega alpha R 1
      (delta : ℝ) (hAclose i hi j hj hactive) (hAbound j hj)
      (by rw [Complex.norm_exp_ofReal_mul_I]) hBclose
    simpa only [j, mul_one,
      Real.coe_toNNReal |c| (abs_nonneg c)] using hraw
  exact norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    A T hk hn
      (fun i omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (k * n) i) omega)
      (fun j omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T k j) omega)
      (alpha + R * |c| * (delta : ℝ))
      (add_nonneg halpha (mul_nonneg (mul_nonneg hR (abs_nonneg c))
        delta.coe_nonneg)) omega hweight

/-- The pathwise complex finite-variation freezing estimate promotes to
convergence in measure when the variation controls are tight and the
Brownian block-oscillation event becomes rare. -/
theorem
    tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (K N : ℕ → ℕ) (hT : 0 < T) (hK : ∀ r, 0 < K r)
    (hN : ∀ r, 0 < N r)
    (alpha R : ℕ → W → ℝ) (halpha : ∀ r omega, 0 ≤ alpha r omega)
    (hR : ∀ r omega, 0 ≤ R r omega)
    (halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0))
    (hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta)
    (delta : ℕ → ℝ≥0)
    (hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0))
    (hdeltaPos : ∀ r, 0 < delta r)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          totalVariationApprox A T (K r * N r) omega} < eta)
    (hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0))
    (hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r * N r) i) omega -
          girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega)
    (hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega) :
    TendstoInMeasure P (fun r omega ↦
      (∑ i ∈ Finset.range (K r * N r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r * N r) i) omega *
          (A (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            A (uniformPartitionTime T (K r * N r) i) omega : ℂ)) -
      ∑ j ∈ Finset.range (K r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r) j) omega *
          (A (uniformPartitionTime T (K r) (j + 1)) omega -
            A (uniformPartitionTime T (K r) j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun r omega ↦
    totalVariationApprox A T (K r * N r) omega
  let small : ℕ → W → ℝ := fun r _ ↦ |c| * (delta r : ℝ)
  let rq : ℕ → W → ℝ := fun r omega ↦ R r omega * q r omega
  let b₁ : ℕ → W → ℝ := fun r omega ↦ alpha r omega * q r omega
  let b₂ : ℕ → W → ℝ := fun r omega ↦ small r omega * rq r omega
  let b : ℕ → W → ℝ := fun r omega ↦ b₁ r omega + b₂ r omega
  have hq_nonneg : ∀ r omega, 0 ≤ q r omega := fun r omega ↦ by
    dsimp only [q, totalVariationApprox]
    exact Finset.sum_nonneg fun _ _hi ↦ abs_nonneg _
  have hq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ q r omega} < eta := by
    simpa only [q] using htvtight
  have hb₁ : TendstoInMeasure P b₁ atTop (fun _ ↦ 0) := by
    apply halphaZero.of_norm_sub_le_mul_of_eventually_tight
      hq_nonneg hq_tight
    intro r omega
    simp only [b₁, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (halpha r omega), q]
    rw [abs_of_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))]
  have hrq_nonneg : ∀ r omega, 0 ≤ rq r omega := fun r omega ↦
    mul_nonneg (hR r omega) (hq_nonneg r omega)
  have hrq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ rq r omega} < eta := by
    exact eventually_tight_mul_of_nonneg hR hq_nonneg hRtight hq_tight
  have hsmall : TendstoInMeasure P small atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro r
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ ↦ by
        simpa only [small, mul_zero] using
          hdelta.const_mul |c|
  have hsmall_nonneg : ∀ r omega, 0 ≤ small r omega := fun r omega ↦
    mul_nonneg (abs_nonneg c) (delta r).coe_nonneg
  have hb₂ : TendstoInMeasure P b₂ atTop (fun _ ↦ 0) := by
    apply hsmall.of_norm_sub_le_mul_of_eventually_tight
      hrq_nonneg hrq_tight
    intro r omega
    simp only [b₂, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hsmall_nonneg r omega)]
    rw [abs_of_nonneg
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))]
  have hbZero : TendstoInMeasure P b atTop (fun _ ↦ 0) := by
    simpa only [b, zero_add] using hb₁.add_real_noMeas hb₂
  let bad : ℕ → Set W := fun r ↦
    ⋃ j ∈ Finset.range (K r), {omega |
      ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
        Finset.nonempty_range_add_one (fun u ↦
          (B (uniformPartitionTime T (K r) j +
              uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
            B (uniformPartitionTime T (K r) j) omega) ^ 4)}
  have hbadZero : Tendsto (fun r ↦ P.real (bad r)) atTop (nhds 0) := by
    simpa only [bad] using hbad
  have hb_nonneg : ∀ r omega, 0 ≤ b r omega := fun r omega ↦
    add_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))
  apply hbZero.of_norm_le_nonneg_outside_noMeas hb_nonneg hbadZero
  intro r omega homega
  have hraw :=
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
      M bracket B C A c T hT (hK r) (hN r)
      (alpha r omega) (R r omega) (halpha r omega) (hR r omega)
      (delta r) (hdeltaPos r) (hAclose r omega) (hAbound r omega) homega
  calc
    _ ≤ (alpha r omega + R r omega * |c| * (delta r : ℝ)) *
        q r omega := by simpa only [q] using hraw
    _ = b r omega := by
      dsimp only [b, b₁, b₂, small, rq]
      ring

/-- Girsanov density data supplies all coefficient and Brownian controls for
finite-variation freezing on the polynomial common-refinement scale. -/
theorem
    GirsanovDensityData.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C A : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox A T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    TendstoInMeasure P (fun r omega ↦
      let K := (r + 1) ^ 5
      let N := n (K - 1) + 1
      (∑ i ∈ Finset.range (K * N),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K * N) i) omega *
          (A (uniformPartitionTime T (K * N) (i + 1)) omega -
            A (uniformPartitionTime T (K * N) i) omega : ℂ)) -
      ∑ j ∈ Finset.range K,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T K j) omega *
          (A (uniformPartitionTime T K (j + 1)) omega -
            A (uniformPartitionTime T K j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let s : ℕ → ℕ := fun r ↦ K r - 1
  let N : ℕ → ℕ := fun r ↦ n (s r) + 1
  let H : ℝ≥0 → W → ℂ :=
    girsanovComplexDoleansContinuousCoefficient M bracket C c
  let alpha : ℕ → W → ℝ := fun r ↦
    commonRefinementMaxComplexStepError H T (s r) (n (s r))
  let e : ℝ := Real.exp (c ^ 2 * (T : ℝ) / 2)
  let R : ℕ → W → ℝ := fun r omega ↦
    e * complexFreezingDensityLeftMax M bracket T (s r) omega
  let delta : ℕ → ℝ≥0 := fun r ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹
  have hKpos : ∀ r, 0 < K r := fun r ↦ by
    dsimp only [K]
    positivity
  have hNpos : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hsadd (r : ℕ) : s r + 1 = K r := by
    dsimp only [s]
    exact Nat.sub_add_cancel (hKpos r)
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have halt : a < K a := by
      dsimp only [K]
      have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hHmeas : ∀ t, StronglyMeasurable (H t) := by
    intro t
    apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    · intro u
      exact (hdata.adapted_martingale u).mono (V.le u)
    · intro u
      exact (hdata.adapted_bracket u).mono (V.le u)
    · exact hCmeas
  have hHcont : ∀ omega, Continuous (fun t ↦ H t omega) := by
    exact continuous_girsanovComplexDoleansContinuousCoefficient
      hdata.continuous_martingale_path
      (fun omega ↦ (hdata.continuous_monotone_bracket omega).1)
      hCcont c
  have halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0) := by
    have hbase := commonRefinementMaxComplexStepError_tendstoInMeasure_zero
      (P := P) (A := H) hHmeas T hT hHcont n
    change TendstoInMeasure P
      ((fun k ↦ commonRefinementMaxComplexStepError H T k (n k)) ∘ s)
      atTop (fun _ ↦ 0)
    exact hbase.comp hsTop
  have halpha : ∀ r omega, 0 ≤ alpha r omega := fun r omega ↦
    commonRefinementMaxComplexStepError_nonneg H T (s r) (n (s r)) omega
  have hRnonneg : ∀ r omega, 0 ≤ R r omega := fun r omega ↦ by
    exact mul_nonneg (Real.exp_pos _).le
      (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
  have hdensityTight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega} < eta := by
    intro eta heta
    obtain ⟨D, hD, htail⟩ :=
      hdata.complexFreezingDensityLeftMax_tight eta heta
    exact ⟨D, hD, Filter.Eventually.of_forall fun r ↦ htail (s r)⟩
  have hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta := by
    exact eventually_tight_const_mul_of_nonneg e (Real.exp_pos _).le
      (fun r omega ↦ complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega) hdensityTight
  have hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun r : ℕ ↦
        ((r + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hinv
    change Tendsto
      (NNReal.toReal ∘ fun r : ℕ ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0)
    exact hcoe
  have hdeltaPos : ∀ r, 0 < delta r := fun r ↦ by
    dsimp only [delta]
    positivity
  have hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0) := by
    simpa only [K, N, s, delta] using
      tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
        hB hsm T N hNpos
  have hHclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖H (uniformPartitionTime T (K r * N r) i) omega -
          H (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega := by
    intro r omega i hi j hj hactive
    have hcounts : (s r + 1) * (n (s r) + 1) = K r * N r := by
      rw [hsadd]
    have hi' : i ∈ Finset.range ((s r + 1) * (n (s r) + 1)) := by
      simpa only [hcounts] using hi
    have hle :
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) i) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖ ≤
          commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega := by
      unfold commonRefinementMaxComplexStepError
      exact (le_refl _).trans (Finset.le_sup' (fun u ↦
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) u) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖) hi')
    have hj' : j ∈ Finset.range (s r + 1) := by
      simpa only [hsadd] using hj
    have hactive' : uniformPartitionTime T (s r + 1) j <
          uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
        uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
          uniformPartitionTime T (s r + 1) (j + 1) := by
      simpa only [hsadd, hcounts] using hactive
    have hsum := uniformPartition_rightEndpoint_complexStep_sum_eq
      T (uniformPartitionTime T
        ((s r + 1) * (n (s r) + 1)) (i + 1)) (s r + 1)
      hT (by positivity)
      (fun l ↦ H (uniformPartitionTime T (s r + 1) l) omega)
      hj' hactive'
    rw [hsum] at hle
    change ‖H (uniformPartitionTime T (K r * N r) i) omega -
        H (uniformPartitionTime T (K r) j) omega‖ ≤
      commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega
    simpa only [hcounts, hsadd] using hle
  have hHbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖H (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega := by
    intro r omega j hj
    have hjle : j ≤ K r := (Finset.mem_range.mp hj).le
    have ht := (uniformPartitionTime_mem_Icc_of_le T (hKpos r) hjle).2
    have hdensity : doleansDadeExponential M bracket
          (uniformPartitionTime T (K r) j) omega ≤
        complexFreezingDensityLeftMax M bracket T (s r) omega := by
      have hj' : j ∈ Finset.range (s r + 1) := by
        simpa only [hsadd] using hj
      have hmax := Finset.le_sup' (fun u ↦
        doleansDadeExponential M bracket
          (min (uniformPartitionTime T (s r + 1) u) T) omega) hj'
      simpa only [complexFreezingDensityLeftMax, hsadd, min_eq_left ht]
        using hmax
    have hexp : Real.exp
          (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤ e := by
      apply Real.exp_le_exp.mpr
      gcongr
    rw [norm_girsanovComplexDoleansContinuousCoefficient]
    calc
      doleansDadeExponential M bracket
            (uniformPartitionTime T (K r) j) omega *
          Real.exp (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega * e :=
        mul_le_mul hdensity hexp (Real.exp_pos _).le
          (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
      _ = e * complexFreezingDensityLeftMax M bracket T (s r) omega :=
        mul_comm _ _
  apply tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    M bracket B C A c T K N hT hKpos hNpos alpha R halpha hRnonneg
      halphaZero hRtight delta hdelta hdeltaPos
  · simpa only [K, N, s] using htvtight
  · exact hbad
  · exact hHclose
  · exact hHbound

/-- At the grid horizon a complex-weighted stopped cross residual is the
difference between the ordinary complex-weighted cross and finite-variation
sums. -/
theorem complexWeightedCrossResidualApprox_terminal
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexWeightedCrossResidualApprox H X Y C U n U omega =
      (∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          ((X (uniformPartitionTime U n (i + 1)) omega -
            X (uniformPartitionTime U n i) omega) *
          (Y (uniformPartitionTime U n (i + 1)) omega -
            Y (uniformPartitionTime U n i) omega) : ℂ)) -
      ∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          (C (uniformPartitionTime U n (i + 1)) omega -
            C (uniformPartitionTime U n i) omega : ℂ) := by
  unfold complexWeightedCrossResidualApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi0).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi1).2]
  push_cast
  ring

/-- A complex-weighted quadratic residual is the self-cross residual. -/
theorem complexWeightedQuadraticResidualApprox_eq_cross_self
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexWeightedQuadraticResidualApprox H X A U n t omega =
      complexWeightedCrossResidualApprox H X X A U n t omega := by
  unfold complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  apply Finset.sum_congr rfl
  intro i _hi
  push_cast
  rw [pow_two]

/-- The complex second-order discrepancy for `M + i c B` is exactly the
sum of the two real quadratic-variation discrepancies and the real cross
variation discrepancy.  This isolates the three cancellations required by
the Fourier proof without imposing real-valuedness on the left weight. -/
theorem complexDoleansWeightedBracketResidualApprox_combination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U n t omega =
      complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M bracket U n t omega -
        (c ^ 2 : ℂ) *
          complexWeightedQuadraticResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            B (fun s _ ↦ (s : ℝ)) U n t omega +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          complexWeightedCrossResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            M B C U n t omega := by
  unfold complexDoleansWeightedBracketResidualApprox
    complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let s := min t (uniformPartitionTime U n i)
  let u := min t (uniformPartitionTime U n (i + 1))
  let h := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c) s omega
  let dM := M u omega - M s omega
  let dA := bracket u omega - bracket s omega
  let dB := B u omega - B s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have hX :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  have hQ :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  change h *
      ((complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega) ^ 2 -
        (complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega)) = _
  rw [hX, hQ]
  change h *
      (((dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I) ^ 2 -
        ((dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I)) =
    h * ((dM : ℂ) ^ 2 - (dA : ℂ)) -
      (c ^ 2 : ℂ) * (h * ((dB : ℂ) ^ 2 - (dt : ℂ))) +
      (((2 * c : ℝ) : ℂ) * Complex.I) *
        (h * (((dM * dB : ℝ) : ℂ) - (dC : ℂ)))
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The sum of higher-order exponential remainders on a stopped uniform
grid. -/
noncomputable def complexDoleansHigherOrderResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      complexDoleansSecondOrderResidual
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

/-- Explicit scalar majorant for the whole stopped-grid higher-order
remainder.  This is the sum of the left exponential modulus times the
one-cell cubic/bracket bound. -/
noncomputable def complexDoleansHigherOrderResidualBoundApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ *
      complexDoleansSecondOrderResidualBound
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

theorem complexDoleansHigherOrderResidualBoundApprox_nonneg
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualBoundApprox
  exact Finset.sum_nonneg fun i _hi => mul_nonneg (norm_nonneg _)
    (complexDoleansSecondOrderResidualBound_nonneg _ _)

/-- The full higher-order majorant is controlled by scalar aggregate bounds.
This separates the analytic input into uniform cell increments and tight
quadratic/finite-variation sums, which can be estimated independently. -/
theorem complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W)
    (K deltaZ deltaX sumZSq sumQ : ℝ)
    (hK : 0 ≤ K) (hdeltaZ : 0 ≤ deltaZ) (hdeltaX : 0 ≤ deltaX)
    (hweight : ∀ i ∈ Finset.range n,
      ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ ≤ K)
    (hz : ∀ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ≤ deltaZ)
    (hx : ∀ i ∈ Finset.range n,
      ‖X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega‖ ≤ deltaX)
    (hzsq : (∑ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ^ 2) ≤ sumZSq)
    (hqsum : (∑ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖) ≤ sumQ) :
    complexDoleansHigherOrderResidualBoundApprox X Q U n t omega ≤
      K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
  let dX : ℕ → ℂ := fun i =>
    X (min t (uniformPartitionTime U n (i + 1))) omega -
      X (min t (uniformPartitionTime U n i)) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (min t (uniformPartitionTime U n (i + 1))) omega -
      Q (min t (uniformPartitionTime U n i)) omega
  let z : ℕ → ℂ := fun i => dX i - dQ i / 2
  let E : ℕ → ℂ := fun i =>
    complexDoleansDadeExponential X Q
      (min t (uniformPartitionTime U n i)) omega
  change (∑ i ∈ Finset.range n, ‖E i‖ *
      (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
        (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤ _
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖E i‖ *
          (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
            (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2) ≤
        K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) := by
    have hzi : ‖z i‖ ≤ deltaZ := by simpa only [z, dX, dQ] using hz i hi
    have hxi : ‖dX i‖ ≤ deltaX := by simpa only [dX] using hx i hi
    apply mul_le_mul (hweight i hi)
    · apply add_le_add
      · calc
          ‖z i‖ ^ 3 * Real.exp ‖z i‖ =
              ‖z i‖ * ‖z i‖ ^ 2 * Real.exp ‖z i‖ := by ring
          _ ≤ deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ := by
            gcongr
      · gcongr
    · positivity
    · exact hK
  calc
    (∑ i ∈ Finset.range n, ‖E i‖ *
        (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
          (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤
        ∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) :=
      Finset.sum_le_sum hcell
    _ = K * (deltaZ * Real.exp deltaZ *
          (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) +
        ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
          (deltaZ + deltaX) / 2) := by
      have hfirst :
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) =
            K * deltaZ * Real.exp deltaZ *
              (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      have hsecond :
          (∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
            K * ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
              (deltaZ + deltaX) / 2 := by
        calc
          _ = ∑ i ∈ Finset.range n,
              (K * (deltaZ + deltaX) / 4) * ‖dQ i‖ := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = (K * (deltaZ + deltaX) / 4) *
              (∑ i ∈ Finset.range n, ‖dQ i‖) := by
            rw [Finset.mul_sum]
          _ = _ := by ring
      rw [show (∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) +
          ∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      rw [hfirst, hsecond]
      ring
    _ ≤ K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
      gcongr

end StochasticCalculus
