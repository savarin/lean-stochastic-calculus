/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.ItoFormula
import StochasticCalculus.ItoMaximal
import StochasticCalculus.QuadraticVariationGrid
import StochasticCalculus.TightProduct

/-!
# General Itô formula: exact partition reduction

This file records the algebraic reduction behind the time-dependent Itô
formula.  For a function `f(t, x)` and a process `X`, its increment along a
uniform partition is split exactly into

* the left time-derivative sum,
* the left space-derivative sum,
* the weighted quadratic-variation sum, and
* an explicit remainder.

Consequently, convergence in probability of the four analytic pieces implies
the almost-everywhere Itô identity.  The final section proves the resulting
formula unconditionally for quadratic state functions of a general Itô
process, using `quadraticVariation_itoProcess`.

The module constructs a continuous modification for every `IsItoProcess` by
elementary predictable density, Doob's inequality, and Borel--Cantelli.  For
both the separable `g(t) + f(x)` projection and unrestricted genuinely
two-variable test functions, the remaining analytic gate is
diffusion-weighted bracket convergence (and, for an explicitly named
stochastic integral rather than an existential `dX` limit, integrand closure
under the derivative weight).  The mixed time/state Taylor remainder is
discharged by a compact-rectangle uniform Taylor bound, path continuity, and
the proved quadratic-variation limit.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

/-- The time partial derivative, with the state variable held fixed. -/
noncomputable def itoTimeDerivative (f : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => f r x) s

/-- The space partial derivative, with the time variable held fixed. -/
noncomputable def itoSpaceDerivative (f : ℝ → ℝ → ℝ) (s x : ℝ) : ℝ :=
  deriv (f s) x

/-- The second space partial derivative. -/
noncomputable def itoSpaceSecondDerivative (f : ℝ → ℝ → ℝ)
    (s x : ℝ) : ℝ :=
  deriv (deriv (f s)) x

/-- The left-endpoint time-derivative sum along the uniform `n`-partition. -/
noncomputable def generalItoTimeApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoTimeDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      ((uniformPartitionTime t n (i + 1) : ℝ) -
        (uniformPartitionTime t n i : ℝ))

/-- The left-endpoint space-derivative sum against the increments of `X`. -/
noncomputable def generalItoSpaceApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoSpaceDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega)

/-- The left-endpoint weighted quadratic-variation term, including the
coefficient `1 / 2`. -/
noncomputable def generalItoQuadraticApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / 2 : ℝ) *
      itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega) *
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega) ^ 2

/-- The second-derivative weight frozen on a coarse `k`-partition and
integrated against completed cells of a fine `n`-partition. -/
noncomputable def generalItoQuadraticCompletedStepApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n k : ℕ) (omega : W) : ℝ :=
  ∑ j ∈ Finset.range k,
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t k j : ℝ)
      (X (uniformPartitionTime t k j) omega)) *
    (quadraticVariationBeforeStopApprox X t n
        (uniformPartitionTime t k (j + 1)) omega -
      quadraticVariationBeforeStopApprox X t n
        (uniformPartitionTime t k j) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A bounded second-derivative weight is dominated pathwise by the ordinary
quadratic-variation sum.  This is the deterministic localization estimate
needed to pass from step weights to continuous weights. -/
theorem abs_generalItoQuadraticApprox_le_quadraticVariationApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) (K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ i ∈ Finset.range n,
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega)| ≤ K) :
    |generalItoQuadraticApprox f X t n omega| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox X t n omega := by
  unfold generalItoQuadraticApprox quadraticVariationApprox
  calc
    |∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) *
          itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
            (X (uniformPartitionTime t n i) omega) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2| ≤
        ∑ i ∈ Finset.range n,
          |(1 / 2 : ℝ) *
            itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
              (X (uniformPartitionTime t n i) omega) *
            (X (uniformPartitionTime t n (i + 1)) omega -
              X (uniformPartitionTime t n i) omega) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) * K *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_sq]
      gcongr
      exact hbound i hi
    _ = (1 / 2 : ℝ) * K *
        ∑ i ∈ Finset.range n,
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
      rw [Finset.mul_sum]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Uniformly close second-derivative weights produce close weighted
quadratic sums, with error controlled by the unweighted quadratic variation.
This is the principal deterministic estimate for a step-weight density
argument. -/
theorem abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
    (f g : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) (K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ i ∈ Finset.range n,
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega) -
        itoSpaceSecondDerivative g (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega)| ≤ K) :
    |generalItoQuadraticApprox f X t n omega -
        generalItoQuadraticApprox g X t n omega| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox X t n omega := by
  have hdiff : generalItoQuadraticApprox f X t n omega -
      generalItoQuadraticApprox g X t n omega =
      ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) *
          (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
              (X (uniformPartitionTime t n i) omega) -
            itoSpaceSecondDerivative g (uniformPartitionTime t n i : ℝ)
              (X (uniformPartitionTime t n i) omega)) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
    unfold generalItoQuadraticApprox
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hdiff]
  calc
    |∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) *
          (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
              (X (uniformPartitionTime t n i) omega) -
            itoSpaceSecondDerivative g (uniformPartitionTime t n i : ℝ)
              (X (uniformPartitionTime t n i) omega)) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2| ≤
        ∑ i ∈ Finset.range n,
          |(1 / 2 : ℝ) *
            (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
                (X (uniformPartitionTime t n i) omega) -
              itoSpaceSecondDerivative g (uniformPartitionTime t n i : ℝ)
                (X (uniformPartitionTime t n i) omega)) *
            (X (uniformPartitionTime t n (i + 1)) omega -
              X (uniformPartitionTime t n i) omega) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) * K *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_sq]
      gcongr
      exact hbound i hi
    _ = (1 / 2 : ℝ) * K *
        ∑ i ∈ Finset.range n,
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
      rw [Finset.mul_sum]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time measurability of a process and continuity of the
second-derivative weight imply measurability of every weighted quadratic
partition sum. -/
theorem aestronglyMeasurable_generalItoQuadraticApprox
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoQuadraticApprox f X t n) P := by
  unfold generalItoQuadraticApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega) *
        (X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) ^ 2) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    have hpair : AEStronglyMeasurable
        (fun omega => ((uniformPartitionTime t n i : ℝ),
          X (uniformPartitionTime t n i) omega)) P :=
      aestronglyMeasurable_const.prodMk
        (hXmeas (uniformPartitionTime t n i))
    have hweight : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f
          (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega)) P :=
      hsecond.comp_aestronglyMeasurable hpair
    have hincrement : AEStronglyMeasurable
        (fun omega => X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) P :=
      (hXmeas (uniformPartitionTime t n (i + 1))).sub
        (hXmeas (uniformPartitionTime t n i))
    exact (aestronglyMeasurable_const.mul hweight).mul (hincrement.pow 2)
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time measurability also makes every completed coarse-step
quadratic approximant measurable.  This exposes measurable two-scale error
events for the remaining convergence-in-probability argument. -/
theorem aestronglyMeasurable_generalItoQuadraticCompletedStepApprox
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n k : ℕ) :
    AEStronglyMeasurable
      (generalItoQuadraticCompletedStepApprox f X t n k) P := by
  unfold generalItoQuadraticCompletedStepApprox
  have hs : AEStronglyMeasurable
      (∑ j ∈ Finset.range k, fun omega =>
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k j : ℝ)
          (X (uniformPartitionTime t k j) omega)) *
        (quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k j) omega)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro j _hj
    have hpair : AEStronglyMeasurable
        (fun omega => ((uniformPartitionTime t k j : ℝ),
          X (uniformPartitionTime t k j) omega)) P :=
      aestronglyMeasurable_const.prodMk
        (hXmeas (uniformPartitionTime t k j))
    have hweight := hsecond.comp_aestronglyMeasurable hpair
    have hblock :=
      (aestronglyMeasurable_quadraticVariationBeforeStopApprox
        hXmeas t n (uniformPartitionTime t k (j + 1))).sub
      (aestronglyMeasurable_quadraticVariationBeforeStopApprox
        hXmeas t n (uniformPartitionTime t k j))
    exact (aestronglyMeasurable_const.mul hweight).mul hblock
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

/-- The exact one-step residual after the time, space, and quadratic terms
have been removed from the increment of `f`. -/
noncomputable def generalItoRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) : ℝ :=
  f s₁ x₁ - f s₀ x₀ -
    itoTimeDerivative f s₀ x₀ * (s₁ - s₀) -
    itoSpaceDerivative f s₀ x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s₀ x₀ * (x₁ - x₀) ^ 2

/-- Sum of the exact one-step residuals along the uniform `n`-partition. -/
noncomputable def generalItoRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Joint continuity of the function and its displayed partial derivatives,
together with fixed-time measurability of the process, makes every finite
general Taylor-remainder sum measurable. -/
theorem aestronglyMeasurable_generalItoRemainderApprox
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hdxx : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (generalItoRemainderApprox f X t n) P := by
  unfold generalItoRemainderApprox
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega =>
        generalItoRemainderIncrement f
          (uniformPartitionTime t n i : ℝ)
          (uniformPartitionTime t n (i + 1) : ℝ)
          (X (uniformPartitionTime t n i) omega)
          (X (uniformPartitionTime t n (i + 1)) omega)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    let s₀ : ℝ := uniformPartitionTime t n i
    let s₁ : ℝ := uniformPartitionTime t n (i + 1)
    have hx₀ := hXmeas (uniformPartitionTime t n i)
    have hx₁ := hXmeas (uniformPartitionTime t n (i + 1))
    have hslice (F : ℝ × ℝ → ℝ) (hF : Continuous F) (s : ℝ) :
        Continuous (fun x => F (s, x)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have hv₀ : AEStronglyMeasurable (fun omega => f s₀ (X _ omega)) P :=
      (hslice _ hf s₀).comp_aestronglyMeasurable hx₀
    have hv₁ : AEStronglyMeasurable (fun omega => f s₁ (X _ omega)) P :=
      (hslice _ hf s₁).comp_aestronglyMeasurable hx₁
    have ht₀ : AEStronglyMeasurable
        (fun omega => itoTimeDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdt s₀).comp_aestronglyMeasurable hx₀
    have hx'₀ : AEStronglyMeasurable
        (fun omega => itoSpaceDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdx s₀).comp_aestronglyMeasurable hx₀
    have hxx₀ : AEStronglyMeasurable
        (fun omega => itoSpaceSecondDerivative f s₀ (X _ omega)) P :=
      (hslice _ hdxx s₀).comp_aestronglyMeasurable hx₀
    have hincrement := hx₁.sub hx₀
    unfold generalItoRemainderIncrement
    exact ((((hv₁.sub hv₀).sub
      (ht₀.mul aestronglyMeasurable_const)).sub
      (hx'₀.mul hincrement)).sub
      ((aestronglyMeasurable_const.mul hxx₀).mul (hincrement.pow 2)))
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

/-- Time Taylor residual with the state frozen at the right endpoint of a
single process increment. -/
noncomputable def generalItoFrozenStateTimeRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₁ : ℝ) : ℝ :=
  f s₁ x₁ - f s₀ x₁ -
    itoTimeDerivative f s₀ x₁ * (s₁ - s₀)

/-- State Taylor residual with time frozen at the left endpoint of a single
process increment. -/
noncomputable def generalItoFrozenTimeStateRemainderIncrement
    (f : ℝ → ℝ → ℝ) (s₀ x₀ x₁ : ℝ) : ℝ :=
  f s₀ x₁ - f s₀ x₀ -
    itoSpaceDerivative f s₀ x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * itoSpaceSecondDerivative f s₀ x₀ * (x₁ - x₀) ^ 2

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The frozen-time state component is exactly the ordinary one-variable
second-order Taylor remainder of the corresponding time slice. -/
theorem generalItoFrozenTimeStateRemainderIncrement_eq_itoTaylorRemainder
    (f : ℝ → ℝ → ℝ) (s₀ x₀ x₁ : ℝ) :
    generalItoFrozenTimeStateRemainderIncrement f s₀ x₀ x₁ =
      itoTaylorRemainder (f s₀) x₀ x₁ := by
  unfold generalItoFrozenTimeStateRemainderIncrement itoTaylorRemainder
    itoSpaceDerivative itoSpaceSecondDerivative
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Uniform second-order Taylor bound for all time slices on a compact
time/state rectangle.  Joint continuity of the second space derivative makes
the little-o modulus independent of the chosen time slice. -/
theorem uniform_generalItoFrozenTimeStateRemainder_bound_on_rectangle
    (f : ℝ → ℝ → ℝ)
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (a b c d : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Icc a b, ∀ x₀ ∈ Set.Icc c d, ∀ x₁ ∈ Set.Icc c d,
        |x₁ - x₀| < δ →
        |generalItoFrozenTimeStateRemainderIncrement f s x₀ x₁| ≤
          ε * (x₁ - x₀) ^ 2 := by
  let S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn
      (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hsecond.continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc
    (2 * ε) (mul_pos (by norm_num) hε)
  refine ⟨δ, hδ, ?_⟩
  intro s hs x₀ hx₀ x₁ hx₁ hxx₀
  rw [generalItoFrozenTimeStateRemainderIncrement_eq_itoTaylorRemainder]
  rcases eq_or_ne x₀ x₁ with rfl | hne
  · simp only [itoTaylorRemainder, sub_self, mul_zero, add_zero, pow_succ,
      abs_zero, le_refl]
  let g : ℝ → ℝ := f s
  obtain ⟨y, hy, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne
      ((hslice s).contDiffOn (s := Set.uIcc x₀ x₁))
  have hu : UniqueDiffOn ℝ (Set.uIcc x₀ x₁) := uniqueDiffOn_uIcc hne
  have hx₀u : x₀ ∈ Set.uIcc x₀ x₁ := Set.left_mem_uIcc
  have hfirst : iteratedDerivWithin 1 g (Set.uIcc x₀ x₁) x₀ =
      deriv g x₀ := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
      ((hslice s).contDiffAt.of_le (by norm_num)) hx₀u]
    rw [show iteratedDeriv 1 g = deriv g by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
  have hycd : y ∈ Set.Icc c d := by
    rcases hx₀ with ⟨hcx₀, hx₀d⟩
    rcases hx₁ with ⟨hcx₁, hx₁d⟩
    grind [Set.uIoo, Set.uIcc]
  have hydist : dist (s, y) (s, x₀) < δ := by
    rw [dist_prod_same_left]
    calc
      dist y x₀ = dist x₀ y := dist_comm _ _
      _ ≤ dist x₀ x₁ :=
        Real.dist_left_le_of_mem_uIcc (Set.uIoo_subset_uIcc_self hy)
      _ = |x₁ - x₀| := by rw [Real.dist_eq, abs_sub_comm]
      _ < δ := hxx₀
  have hmod' := hmod (s, y) ⟨hs, hycd⟩ (s, x₀) ⟨hs, hx₀⟩ hydist
  rw [Real.dist_eq] at hmod'
  have hsecondSlice : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
      show iteratedDeriv 1 g = deriv g by
        rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
        simp only [iteratedDeriv_zero]]
  have hTaylor' : g x₁ -
      (g x₀ + deriv g x₀ * (x₁ - x₀)) =
        deriv (deriv g) y * (x₁ - x₀) ^ 2 / 2 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, hfirst] at hTaylor
    rw [hsecondSlice] at hTaylor
    norm_num at hTaylor ⊢
    simpa [smul_eq_mul, mul_comm] using hTaylor
  dsimp only [g] at hTaylor' hsecondSlice
  unfold itoTaylorRemainder
  rw [show f s x₁ -
      (f s x₀ + deriv (f s) x₀ * (x₁ - x₀) +
        (1 / 2 : ℝ) * deriv (deriv (f s)) x₀ * (x₁ - x₀) ^ 2) =
      (f s x₁ - (f s x₀ + deriv (f s) x₀ * (x₁ - x₀))) -
        (1 / 2 : ℝ) * deriv (deriv (f s)) x₀ * (x₁ - x₀) ^ 2 by
      ring, hTaylor']
  rw [show deriv (deriv (f s)) y * (x₁ - x₀) ^ 2 / 2 -
      (1 / 2 : ℝ) * deriv (deriv (f s)) x₀ * (x₁ - x₀) ^ 2 =
      (1 / 2 : ℝ) *
        (deriv (deriv (f s)) y - deriv (deriv (f s)) x₀) *
          (x₁ - x₀) ^ 2 by ring]
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (sq_nonneg (x₁ - x₀)),
    itoSpaceSecondDerivative] at hmod' ⊢
  calc
    (1 / 2 : ℝ) *
        |deriv (deriv (f s)) y - deriv (deriv (f s)) x₀| *
          (x₁ - x₀) ^ 2 ≤
      (1 / 2 : ℝ) * (2 * ε) * (x₁ - x₀) ^ 2 := by
        gcongr
    _ = ε * (x₁ - x₀) ^ 2 := by ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Joint continuity of the second space derivative makes the frozen-time
state Taylor little-o estimate uniform along every continuous compact
sample path. -/
theorem generalItoFrozenTimeStateRemainder_eventually_bound_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ε * (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2 := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hpath
  have hRnonneg : 0 ≤ R := by
    have hzero : (0 : ℝ≥0) ∈ Set.Icc 0 t := ⟨le_rfl, bot_le⟩
    exact (norm_nonneg (X 0 omega)).trans (hR 0 hzero)
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ :=
    uniform_generalItoFrozenTimeStateRemainder_bound_on_rectangle
      f hslice hsecond 0 (t : ℝ) (-R) R ε hε
  filter_upwards [continuousOn_uniformPartition_increments_tendsto
    (fun s => X s omega) t hpath δ hδ] with n hn
  intro i hi
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hile : i ≤ n + 1 := (Nat.le_add_right i 1).trans hipos
  have hti := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hti1 := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  have hs : (uniformPartitionTime t (n + 1) i : ℝ) ∈
      Set.Icc (0 : ℝ) (t : ℝ) := by
    exact ⟨by exact_mod_cast hti.1, by exact_mod_cast hti.2⟩
  have hx₀ : X (uniformPartitionTime t (n + 1) i) omega ∈ Set.Icc (-R) R := by
    exact abs_le.mp (by
      simpa only [Real.norm_eq_abs] using
        hR (uniformPartitionTime t (n + 1) i) hti)
  have hx₁ : X (uniformPartitionTime t (n + 1) (i + 1)) omega ∈
      Set.Icc (-R) R := by
    exact abs_le.mp (by
      simpa only [Real.norm_eq_abs] using
        hR (uniformPartitionTime t (n + 1) (i + 1)) hti1)
  exact hbound _ hs _ hx₀ _ hx₁ (hn i hi)

/-- Mixed error caused by evaluating the time derivative at the left state
rather than the right state of a single process increment. -/
noncomputable def generalItoTimeStateCrossIncrement
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) : ℝ :=
  (itoTimeDerivative f s₀ x₁ - itoTimeDerivative f s₀ x₀) *
    (s₁ - s₀)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A frozen-state first-order time residual is controlled by the oscillation
of the time derivative on the corresponding time interval. -/
theorem abs_generalItoFrozenStateTimeRemainderIncrement_le
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₁ K : ℝ)
    (hfdiff : Differentiable ℝ (fun s => f s x₁))
    (hdt : Continuous (fun s => itoTimeDerivative f s x₁))
    (hbound : ∀ s ∈ Set.uIoc s₀ s₁,
      |itoTimeDerivative f s x₁ - itoTimeDerivative f s₀ x₁| ≤ K) :
    |generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁| ≤
      K * |s₁ - s₀| := by
  let F : ℝ → ℝ := fun s => f s x₁
  let D : ℝ → ℝ := fun s => itoTimeDerivative f s x₁
  have hDint : IntervalIntegrable D volume s₀ s₁ :=
    hdt.intervalIntegrable s₀ s₁
  have hconst : IntervalIntegrable (fun _ : ℝ => D s₀) volume s₀ s₁ :=
    intervalIntegrable_const
  have hfund : ∫ s in s₀..s₁, D s = F s₁ - F s₀ := by
    have hraw := intervalIntegral.integral_deriv_eq_sub
      (f := F) (fun s _hs => hfdiff.differentiableAt) (by
        simpa only [F, D, itoTimeDerivative] using hDint)
    simpa only [F, D, itoTimeDerivative] using hraw
  have heq : generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁ =
      ∫ s in s₀..s₁, D s - D s₀ := by
    rw [intervalIntegral.integral_sub hDint hconst, hfund,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    unfold generalItoFrozenStateTimeRemainderIncrement
    dsimp only [F, D]
    ring
  rw [heq]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => D s - D s₀) (C := K)
      (fun s hs => by
        simpa only [D, Real.norm_eq_abs] using hbound s hs))

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Exact factorization of a genuinely two-variable one-step Itô residual.
It separates the two ordinary one-variable Taylor errors from the sole mixed
time/state cross term. -/
theorem generalItoRemainderIncrement_eq_frozenTime_frozenState_cross
    (f : ℝ → ℝ → ℝ) (s₀ s₁ x₀ x₁ : ℝ) :
    generalItoRemainderIncrement f s₀ s₁ x₀ x₁ =
      generalItoFrozenStateTimeRemainderIncrement f s₀ s₁ x₁ +
      generalItoFrozenTimeStateRemainderIncrement f s₀ x₀ x₁ +
      generalItoTimeStateCrossIncrement f s₀ s₁ x₀ x₁ := by
  unfold generalItoRemainderIncrement
    generalItoFrozenStateTimeRemainderIncrement
    generalItoFrozenTimeStateRemainderIncrement
    generalItoTimeStateCrossIncrement
  ring

/-- Accumulated frozen-state time Taylor residual along a uniform
partition. -/
noncomputable def generalItoFrozenStateTimeRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoFrozenStateTimeRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n (i + 1)) omega)

/-- Accumulated frozen-time state Taylor residual along a uniform
partition. -/
noncomputable def generalItoFrozenTimeStateRemainderApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoFrozenTimeStateRemainderIncrement f
      (uniformPartitionTime t n i : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)

/-- Accumulated mixed time/state cross error along a uniform partition. -/
noncomputable def generalItoTimeStateCrossApprox
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    generalItoTimeStateCrossIncrement f
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The full accumulated residual is exactly the sum of its frozen-state
time, frozen-time state, and mixed cross components. -/
theorem generalItoRemainderApprox_eq_frozenTime_frozenState_cross
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    generalItoRemainderApprox f X t n omega =
      generalItoFrozenStateTimeRemainderApprox f X t n omega +
      generalItoFrozenTimeStateRemainderApprox f X t n omega +
      generalItoTimeStateCrossApprox f X t n omega := by
  unfold generalItoRemainderApprox generalItoFrozenStateTimeRemainderApprox
    generalItoFrozenTimeStateRemainderApprox generalItoTimeStateCrossApprox
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact generalItoRemainderIncrement_eq_frozenTime_frozenState_cross
    f _ _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Convergence of the three factored components closes the full
two-variable remainder pathwise. -/
theorem generalItoRemainderApprox_tendsto_zero_of_components
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (htime : Filter.Tendsto
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0))
    (hstate : Filter.Tendsto
      (fun n => generalItoFrozenTimeStateRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0))
    (hcross : Filter.Tendsto
      (fun n => generalItoTimeStateCrossApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => generalItoRemainderApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) := by
  rw [show (fun n => generalItoRemainderApprox f X t (n + 1) omega) =
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega +
        generalItoFrozenTimeStateRemainderApprox f X t (n + 1) omega +
        generalItoTimeStateCrossApprox f X t (n + 1) omega) by
    funext n
    exact generalItoRemainderApprox_eq_frozenTime_frozenState_cross
      f X t (n + 1) omega]
  simpa only [zero_add] using (htime.add hstate).add hcross

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Convergence in measure of the three factored components closes the full
two-variable remainder in measure. -/
theorem generalItoRemainderApprox_tendstoInMeasure_zero_of_components
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (htime : TendstoInMeasure P
      (fun n => generalItoFrozenStateTimeRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0))
    (hstate : TendstoInMeasure P
      (fun n => generalItoFrozenTimeStateRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0))
    (hcross : TendstoInMeasure P
      (fun n => generalItoTimeStateCrossApprox f X t (n + 1))
      Filter.atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  rw [show (fun n => generalItoRemainderApprox f X t (n + 1)) =
      (fun n omega => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega +
        generalItoFrozenTimeStateRemainderApprox f X t (n + 1) omega +
        generalItoTimeStateCrossApprox f X t (n + 1) omega) by
    funext n omega
    exact generalItoRemainderApprox_eq_frozenTime_frozenState_cross
      f X t (n + 1) omega]
  simpa only [zero_add] using
    (htime.add_real_noMeas hstate).add_real_noMeas hcross

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Abstract closure of the frozen-time state Taylor component: a termwise
little-o bound times an eventually bounded quadratic-variation sum has
vanishing accumulated remainder. -/
theorem generalItoFrozenTimeStateRemainderApprox_tendsto_zero_of_bound
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (C : ℝ) (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (n + 1) omega ≤ C)
    (hremainder : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ε * (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2) :
    Filter.Tendsto
      (fun n => generalItoFrozenTimeStateRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨nq, hnq⟩ := Filter.eventually_atTop.1 hquadratic
  obtain ⟨nr, hnr⟩ := Filter.eventually_atTop.1 (hremainder δ hδ)
  refine ⟨max nq nr, fun n hn => ?_⟩
  have hq := hnq n ((le_max_left _ _).trans hn)
  have hr := hnr n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero]
  unfold generalItoFrozenTimeStateRemainderApprox
  calc
    |∑ i ∈ Finset.range (n + 1),
        generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (n + 1),
          |generalItoFrozenTimeStateRemainderIncrement f
            (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
        (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2 :=
      Finset.sum_le_sum fun i hi => hr i hi
    _ = δ * quadraticVariationApprox X t (n + 1) omega := by
      rw [← Finset.mul_sum]
      rfl
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hq hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [hC.ne']
    _ < ε := by linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Subsequence form of the frozen-time state closure, used when quadratic
variation in probability supplies almost-sure convergence only after taking
a subsubsequence. -/
theorem generalItoFrozenTimeStateRemainderApprox_subseq_tendsto_zero_of_bound
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (k : ℕ → ℕ) (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (C : ℝ) (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (k n + 1) omega ≤ C)
    (hremainder : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ε * (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2) :
    Filter.Tendsto
      (fun n => generalItoFrozenTimeStateRemainderApprox
        f X t (k n + 1) omega) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨nq, hnq⟩ := Filter.eventually_atTop.1 hquadratic
  obtain ⟨nr, hnr⟩ :=
    Filter.eventually_atTop.1 (hk.eventually (hremainder δ hδ))
  refine ⟨max nq nr, fun n hn => ?_⟩
  have hq := hnq n ((le_max_left _ _).trans hn)
  have hr := hnr n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq, sub_zero]
  unfold generalItoFrozenTimeStateRemainderApprox
  calc
    |∑ i ∈ Finset.range (k n + 1),
        generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (k n + 1) i : ℝ)
          (X (uniformPartitionTime t (k n + 1) i) omega)
          (X (uniformPartitionTime t (k n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (k n + 1),
          |generalItoFrozenTimeStateRemainderIncrement f
            (uniformPartitionTime t (k n + 1) i : ℝ)
            (X (uniformPartitionTime t (k n + 1) i) omega)
            (X (uniformPartitionTime t (k n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k n + 1), δ *
        (X (uniformPartitionTime t (k n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (k n + 1) i) omega) ^ 2 :=
      Finset.sum_le_sum fun i hi => hr i hi
    _ = δ * quadraticVariationApprox X t (k n + 1) omega := by
      rw [← Finset.mul_sum]
      rfl
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hq hδ.le
    _ = ε / 2 := by
      dsimp only [δ]
      field_simp [hC.ne']
    _ < ε := by linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Uniformly small oscillation of the time derivative within every fine
partition interval forces the accumulated frozen-state time Taylor error to
vanish. -/
theorem generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_derivative_oscillation
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hfdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1), ∀ s ∈ Set.uIoc
        (uniformPartitionTime t (n + 1) i : ℝ)
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ),
        |itoTimeDerivative f s
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤ δ)
    (hdt : ∀ x, Continuous (fun s => itoTimeDerivative f s x)) :
    Filter.Tendsto
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / ((t : ℝ) + 1)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε ht1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsmall δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  unfold generalItoFrozenStateTimeRemainderApprox
  calc
    |∑ i ∈ Finset.range (n + 1),
        generalItoFrozenStateTimeRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (n + 1),
          |generalItoFrozenStateTimeRemainderIncrement f
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
        ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime t (n + 1) i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        norm_cast
        unfold uniformPartitionTime
        gcongr
        omega
      simpa only [abs_of_nonneg (sub_nonneg.mpr htime)] using
        (abs_generalItoFrozenStateTimeRemainderIncrement_le
          f (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) δ
            (hfdiff _) (hdt _) (hN n hn i hi))
    _ = δ * (t : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ i ∈ Finset.range (n + 1),
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) =
            (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) 0 : ℝ) := by
          simpa using (Finset.sum_range_sub
            (fun i => (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1))
        _ = (t : ℝ) := by
          simp only [uniformPartitionTime, Nat.cast_add, Nat.cast_one,
            NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
          field_simp
          norm_num
    _ < ε := by
      calc
        δ * (t : ℝ) < δ * ((t : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (lt_add_one _) hδ
        _ = ε := by
          dsimp only [δ]
          exact div_mul_cancel₀ ε ht1.ne'

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- On a continuous compact path, joint continuity of the time derivative
makes its oscillation uniformly small within each sufficiently fine time
interval, even though the frozen state varies from interval to interval. -/
theorem generalItoTimeDerivative_time_oscillation_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1), ∀ s ∈ Set.uIoc
        (uniformPartitionTime t (n + 1) i : ℝ)
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ),
        |itoTimeDerivative f s
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤ δ := by
  let R : Set ℝ := (fun s : ℝ≥0 => X s omega) '' Set.Icc 0 t
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ R
  have hRcompact : IsCompact R := by
    simpa only [R] using isCompact_Icc.image_of_continuousOn hpath
  have hScompact : IsCompact S := isCompact_Icc.prod hRcompact
  have huc : UniformContinuousOn
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hdt.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  filter_upwards [continuousOn_uniformPartition_increments_tendsto
    (fun s : ℝ≥0 => (s : ℝ)) t NNReal.continuous_coe.continuousOn η hη]
    with n hn
  intro i hi s hs
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hile : i ≤ n + 1 := (Nat.le_add_right i 1).trans hipos
  have hti := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hti1 := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
      (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
    norm_cast
    unfold uniformPartitionTime
    gcongr
    omega
  rw [Set.uIoc_of_le htime] at hs
  let p : ℝ × ℝ :=
    (s, X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  let q : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  have hsIcc : s ∈ Set.Icc (0 : ℝ) (t : ℝ) := by
    have hzero : (0 : ℝ) ≤ (uniformPartitionTime t (n + 1) i : ℝ) := by
      exact_mod_cast hti.1
    have htop : (uniformPartitionTime t (n + 1) (i + 1) : ℝ) ≤
        (t : ℝ) := by
      exact_mod_cast hti1.2
    constructor
    · exact hzero.trans hs.1.le
    · exact hs.2.trans htop
  have hxR : X (uniformPartitionTime t (n + 1) (i + 1)) omega ∈ R :=
    ⟨uniformPartitionTime t (n + 1) (i + 1), hti1, rfl⟩
  have hp : p ∈ S := ⟨hsIcc, hxR⟩
  have hq : q ∈ S := by
    refine ⟨⟨?_, ?_⟩, hxR⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
  have hpq : dist p q < η := by
    dsimp only [p, q]
    rw [dist_prod_same_right]
    have hle : dist s (uniformPartitionTime t (n + 1) i : ℝ) ≤
        dist (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (uniformPartitionTime t (n + 1) i : ℝ) := by
      rw [dist_comm s, dist_comm
        (uniformPartitionTime t (n + 1) (i + 1) : ℝ)]
      have hsu : s ∈ Set.uIcc
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        rw [Set.uIcc_of_le htime]
        exact Set.Ioc_subset_Icc_self hs
      exact Real.dist_left_le_of_mem_uIcc
        hsu
    exact hle.trans_lt (by simpa only [Real.dist_eq] using hn i hi)
  have hout := hmod p hp q hq hpq
  dsimp only [p, q] at hout
  simpa only [Real.dist_eq] using hout.le

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The frozen-state time component of the general Itô remainder vanishes
pathwise for a jointly continuous time derivative and time-differentiable
test function along every continuous sample path. -/
theorem generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hfdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => generalItoFrozenStateTimeRemainderApprox
        f X t (n + 1) omega) Filter.atTop (nhds 0) := by
  apply generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_derivative_oscillation
    f X t omega hfdiff
      (generalItoTimeDerivative_time_oscillation_eventually_small
        f X t omega hdt hpath)
  intro x
  exact hdt.comp (continuous_id.prodMk continuous_const)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- If the time derivative changes uniformly little across every state
increment of a fine partition, then the accumulated mixed time/state cross
term vanishes.  Continuity of the derivative along a continuous compact path
is intended to discharge the explicit `hsmall` premise. -/
theorem generalItoTimeStateCrossApprox_tendsto_zero_of_derivative_increments
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)| ≤ δ) :
    Filter.Tendsto
      (fun n => generalItoTimeStateCrossApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / ((t : ℝ) + 1)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε ht1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hsmall δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  unfold generalItoTimeStateCrossApprox
  calc
    |∑ i ∈ Finset.range (n + 1),
        generalItoTimeStateCrossIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ∑ i ∈ Finset.range (n + 1),
          |generalItoTimeStateCrossIncrement f
            (uniformPartitionTime t (n + 1) i : ℝ)
            (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ *
        ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime t (n + 1) i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have htime : (uniformPartitionTime t (n + 1) i : ℝ) ≤
          (uniformPartitionTime t (n + 1) (i + 1) : ℝ) := by
        norm_cast
        unfold uniformPartitionTime
        gcongr
        omega
      unfold generalItoTimeStateCrossIncrement
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr htime)]
      exact mul_le_mul_of_nonneg_right (hN n hn i hi) (sub_nonneg.mpr htime)
    _ = δ * (t : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      have hn0 : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
      calc
        (∑ i ∈ Finset.range (n + 1),
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) =
            (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) 0 : ℝ) :=
          by
            simpa using (Finset.sum_range_sub
              (fun i => (uniformPartitionTime t (n + 1) i : ℝ)) (n + 1))
        _ = (t : ℝ) := by
          simp only [uniformPartitionTime, Nat.cast_add, Nat.cast_one,
            NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
          field_simp
          norm_num
    _ < ε := by
      calc
        δ * (t : ℝ) < δ * ((t : ℝ) + 1) := by
          exact mul_lt_mul_of_pos_left (lt_add_one _) hδ
        _ = ε := by
          dsimp only [δ]
          exact div_mul_cancel₀ ε ht1.ne'

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Joint continuity of the time derivative and continuity of one sample path
make the derivative uniformly insensitive to adjacent state increments on a
fixed compact horizon. -/
theorem generalItoTimeDerivative_state_increments_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          itoTimeDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)| ≤ δ := by
  let R : Set ℝ := (fun s : ℝ≥0 => X s omega) '' Set.Icc 0 t
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ R
  have hRcompact : IsCompact R := by
    simpa only [R] using
      isCompact_Icc.image_of_continuousOn hpath
  have hScompact : IsCompact S := isCompact_Icc.prod hRcompact
  have huc : UniformContinuousOn
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hdt.continuousOn
  intro δ hδ
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  filter_upwards [continuousOn_uniformPartition_increments_tendsto
    (fun s => X s omega) t hpath η hη] with n hn
  intro i hi
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hipos : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hile : i ≤ n + 1 := (Nat.le_add_right i 1).trans hipos
  have hti := uniformPartitionTime_mem_Icc_of_le t hnpos hile
  have hti1 := uniformPartitionTime_mem_Icc_of_le t hnpos hipos
  let p : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) (i + 1)) omega)
  let q : ℝ × ℝ :=
    ((uniformPartitionTime t (n + 1) i : ℝ),
      X (uniformPartitionTime t (n + 1) i) omega)
  have hp : p ∈ S := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
    · exact ⟨uniformPartitionTime t (n + 1) (i + 1), hti1, rfl⟩
  have hq : q ∈ S := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast hti.1
    · exact_mod_cast hti.2
    · exact ⟨uniformPartitionTime t (n + 1) i, hti, rfl⟩
  have hpq : dist p q < η := by
    dsimp only [p, q]
    rw [dist_prod_same_left, Real.dist_eq]
    exact hn i hi
  have hout := hmod p hp q hq hpq
  dsimp only [p, q] at hout
  simpa only [Real.dist_eq] using hout.le

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The mixed time/state component of the general Itô remainder vanishes
pathwise along every continuous path when the time derivative is jointly
continuous. -/
theorem generalItoTimeStateCrossApprox_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => generalItoTimeStateCrossApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) :=
  generalItoTimeStateCrossApprox_tendsto_zero_of_derivative_increments
    f X t omega
      (generalItoTimeDerivative_state_increments_eventually_small
        f X t omega hdt hpath)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- After the exact three-way factorization, joint continuity completely
discharges the time and mixed pieces.  Thus a termwise little-o estimate for
the frozen-time state Taylor term, together with bounded quadratic sums, is
the sole remaining pathwise remainder obligation. -/
theorem generalItoRemainderApprox_tendsto_zero_of_continuous_path_of_state_bound
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hfdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t))
    (C : ℝ) (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (n + 1) omega ≤ C)
    (hstate : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      ∀ i ∈ Finset.range (n + 1),
        |generalItoFrozenTimeStateRemainderIncrement f
          (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)
          (X (uniformPartitionTime t (n + 1) (i + 1)) omega)| ≤
        ε * (X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega) ^ 2) :
    Filter.Tendsto
      (fun n => generalItoRemainderApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) := by
  exact generalItoRemainderApprox_tendsto_zero_of_components f X t omega
    (generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_continuous_path
      f X t omega hfdiff hdt hpath)
    (generalItoFrozenTimeStateRemainderApprox_tendsto_zero_of_bound
      f X t omega C hC hquadratic hstate)
    (generalItoTimeStateCrossApprox_tendsto_zero_of_continuous_path
      f X t omega hdt hpath)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Full genuinely two-variable Taylor-remainder convergence along a
continuous path with eventually bounded quadratic sums. -/
theorem generalItoRemainderApprox_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t))
    (C : ℝ) (hC : 0 < C)
    (hquadratic : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (n + 1) omega ≤ C) :
    Filter.Tendsto
      (fun n => generalItoRemainderApprox f X t (n + 1) omega)
      Filter.atTop (nhds 0) :=
  generalItoRemainderApprox_tendsto_zero_of_continuous_path_of_state_bound
    f X t omega htdiff hdt hpath C hC hquadratic
      (generalItoFrozenTimeStateRemainder_eventually_bound_of_continuous_path
        f X t omega hslice hsecond hpath)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Subsequence-stable form of the full pathwise remainder theorem. -/
theorem generalItoRemainderApprox_subseq_tendsto_zero_of_continuous_path
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (k : ℕ → ℕ) (hk : Filter.Tendsto k Filter.atTop Filter.atTop)
    (q : ℝ)
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t))
    (hquadratic : Filter.Tendsto
      (fun n => quadraticVariationApprox X t (k n + 1) omega)
      Filter.atTop (nhds q)) :
    Filter.Tendsto
      (fun n => generalItoRemainderApprox f X t (k n + 1) omega)
      Filter.atTop (nhds 0) := by
  let C : ℝ := |q| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hqbound : ∀ᶠ n in Filter.atTop,
      quadraticVariationApprox X t (k n + 1) omega ≤ C := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hquadratic 1 zero_lt_one
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    dsimp only [C]
    have hupper := (abs_lt.mp hd).2
    linarith [le_abs_self q]
  have htime :=
    (generalItoFrozenStateTimeRemainderApprox_tendsto_zero_of_continuous_path
      f X t omega htdiff hdt hpath).comp hk
  have hcross :=
    (generalItoTimeStateCrossApprox_tendsto_zero_of_continuous_path
      f X t omega hdt hpath).comp hk
  have hstate :=
    generalItoFrozenTimeStateRemainderApprox_subseq_tendsto_zero_of_bound
      f X t omega k hk C hC hqbound
        (generalItoFrozenTimeStateRemainder_eventually_bound_of_continuous_path
          f X t omega hslice hsecond hpath)
  have hsum := (htime.add hstate).add hcross
  convert hsum using 1
  · funext n
    simpa only [Function.comp_apply] using
      (generalItoRemainderApprox_eq_frozenTime_frozenState_cross
        f X t (k n + 1) omega)
  · simp only [zero_add]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a measurable process with almost-everywhere continuous paths and
quadratic variation in probability, the full genuinely two-variable Taylor
remainder vanishes in probability. -/
theorem generalItoRemainderApprox_tendstoInMeasure_of_continuous_qv
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (q : W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hcontinuous : ∀ᵐ omega ∂P,
      ContinuousOn (fun s => X s omega) (Set.Icc 0 t))
    (hquadratic : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop q) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (generalItoRemainderApprox f X t (n + 1)) P := fun n =>
    aestronglyMeasurable_generalItoRemainderApprox
      f hf hdt hdx hsecond X hXmeas t (n + 1)
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ms, hms, hquadratic'⟩ :=
    (hquadratic.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hcontinuous, hquadratic'] with omega hpath hq
  apply generalItoRemainderApprox_subseq_tendsto_zero_of_continuous_path
    f X t omega (ns ∘ ms)
      (hns.tendsto_atTop.comp hms.tendsto_atTop) (q omega)
      htdiff hslice hdt hsecond hpath
  simpa only [Function.comp_apply] using hq

/-- A process `Y` is a continuous modification of `X` when the two agree
almost everywhere at each fixed time and `Y` has almost-everywhere continuous
sample paths.  The fixed-time quantifier is deliberately outside the
almost-everywhere quantifier, matching the standard notion of modification. -/
structure IsContinuousProcessModification
    (X Y : ℝ≥0 → W → ℝ) (P : Measure W) : Prop where
  fixedTime_ae_eq : ∀ s, X s =ᵐ[P] Y s
  continuous_paths : ∀ᵐ omega ∂P, Continuous (fun s => Y s omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Continuous scalar functions preserve continuous modifications. -/
theorem IsContinuousProcessModification.continuous_comp
    {X Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ) (hf : Continuous f) :
    IsContinuousProcessModification
      (fun t omega ↦ f (X t omega)) (fun t omega ↦ f (Y t omega)) P where
  fixedTime_ae_eq t := by
    filter_upwards [hmod.fixedTime_ae_eq t] with omega homega
    rw [homega]
  continuous_paths := by
    filter_upwards [hmod.continuous_paths] with omega homega
    exact hf.comp homega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Two continuous modifications of the same process are indistinguishable:
outside one null set they agree at every time, not merely at each fixed time.
The proof intersects the fixed-time equalities along a countable dense set
and extends them using continuity. -/
theorem IsContinuousProcessModification.indistinguishable
    {X Y Z : ℝ≥0 → W → ℝ}
    (hY : IsContinuousProcessModification X Y P)
    (hZ : IsContinuousProcessModification X Z P) :
    ∀ᵐ omega ∂P, ∀ s : ℝ≥0, Y s omega = Z s omega := by
  have hdense : ∀ᵐ omega ∂P, ∀ n : ℕ,
      Y (TopologicalSpace.denseSeq ℝ≥0 n) omega =
        Z (TopologicalSpace.denseSeq ℝ≥0 n) omega := by
    apply ae_all_iff.mpr
    intro n
    exact (hY.fixedTime_ae_eq
      (TopologicalSpace.denseSeq ℝ≥0 n)).symm.trans
        (hZ.fixedTime_ae_eq (TopologicalSpace.denseSeq ℝ≥0 n))
  filter_upwards [hY.continuous_paths, hZ.continuous_paths, hdense]
    with omega hYcontinuous hZcontinuous heq
  have hfun : (fun s => Y s omega) = (fun s => Z s omega) := by
    apply Continuous.ext_on (TopologicalSpace.denseRange_denseSeq ℝ≥0)
      hYcontinuous hZcontinuous
    rw [Set.eqOn_range]
    funext n
    exact heq n
  intro s
  exact congrFun hfun s

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A fixed-time modification agrees simultaneously at every point of all
uniform partitions of a fixed horizon.  Countability of the two natural-number
indices is the key distinction from an uncountable simultaneous-time claim. -/
theorem fixedTime_ae_eq_uniformPartitions
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ n i : ℕ,
      X (uniformPartitionTime t (n + 1) i) omega =
        Y (uniformPartitionTime t (n + 1) i) omega := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro i
  exact hXY (uniformPartitionTime t (n + 1) i)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Along the countable family of uniform partitions, the original
representative of a process with a continuous modification inherits uniformly
vanishing mesh increments almost everywhere. -/
theorem IsContinuousProcessModification.uniformPartition_increments_tendsto
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in Filter.atTop, ∀ i ∈ Finset.range (n + 1),
        |X (uniformPartitionTime t (n + 1) (i + 1)) omega -
          X (uniformPartitionTime t (n + 1) i) omega| < δ := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid] with omega hcontinuous hagree
  intro δ hδ
  filter_upwards [continuous_uniformPartition_increments_tendsto
    (fun s => Y s omega) hcontinuous t δ hδ] with n hn
  intro i hi
  rw [hagree n (i + 1), hagree n i]
  exact hn i hi

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For a process admitting a continuous modification, every deterministic
stopping boundary contributes vanishing quadratic mass in probability.  This
is the analytic boundary-error input for replacing stopped cumulative sums by
ordinary prefix sums in the weighted-bracket argument. -/
theorem IsContinuousProcessModification.quadraticVariationCrossingStopApprox_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t a : ℝ≥0) (ha : a ∈ Set.Icc 0 t) :
    TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X t (n + 1) a)
      Filter.atTop (fun _ => 0) := by
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hXmeas s).congr (hmod.fixedTime_ae_eq s)
  have hY : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox Y t (n + 1) a)
      Filter.atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_quadraticVariationCrossingStopApprox
        hYmeas t (n + 1) a
    · filter_upwards [hmod.continuous_paths] with omega hcontinuous
      exact quadraticVariationCrossingStopApprox_tendsto_zero_of_continuousOn
        Y t a omega ha hcontinuous.continuousOn
  exact hY.congr_left fun n =>
    (quadraticVariationCrossingStopApprox_ae_eq_of_fixedTime_ae_eq
      hmod.fixedTime_ae_eq t (n + 1) a).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Once the stopped quadratic sums have a limit, continuity removes their
single partial boundary cell and gives the same limit for the completed cells
strictly before the stopping time. -/
theorem IsContinuousProcessModification.quadraticVariationBeforeStopApprox_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t a : ℝ≥0) (ha : a ∈ Set.Icc 0 t) (Q : W → ℝ)
    (hstop : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s => X (min s a)) t (n + 1))
      Filter.atTop Q) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox X t (n + 1) a)
      Filter.atTop Q := by
  have hcross :=
    hmod.quadraticVariationCrossingStopApprox_tendstoInMeasure
      hXmeas t a ha
  have hsub := hstop.sub_real_noMeas hcross
  have hsource : ∀ n,
      (fun omega =>
        quadraticVariationApprox (fun s => X (min s a)) t (n + 1) omega -
          quadraticVariationCrossingStopApprox X t (n + 1) a omega) =ᵐ[P]
        quadraticVariationBeforeStopApprox X t (n + 1) a := by
    intro n
    filter_upwards with omega
    rw [quadraticVariationApprox_stop_eq_before_add_crossing]
    ring
  simpa only [sub_zero] using hsub.congr_left hsource

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A continuous modification also supplies a sample-dependent compact-range
bound simultaneously on every uniform partition point of a fixed horizon.
This is the pathwise localization datum used to bound derivatives on compact
state ranges. -/
theorem IsContinuousProcessModification.uniformPartition_bounded
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, ∀ n i : ℕ, i ≤ n + 1 →
      |X (uniformPartitionTime t (n + 1) i) omega| ≤ K := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid] with omega hcontinuous hagree
  have hbounded : BddAbove
      ((fun s : ℝ≥0 => |Y s omega|) '' Set.Icc 0 t) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) t)).bddAbove_image
      hcontinuous.abs.continuousOn
  rcases hbounded with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro n i hi
  rw [hagree n i]
  apply hK
  exact ⟨uniformPartitionTime t (n + 1) i,
    uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) hi, rfl⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A continuous modification localizes every continuous second-derivative
weight on the countable family of uniform grids.  The bound may depend on the
sample and horizon, but is simultaneous in the partition size and index. -/
theorem IsContinuousProcessModification.uniformPartition_secondDerivative_bounded
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∃ K : ℝ, 0 ≤ K ∧ ∀ n i : ℕ, i ≤ n + 1 →
      |itoSpaceSecondDerivative f (uniformPartitionTime t (n + 1) i : ℝ)
        (X (uniformPartitionTime t (n + 1) i) omega)| ≤ K := by
  filter_upwards [hmod.uniformPartition_bounded t] with omega homega
  obtain ⟨R, hR⟩ := homega
  have hRnonneg : 0 ≤ R := by
    exact (abs_nonneg (X (uniformPartitionTime t 1 0) omega)).trans
      (hR 0 0 (by omega))
  let S : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.Icc (-R) R
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hbounded : BddAbove
      ((fun p : ℝ × ℝ => |itoSpaceSecondDerivative f p.1 p.2|) '' S) :=
    hcompact.bddAbove_image hsecond.abs.continuousOn
  obtain ⟨K, hK⟩ := hbounded
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n i hi
  apply (hK ?_).trans (le_max_left _ _)
  refine ⟨((uniformPartitionTime t (n + 1) i : ℝ),
    X (uniformPartitionTime t (n + 1) i) omega), ?_, rfl⟩
  have htime := uniformPartitionTime_mem_Icc_of_le
    t (Nat.zero_lt_succ n) hi
  have hstate := abs_le.mp (hR n i hi)
  exact ⟨⟨by exact_mod_cast htime.1, by exact_mod_cast htime.2⟩,
    hstate⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time modifications give the same time partition term almost
everywhere for every fixed finite partition. -/
theorem generalItoTimeApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoTimeApprox f X t n =ᵐ[P]
      generalItoTimeApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
        Y (uniformPartitionTime t n i) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      hXY (uniformPartitionTime t n i)
  filter_upwards [hall] with omega homega
  unfold generalItoTimeApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [homega i hi]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time modifications give the same space-increment partition term
almost everywhere for every fixed finite partition. -/
theorem generalItoSpaceApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoSpaceApprox f X t n =ᵐ[P]
      generalItoSpaceApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold generalItoSpaceApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time modifications give the same quadratic partition term almost
everywhere for every fixed finite partition. -/
theorem generalItoQuadraticApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoQuadraticApprox f X t n =ᵐ[P]
      generalItoQuadraticApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold generalItoQuadraticApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Fixed-time modifications give the same explicit Taylor residual term
almost everywhere for every fixed finite partition. -/
theorem generalItoRemainderApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    generalItoRemainderApprox f X t n =ᵐ[P]
      generalItoRemainderApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold generalItoRemainderApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- All four convergence-in-probability inputs of the general Itô reduction
transport from a fixed-time modification `Y` back to the original process
`X`. -/
theorem generalIto_partition_limits_congr_process
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f Y t (n + 1)) Filter.atTop T)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f Y t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f Y t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f Y t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    TendstoInMeasure P
        (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T ∧
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      TendstoInMeasure P
        (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q ∧
      TendstoInMeasure P
        (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
          (fun _ => 0) := by
  exact ⟨htime.congr_left (fun n =>
      (generalItoTimeApprox_ae_eq_of_fixedTime_ae_eq
        hXY f t (n + 1)).symm),
    hspace.congr_left (fun n =>
      (generalItoSpaceApprox_ae_eq_of_fixedTime_ae_eq
        hXY f t (n + 1)).symm),
    hquadratic.congr_left (fun n =>
      (generalItoQuadraticApprox_ae_eq_of_fixedTime_ae_eq
        hXY f t (n + 1)).symm),
    hremainder.congr_left (fun n =>
      (generalItoRemainderApprox_ae_eq_of_fixedTime_ae_eq
        hXY f t (n + 1)).symm)⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A continuous modification can be used transparently to prove all four
partition limits for the original representative. -/
theorem IsContinuousProcessModification.partition_limits
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f Y t (n + 1)) Filter.atTop T)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f Y t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f Y t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f Y t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    TendstoInMeasure P
        (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T ∧
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      TendstoInMeasure P
        (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q ∧
      TendstoInMeasure P
        (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
          (fun _ => 0) :=
  generalIto_partition_limits_congr_process hmod.fixedTime_ae_eq
    f t T I Q htime hspace hquadratic hremainder

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Exact four-term decomposition of a time-dependent function increment
along the uniform partition.  No differentiability or probability hypothesis
is needed: the remainder was defined to make this identity exact. -/
theorem generalIto_uniformPartition_decomposition
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    f t (X t omega) - f 0 (X 0 omega) =
      generalItoTimeApprox f X t (n + 1) omega +
      generalItoSpaceApprox f X t (n + 1) omega +
      generalItoQuadraticApprox f X t (n + 1) omega +
      generalItoRemainderApprox f X t (n + 1) omega := by
  have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  calc
    _ = f (uniformPartitionTime t (n + 1) (n + 1) : ℝ)
          (X (uniformPartitionTime t (n + 1) (n + 1)) omega) -
        f (uniformPartitionTime t (n + 1) 0 : ℝ)
          (X (uniformPartitionTime t (n + 1) 0) omega) := by
      simp only [htop, hzero, NNReal.coe_zero]
    _ = ∑ i ∈ Finset.range (n + 1),
        (f (uniformPartitionTime t (n + 1) (i + 1) : ℝ)
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          f (uniformPartitionTime t (n + 1) i : ℝ)
            (X (uniformPartitionTime t (n + 1) i) omega)) := by
      exact (Finset.sum_range_sub
        (fun i => f (uniformPartitionTime t (n + 1) i : ℝ)
          (X (uniformPartitionTime t (n + 1) i) omega)) (n + 1)).symm
    _ = _ := by
      unfold generalItoTimeApprox generalItoSpaceApprox
        generalItoQuadraticApprox generalItoRemainderApprox
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      unfold generalItoRemainderIncrement
      ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The general Itô formula reduced to convergence in probability of its
partition terms.  This is the analytic interface needed by any future
continuous-modification and localization layer. -/
theorem generalIto_formula_ae_of_partition_limits
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        T omega + I omega + Q omega := by
  have htimeSpace := htime.add_real_noMeas hspace
  have hwithQuadratic := htimeSpace.add_real_noMeas hquadratic
  have htotal := hwithQuadratic.add_real_noMeas hremainder
  have htotal' : TendstoInMeasure P
      (fun n omega =>
        generalItoTimeApprox f X t (n + 1) omega +
          generalItoSpaceApprox f X t (n + 1) omega +
          generalItoQuadraticApprox f X t (n + 1) omega +
          generalItoRemainderApprox f X t (n + 1) omega)
      Filter.atTop (fun omega => T omega + I omega + Q omega) := by
    apply htotal.congr_right
    filter_upwards with omega
    simp only [add_zero]
  have hdecomp : ∀ n : ℕ,
      (fun omega =>
        generalItoTimeApprox f X t (n + 1) omega +
          generalItoSpaceApprox f X t (n + 1) omega +
          generalItoQuadraticApprox f X t (n + 1) omega +
          generalItoRemainderApprox f X t (n + 1) omega) =ᵐ[P]
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) := by
    intro n
    filter_upwards with omega
    exact (generalIto_uniformPartition_decomposition f X t n omega).symm
  have hconstantTarget : TendstoInMeasure P
      (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
      Filter.atTop (fun omega => T omega + I omega + Q omega) :=
    htotal'.congr_left hdecomp
  have hconstantSelf : TendstoInMeasure P
      (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
      Filter.atTop (fun omega => f t (X t omega) - f 0 (X 0 omega)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hendpoint) (by
      filter_upwards with omega
      exact tendsto_const_nhds)
  have hunique := tendstoInMeasure_ae_unique hconstantSelf hconstantTarget
  filter_upwards [hunique] with omega homega
  linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Once the time, quadratic, and remainder sums have their intended limits,
the general Itô identity is equivalent to convergence of the concrete `dX`
left sums.  In particular, the stochastic term cannot be chosen independently
of the partition approximation. -/
theorem generalIto_formula_ae_iff_space_limit
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T I Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ↔
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          T omega + I omega + Q omega := by
  constructor
  · intro hspace
    exact generalIto_formula_ae_of_partition_limits f X t T I Q
      hendpoint htime hspace hquadratic hremainder
  · intro hformula
    have hconstant : TendstoInMeasure P
        (fun _ : ℕ => fun omega => f t (X t omega) - f 0 (X 0 omega))
        Filter.atTop
        (fun omega => f t (X t omega) - f 0 (X 0 omega)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => hendpoint) (by
        filter_upwards with omega
        exact tendsto_const_nhds)
    have hraw := ((hconstant.sub_real_noMeas htime).sub_real_noMeas
      hquadratic).sub_real_noMeas hremainder
    have hspace : TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop
        (fun omega =>
          (f t (X t omega) - f 0 (X 0 omega) - T omega - Q omega) - 0) := by
      apply hraw.congr_left
      intro n
      filter_upwards with omega
      have hdecomp :=
        generalIto_uniformPartition_decomposition f X t n omega
      linarith
    apply hspace.congr_right
    filter_upwards [hformula] with omega homega
    linarith

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Once the other three partition terms converge, the exact decomposition
itself constructs the `dX`-sum limit.  This is useful when the theorem only
needs the stochastic first-order term existentially: its canonical value is
the endpoint increment minus the time and quadratic limits. -/
theorem generalIto_exists_space_limit_and_formula
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (T Q : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop T)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop Q)
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          T omega + I omega + Q omega := by
  let I : W → ℝ := fun omega =>
    f t (X t omega) - f 0 (X 0 omega) - T omega - Q omega
  have hformula : ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        T omega + I omega + Q omega := by
    filter_upwards with omega
    simp only [I]
    ring
  exact ⟨I, (generalIto_formula_ae_iff_space_limit
    f X t T I Q hendpoint htime hquadratic hremainder).2 hformula,
      hformula⟩

/-- The pathwise time integral appearing in the general Itô formula. -/
noncomputable def generalItoTimeIntegral
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoTimeDerivative f s (X s.toNNReal omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Along a continuous sample path, a jointly continuous time derivative has
the expected uniform-partition Riemann-sum limit. -/
theorem generalItoTimeApprox_tendsto_of_continuous_path
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hcontinuous : Continuous (fun s => X s omega)) :
    Filter.Tendsto
      (fun n => generalItoTimeApprox f X t (n + 1) omega)
      Filter.atTop (nhds (generalItoTimeIntegral f X t omega)) := by
  have hstate : Continuous (fun s : ℝ => X s.toNNReal omega) :=
    hcontinuous.comp continuous_real_toNNReal
  have hg : Continuous
      (fun s : ℝ => itoTimeDerivative f s (X s.toNNReal omega)) :=
    hdt.comp (continuous_id.prodMk hstate)
  have hRiemann := tendsto_uniformPartition_leftRiemann
    (fun s : ℝ => itoTimeDerivative f s (X s.toNNReal omega)) hg t
  simpa only [generalItoTimeApprox, generalItoTimeIntegral,
    Real.toNNReal_coe] using hRiemann

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- If fixed-time process values are measurable and paths are almost
everywhere continuous, the generic time term converges in probability for
every jointly continuous time derivative. -/
theorem generalItoTimeApprox_tendstoInMeasure_of_continuous_paths
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun s => X s omega)) :
    TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1))
      Filter.atTop (generalItoTimeIntegral f X t) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (generalItoTimeApprox f X t (n + 1)) P := by
    intro n
    unfold generalItoTimeApprox
    have hs := Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
      (fun i _hi => by
        have hp : AEStronglyMeasurable
            (fun omega =>
              ((uniformPartitionTime t (n + 1) i : ℝ),
                X (uniformPartitionTime t (n + 1) i) omega)) P :=
          aestronglyMeasurable_const.prodMk
            (hXmeas (uniformPartitionTime t (n + 1) i))
        have hincrement : AEStronglyMeasurable
            (fun _ : W =>
              (uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime t (n + 1) i : ℝ)) P :=
          aestronglyMeasurable_const
        exact (hdt.comp_aestronglyMeasurable hp).mul hincrement)
    apply hs.congr
    filter_upwards with omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  apply tendstoInMeasure_of_tendsto_ae hmeas
  filter_upwards [hcontinuous] with omega hpath
  exact generalItoTimeApprox_tendsto_of_continuous_path
    f hdt X t omega hpath

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The time-term limit may be proved on a continuous modification and then
transported to the original fixed-time representative.  The limiting path
integral is naturally evaluated on that continuous modification. -/
theorem IsContinuousProcessModification.timeApprox_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (t : ℝ≥0) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P) :
    TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1))
      Filter.atTop (generalItoTimeIntegral f Y t) := by
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hXmeas s).congr (hmod.fixedTime_ae_eq s)
  have hY := generalItoTimeApprox_tendstoInMeasure_of_continuous_paths
    f hdt Y t hYmeas hmod.continuous_paths
  exact hY.congr_left fun n =>
    (generalItoTimeApprox_ae_eq_of_fixedTime_ae_eq
      hmod.fixedTime_ae_eq f t (n + 1)).symm

/-- The pathwise diffusion-weighted second-order integral appearing in the
general Itô formula. -/
noncomputable def generalItoQuadraticIntegral
    (f : ℝ → ℝ → ℝ) (X σ : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    itoSpaceSecondDerivative f s (X s.toNNReal omega) *
      (σ s.toNNReal omega) ^ 2

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Uniformly close second-derivative weights produce uniformly close
candidate bracket integrals along every path on which the relevant
integrands are integrable.  This is the continuous-target counterpart of
`abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox`. -/
theorem abs_generalItoQuadraticIntegral_sub_le_integratedDiffusionVariance
    (f g : ℝ → ℝ → ℝ) (X σ : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) (K : ℝ)
    (hfint : IntegrableOn (fun s : ℝ =>
      itoSpaceSecondDerivative f s (X s.toNNReal omega) *
        (σ s.toNNReal omega) ^ 2) (Set.Icc 0 (t : ℝ)))
    (hgint : IntegrableOn (fun s : ℝ =>
      itoSpaceSecondDerivative g s (X s.toNNReal omega) *
        (σ s.toNNReal omega) ^ 2) (Set.Icc 0 (t : ℝ)))
    (hσint : IntegrableOn (fun s : ℝ => (σ s.toNNReal omega) ^ 2)
      (Set.Icc 0 (t : ℝ)))
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
      |itoSpaceSecondDerivative f s (X s.toNNReal omega) -
        itoSpaceSecondDerivative g s (X s.toNNReal omega)| ≤ K) :
    |generalItoQuadraticIntegral f X σ t omega -
        generalItoQuadraticIntegral g X σ t omega| ≤
      (1 / 2 : ℝ) * K * integratedDiffusionVariance σ t omega := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 (t : ℝ))
  let F : ℝ → ℝ := fun s =>
    itoSpaceSecondDerivative f s (X s.toNNReal omega) *
      (σ s.toNNReal omega) ^ 2
  let G : ℝ → ℝ := fun s =>
    itoSpaceSecondDerivative g s (X s.toNNReal omega) *
      (σ s.toNNReal omega) ^ 2
  let Q : ℝ → ℝ := fun s => (σ s.toNNReal omega) ^ 2
  have hdiffint : Integrable (fun s => F s - G s) ν :=
    hfint.sub hgint
  have hdomint : Integrable (fun s => K * Q s) ν :=
    hσint.const_mul K
  have hpoint : ∀ᵐ s ∂ν, |F s - G s| ≤ K * Q s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    dsimp only [F, G, Q]
    rw [← sub_mul, abs_mul, abs_sq]
    exact mul_le_mul_of_nonneg_right (hbound s hs) (sq_nonneg _)
  unfold generalItoQuadraticIntegral integratedDiffusionVariance
  change |(1 / 2 : ℝ) * ∫ s, F s ∂ν -
      (1 / 2 : ℝ) * ∫ s, G s ∂ν| ≤
    (1 / 2 : ℝ) * K * ∫ s, Q s ∂ν
  rw [← mul_sub, ← integral_sub hfint hgint, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∫ s, F s - G s ∂ν| ≤
        (1 / 2 : ℝ) * ∫ s, K * Q s ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact abs_integral_le_integral_abs.trans
        (integral_mono_ae hdiffint.abs hdomint hpoint)
    _ = (1 / 2 : ℝ) * K * ∫ s, Q s ∂ν := by
      rw [integral_const_mul]
      ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A specialization of `generalIto_formula_ae_of_partition_limits` whose
limits are exactly the pathwise integrals in the target Itô formula.

The four convergence assumptions are intentionally visible.  They identify
the precise analytic bridge still required for unrestricted functions and
general Itô processes; none is encoded as an opaque stochastic primitive. -/
theorem generalIto_formula_ae_of_uniformPartition_convergence
    [IsFiniteMeasure P]
    (f : ℝ → ℝ → ℝ) (X σ : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (I : W → ℝ)
    (hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P)
    (htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop
        (generalItoTimeIntegral f X t))
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop
        (generalItoQuadraticIntegral f X σ t))
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        generalItoTimeIntegral f X t omega + I omega +
          generalItoQuadraticIntegral f X σ t omega := by
  exact generalIto_formula_ae_of_partition_limits f X t
    (generalItoTimeIntegral f X t) I
    (generalItoQuadraticIntegral f X σ t)
    hendpoint htime hspace hquadratic hremainder

/-- A quadratic polynomial, used for the unconditional general-process
specialization below. -/
def quadraticPolynomial (a b c x : ℝ) : ℝ :=
  a * x ^ 2 + b * x + c

/-- A time-affine, state-quadratic test function.  This is the largest simple
class for which the time contribution and Taylor remainder are algebraically
exact without additional path regularity. -/
def timeAffineQuadraticPolynomial
    (tau a b c s x : ℝ) : ℝ :=
  tau * s + quadraticPolynomial a b c x

/-- A function with arbitrary time dependence and quadratic state
dependence. -/
def timeAddQuadraticPolynomial
    (g : ℝ → ℝ) (a b c s x : ℝ) : ℝ :=
  g s + quadraticPolynomial a b c x

/-- A time/state-separable test function. -/
def timeAddStateFunction
    (g f : ℝ → ℝ) (s x : ℝ) : ℝ :=
  g s + f x

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
@[simp]
theorem deriv_quadraticPolynomial (a b c x : ℝ) :
    deriv (quadraticPolynomial a b c) x = 2 * a * x + b := by
  unfold quadraticPolynomial
  have h := (((((hasDerivAt_id x).pow 2).const_mul a).add
    ((hasDerivAt_id x).const_mul b)).add_const c).deriv
  simpa [id_eq, mul_comm, mul_left_comm, mul_assoc] using h

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
@[simp]
theorem secondDeriv_quadraticPolynomial (a b c x : ℝ) :
    deriv (deriv (quadraticPolynomial a b c)) x = 2 * a := by
  have hfirst : deriv (quadraticPolynomial a b c) =
      fun y => 2 * a * y + b := by
    funext y
    exact deriv_quadraticPolynomial a b c y
  rw [hfirst]
  have h : HasDerivAt (fun y : ℝ => 2 * a * y + b) (2 * a) x := by
    convert ((hasDerivAt_const_mul (x := x) (2 * a)).add_const b) using 1
  exact h.deriv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- First derivative of a function after a deterministic affine change of
variable. -/
theorem deriv_comp_const_add_const_mul
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x₀ c y : ℝ) :
    deriv (fun z => f (x₀ + c * z)) y = deriv f (x₀ + c * y) * c := by
  have hinner : HasDerivAt (fun z : ℝ => x₀ + c * z) c y := by
    exact (hasDerivAt_const_mul (x := y) c).const_add x₀
  exact ((hf (x₀ + c * y)).hasDerivAt.comp y hinner).deriv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Second derivative of a `C²` function after a deterministic affine change
of variable. -/
theorem secondDeriv_comp_const_add_const_mul
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x₀ c y : ℝ) :
    deriv (deriv (fun z => f (x₀ + c * z))) y =
      deriv (deriv f) (x₀ + c * y) * c ^ 2 := by
  have hfirst : deriv (fun z => f (x₀ + c * z)) =
      fun z => deriv f (x₀ + c * z) * c := by
    funext z
    exact deriv_comp_const_add_const_mul f
      (hf.differentiable (by norm_num)) x₀ c z
  rw [hfirst]
  have hinner : HasDerivAt (fun z : ℝ => x₀ + c * z) c y := by
    exact (hasDerivAt_const_mul (x := y) c).const_add x₀
  have hfderiv : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have houter : HasDerivAt (deriv f)
      (deriv (deriv f) (x₀ + c * y)) (x₀ + c * y) :=
    (hfderiv.differentiable (by norm_num)
      (x₀ + c * y)).hasDerivAt
  have hcomp := (houter.comp y hinner).const_mul c
  simpa only [Function.comp_apply, pow_two, mul_assoc, mul_comm,
    mul_left_comm] using hcomp.deriv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
@[simp]
theorem itoTimeDerivative_timeAddStateFunction
    (g f : ℝ → ℝ) (hg : Differentiable ℝ g) (s x : ℝ) :
    itoTimeDerivative (timeAddStateFunction g f) s x = deriv g s := by
  unfold itoTimeDerivative timeAddStateFunction
  exact ((hg s).hasDerivAt.add_const (f x)).deriv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
@[simp]
theorem itoSpaceDerivative_timeAddStateFunction
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f) (s x : ℝ) :
    itoSpaceDerivative (timeAddStateFunction g f) s x = deriv f x := by
  unfold itoSpaceDerivative timeAddStateFunction
  exact ((hf x).hasDerivAt.const_add (g s)).deriv

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
@[simp]
theorem itoSpaceSecondDerivative_timeAddStateFunction
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f) (s x : ℝ) :
    itoSpaceSecondDerivative (timeAddStateFunction g f) s x =
      deriv (deriv f) x := by
  unfold itoSpaceSecondDerivative timeAddStateFunction
  have hfirst : deriv (fun y => g s + f y) = deriv f := by
    funext y
    exact ((hf y).hasDerivAt.const_add (g s)).deriv
  rw [hfirst]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For a separable function, the time component of the general partition sum
is the ordinary deterministic derivative Riemann sum. -/
theorem generalItoTimeApprox_timeAddStateFunction
    (g f : ℝ → ℝ) (hg : Differentiable ℝ g)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoTimeApprox (timeAddStateFunction g f) X t n omega =
      ∑ i ∈ Finset.range n,
        deriv g (uniformPartitionTime t n i : ℝ) *
          ((uniformPartitionTime t n (i + 1) : ℝ) -
            (uniformPartitionTime t n i : ℝ)) := by
  unfold generalItoTimeApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [itoTimeDerivative_timeAddStateFunction g f hg]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For a separable function, the space component is the standard left sum
of `f'` against `X`. -/
theorem generalItoSpaceApprox_timeAddStateFunction
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoSpaceApprox (timeAddStateFunction g f) X t n omega =
      ∑ i ∈ Finset.range n,
        deriv f (X (uniformPartitionTime t n i) omega) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) := by
  unfold generalItoSpaceApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [itoSpaceDerivative_timeAddStateFunction g f hf]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For a separable function, the quadratic component is the standard
second-derivative-weighted quadratic-variation sum. -/
theorem generalItoQuadraticApprox_timeAddStateFunction
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoQuadraticApprox (timeAddStateFunction g f) X t n omega =
      ∑ i ∈ Finset.range n,
        (1 / 2 : ℝ) * deriv (deriv f)
            (X (uniformPartitionTime t n i) omega) *
          (X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) ^ 2 := by
  unfold generalItoQuadraticApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [itoSpaceSecondDerivative_timeAddStateFunction g f hf]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The time partition term for a separable `C¹_t` function converges to its
time integral along every sample path. -/
theorem generalItoTimeApprox_timeAddStateFunction_tendsto
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    Filter.Tendsto
      (fun n => generalItoTimeApprox
        (timeAddStateFunction g f) X t (n + 1) omega)
      Filter.atTop
      (nhds (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s)) := by
  have h := tendsto_uniformPartition_leftRiemann (deriv g)
    (hg.continuous_deriv (by norm_num)) t
  convert h using 1
  funext n
  exact generalItoTimeApprox_timeAddStateFunction g f
    (hg.differentiable (by norm_num)) X t (n + 1) omega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Convergence of the separable time term also holds in probability. -/
theorem generalItoTimeApprox_timeAddStateFunction_tendstoInMeasure
    [IsFiniteMeasure P]
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoTimeApprox
        (timeAddStateFunction g f) X t (n + 1))
      Filter.atTop
      (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hconst : AEStronglyMeasurable
        (fun _ : W => ∑ i ∈ Finset.range (n + 1),
          deriv g (uniformPartitionTime t (n + 1) i : ℝ) *
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) P :=
      aestronglyMeasurable_const
    refine hconst.congr ?_
    filter_upwards with omega
    exact (generalItoTimeApprox_timeAddStateFunction g f
      (hg.differentiable (by norm_num)) X t (n + 1) omega).symm
  · filter_upwards with omega
    exact generalItoTimeApprox_timeAddStateFunction_tendsto
      g f hg X t omega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The abstract time integral reduces to the ordinary derivative integral
for a time/state-separable function. -/
theorem generalItoTimeIntegral_timeAddStateFunction
    (g f : ℝ → ℝ) (hg : Differentiable ℝ g)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    generalItoTimeIntegral (timeAddStateFunction g f) X t omega =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s := by
  unfold generalItoTimeIntegral
  apply integral_congr_ae
  filter_upwards with s
  exact itoTimeDerivative_timeAddStateFunction g f hg s _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The abstract quadratic integral reduces to the familiar state second
derivative weighted by the diffusion square. -/
theorem generalItoQuadraticIntegral_timeAddStateFunction
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (X σ : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    generalItoQuadraticIntegral
        (timeAddStateFunction g f) X σ t omega =
      (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        deriv (deriv f) (X s.toNNReal omega) *
          (σ s.toNNReal omega) ^ 2 := by
  unfold generalItoQuadraticIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  rw [itoSpaceSecondDerivative_timeAddStateFunction g f hf]

/-- The first-order Taylor residual in the time coordinate. -/
noncomputable def itoTimeTaylorRemainder
    (g : ℝ → ℝ) (s₀ s₁ : ℝ) : ℝ :=
  g s₁ - g s₀ - deriv g s₀ * (s₁ - s₀)

/-- The second-order Taylor residual in the state coordinate. -/
noncomputable def itoStateTaylorRemainder
    (f : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  f x₁ - f x₀ - deriv f x₀ * (x₁ - x₀) -
    (1 / 2 : ℝ) * deriv (deriv f) x₀ * (x₁ - x₀) ^ 2

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
theorem itoStateTaylorRemainder_eq_itoTaylorRemainder
    (f : ℝ → ℝ) (x₀ x₁ : ℝ) :
    itoStateTaylorRemainder f x₀ x₁ =
      itoTaylorRemainder f x₀ x₁ := by
  unfold itoStateTaylorRemainder itoTaylorRemainder
  ring

/-- Accumulated first-order time residual along the uniform partition. -/
noncomputable def itoTimeTaylorRemainderApprox
    (g : ℝ → ℝ) (t : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoTimeTaylorRemainder g
      (uniformPartitionTime t n i : ℝ)
      (uniformPartitionTime t n (i + 1) : ℝ)

/-- Accumulated second-order state residual along the uniform partition. -/
noncomputable def itoStateTaylorRemainderApprox
    (f : ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    itoStateTaylorRemainder f
      (X (uniformPartitionTime t n i) omega)
      (X (uniformPartitionTime t n (i + 1)) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The accumulated state-only Taylor residual is invariant almost everywhere
under fixed-time modification of the process. -/
theorem itoStateTaylorRemainderApprox_ae_eq_of_fixedTime_ae_eq
    {Y : ℝ≥0 → W → ℝ}
    (hXY : ∀ s, X s =ᵐ[P] Y s)
    (f : ℝ → ℝ) (t : ℝ≥0) (n : ℕ) :
    itoStateTaylorRemainderApprox f X t n =ᵐ[P]
      itoStateTaylorRemainderApprox f Y t n := by
  have hall : ∀ᵐ omega ∂P, ∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) omega =
          Y (uniformPartitionTime t n i) omega ∧
        X (uniformPartitionTime t n (i + 1)) omega =
          Y (uniformPartitionTime t n (i + 1)) omega :=
    (Finset.range n).eventually_all.mpr fun i _hi =>
      (hXY (uniformPartitionTime t n i)).and
        (hXY (uniformPartitionTime t n (i + 1)))
  filter_upwards [hall] with omega homega
  unfold itoStateTaylorRemainderApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homega i hi).1, (homega i hi).2]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For a separable test function, each general residual is exactly the sum
of an independent time residual and state residual. -/
theorem generalItoRemainderIncrement_timeAddStateFunction
    (g f : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hf : Differentiable ℝ f) (s₀ s₁ x₀ x₁ : ℝ) :
    generalItoRemainderIncrement
        (timeAddStateFunction g f) s₀ s₁ x₀ x₁ =
      itoTimeTaylorRemainder g s₀ s₁ +
        itoStateTaylorRemainder f x₀ x₁ := by
  unfold generalItoRemainderIncrement itoTimeTaylorRemainder
    itoStateTaylorRemainder
  rw [itoTimeDerivative_timeAddStateFunction g f hg,
    itoSpaceDerivative_timeAddStateFunction g f hf,
    itoSpaceSecondDerivative_timeAddStateFunction g f hf]
  unfold timeAddStateFunction
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The accumulated general residual for a separable function splits into its
time and state Taylor residual sums. -/
theorem generalItoRemainderApprox_timeAddStateFunction
    (g f : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hf : Differentiable ℝ f) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoRemainderApprox
        (timeAddStateFunction g f) X t n omega =
      itoTimeTaylorRemainderApprox g t n +
        itoStateTaylorRemainderApprox f X t n omega := by
  unfold generalItoRemainderApprox itoTimeTaylorRemainderApprox
    itoStateTaylorRemainderApprox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact generalItoRemainderIncrement_timeAddStateFunction g f hg hf _ _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The deterministic time Taylor residual vanishes along uniform partitions
for every `C¹` function. -/
theorem itoTimeTaylorRemainderApprox_tendsto_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) :
    Filter.Tendsto
      (fun n => itoTimeTaylorRemainderApprox g t (n + 1))
      Filter.atTop (nhds 0) := by
  have hderiv := tendsto_uniformPartition_deriv_mul_increment hg t
  have hdecomp (n : ℕ) :
      g t - g 0 =
        (∑ i ∈ Finset.range (n + 1),
          deriv g (uniformPartitionTime t (n + 1) i : ℝ) *
            ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime t (n + 1) i : ℝ))) +
          itoTimeTaylorRemainderApprox g t (n + 1) := by
    have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
      rw [uniformPartitionTime]
      exact mul_div_cancel_right₀ t hn
    have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
    calc
      _ = g (uniformPartitionTime t (n + 1) (n + 1) : ℝ) -
          g (uniformPartitionTime t (n + 1) 0 : ℝ) := by
        simp only [htop, hzero, NNReal.coe_zero]
      _ = ∑ i ∈ Finset.range (n + 1),
          (g (uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
            g (uniformPartitionTime t (n + 1) i : ℝ)) := by
        exact (Finset.sum_range_sub
          (fun i => g (uniformPartitionTime t (n + 1) i : ℝ))
          (n + 1)).symm
      _ = _ := by
        unfold itoTimeTaylorRemainderApprox itoTimeTaylorRemainder
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have heq (n : ℕ) :
      itoTimeTaylorRemainderApprox g t (n + 1) =
        (g t - g 0) -
          ∑ i ∈ Finset.range (n + 1),
            deriv g (uniformPartitionTime t (n + 1) i : ℝ) *
              ((uniformPartitionTime t (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime t (n + 1) i : ℝ)) := by
    linarith [hdecomp n]
  convert tendsto_const_nhds.sub hderiv using 1
  · funext n
    exact heq n
  · simp only [sub_self]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The deterministic time Taylor residual also vanishes in probability when
viewed as a constant random variable. -/
theorem itoTimeTaylorRemainderApprox_tendstoInMeasure_zero
    [IsFiniteMeasure P]
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n _ => itoTimeTaylorRemainderApprox g t (n + 1))
      Filter.atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact aestronglyMeasurable_const
  · filter_upwards with omega
    exact itoTimeTaylorRemainderApprox_tendsto_zero g hg t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For any measurable process with almost-everywhere continuous paths and
quadratic variation in probability, the accumulated second-order state
Taylor residual vanishes in probability.  This is the Brownian-independent
analytic remainder theorem needed by the general Itô reduction. -/
theorem itoStateTaylorRemainderApprox_tendstoInMeasure_of_continuous_qv
    [IsFiniteMeasure P]
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (q : W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hcontinuous : ∀ᵐ omega ∂P, Continuous (fun s => X s omega))
    (hquadratic : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1))
      Filter.atTop q) :
    TendstoInMeasure P
      (fun n => itoStateTaylorRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  have hfirst : Continuous (deriv f) := by
    rw [← show iteratedDeriv 1 f = deriv f by
      rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
      simp only [iteratedDeriv_zero]]
    exact hf.continuous_iteratedDeriv 1 (by norm_num)
  have hsecond : Continuous (deriv (deriv f)) := by
    rw [← show iteratedDeriv 2 f = deriv (deriv f) by
      rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
        show iteratedDeriv 1 f = deriv f by
          rw [show 1 = 0 + 1 by omega, iteratedDeriv_succ]
          simp only [iteratedDeriv_zero]]]
    exact hf.continuous_iteratedDeriv 2 (by norm_num)
  have hremainder : Continuous
      (fun p : ℝ × ℝ => itoStateTaylorRemainder f p.1 p.2) := by
    unfold itoStateTaylorRemainder
    fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (itoStateTaylorRemainderApprox f X t (n + 1)) P := by
    intro n
    unfold itoStateTaylorRemainderApprox
    have hs := Finset.aestronglyMeasurable_sum (Finset.range (n + 1))
      (fun i _hi =>
        (hremainder.measurable.comp_aemeasurable
          ((hXmeas (uniformPartitionTime t (n + 1) i)).aemeasurable.prodMk
            (hXmeas
              (uniformPartitionTime t (n + 1) (i + 1))).aemeasurable)).aestronglyMeasurable)
    apply hs.congr
    filter_upwards with omega
    simp only [Finset.sum_apply, Function.comp_apply]
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ms, hms, hquadratic'⟩ :=
    (hquadratic.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hcontinuous, hquadratic'] with omega hcont hq
  have hrem :=
    tendsto_subseq_uniformPartition_taylorRemainder_of_quadraticVariation
      hf X t omega (q omega) (fun k => ns (ms k))
      (hns.tendsto_atTop.comp hms.tendsto_atTop) hcont
      (by simpa only [Function.comp_apply] using hq)
  simpa only [itoStateTaylorRemainderApprox,
    itoStateTaylorRemainder_eq_itoTaylorRemainder] using hrem

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A continuous modification is enough to obtain state Taylor-remainder
convergence for the original representative, because both its quadratic sums
and its Taylor sums are invariant on each finite partition almost everywhere. -/
theorem IsContinuousProcessModification.stateTaylorRemainder_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (q : W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hquadratic : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1))
      Filter.atTop q) :
    TendstoInMeasure P
      (fun n => itoStateTaylorRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hXmeas s).congr (hmod.fixedTime_ae_eq s)
  have hquadraticY : TendstoInMeasure P
      (fun n => quadraticVariationApprox Y t (n + 1))
      Filter.atTop q :=
    hquadratic.congr_left fun n =>
      quadraticVariationApprox_congr_ae hmod.fixedTime_ae_eq t (n + 1)
  have hremainderY :=
    itoStateTaylorRemainderApprox_tendstoInMeasure_of_continuous_qv
      f hf Y t q hYmeas hmod.continuous_paths hquadraticY
  exact hremainderY.congr_left fun n =>
    (itoStateTaylorRemainderApprox_ae_eq_of_fixedTime_ae_eq
      hmod.fixedTime_ae_eq f t (n + 1)).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A continuous modification upgrades the full genuinely two-variable
Taylor-remainder theorem back to the original fixed-time representative. -/
theorem IsContinuousProcessModification.generalRemainder_tendstoInMeasure
    [IsFiniteMeasure P]
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (htdiff : ∀ x, Differentiable ℝ (fun s => f s x))
    (hslice : ∀ s, ContDiff ℝ 2 (f s))
    (hdt : Continuous (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (hdx : Continuous (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2))
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (q : W → ℝ)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hquadratic : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop q) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hXmeas s).congr (hmod.fixedTime_ae_eq s)
  have hquadraticY : TendstoInMeasure P
      (fun n => quadraticVariationApprox Y t (n + 1)) Filter.atTop q :=
    hquadratic.congr_left fun n =>
      quadraticVariationApprox_congr_ae hmod.fixedTime_ae_eq t (n + 1)
  have hcontinuous : ∀ᵐ omega ∂P,
      ContinuousOn (fun s => Y s omega) (Set.Icc 0 t) :=
    hmod.continuous_paths.mono fun _ homega => homega.continuousOn
  have hremainderY :=
    generalItoRemainderApprox_tendstoInMeasure_of_continuous_qv
      f hf htdiff hslice hdt hdx hsecond Y t q hYmeas hcontinuous hquadraticY
  exact hremainderY.congr_left fun n =>
    (generalItoRemainderApprox_ae_eq_of_fixedTime_ae_eq
      hmod.fixedTime_ae_eq f t (n + 1)).symm

/-- A Brownian motion after a deterministic affine change of state. -/
def affineBrownianProcess
    (x₀ c : ℝ) (B : ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun s omega => x₀ + c * B s omega

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The state Taylor residual along an affine Brownian state is exactly the
ordinary Taylor residual of the affine composite, so it vanishes in
probability. -/
theorem itoStateTaylorRemainderApprox_affineBrownian_tendstoInMeasure_zero
    (hB : IsBrownianMotion B P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStateTaylorRemainderApprox f
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop (fun _ => 0) := by
  let F : ℝ → ℝ := fun y => f (x₀ + c * y)
  have hF : ContDiff ℝ 2 F := by
    dsimp only [F]
    fun_prop
  have h := taylorRemainderSum_tendstoInMeasure hB hF t
  apply h.congr_left
  intro n
  filter_upwards with omega
  unfold itoStateTaylorRemainderApprox itoStateTaylorRemainder
    affineBrownianProcess
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only [F]
  rw [deriv_comp_const_add_const_mul f
      (hf.differentiable (by norm_num)) x₀ c,
    secondDeriv_comp_const_add_const_mul f hf x₀ c]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- All residual terms in the generic partition decomposition vanish for a
separable `C¹_t + C²_x` function evaluated along an affine Brownian state. -/
theorem generalItoRemainderApprox_timeAddState_affineBrownian_tendstoInMeasure_zero
    (hB : IsBrownianMotion B P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop (fun _ => 0) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  have htime :=
    itoTimeTaylorRemainderApprox_tendstoInMeasure_zero (P := P) g hg t
  have hstate :=
    itoStateTaylorRemainderApprox_affineBrownian_tendstoInMeasure_zero
      hB f hf x₀ c t
  rw [show
    (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
      (affineBrownianProcess x₀ c B) t (n + 1)) =
    (fun n omega =>
      itoTimeTaylorRemainderApprox g t (n + 1) +
        itoStateTaylorRemainderApprox f
          (affineBrownianProcess x₀ c B) t (n + 1) omega) by
    funext n omega
    exact generalItoRemainderApprox_timeAddStateFunction g f
      (hg.differentiable (by norm_num))
      (hf.differentiable (by norm_num))
      (affineBrownianProcess x₀ c B) t (n + 1) omega]
  simpa only [zero_add] using htime.add_real_noMeas hstate

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- For an affine Brownian state, the generic quadratic partition term for a
separable function converges to the expected constant-volatility integral. -/
theorem generalItoQuadraticApprox_timeAddState_affineBrownian_tendstoInMeasure
    (hB : IsBrownianMotion B P)
    (g f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop
      (generalItoQuadraticIntegral (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B)
        (fun _ : ℝ≥0 => fun _ : W => c) t) := by
  let F : ℝ → ℝ := fun y => f (x₀ + c * y)
  have hF : ContDiff ℝ 2 F := by
    dsimp only [F]
    fun_prop
  have hsecond : deriv (deriv F) =
      fun y => deriv (deriv f) (x₀ + c * y) * c ^ 2 := by
    funext y
    exact secondDeriv_comp_const_add_const_mul f hf x₀ c y
  have hbase := secondOrderTaylorSum_tendstoInMeasure hB hF t
  rw [hsecond] at hbase
  have hsource : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop
      (fun omega => (1 / 2 : ℝ) *
        ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
          deriv (deriv f) (x₀ + c * B s.toNNReal omega) * c ^ 2) := by
    apply hbase.congr_left
    intro n
    filter_upwards with omega
    rw [generalItoQuadraticApprox_timeAddStateFunction g f
      (hf.differentiable (by norm_num))]
    unfold affineBrownianProcess
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  apply hsource.congr_right
  filter_upwards with omega
  rw [generalItoQuadraticIntegral_timeAddStateFunction g f
    (hf.differentiable (by norm_num))]
  congr 1

/-- The standard left sum against a deterministic affine transform of
Brownian motion. -/
noncomputable def affineBrownianItoSpaceApprox
    (f : ℝ → ℝ) (x₀ c : ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    deriv f (affineBrownianProcess x₀ c B
      (uniformPartitionTime t n i) omega) *
      (affineBrownianProcess x₀ c B
          (uniformPartitionTime t n (i + 1)) omega -
        affineBrownianProcess x₀ c B
          (uniformPartitionTime t n i) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For separable test functions, the generic space partition term is the
affine-Brownian left sum used by the specialized theorem. -/
theorem generalItoSpaceApprox_timeAddState_affineBrownian
    (g f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (x₀ c : ℝ) (B : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    generalItoSpaceApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t n omega =
      affineBrownianItoSpaceApprox f x₀ c B t n omega := by
  rw [generalItoSpaceApprox_timeAddStateFunction g f hf]
  rfl

/-- The left sum of the derivative of a quadratic polynomial against `X`. -/
noncomputable def quadraticItoSpaceApprox
    (a b : ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (2 * a * X (uniformPartitionTime t n i) omega + b) *
      (X (uniformPartitionTime t n (i + 1)) omega -
        X (uniformPartitionTime t n i) omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The quadratic Taylor formula summed along a uniform partition. -/
theorem quadraticPolynomial_uniformPartition_decomposition
    (a b c : ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) :
    quadraticPolynomial a b c (X t omega) -
        quadraticPolynomial a b c (X 0 omega) =
      quadraticItoSpaceApprox a b X t (n + 1) omega +
        a * quadraticVariationApprox X t (n + 1) omega := by
  have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  have hzero : uniformPartitionTime t (n + 1) 0 = 0 := by
    simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
  calc
    _ = quadraticPolynomial a b c
          (X (uniformPartitionTime t (n + 1) (n + 1)) omega) -
        quadraticPolynomial a b c
          (X (uniformPartitionTime t (n + 1) 0) omega) := by
      rw [htop, hzero]
    _ = ∑ i ∈ Finset.range (n + 1),
        (quadraticPolynomial a b c
            (X (uniformPartitionTime t (n + 1) (i + 1)) omega) -
          quadraticPolynomial a b c
            (X (uniformPartitionTime t (n + 1) i) omega)) := by
      exact (Finset.sum_range_sub
        (fun i => quadraticPolynomial a b c
          (X (uniformPartitionTime t (n + 1) i) omega)) (n + 1)).symm
    _ = _ := by
      unfold quadraticItoSpaceApprox quadraticVariationApprox
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      unfold quadraticPolynomial
      ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- A quadratic polynomial has zero second-order Taylor residual. -/
@[simp]
theorem itoStateTaylorRemainder_quadraticPolynomial
    (a b c x₀ x₁ : ℝ) :
    itoStateTaylorRemainder (quadraticPolynomial a b c) x₀ x₁ = 0 := by
  unfold itoStateTaylorRemainder
  rw [deriv_quadraticPolynomial, secondDeriv_quadraticPolynomial]
  unfold quadraticPolynomial
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The generic space term for an arbitrary-time, quadratic-state function
is the standard quadratic left sum. -/
theorem generalItoSpaceApprox_timeAddQuadraticPolynomial
    (g : ℝ → ℝ) (a b c : ℝ)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoSpaceApprox (timeAddQuadraticPolynomial g a b c)
        X t n omega = quadraticItoSpaceApprox a b X t n omega := by
  have hp : Differentiable ℝ (quadraticPolynomial a b c) := by
    unfold quadraticPolynomial
    fun_prop
  change generalItoSpaceApprox
      (timeAddStateFunction g (quadraticPolynomial a b c)) X t n omega = _
  rw [generalItoSpaceApprox_timeAddStateFunction g
    (quadraticPolynomial a b c) hp]
  unfold quadraticItoSpaceApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [deriv_quadraticPolynomial]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The generic quadratic term for a quadratic state function is exactly the
coefficient `a` times the unweighted quadratic-variation sum. -/
theorem generalItoQuadraticApprox_timeAddQuadraticPolynomial
    (g : ℝ → ℝ) (a b c : ℝ)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoQuadraticApprox (timeAddQuadraticPolynomial g a b c)
        X t n omega = a * quadraticVariationApprox X t n omega := by
  have hp : Differentiable ℝ (quadraticPolynomial a b c) := by
    unfold quadraticPolynomial
    fun_prop
  change generalItoQuadraticApprox
      (timeAddStateFunction g (quadraticPolynomial a b c)) X t n omega = _
  rw [generalItoQuadraticApprox_timeAddStateFunction g
    (quadraticPolynomial a b c) hp]
  unfold quadraticVariationApprox
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [secondDeriv_quadraticPolynomial]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- For arbitrary time dependence and quadratic state dependence, the
generic residual is only the deterministic first-order time residual. -/
theorem generalItoRemainderApprox_timeAddQuadraticPolynomial
    (g : ℝ → ℝ) (hg : Differentiable ℝ g) (a b c : ℝ)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W) :
    generalItoRemainderApprox (timeAddQuadraticPolynomial g a b c)
        X t n omega = itoTimeTaylorRemainderApprox g t n := by
  have hp : Differentiable ℝ (quadraticPolynomial a b c) := by
    unfold quadraticPolynomial
    fun_prop
  change generalItoRemainderApprox
      (timeAddStateFunction g (quadraticPolynomial a b c)) X t n omega = _
  rw [generalItoRemainderApprox_timeAddStateFunction g
    (quadraticPolynomial a b c) hg hp]
  unfold itoStateTaylorRemainderApprox
  simp only [itoStateTaylorRemainder_quadraticPolynomial, Finset.sum_const_zero,
    add_zero]

variable [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian P]

omit [CompleteSpace W] [BorelSpace W] in
/-- Uniform perturbation estimate for weighted quadratic sums of a natural
Itô process.  A global `K`-bound on the difference of two continuous weights
costs at most `(K / 2) · ‖U‖²` in `L¹`, uniformly in the partition and
horizon.  This is the quantitative input for extending weighted bracket
identities from a dense class of weights. -/
theorem integral_abs_generalItoQuadraticApprox_sub_naturalIto_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative g p.1 p.2))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ s x,
      |itoSpaceSecondDerivative f s x -
        itoSpaceSecondDerivative g s x| ≤ K)
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ omega,
      |generalItoQuadraticApprox f
          (naturalItoProcessRepresentative hB hsm rfl U) t n omega -
        generalItoQuadraticApprox g
          (naturalItoProcessRepresentative hB hsm rfl U) t n omega| ∂P ≤
      (1 / 2 : ℝ) * K * ‖U‖ ^ 2 := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB hsm rfl U
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB hsm rfl U s).aestronglyMeasurable
  have hfmeas := aestronglyMeasurable_generalItoQuadraticApprox
    f hf M hMmeas t n
  have hgmeas := aestronglyMeasurable_generalItoQuadraticApprox
    g hg M hMmeas t n
  have hqint : Integrable (quadraticVariationApprox M t n) P := by
    simpa only [M] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm U t n
  have hright : Integrable
      (fun omega => (1 / 2 : ℝ) * K *
        quadraticVariationApprox M t n omega) P :=
    hqint.const_mul ((1 / 2 : ℝ) * K)
  have hpoint : ∀ omega,
      |generalItoQuadraticApprox f M t n omega -
        generalItoQuadraticApprox g M t n omega| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox M t n omega := by
    intro omega
    exact abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
      f g M t n omega K hK (fun i _hi => hbound _ _)
  have hleft : Integrable
      (fun omega => |generalItoQuadraticApprox f M t n omega -
        generalItoQuadraticApprox g M t n omega|) P := by
    apply hright.mono' ((hfmeas.sub hgmeas).norm)
    filter_upwards with omega
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_abs] using hpoint omega
  calc
    (∫ omega,
        |generalItoQuadraticApprox f M t n omega -
          generalItoQuadraticApprox g M t n omega| ∂P) ≤
        ∫ omega, (1 / 2 : ℝ) * K *
          quadraticVariationApprox M t n omega ∂P :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = (1 / 2 : ℝ) * K *
        ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 := by
      rw [integral_const_mul,
        integral_quadraticVariationApprox_naturalItoProcessRepresentative
          hB hsm U t hn]
    _ ≤ (1 / 2 : ℝ) * K * ‖U‖ ^ 2 := by
      gcongr
      exact norm_naturalItoProcess_le hB hsm rfl U t

omit [CompleteSpace W] [BorelSpace W] in
/-- The expected canonical bracket up to a finite horizon is bounded by the
global predictable-process `L²` norm. -/
theorem integral_predictableQuadraticVariation_le_norm_sq
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) :
    ∫ omega, predictableQuadraticVariation hsm U t omega ∂P ≤
      ‖U‖ ^ 2 := by
  let Q : Measure ℝ≥0 :=
    nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)
  let A : ℝ≥0 × W → ℝ := fun p =>
    ((U : ℝ≥0 × W → ℝ) p) ^ 2
  have hAint : Integrable A (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [A] using (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  have hmeasure : Q.prod P ≤ nonnegativeLebesgueMeasure.prod P :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hAQint := hAint.mono_measure hmeasure
  unfold predictableQuadraticVariation
  change (∫ omega, ∫ s, A (s, omega) ∂Q ∂P) ≤ ‖U‖ ^ 2
  calc
    (∫ omega, ∫ s, A (s, omega) ∂Q ∂P) =
        ∫ p, A p ∂(Q.prod P) := (integral_prod_symm A hAQint).symm
    _ ≤ ∫ p, A p ∂(nonnegativeLebesgueMeasure.prod P) :=
      integral_mono_measure hmeasure
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hAint
    _ = ‖U‖ ^ 2 := integral_sq_predictableProcess_eq_norm_sq hsm U

omit [CompleteSpace W] [BorelSpace W] in
/-- Weighted quadratic variation is closed under uniform approximation of
the second-derivative weight, provided the corresponding candidate limits
obey the same `L¹` approximation estimate.  This packages the final density
step: it is enough to prove convergence on a uniformly dense class of
weights and to identify their limits compatibly. -/
theorem generalItoQuadraticApprox_naturalIto_tendstoInMeasure_of_weight_approx
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0)
    (f : ℝ → ℝ → ℝ) (fk : ℕ → ℝ → ℝ → ℝ)
    (G : W → ℝ) (Gk : ℕ → W → ℝ) (K : ℕ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hfk : ∀ k, Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative (fk k) p.1 p.2))
    (hK : Filter.Tendsto K Filter.atTop (nhds 0))
    (hK_nonneg : ∀ k, 0 ≤ K k)
    (hweight : ∀ k s x,
      |itoSpaceSecondDerivative f s x -
        itoSpaceSecondDerivative (fk k) s x| ≤ K k)
    (happrox : ∀ k, TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (fk k)
        (naturalItoProcessRepresentative hB hsm rfl U) t (n + 1))
      Filter.atTop (Gk k))
    (hrightInt : ∀ k, Integrable (fun omega => ‖Gk k omega - G omega‖) P)
    (hright : ∀ k, ∫ omega, ‖Gk k omega - G omega‖ ∂P ≤
      (1 / 2 : ℝ) * K k * ‖U‖ ^ 2) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f
        (naturalItoProcessRepresentative hB hsm rfl U) t (n + 1))
      Filter.atTop G := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB hsm rfl U
  let a : ℕ → ℝ := fun k => (1 / 2 : ℝ) * K k * ‖U‖ ^ 2
  have ha : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
    have hnorm : Filter.Tendsto (fun _ : ℕ => ‖U‖ ^ 2)
        Filter.atTop (nhds (‖U‖ ^ 2)) := tendsto_const_nhds
    simpa only [a, mul_zero, zero_mul] using (hconst.mul hK).mul hnorm
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB hsm rfl U s).aestronglyMeasurable
  apply tendstoInMeasure_of_uniform_integral_approx
    (fun n => generalItoQuadraticApprox f M t (n + 1)) G
    (fun k n => generalItoQuadraticApprox (fk k) M t (n + 1)) Gk a ha
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) (hK_nonneg k)) (sq_nonneg _)
  · intro k
    simpa only [M] using happrox k
  · intro k n
    have hfmeas := aestronglyMeasurable_generalItoQuadraticApprox
      f hf M hMmeas t (n + 1)
    have hkmeas := aestronglyMeasurable_generalItoQuadraticApprox
      (fk k) (hfk k) M hMmeas t (n + 1)
    have hqint : Integrable (quadraticVariationApprox M t (n + 1)) P := by
      simpa only [M] using
        integrable_quadraticVariationApprox_naturalItoProcessRepresentative
          hB hsm U t (n + 1)
    have hdom : Integrable (fun omega =>
        (1 / 2 : ℝ) * K k * quadraticVariationApprox M t (n + 1) omega) P :=
      hqint.const_mul ((1 / 2 : ℝ) * K k)
    apply hdom.mono' ((hfmeas.sub hkmeas).norm)
    filter_upwards with omega
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_abs] using
      (abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
        f (fk k) M t (n + 1) omega (K k) (hK_nonneg k)
          (fun i _hi => hweight k _ _))
  · intro k n
    simpa only [M, a, Real.norm_eq_abs] using
      integral_abs_generalItoQuadraticApprox_sub_naturalIto_le
        hB hsm U f (fk k) hf (hfk k) (K k) (hK_nonneg k)
          (hweight k) t (Nat.zero_lt_succ n)
  · exact hrightInt
  · exact hright

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- Abstract weighted-bracket density closure for a process whose uniform
quadratic sums have a common `L¹` bound.  This is the version applicable to
a full Itô process once its drift-plus-martingale quadratic sums are bounded:
uniform approximation of the weight reduces convergence to the approximating
class and stability of the candidate limits. -/
theorem generalItoQuadraticApprox_tendstoInMeasure_of_weight_approx
    (X : ℝ≥0 → W → ℝ) (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (t : ℝ≥0)
    (f : ℝ → ℝ → ℝ) (fk : ℕ → ℝ → ℝ → ℝ)
    (G : W → ℝ) (Gk : ℕ → W → ℝ) (K : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hfk : ∀ k, Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative (fk k) p.1 p.2))
    (hK : Filter.Tendsto K Filter.atTop (nhds 0))
    (hK_nonneg : ∀ k, 0 ≤ K k)
    (hweight : ∀ k s x,
      |itoSpaceSecondDerivative f s x -
        itoSpaceSecondDerivative (fk k) s x| ≤ K k)
    (hqint : ∀ n, Integrable (quadraticVariationApprox X t (n + 1)) P)
    (hqbound : ∀ n,
      ∫ omega, quadraticVariationApprox X t (n + 1) omega ∂P ≤ C)
    (happrox : ∀ k, TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (fk k) X t (n + 1))
      Filter.atTop (Gk k))
    (hrightInt : ∀ k, Integrable (fun omega => ‖Gk k omega - G omega‖) P)
    (hright : ∀ k, ∫ omega, ‖Gk k omega - G omega‖ ∂P ≤
      (1 / 2 : ℝ) * K k * C) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1))
      Filter.atTop G := by
  let a : ℕ → ℝ := fun k => (1 / 2 : ℝ) * K k * C
  have ha : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
    have hCconst : Filter.Tendsto (fun _ : ℕ => C)
        Filter.atTop (nhds C) := tendsto_const_nhds
    simpa only [a, mul_zero, zero_mul] using (hconst.mul hK).mul hCconst
  apply tendstoInMeasure_of_uniform_integral_approx
    (fun n => generalItoQuadraticApprox f X t (n + 1)) G
    (fun k n => generalItoQuadraticApprox (fk k) X t (n + 1)) Gk a ha
  · intro k
    exact mul_nonneg (mul_nonneg (by norm_num) (hK_nonneg k)) hC
  · exact happrox
  · intro k n
    have hfmeas := aestronglyMeasurable_generalItoQuadraticApprox
      f hf X hXmeas t (n + 1)
    have hkmeas := aestronglyMeasurable_generalItoQuadraticApprox
      (fk k) (hfk k) X hXmeas t (n + 1)
    have hdom : Integrable (fun omega =>
        (1 / 2 : ℝ) * K k *
          quadraticVariationApprox X t (n + 1) omega) P :=
      (hqint n).const_mul ((1 / 2 : ℝ) * K k)
    apply hdom.mono' ((hfmeas.sub hkmeas).norm)
    filter_upwards with omega
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_abs] using
      (abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
        f (fk k) X t (n + 1) omega (K k) (hK_nonneg k)
          (fun i _hi => hweight k _ _))
  · intro k n
    have hfmeas := aestronglyMeasurable_generalItoQuadraticApprox
      f hf X hXmeas t (n + 1)
    have hkmeas := aestronglyMeasurable_generalItoQuadraticApprox
      (fk k) (hfk k) X hXmeas t (n + 1)
    have hdom : Integrable (fun omega =>
        (1 / 2 : ℝ) * K k *
          quadraticVariationApprox X t (n + 1) omega) P :=
      (hqint n).const_mul ((1 / 2 : ℝ) * K k)
    have hleft : Integrable (fun omega =>
        |generalItoQuadraticApprox f X t (n + 1) omega -
          generalItoQuadraticApprox (fk k) X t (n + 1) omega|) P := by
      apply hdom.mono' ((hfmeas.sub hkmeas).norm)
      filter_upwards with omega
      simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_abs] using
        (abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
          f (fk k) X t (n + 1) omega (K k) (hK_nonneg k)
            (fun i _hi => hweight k _ _))
    calc
      (∫ omega, ‖generalItoQuadraticApprox f X t (n + 1) omega -
          generalItoQuadraticApprox (fk k) X t (n + 1) omega‖ ∂P) ≤
          ∫ omega, (1 / 2 : ℝ) * K k *
            quadraticVariationApprox X t (n + 1) omega ∂P := by
        apply integral_mono_ae hleft hdom
        filter_upwards with omega
        simpa only [Real.norm_eq_abs] using
          (abs_generalItoQuadraticApprox_sub_le_quadraticVariationApprox
            f (fk k) X t (n + 1) omega (K k) (hK_nonneg k)
              (fun i _hi => hweight k _ _))
      _ = (1 / 2 : ℝ) * K k *
          ∫ omega, quadraticVariationApprox X t (n + 1) omega ∂P := by
        rw [integral_const_mul]
      _ ≤ (1 / 2 : ℝ) * K k * C := by
        exact mul_le_mul_of_nonneg_left (hqbound n)
          (mul_nonneg (by norm_num) (hK_nonneg k))
  · exact hrightInt
  · exact hright

omit [CompleteSpace W] [BorelSpace W] in
/-- A continuous modification of a natural Itô process satisfies Doob's
compact-time `L²` bound.  The proof first controls the increasing union of
dyadic-grid events, transfers those countably many values across the
fixed-time modification relation, and then uses path continuity to detect
every strict excursion on `[0,t]`. -/
theorem IsContinuousProcessModification.naturalIto_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) Y P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let R : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB hsm rfl U
  let A : Set W :=
    {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2}
  let D : Set W :=
    ⋃ n : ℕ, {omega | (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega}
  have hdyadic : ∀ᵐ omega ∂P, ∀ n : ℕ,
      dyadicPartitionSqMax Y t n omega =
        dyadicPartitionSqMax R t n omega := by
    apply ae_all_iff.mpr
    intro n
    exact (dyadicPartitionSqMax_congr_ae hmod.fixedTime_ae_eq t n).symm
  have hAD : A ≤ᵐ[P] D := by
    filter_upwards [hmod.continuous_paths, hdyadic] with omega hcontinuous heq
    intro homega
    change ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2 at homega
    obtain ⟨s, hst, hs⟩ := homega
    obtain ⟨n, hn⟩ := exists_lt_dyadicPartitionSqMax_of_continuous
      Y t omega hcontinuous hst hs
    change omega ∈ D
    simp only [D, Set.mem_iUnion]
    refine ⟨n, ?_⟩
    change (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega
    rw [← heq n]
    exact hn.le
  change (ε : ℝ≥0∞) * P A ≤ ENNReal.ofReal (‖U‖ ^ 2)
  calc
    (ε : ℝ≥0∞) * P A ≤ (ε : ℝ≥0∞) * P D :=
      mul_le_mul_of_nonneg_left (measure_mono_ae hAD) bot_le
    _ ≤ ENNReal.ofReal (‖U‖ ^ 2) := by
      exact naturalItoProcessRepresentative_dyadicPartition_maximal_sq_iUnion
        hB hsm U ε t

omit [CompleteSpace W] [BorelSpace W] in
/-- The difference of continuous modifications of two natural Itô processes
is a continuous modification of the natural Itô process of the integrand
difference.  Representative linearity is used only at fixed times, where it
is valid almost everywhere. -/
theorem naturalItoContinuousModification_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V) YV P) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U - V))
      (fun s omega => YU s omega - YV s omega) P := by
  constructor
  · intro s
    filter_upwards [naturalItoProcessRepresentative_sub_ae hB hsm U V s,
      hU.fixedTime_ae_eq s, hV.fixedTime_ae_eq s]
      with omega hsub hYU hYV
    rw [← hsub, hYU, hYV]
  · filter_upwards [hU.continuous_paths, hV.continuous_paths]
      with omega hYU hYV
    exact hYU.sub hYV

omit [CompleteSpace W] [BorelSpace W] in
/-- Compact-time Doob estimate for the difference of any two continuous
natural-Itô representatives.  This is the uniform-Cauchy estimate consumed
by the predictable-`L²` density construction. -/
theorem naturalItoContinuousModification_sub_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V) YV P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧
        (ε : ℝ) < (YU s omega - YV s omega) ^ 2} ≤
      ENNReal.ofReal (‖U - V‖ ^ 2) := by
  have hmod := naturalItoContinuousModification_sub hB hsm U V hU hV
  exact hmod.naturalIto_compact_maximal_sq_ineq hB hsm (U - V) ε t

omit [CompleteSpace W] [BorelSpace W] in
/-- Borel--Cantelli consequence of the compact maximal estimate.  If the
normalized squared `L²` increments of a sequence of integrands are summable,
then the corresponding continuous representatives eventually have uniformly
small successive increments on `[0,t]`, almost surely. -/
theorem naturalItoContinuousModifications_eventually_uniform_step
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U n)) (Y n) P)
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsum : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ t →
      (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
  let A : ℕ → Set W := fun n =>
    {omega | ∃ s : ℝ≥0, s ≤ t ∧
      (δ n : ℝ) < (Y (n + 1) s omega - Y n s omega) ^ 2}
  have hmeasure : ∀ n,
      P (A n) ≤
        ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) := by
    intro n
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr (ne_of_gt (hδ n))))
      (Or.inl ENNReal.coe_ne_top)).2
    rw [mul_comm]
    exact naturalItoContinuousModification_sub_compact_maximal_sq_ineq
      hB hsm (U (n + 1)) (U n) (hmod (n + 1)) (hmod n) (δ n) t
  have hsumMeasure : (∑' n : ℕ, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hmeasure)
  have hBC := ae_eventually_notMem hsumMeasure
  filter_upwards [hBC] with omega homega
  filter_upwards [homega] with n hn
  intro s hst
  by_contra hle
  exact hn ⟨s, hst, lt_of_not_ge hle⟩

/-- Pointwise canonical limit of a sequence of candidate process
representatives.  The fallback branch is irrelevant on the almost-everywhere
set where the sequence is Cauchy. -/
noncomputable def continuousModificationSequenceLimit
    (Y : ℕ → ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun s omega => completeCauchySeqLimit (fun n => Y n s omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- Closure of continuous natural-Itô modifications under a sufficiently
fast predictable-`L²` limit.  The two summability hypotheses are exactly the
probabilistic Borel--Cantelli bound and the deterministic uniform-Cauchy
bound, respectively. -/
theorem continuousModification_naturalItoProcess_of_fast_tendsto
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (V : PredictableProcessL2 (Filtration.natural B hsm) P)
    (U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U n)) (Y n) P)
    (hUV : Filter.Tendsto U Filter.atTop (nhds V))
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ))) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V)
      (continuousModificationSequenceLimit Y) P := by
  have hcontinuous : ∀ᵐ omega ∂P, ∀ n : ℕ,
      Continuous (fun s => Y n s omega) := by
    apply ae_all_iff.mpr
    intro n
    exact (hmod n).continuous_paths
  have hsteps : ∀ᵐ omega ∂P, ∀ k : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) →
        (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    exact naturalItoContinuousModifications_eventually_uniform_step
      hB hsm U Y hmod δ hδ hsumProbability k
  have huniform : ∀ᵐ omega ∂P, ∀ k : ℕ,
      UniformCauchySeqOn (fun n s => Y n s omega) Filter.atTop
        (Set.Iic (k : ℝ≥0)) := by
    filter_upwards [hsteps] with omega homega
    intro k
    apply uniformCauchySeqOn_of_eventually_dist_le_of_summable
      (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0))
      (fun n => Real.sqrt (δ n : ℝ))
      (fun n => Real.sqrt_nonneg _) hsumUniform
    filter_upwards [homega k] with n hn
    intro s hs
    have hsqrt := Real.sqrt_le_sqrt (hn s hs)
    simpa only [Real.dist_eq, Real.sqrt_sq_eq_abs, abs_sub_comm] using hsqrt
  constructor
  · intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s ≤ (k : ℝ≥0) := exists_nat_ge s
    have hpointwise : ∀ᵐ omega ∂P,
        Filter.Tendsto (fun n => Y n s omega) Filter.atTop
          (nhds (continuousModificationSequenceLimit Y s omega)) := by
      filter_upwards [huniform] with omega homega
      unfold continuousModificationSequenceLimit
      exact tendsto_completeCauchySeqLimit ((homega k).cauchySeq hsk)
    have hYmeas : ∀ n, AEStronglyMeasurable (Y n s) P := by
      intro n
      have hrepmeas : AEStronglyMeasurable
          (naturalItoProcessRepresentative hB hsm rfl (U n) s) P :=
        AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
          (stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm rfl (U n) s).aestronglyMeasurable
      exact hrepmeas.congr ((hmod n).fixedTime_ae_eq s)
    have hrestrict : Filter.Tendsto
        (fun n => predictableTimeRestrict (Filtration.natural B hsm) s (U n))
        Filter.atTop
        (nhds (predictableTimeRestrict (Filtration.natural B hsm) s V)) := by
      change Filter.Tendsto
        ((predictableTimeRestrictCLM (Filtration.natural B hsm) s) ∘ U)
        Filter.atTop
        (nhds (predictableTimeRestrict (Filtration.natural B hsm) s V))
      exact ((predictableTimeRestrictCLM
        (Filtration.natural B hsm) s).continuous.tendsto V).comp hUV
    have hLp : Filter.Tendsto
        (fun n => naturalItoProcess hB hsm rfl (U n) s)
        Filter.atTop (nhds (naturalItoProcess hB hsm rfl V s)) := by
      change Filter.Tendsto
        ((naturalItoIntegral hB hsm rfl) ∘
          fun n => predictableTimeRestrict (Filtration.natural B hsm) s (U n))
        Filter.atTop
        (nhds (naturalItoProcess hB hsm rfl V s))
      exact ((naturalItoIntegral hB hsm rfl).continuous.tendsto
        (predictableTimeRestrict (Filtration.natural B hsm) s V)).comp hrestrict
    have htoTarget : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (naturalItoProcessRepresentative hB hsm rfl V s) := by
      have hraw := tendstoInMeasure_of_tendsto_Lp hLp
      apply TendstoInMeasure.congr_right
        (naturalItoProcess_ae_eq_representative hB hsm rfl V s)
      apply TendstoInMeasure.congr_left _ hraw
      intro n
      exact (naturalItoProcess_ae_eq_representative hB hsm rfl (U n) s).trans
        ((hmod n).fixedTime_ae_eq s)
    have htoLimit : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (continuousModificationSequenceLimit Y s) :=
      tendstoInMeasure_of_tendsto_ae hYmeas hpointwise
    exact tendstoInMeasure_ae_unique htoTarget htoLimit
  · filter_upwards [hcontinuous, huniform] with omega hcont huc
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s < (k : ℝ≥0) := exists_nat_gt s
    have hlimitContinuous : ContinuousOn
        (continuousModificationSequenceLimit Y · omega)
        (Set.Iic (k : ℝ≥0)) := by
      unfold continuousModificationSequenceLimit
      exact continuousOn_completeCauchySeqLimit
        (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0)) (huc k)
          (fun n => (hcont n).continuousOn)
    exact hlimitContinuous.continuousAt (Iic_mem_nhds hsk)

omit [CompleteSpace W] [BorelSpace W] in
/-- An Itô process has measurable fixed-time representatives as soon as its
initial representative is measurable.  The drift integral and selected
stochastic-integral representative are already measurable by construction. -/
theorem IsItoProcess.aestronglyMeasurable_of_initial
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P) (s : ℝ≥0) :
    AEStronglyMeasurable (X s) P := by
  have hdrift : AEStronglyMeasurable
      (integratedDrift μ s) P :=
    (stronglyMeasurable_integratedDrift
      hX.drift_measurable s).aestronglyMeasurable
  have hrhs : AEStronglyMeasurable
      (fun omega => X 0 omega +
        integratedDrift μ s omega +
        hX.integralProcess s omega) P :=
    (hXzero.add hdrift).add (aestronglyMeasurable_integralProcess hX s)
  apply hrhs.congr
  filter_upwards [hX.integral_eq_integralProcess s] with omega heq
  simpa only [integratedDrift] using heq.symm

omit [CompleteSpace W] [BorelSpace W] in
/-- A continuous modification of an Itô process discharges the generic time
Riemann-sum term for any jointly continuous time partial derivative. -/
theorem IsItoProcess.timeApprox_tendstoInMeasure
    {Y : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X μ σ B P)
    (hmod : IsContinuousProcessModification X Y P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1))
      Filter.atTop (generalItoTimeIntegral f Y t) := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact hmod.timeApprox_tendstoInMeasure f hdt t
    (hX.aestronglyMeasurable_of_initial hXzero)

omit [CompleteSpace W] [BorelSpace W] in
/-- With a continuous modification and jointly continuous function/time
derivative, the general Itô reduction no longer needs an endpoint-measurability
or time-sum hypothesis.  The remaining assumptions are precisely the `dX`
limit, weighted bracket limit, and genuinely two-variable Taylor remainder. -/
theorem ito_formula_itoProcess_of_continuousModification
    {Y : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X μ σ B P)
    (hmod : IsContinuousProcessModification X Y P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hdt : Continuous
      (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2))
    (t : ℝ≥0) (I : W → ℝ)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral f Y σ t))
    (hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1)) Filter.atTop
        (fun _ => 0)) :
    ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        generalItoTimeIntegral f Y t omega + I omega +
          generalItoQuadraticIntegral f Y σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hXmeas := hX.aestronglyMeasurable_of_initial hXzero
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
  exact generalIto_formula_ae_of_partition_limits f X t
    (generalItoTimeIntegral f Y t) I
    (generalItoQuadraticIntegral f Y σ t) hendpoint
    (hX.timeApprox_tendstoInMeasure hmod hXzero f hdt t)
    hspace hquadratic hremainder

omit [CompleteSpace W] [BorelSpace W] in
/-- Once a continuous modification is supplied, the proved quadratic
variation of an Itô process forces every `C²` state Taylor-remainder sum to
vanish in probability. -/
theorem IsItoProcess.stateTaylorRemainder_tendstoInMeasure
    {Y : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X μ σ B P)
    (hmod : IsContinuousProcessModification X Y P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStateTaylorRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  exact hmod.stateTaylorRemainder_tendstoInMeasure f hf t
    (integratedDiffusionVariance σ t)
    (hX.aestronglyMeasurable_of_initial hXzero)
    (quadraticVariation_itoProcess hX t)

omit [CompleteSpace W] [BorelSpace W] in
/-- For a separable `C¹_t + C²_x` test function, a continuous modification
of a general Itô process discharges the entire generic Taylor-remainder term. -/
theorem IsItoProcess.generalItoRemainder_timeAddState_tendstoInMeasure
    {Y : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X μ σ B P)
    (hmod : IsContinuousProcessModification X Y P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have htime :=
    itoTimeTaylorRemainderApprox_tendstoInMeasure_zero (P := P) g hg t
  have hstate := hX.stateTaylorRemainder_tendstoInMeasure
    hmod hXzero f hf t
  rw [show
    (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
      X t (n + 1)) =
    (fun n omega =>
      itoTimeTaylorRemainderApprox g t (n + 1) +
        itoStateTaylorRemainderApprox f X t (n + 1) omega) by
    funext n omega
    exact generalItoRemainderApprox_timeAddStateFunction g f
      (hg.differentiable (by norm_num))
      (hf.differentiable (by norm_num)) X t (n + 1) omega]
  simpa only [zero_add] using htime.add_real_noMeas hstate

omit [CompleteSpace W] [BorelSpace W] in
/-- Conditional general-process Itô formula for the full separable
`C¹_t + C²_x` class.  A continuous modification discharges the time and
Taylor-remainder limits; only the defining `dX`-sum limit and the genuinely
missing diffusion-weighted bracket limit remain as explicit hypotheses. -/
theorem ito_formula_timeAddState_itoProcess_of_continuousModification
    {Y : ℝ≥0 → W → ℝ}
    (hX : IsItoProcess X μ σ B P)
    (hmod : IsContinuousProcessModification X Y P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral (timeAddStateFunction g f) X σ t)) :
    ∀ᵐ omega ∂P,
      timeAddStateFunction g f t (X t omega) =
        timeAddStateFunction g f 0 (X 0 omega) +
          generalItoTimeIntegral (timeAddStateFunction g f) X t omega +
          I omega +
          generalItoQuadraticIntegral
            (timeAddStateFunction g f) X σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hXmeas := hX.aestronglyMeasurable_of_initial hXzero
  have hvalueMeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (fun omega => timeAddStateFunction g f s (X s omega)) P := by
    intro s
    unfold timeAddStateFunction
    exact aestronglyMeasurable_const.add
      (hf.continuous.measurable.comp_aemeasurable
        (hXmeas s).aemeasurable).aestronglyMeasurable
  have hendpoint : AEStronglyMeasurable
      (fun omega =>
        timeAddStateFunction g f t (X t omega) -
          timeAddStateFunction g f 0 (X 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  have htimeRaw :=
    generalItoTimeApprox_timeAddStateFunction_tendstoInMeasure
      (P := P) g f hg X t
  have htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop
      (generalItoTimeIntegral (timeAddStateFunction g f) X t) := by
    rw [show
      generalItoTimeIntegral (timeAddStateFunction g f) X t =
        (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) by
      funext omega
      exact generalItoTimeIntegral_timeAddStateFunction g f
        (hg.differentiable (by norm_num)) X t omega]
    exact htimeRaw
  exact generalIto_formula_ae_of_uniformPartition_convergence
    (timeAddStateFunction g f) X σ t I hendpoint htime hspace hquadratic
    (hX.generalItoRemainder_timeAddState_tendstoInMeasure
      hmod hXzero g f hg hf t)

omit [CompleteSpace W] [BorelSpace W] in
/-- The finite-variation drift component of an Itô process has continuous
paths on every finite horizon. -/
theorem IsItoProcess.continuousOn_integratedDrift
    (hX : IsItoProcess X μ σ B P) (T : ℝ≥0) (omega : W) :
    ContinuousOn (fun t => integratedDrift μ t omega)
      (Set.Icc (0 : ℝ≥0) T) := by
  let g : ℝ → ℝ := fun r => μ r.toNNReal omega
  have hcontinuous := continuousOn_nnrealIntegralPrimitive
    (hX.drift_integrable T omega)
  change ContinuousOn (nnrealIntegralPrimitive g) (Set.Icc (0 : ℝ≥0) T)
  exact hcontinuous

omit [CompleteSpace W] [BorelSpace W] in
/-- Local integrability on every finite horizon makes the integrated drift a
globally continuous path on nonnegative time. -/
theorem IsItoProcess.continuous_integratedDrift
    (hX : IsItoProcess X μ σ B P) (omega : W) :
    Continuous (fun t => integratedDrift μ t omega) := by
  rw [continuous_iff_continuousAt]
  intro s
  let T : ℝ≥0 := s + 1
  have hsT : s < T := by
    dsimp only [T]
    exact lt_add_of_pos_right s zero_lt_one
  have hs : s ∈ Set.Icc (0 : ℝ≥0) T := ⟨zero_le, hsT.le⟩
  have hnhds : Set.Icc (0 : ℝ≥0) T ∈ nhds s := by
    rw [show Set.Icc (0 : ℝ≥0) T = Set.Iic T by ext u; simp]
    exact Iic_mem_nhds hsT
  exact (hX.continuousOn_integratedDrift T omega s hs).continuousAt hnhds

/-- Reassemble a candidate continuous representative of an Itô process from
its initial value, continuous drift, and a candidate representative `J` of
the stochastic-integral component. -/
noncomputable def IsItoProcess.continuousRepresentative
    (_hX : IsItoProcess X μ σ B P) (J : ℝ≥0 → W → ℝ) :
    ℝ≥0 → W → ℝ :=
  fun s omega => X 0 omega + integratedDrift μ s omega + J s omega

omit [CompleteSpace W] [BorelSpace W] in
/-- A continuous modification of the selected stochastic-integral process
canonically yields a continuous modification of the full Itô process.  Thus
the remaining representation problem is localized entirely to the natural
Itô integral. -/
theorem IsItoProcess.continuousModification_of_integralProcess
    (hX : IsItoProcess X μ σ B P) (J : ℝ≥0 → W → ℝ)
    (hJ : IsContinuousProcessModification hX.integralProcess J P) :
    IsContinuousProcessModification X (hX.continuousRepresentative J) P := by
  constructor
  · intro s
    filter_upwards [hX.integral_eq_integralProcess s,
      hJ.fixedTime_ae_eq s] with omega hXeq hJeq
    unfold IsItoProcess.continuousRepresentative integratedDrift
    rw [hXeq, hJeq]
  · filter_upwards [hJ.continuous_paths] with omega hJcontinuous
    unfold IsItoProcess.continuousRepresentative
    exact (continuous_const.add
      (hX.continuous_integratedDrift omega)).add hJcontinuous

/-- The explicit continuous Brownian-block representative of the natural Itô
process associated with a finite elementary predictable integrand. -/
noncomputable def elementaryFinsuppItoContinuousRepresentative
    (B : ℝ≥0 → W → ℝ) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    ℝ≥0 → W → ℝ :=
  fun s omega => ∑ x ∈ v.support,
    v x * (x.2.2 : W → ℝ) omega *
      (B (min s x.2.1.1) omega - B (min s x.1) omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- On the finite elementary predictable layer, the selected natural Itô
representative has an explicit continuous modification. -/
theorem elementaryFinsuppItoContinuousModification
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P v))
      (elementaryFinsuppItoContinuousRepresentative B hsm v) P := by
  constructor
  · intro s
    change naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P v) s =ᵐ[P]
      (fun omega => ∑ x ∈ v.support, v x * (x.2.2 : W → ℝ) omega *
        (B (min s x.2.1.1) omega - B (min s x.1) omega))
    exact naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
      hB.toIsPreBrownianReal hsm v s
  · filter_upwards [hB.cont] with omega hBcontinuous
    unfold elementaryFinsuppItoContinuousRepresentative
    apply continuous_finsetSum
    intro x _hx
    exact continuous_const.mul
      ((hBcontinuous.comp (continuous_id.min continuous_const)).sub
        (hBcontinuous.comp (continuous_id.min continuous_const)))

omit [CompleteSpace W] [BorelSpace W] in
/-- Every predictable `L²` integrand is the norm limit of elementary
integrands whose natural Itô processes carry the explicit continuous
Brownian-block representatives above.  Together with
`naturalItoContinuousModifications_eventually_uniform_step`, this reduces the
general continuous-modification construction to the fast-subsequence and
uniform-limit argument implemented below. -/
theorem exists_elementaryFinsupp_continuousModifications_tendsto
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ∃ v : ℕ →
        (ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ),
      Filter.Tendsto
        (fun n => elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P (v n))
        Filter.atTop (nhds U) ∧
      ∀ n, IsContinuousProcessModification
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
          (elementaryFinsuppToPredictable
            (Filtration.natural B hsm) P (v n)))
        (elementaryFinsuppItoContinuousRepresentative B hsm (v n)) P := by
  let e := elementaryFinsuppToPredictable (Filtration.natural B hsm) P
  have hUdense : U ∈ closure (Set.range e) :=
    (denseRange_elementaryFinsuppToPredictable (P := P)
      (Filtration.natural B hsm)) U
  obtain ⟨Uk, hUkRange, hUk⟩ := mem_closure_iff_seq_limit.mp hUdense
  choose v hv using hUkRange
  refine ⟨v, ?_, ?_⟩
  · convert hUk using 1
    funext n
    exact hv n
  · intro n
    exact elementaryFinsuppItoContinuousModification hB hsm (v n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Quantitative version of elementary density: the approximation rate may
be prescribed arbitrarily, as long as every requested radius is positive.
This is the form used to choose a Borel--Cantelli-fast sequence. -/
theorem exists_elementaryFinsupp_continuousModifications_dist_lt
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ v : ℕ →
        (ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ),
      (∀ n, dist U
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P (v n)) < r n) ∧
      ∀ n, IsContinuousProcessModification
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
          (elementaryFinsuppToPredictable
            (Filtration.natural B hsm) P (v n)))
        (elementaryFinsuppItoContinuousRepresentative B hsm (v n)) P := by
  have hdense := denseRange_elementaryFinsuppToPredictable (P := P)
    (Filtration.natural B hsm)
  choose v hv using fun n => hdense.exists_dist_lt U (hr n)
  refine ⟨v, hv, ?_⟩
  intro n
  exact elementaryFinsuppItoContinuousModification hB hsm (v n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Every natural Itô process has a continuous modification.  Choose
elementary predictable integrands within `8⁻ⁿ` of the target.  Their
successive squared `L²` distances are dominated by `4 · 64⁻ⁿ`; with
thresholds `4⁻ⁿ`, both series required by the fast-limit closure theorem
are geometric. -/
theorem exists_continuousModification_naturalItoProcess
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (V : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ∃ Y : ℝ≥0 → W → ℝ, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl V) Y P := by
  let r : ℕ → ℝ := fun n => (1 / 8 : ℝ) ^ n
  obtain ⟨v, hv, hvmod⟩ :=
    exists_elementaryFinsupp_continuousModifications_dist_lt
      hB hsm V r (by intro n; simp only [r]; positivity)
  let U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P :=
    fun n => elementaryFinsuppToPredictable
      (Filtration.natural B hsm) P (v n)
  let Y : ℕ → ℝ≥0 → W → ℝ :=
    fun n => elementaryFinsuppItoContinuousRepresentative B hsm (v n)
  let δ : ℕ → ℝ≥0 := fun n => (1 / 4 : ℝ≥0) ^ n
  have hdist : ∀ n, dist V (U n) < (1 / 8 : ℝ) ^ n := by
    intro n
    simpa only [U, r] using hv n
  have hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl (U n))
      (Y n) P := by
    intro n
    simpa only [U, Y] using hvmod n
  have hUV : Filter.Tendsto U Filter.atTop (nhds V) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hpow : Filter.Tendsto (fun n : ℕ => (1 / 8 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hpow ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hr : (1 / 8 : ℝ) ^ n < ε := by
      have hrabs := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (pow_nonneg (by norm_num) n)] at hrabs
      exact hrabs
    have hn := hdist n
    rw [dist_comm] at hn
    exact hn.trans hr
  have hδ : ∀ n, 0 < δ n := by
    intro n
    simp only [δ]
    positivity
  have hsq : ∀ n, ‖U (n + 1) - U n‖ ^ 2 ≤
      4 * (1 / 64 : ℝ) ^ n := by
    intro n
    have hstep : ‖U (n + 1) - U n‖ < 2 * (1 / 8 : ℝ) ^ n := by
      calc
        ‖U (n + 1) - U n‖ = dist (U (n + 1)) (U n) :=
          (dist_eq_norm _ _).symm
        _ ≤ dist (U (n + 1)) V + dist V (U n) := dist_triangle _ _ _
        _ < (1 / 8 : ℝ) ^ (n + 1) + (1 / 8 : ℝ) ^ n :=
          add_lt_add (by simpa only [dist_comm] using hdist (n + 1))
            (hdist n)
        _ ≤ 2 * (1 / 8 : ℝ) ^ n := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) n]
    have hsq' : ‖U (n + 1) - U n‖ ^ 2 ≤
        (2 * (1 / 8 : ℝ) ^ n) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hstep.le
    calc
      ‖U (n + 1) - U n‖ ^ 2 ≤ (2 * (1 / 8 : ℝ) ^ n) ^ 2 := hsq'
      _ = 4 * (1 / 64 : ℝ) ^ n := by
        have hp : ((1 / 8 : ℝ) ^ n) ^ 2 = (1 / 64 : ℝ) ^ n := by
          rw [show (1 / 64 : ℝ) = (1 / 8 : ℝ) ^ 2 by norm_num]
          simp only [← pow_mul, Nat.mul_comm]
        rw [mul_pow, hp]
        norm_num
  have hnormalized : ∀ n,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) ≤
        4 * (1 / 16 : ℝ≥0∞) ^ n := by
    intro n
    change ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
        ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
      4 * (1 / 16 : ℝ≥0∞) ^ n
    calc
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
          ENNReal.ofReal (4 * (1 / 64 : ℝ) ^ n) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact hsq n
      _ = 4 * (1 / 16 : ℝ≥0∞) ^ n := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.coe_pow]
        have hofReal : ENNReal.ofReal (1 / 64 : ℝ) =
            (1 / 64 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)]
          norm_num
        rw [hofReal]
        norm_num only [ENNReal.ofReal_ofNat, ENNReal.coe_div,
          ENNReal.coe_one, ENNReal.coe_ofNat]
        rw [mul_div_assoc]
        congr 1
        simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, ← mul_pow]
        congr 1
        simp only [mul_one, inv_inv]
        change ((4 : ℝ≥0) : ℝ≥0∞) *
            (((64 : ℝ≥0) : ℝ≥0∞))⁻¹ =
          (((16 : ℝ≥0) : ℝ≥0∞))⁻¹
        rw [← ENNReal.coe_inv (by norm_num : (64 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_inv (by norm_num : (16 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_mul]
        norm_num
  have hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (b := ∑' n : ℕ, 4 * (1 / 16 : ℝ≥0∞) ^ n)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.inv_ne_top.mpr
          (ne_of_gt (tsub_pos_iff_lt.mpr
            (by norm_num : (1 / 16 : ℝ≥0∞) < 1)))
    · exact ENNReal.tsum_le_tsum hnormalized
  have hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ)) := by
    change Summable (fun n : ℕ => Real.sqrt ((1 / 4 : ℝ) ^ n))
    apply (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
      (by positivity) (by norm_num)).congr
    intro n
    have hp : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
      simp only [← pow_mul, Nat.mul_comm]
    rw [hp, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  exact ⟨continuousModificationSequenceLimit Y,
    continuousModification_naturalItoProcess_of_fast_tendsto
      hB.toIsPreBrownianReal hsm V U Y hmod hUV δ hδ
        hsumProbability hsumUniform⟩

/-- Completed fine-grid cells before a deterministic time converge to the
stopped bracket of a natural Itô integral.  Unlike the earlier rational-grid
prefix theorem, the partition size is unrestricted; continuity has removed
the unique boundary-crossing cell. -/
theorem quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t a : ℝ≥0) (ha : a ≤ t) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1) a)
      Filter.atTop (predictableQuadraticVariation hsm U (min t a)) := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  obtain ⟨Y, hmod⟩ :=
    exists_continuousModification_naturalItoProcess hB hsm U
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono
      ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U s).aestronglyMeasurable
  have hstop :=
    quadraticVariation_stopped_naturalItoProcessRepresentative_bracket
      hB hsm U a t
  exact hmod.quadraticVariationBeforeStopApprox_tendstoInMeasure
    hMmeas t a ⟨bot_le, ha⟩
      (predictableQuadraticVariation hsm U (min t a)) hstop

/-- Differences of completed-cell stopped sums converge on arbitrary uniform
partition sizes to the corresponding natural-Itô bracket block. -/
theorem quadraticVariationBeforeStop_block_naturalItoProcess_tendstoInMeasure
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t a b : ℝ≥0) (ha : a ≤ t) (hb : b ≤ t) :
    TendstoInMeasure P
      (fun n omega =>
        quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) b omega -
          quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) a omega)
      Filter.atTop (fun omega =>
        predictableQuadraticVariation hsm U (min t b) omega -
          predictableQuadraticVariation hsm U (min t a) omega) := by
  exact (quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
    hB hsm U t b hb).sub_real_noMeas
      (quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
        hB hsm U t a ha)

/-- A finite random step weight integrates against every completed-cell
natural-Itô bracket block on arbitrary uniform partition sizes.  Boundary
cells have already been removed in probability, so there is no divisibility
or common-refinement restriction. -/
theorem quadraticVariationBeforeStop_block_finset_weighted_naturalItoProcess
    {I : Type*}
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (S : Finset I) (a b : I → ℝ≥0) (c : I → W → ℝ)
    (hcmeas : ∀ i ∈ S, AEStronglyMeasurable (c i) P)
    (t : ℝ≥0) (ha : ∀ i ∈ S, a i ≤ t) (hb : ∀ i ∈ S, b i ≤ t) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ S, c i omega *
        (quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (b i) omega -
          quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (a i) omega))
      Filter.atTop (fun omega => ∑ i ∈ S, c i omega *
        (predictableQuadraticVariation hsm U (min t (b i)) omega -
          predictableQuadraticVariation hsm U (min t (a i)) omega)) := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono
      ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U s).aestronglyMeasurable
  apply tendstoInMeasure_finset_sum_mul_fixed_real S
    (fun i n omega =>
      quadraticVariationBeforeStopApprox M t (n + 1) (b i) omega -
        quadraticVariationBeforeStopApprox M t (n + 1) (a i) omega)
    (fun i omega =>
      predictableQuadraticVariation hsm U (min t (b i)) omega -
        predictableQuadraticVariation hsm U (min t (a i)) omega) c
  · intro i hi
    exact quadraticVariationBeforeStop_block_naturalItoProcess_tendstoInMeasure
      hB hsm U t (a i) (b i) (ha i hi) (hb i hi)
  · intro i _hi n
    exact (aestronglyMeasurable_quadraticVariationBeforeStopApprox
      hMmeas t (n + 1) (b i)).sub
        (aestronglyMeasurable_quadraticVariationBeforeStopApprox
          hMmeas t (n + 1) (a i))
  · exact hcmeas

/-- Complete `k`-step random left weights now integrate the natural-Itô
bracket on every refining partition size, rather than only on the subsequence
of partition sizes divisible by `k`. -/
theorem quadraticVariation_completedStepWeight_naturalItoProcess
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) (k : ℕ) (hk : 0 < k) (c : ℕ → W → ℝ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range k, c i omega *
        (quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (uniformPartitionTime t k (i + 1)) omega -
          quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (uniformPartitionTime t k i) omega))
      Filter.atTop (fun omega => ∑ i ∈ Finset.range k, c i omega *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t k (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t k i) omega)) := by
  have hraw :=
    quadraticVariationBeforeStop_block_finset_weighted_naturalItoProcess
      hB hsm U (Finset.range k)
      (fun i => uniformPartitionTime t k i)
      (fun i => uniformPartitionTime t k (i + 1)) c hcmeas t
      (fun i hi =>
        (uniformPartitionTime_mem_Icc_of_le t hk
          ((Nat.le_add_right i 1).trans (Finset.mem_range.mp hi))).2)
      (fun i hi =>
        (uniformPartitionTime_mem_Icc_of_le t hk
          (Finset.mem_range.mp hi)).2)
  apply hraw.congr_right
  filter_upwards with omega
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ k := Finset.mem_range.mp hi
  have hi0 : i ≤ k := (Nat.le_add_right i 1).trans hi1
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le t hk hi1).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le t hk hi0).2]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- The actual Itô second-derivative weighted sum differs from the completed
coarse-step freezing by at most half the derivative-weight error times the
unweighted quadratic variation. -/
theorem abs_generalItoQuadraticApprox_sub_completedStep_le
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n k : ℕ) (K : ℝ) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega) -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
              (X (uniformPartitionTime t k j) omega)
          else 0| ≤ K)
    :
    |generalItoQuadraticApprox f X t n omega -
      ∑ j ∈ Finset.range k,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k j : ℝ)
          (X (uniformPartitionTime t k j) omega)) *
        (quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k j) omega)| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox X t n omega := by
  unfold generalItoQuadraticApprox
  apply abs_weightedQuadraticVariation_sub_completedBlocks_le
    X t n k
      (fun i omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega))
      (fun j omega => (1 / 2 : ℝ) * itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (X (uniformPartitionTime t k j) omega))
      ((1 / 2 : ℝ) * K) omega
  intro i hi
  have hsum :
      (∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t k j : ℝ)
            (X (uniformPartitionTime t k j) omega)
        else 0) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j <
              uniformPartitionTime t n (i + 1) ∧
            uniformPartitionTime t n (i + 1) ≤
              uniformPartitionTime t k (j + 1) then
          itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
            (X (uniformPartitionTime t k j) omega)
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    split_ifs <;> simp
  rw [hsum, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left (hweight i hi) (by norm_num)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- It suffices to compare the fine left-endpoint derivative weight with the
coarse left endpoint of every active right-endpoint block.  Positivity of
the horizon ensures every fine right endpoint belongs to exactly one block. -/
theorem abs_generalItoQuadraticApprox_sub_completedStep_le_of_blockWeight
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (ht : 0 < t) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (K : ℝ)
    (omega : W)
    (hweight : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < uniformPartitionTime t n (i + 1) ∧
        uniformPartitionTime t n (i + 1) ≤
          uniformPartitionTime t k (j + 1) →
      |itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
          (X (uniformPartitionTime t n i) omega) -
        itoSpaceSecondDerivative f (uniformPartitionTime t k j : ℝ)
          (X (uniformPartitionTime t k j) omega)| ≤ K)
    :
    |generalItoQuadraticApprox f X t n omega -
      ∑ j ∈ Finset.range k,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k j : ℝ)
          (X (uniformPartitionTime t k j) omega)) *
        (quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticVariationBeforeStopApprox X t n
            (uniformPartitionTime t k j) omega)| ≤
      (1 / 2 : ℝ) * K * quadraticVariationApprox X t n omega := by
  apply abs_generalItoQuadraticApprox_sub_completedStep_le
    f X t n k K omega
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hr0 : 0 < uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    positivity
  have hrt : uniformPartitionTime t n (i + 1) ≤ t :=
    (uniformPartitionTime_mem_Icc_of_le t hn hi1).2
  apply abs_sub_uniformPartition_rightEndpoint_step_sum_le
    t (uniformPartitionTime t n (i + 1)) k hk hr0 hrt
      (itoSpaceSecondDerivative f (uniformPartitionTime t n i : ℝ)
        (X (uniformPartitionTime t n i) omega))
      (fun j => itoSpaceSecondDerivative f
        (uniformPartitionTime t k j : ℝ)
        (X (uniformPartitionTime t k j) omega)) K
  intro j hj hactive
  exact hweight i hi j hj hactive

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Along a continuous path, the second-derivative weights at a fine left
endpoint and at the left endpoint of its active coarse block become uniformly
close as both meshes vanish. -/
theorem generalItoSecondDerivative_activeBlockWeight_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
        ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (k + 1),
          uniformPartitionTime t (k + 1) j <
              uniformPartitionTime t (n + 1) (i + 1) ∧
            uniformPartitionTime t (n + 1) (i + 1) ≤
              uniformPartitionTime t (k + 1) (j + 1) →
          |itoSpaceSecondDerivative f
              (uniformPartitionTime t (n + 1) i : ℝ)
              (X (uniformPartitionTime t (n + 1) i) omega) -
            itoSpaceSecondDerivative f
              (uniformPartitionTime t (k + 1) j : ℝ)
              (X (uniformPartitionTime t (k + 1) j) omega)| < epsilon := by
  let g : ℝ≥0 → ℝ := fun s =>
    itoSpaceSecondDerivative f (s : ℝ) (X s omega)
  have hpair : ContinuousOn
      (fun s : ℝ≥0 => ((s : ℝ), X s omega)) (Set.Icc 0 t) :=
    NNReal.continuous_coe.continuousOn.prodMk hpath
  have hg : ContinuousOn g (Set.Icc 0 t) := by
    exact hsecond.comp_continuousOn hpair
  have huc : UniformContinuousOn g (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  intro epsilon hepsilon
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Filter.Tendsto
      (fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun m : ℕ => ((t / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0))
      Filter.atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv (eta / 2) (half_pos heta)
  refine ⟨N, ?_⟩
  intro k n hkN hnN
  have hkmesh : ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN k hkN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  have hnmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN n hnN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  intro i hi j hj hactive
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hi0 : i ≤ n + 1 :=
    (Nat.le_add_right i 1).trans (Finset.mem_range.mp hi)
  have hj0 : j ≤ k + 1 :=
    (Nat.le_add_right j 1).trans (Finset.mem_range.mp hj)
  have hifine := uniformPartitionTime_mem_Icc_of_le t hnpos hi0
  have hjcoarse := uniformPartitionTime_mem_Icc_of_le t hkpos hj0
  have hdistLe := dist_uniformPartition_left_to_active_coarse_left_le
    t (n + 1) (k + 1) i j hnpos hkpos hactive
  have hdist : dist (uniformPartitionTime t (n + 1) i)
      (uniformPartitionTime t (k + 1) j) < eta := by
    calc
      _ ≤ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
          ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := hdistLe
      _ < eta / 2 + eta / 2 := add_lt_add hnmesh hkmesh
      _ = eta := by ring
  have hout := hmod
    (uniformPartitionTime t (n + 1) i) hifine
    (uniformPartitionTime t (k + 1) j) hjcoarse hdist
  simpa only [g, Real.dist_eq] using hout

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Consequently, on every continuous path the actual weighted quadratic
sum is eventually controlled by an arbitrarily small multiple of the
unweighted quadratic variation relative to completed coarse-step sums. -/
theorem generalItoQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ K : ℝ, 0 < K → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
      |generalItoQuadraticApprox f X t (n + 1) omega -
        ∑ j ∈ Finset.range (k + 1),
          ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
            (uniformPartitionTime t (k + 1) j : ℝ)
            (X (uniformPartitionTime t (k + 1) j) omega)) *
          (quadraticVariationBeforeStopApprox X t (n + 1)
              (uniformPartitionTime t (k + 1) (j + 1)) omega -
            quadraticVariationBeforeStopApprox X t (n + 1)
              (uniformPartitionTime t (k + 1) j) omega)| ≤
        (1 / 2 : ℝ) * K *
          quadraticVariationApprox X t (n + 1) omega := by
  intro K hK
  obtain ⟨N, hN⟩ := generalItoSecondDerivative_activeBlockWeight_eventually_small
    f X t omega hsecond hpath K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  apply abs_generalItoQuadraticApprox_sub_completedStep_le_of_blockWeight
    f X t ht (n + 1) (k + 1) (Nat.zero_lt_succ n) (Nat.zero_lt_succ k) K omega
  intro i hi j hj hactive
  simpa only using (hN k n hk hn i hi j hj hactive).le

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The two-scale completed-step estimate transfers simultaneously over all
uniform grids from a continuous modification to the original representative. -/
theorem IsContinuousProcessModification.generalItoQuadraticApprox_sub_completedStep_eventually_le
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification X Y P)
    (f : ℝ → ℝ → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2)) :
    ∀ᵐ omega ∂P, ∀ K : ℝ, 0 < K → ∃ N : ℕ,
      ∀ k n, N ≤ k → N ≤ n →
        |generalItoQuadraticApprox f X t (n + 1) omega -
          ∑ j ∈ Finset.range (k + 1),
            ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
              (uniformPartitionTime t (k + 1) j : ℝ)
              (X (uniformPartitionTime t (k + 1) j) omega)) *
            (quadraticVariationBeforeStopApprox X t (n + 1)
                (uniformPartitionTime t (k + 1) (j + 1)) omega -
              quadraticVariationBeforeStopApprox X t (n + 1)
                (uniformPartitionTime t (k + 1) j) omega)| ≤
          (1 / 2 : ℝ) * K *
            quadraticVariationApprox X t (n + 1) omega := by
  have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
  filter_upwards [hmod.continuous_paths, hgrid] with omega hcontinuous hagree
  intro K hK
  obtain ⟨N, hYbound⟩ :=
    generalItoQuadraticApprox_sub_completedStep_eventually_le_of_continuousPath
      f Y t ht omega hsecond hcontinuous.continuousOn K hK
  refine ⟨N, fun k n hk hn => ?_⟩
  have hgeneral : generalItoQuadraticApprox f X t (n + 1) omega =
      generalItoQuadraticApprox f Y t (n + 1) omega := by
    unfold generalItoQuadraticApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hagree n i, hagree n (i + 1)]
  have hqv : quadraticVariationApprox X t (n + 1) omega =
      quadraticVariationApprox Y t (n + 1) omega := by
    unfold quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hagree n i, hagree n (i + 1)]
  have hbefore : ∀ a : ℝ≥0,
      quadraticVariationBeforeStopApprox X t (n + 1) a omega =
        quadraticVariationBeforeStopApprox Y t (n + 1) a omega := by
    intro a
    unfold quadraticVariationBeforeStopApprox
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hright : uniformPartitionTime t (n + 1) (i + 1) ≤ a
    · simp only [hright, ↓reduceIte]
      rw [hagree n i, hagree n (i + 1)]
    · simp only [hright, ↓reduceIte]
  have hcoarse :
      (∑ j ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) j : ℝ)
          (X (uniformPartitionTime t (k + 1) j) omega)) *
        (quadraticVariationBeforeStopApprox X t (n + 1)
            (uniformPartitionTime t (k + 1) (j + 1)) omega -
          quadraticVariationBeforeStopApprox X t (n + 1)
            (uniformPartitionTime t (k + 1) j) omega)) =
      ∑ j ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) j : ℝ)
          (Y (uniformPartitionTime t (k + 1) j) omega)) *
        (quadraticVariationBeforeStopApprox Y t (n + 1)
            (uniformPartitionTime t (k + 1) (j + 1)) omega -
          quadraticVariationBeforeStopApprox Y t (n + 1)
            (uniformPartitionTime t (k + 1) j) omega) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hagree k j, hbefore, hbefore]
  rw [hgeneral, hqv, hcoarse]
  exact hYbound k n hk hn

/-- Freezing the continuous Itô second-derivative weight on a coarse uniform
partition gives a random step integrand whose completed fine-cell sums
converge on every refining partition size to the corresponding bracket
Riemann sum.  This is the dense step-weight core of the quadratic term. -/
theorem generalItoQuadratic_completedStep_naturalItoProcess_tendstoInMeasure
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    TendstoInMeasure P
      (fun n omega => ∑ i ∈ Finset.range k,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k i : ℝ)
          (naturalItoProcessRepresentative hB.toIsPreBrownianReal
            hsm rfl U (uniformPartitionTime t k i) omega)) *
        (quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (uniformPartitionTime t k (i + 1)) omega -
          quadraticVariationBeforeStopApprox
            (naturalItoProcessRepresentative hB.toIsPreBrownianReal
              hsm rfl U) t (n + 1) (uniformPartitionTime t k i) omega))
      Filter.atTop (fun omega => ∑ i ∈ Finset.range k,
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t k i : ℝ)
          (naturalItoProcessRepresentative hB.toIsPreBrownianReal
            hsm rfl U (uniformPartitionTime t k i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t k (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t k i) omega)) := by
  apply quadraticVariation_completedStepWeight_naturalItoProcess
    hB hsm U t k hk
  intro i _hi
  have hM : AEStronglyMeasurable
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
        (uniformPartitionTime t k i)) P :=
    AEStronglyMeasurable.mono
      ((Filtration.natural B hsm).le (uniformPartitionTime t k i))
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U
          (uniformPartitionTime t k i)).aestronglyMeasurable
  have hpair : AEStronglyMeasurable
      (fun omega => ((uniformPartitionTime t k i : ℝ),
        naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
          (uniformPartitionTime t k i) omega)) P :=
    aestronglyMeasurable_const.prodMk hM
  exact aestronglyMeasurable_const.mul
    (hsecond.comp_aestronglyMeasurable hpair)

/-- The completed-step bracket approximation closes the actual continuous
weight along a natural Itô process once its coarse bracket Riemann sums have
a limit.  No measurable choice of pathwise mesh cutoffs is needed: the
two-scale subsequence theorem combines the uniform pathwise modulus with the
tight (indeed convergent) unweighted quadratic sums. -/
theorem generalItoQuadratic_naturalItoProcess_tendstoInMeasure_of_bracketStep_limit
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (f : ℝ → ℝ → ℝ)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (t : ℝ≥0) (ht : 0 < t) (G : W → ℝ)
    (hG : TendstoInMeasure P
      (fun k omega => ∑ i ∈ Finset.range (k + 1),
        ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
          (uniformPartitionTime t (k + 1) i : ℝ)
          (naturalItoProcessRepresentative hB.toIsPreBrownianReal
            hsm rfl U (uniformPartitionTime t (k + 1) i) omega)) *
        (predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) (i + 1)) omega -
          predictableQuadraticVariation hsm U
            (uniformPartitionTime t (k + 1) i) omega))
      Filter.atTop G) :
    TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1)) Filter.atTop G := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  let F : ℕ → ℕ → W → ℝ := fun k n =>
    generalItoQuadraticCompletedStepApprox f M t (n + 1) (k + 1)
  let Gk : ℕ → W → ℝ := fun k omega => ∑ i ∈ Finset.range (k + 1),
    ((1 / 2 : ℝ) * itoSpaceSecondDerivative f
      (uniformPartitionTime t (k + 1) i : ℝ)
      (M (uniformPartitionTime t (k + 1) i) omega)) *
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
    have hraw :=
      generalItoQuadratic_completedStep_naturalItoProcess_tendstoInMeasure
        hB hsm U f hsecond t (k + 1) (Nat.zero_lt_succ k)
    change TendstoInMeasure P
      (fun n => generalItoQuadraticCompletedStepApprox f M t (n + 1) (k + 1))
      Filter.atTop (Gk k)
    apply hraw.congr_left
    intro n
    filter_upwards with omega
    rfl
  obtain ⟨Y, hmod⟩ := exists_continuousModification_naturalItoProcess hB hsm U
  apply TendstoInMeasure.of_ae_two_scale_uniform_control
    (P := P)
    (f := fun n => generalItoQuadraticApprox f M t (n + 1))
    (q := fun n => quadraticVariationApprox M t (n + 1))
    (F := F) (G := Gk)
    (qlim := predictableQuadraticVariation hsm U t)
  · intro n
    exact aestronglyMeasurable_generalItoQuadraticApprox
      f hsecond M hMmeas t (n + 1)
  · exact hFG
  · simpa only [Gk, M] using hG
  · simpa only [HasQuadraticVariationInProbabilityAt, M] using
      (quadraticVariation_naturalItoProcessRepresentative hB hsm U t)
  · intro n omega
    exact quadraticVariationApprox_nonneg M t (n + 1) omega
  · have hbound :=
      hmod.generalItoQuadraticApprox_sub_completedStep_eventually_le
        f t ht hsecond
    filter_upwards [hbound] with omega homega
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := homega (2 * epsilon) (mul_pos (by norm_num) hepsilon)
    refine ⟨N, fun k n hk hn => ?_⟩
    have hraw := hN k n hk hn
    simpa only [F, M, generalItoQuadraticCompletedStepApprox,
      Real.norm_eq_abs, mul_assoc,
      show (1 / 2 : ℝ) * (2 * epsilon) = epsilon by ring] using hraw

omit [CompleteSpace W] [BorelSpace W] in
/-- Every Itô process has a continuous modification: combine the continuous
natural-Itô representative above with the pathwise continuous drift
primitive and the initial value. -/
theorem IsItoProcess.exists_continuousModification
    (hX : IsItoProcess X μ σ B P) :
    ∃ Y : ℝ≥0 → W → ℝ, IsContinuousProcessModification X Y P := by
  obtain ⟨J, hJ⟩ := exists_continuousModification_naturalItoProcess
    hX.driver_brownian hX.driver_stronglyMeasurable hX.diffusion
  have hJ' : IsContinuousProcessModification hX.integralProcess J P := by
    simpa only [IsItoProcess.integralProcess, stochasticIntegralProcess] using hJ
  exact ⟨hX.continuousRepresentative J,
    hX.continuousModification_of_integralProcess J hJ'⟩

/-- A canonical (classically chosen) continuous version of an Itô process.
This lets later constructions use a concrete process rather than repeatedly
carrying an existential modification witness. -/
noncomputable def IsItoProcess.continuousVersion
    (hX : IsItoProcess X μ σ B P) : ℝ≥0 → W → ℝ :=
  Classical.choose hX.exists_continuousModification

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical continuous version is a modification of the original Itô
process. -/
theorem IsItoProcess.continuousVersion_spec
    (hX : IsItoProcess X μ σ B P) :
    IsContinuousProcessModification X hX.continuousVersion P :=
  Classical.choose_spec hX.exists_continuousModification

omit [CompleteSpace W] [BorelSpace W] in
/-- Any continuous modification agrees almost surely, simultaneously at all
times, with the canonical continuous version. -/
theorem IsItoProcess.indistinguishable_continuousVersion
    (hX : IsItoProcess X μ σ B P) {Y : ℝ≥0 → W → ℝ}
    (hY : IsContinuousProcessModification X Y P) :
    ∀ᵐ omega ∂P, ∀ s : ℝ≥0,
      Y s omega = hX.continuousVersion s omega :=
  hY.indistinguishable hX.continuousVersion_spec

omit [CompleteSpace W] [BorelSpace W] in
/-- The generic time-derivative Riemann sums converge unconditionally when
their target is evaluated on the canonical continuous version. -/
theorem IsItoProcess.timeApprox_tendstoInMeasure_continuousVersion
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ → ℝ)
    (hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoTimeApprox f X t (n + 1)) Filter.atTop
      (generalItoTimeIntegral f hX.continuousVersion t) :=
  hX.timeApprox_tendstoInMeasure hX.continuousVersion_spec
    hXzero f hdt t

omit [CompleteSpace W] [BorelSpace W] in
/-- The state Taylor remainder vanishes for every Itô process; the required
continuous modification is constructed internally. -/
theorem IsItoProcess.stateTaylorRemainder_tendstoInMeasure_unconditional
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => itoStateTaylorRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  obtain ⟨Y, hmod⟩ := hX.exists_continuousModification
  exact hX.stateTaylorRemainder_tendstoInMeasure hmod hXzero f hf t

omit [CompleteSpace W] [BorelSpace W] in
/-- The full genuinely two-variable Taylor remainder vanishes for every Itô
process.  The continuous modification and its quadratic-variation limit are
constructed internally, so downstream formula theorems do not need either as
an additional hypothesis. -/
theorem IsItoProcess.generalItoRemainder_tendstoInMeasure_unconditional
    (hX : IsItoProcess X μ σ B P)
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
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox f X t (n + 1))
      Filter.atTop (fun _ => 0) := by
  obtain ⟨Y, hmod⟩ := hX.exists_continuousModification
  exact hmod.generalRemainder_tendstoInMeasure
    f hf htdiff hslice hdt hdx hsecond t
    (integratedDiffusionVariance σ t)
    (hX.aestronglyMeasurable_of_initial hXzero)
    (quadraticVariation_itoProcess hX t)

omit [CompleteSpace W] [BorelSpace W] in
/-- General Itô reduction for a genuinely two-variable test function.  The
time and Taylor-remainder limits are unconditional; only the concrete `dX`
sum and diffusion-weighted quadratic-variation limit remain as hypotheses. -/
theorem ito_formula_itoProcess
    (hX : IsItoProcess X μ σ B P)
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
    (t : ℝ≥0) (I : W → ℝ)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral f hX.continuousVersion σ t)) :
    ∀ᵐ omega ∂P,
      f t (X t omega) = f 0 (X 0 omega) +
        generalItoTimeIntegral f hX.continuousVersion t omega + I omega +
          generalItoQuadraticIntegral
            f hX.continuousVersion σ t omega := by
  exact ito_formula_itoProcess_of_continuousModification
    hX hX.continuousVersion_spec hXzero f hf hdt t I hspace hquadratic
      (hX.generalItoRemainder_tendstoInMeasure_unconditional
        hXzero f hf htdiff hslice hdt hdx hsecond t)

omit [CompleteSpace W] [BorelSpace W] in
/-- If the diffusion-weighted quadratic sums have their intended limit, the
exact partition identity constructs the `dX` limit and proves the full general
Itô formula.  Thus weighted quadratic variation is the sole remaining
analytic hypothesis in this existential formulation. -/
theorem exists_ito_formula_itoProcess_of_quadratic_limit
    (hX : IsItoProcess X μ σ B P)
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
    (t : ℝ≥0)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox f X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral f hX.continuousVersion σ t)) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox f X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f t (X t omega) = f 0 (X 0 omega) +
          generalItoTimeIntegral f hX.continuousVersion t omega + I omega +
            generalItoQuadraticIntegral
              f hX.continuousVersion σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hXmeas := hX.aestronglyMeasurable_of_initial hXzero
  have hvalueMeas : ∀ s : ℝ≥0,
      AEStronglyMeasurable (fun omega => f s (X s omega)) P := by
    intro s
    have hp : AEStronglyMeasurable
        (fun omega => ((s : ℝ), X s omega)) P :=
      aestronglyMeasurable_const.prodMk (hXmeas s)
    exact hf.comp_aestronglyMeasurable hp
  have hendpoint : AEStronglyMeasurable
      (fun omega => f t (X t omega) - f 0 (X 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  exact generalIto_exists_space_limit_and_formula f X t
    (generalItoTimeIntegral f hX.continuousVersion t)
    (generalItoQuadraticIntegral f hX.continuousVersion σ t)
    hendpoint
    (hX.timeApprox_tendstoInMeasure_continuousVersion hXzero f hdt t)
    hquadratic
    (hX.generalItoRemainder_tendstoInMeasure_unconditional
      hXzero f hf htdiff hslice hdt hdx hsecond t)

omit [CompleteSpace W] [BorelSpace W] in
/-- The complete Taylor remainder for a separable `C¹_t + C²_x` test
function vanishes for every Itô process, without a modification hypothesis. -/
theorem IsItoProcess.generalItoRemainder_timeAddState_tendstoInMeasure_unconditional
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop (fun _ => 0) := by
  obtain ⟨Y, hmod⟩ := hX.exists_continuousModification
  exact hX.generalItoRemainder_timeAddState_tendstoInMeasure
    hmod hXzero g f hg hf t

omit [CompleteSpace W] [BorelSpace W] in
/-- General-process Itô reduction for the full separable
`C¹_t + C²_x` class, with continuity and Taylor remainders now discharged
unconditionally.  The two remaining hypotheses are exactly the stochastic
`dX` sum and diffusion-weighted quadratic-variation limits. -/
theorem ito_formula_timeAddState_itoProcess
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) (I : W → ℝ)
    (hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop I)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral (timeAddStateFunction g f) X σ t)) :
    ∀ᵐ omega ∂P,
      timeAddStateFunction g f t (X t omega) =
        timeAddStateFunction g f 0 (X 0 omega) +
          generalItoTimeIntegral (timeAddStateFunction g f) X t omega +
          I omega +
          generalItoQuadraticIntegral
            (timeAddStateFunction g f) X σ t omega := by
  obtain ⟨Y, hmod⟩ := hX.exists_continuousModification
  exact ito_formula_timeAddState_itoProcess_of_continuousModification
    hX hmod hXzero g f hg hf t I hspace hquadratic

omit [CompleteSpace W] [BorelSpace W] in
/-- If the diffusion-weighted quadratic sums have their intended limit, the
exact partition identity constructs the remaining `dX` limit and proves the
separable general Itô formula.  Thus weighted quadratic variation is the sole
analytic hypothesis left in this existential form of the theorem. -/
theorem exists_ito_formula_timeAddState_itoProcess_of_quadratic_limit
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0)
    (hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop
      (generalItoQuadraticIntegral (timeAddStateFunction g f) X σ t)) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
          X t (n + 1)) Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddStateFunction g f t (X t omega) =
          timeAddStateFunction g f 0 (X 0 omega) +
            generalItoTimeIntegral (timeAddStateFunction g f) X t omega +
            I omega +
            generalItoQuadraticIntegral
              (timeAddStateFunction g f) X σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hXmeas := hX.aestronglyMeasurable_of_initial hXzero
  have hvalueMeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (fun omega => timeAddStateFunction g f s (X s omega)) P := by
    intro s
    unfold timeAddStateFunction
    exact aestronglyMeasurable_const.add
      (hf.continuous.measurable.comp_aemeasurable
        (hXmeas s).aemeasurable).aestronglyMeasurable
  have hendpoint : AEStronglyMeasurable
      (fun omega =>
        timeAddStateFunction g f t (X t omega) -
          timeAddStateFunction g f 0 (X 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  have htimeRaw :=
    generalItoTimeApprox_timeAddStateFunction_tendstoInMeasure
      (P := P) g f hg X t
  have htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop
      (generalItoTimeIntegral (timeAddStateFunction g f) X t) := by
    rw [show
      generalItoTimeIntegral (timeAddStateFunction g f) X t =
        (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) by
      funext omega
      exact generalItoTimeIntegral_timeAddStateFunction g f
        (hg.differentiable (by norm_num)) X t omega]
    exact htimeRaw
  exact generalIto_exists_space_limit_and_formula
    (timeAddStateFunction g f) X t
      (generalItoTimeIntegral (timeAddStateFunction g f) X t)
      (generalItoQuadraticIntegral (timeAddStateFunction g f) X σ t)
      hendpoint htime hquadratic
      (hX.generalItoRemainder_timeAddState_tendstoInMeasure_unconditional
        hXzero g f hg hf t)

omit [CompleteSpace W] [BorelSpace W] in
/-- An Itô process whose bundled diffusion is finite elementary has a
continuous modification.  This proves the representation layer on the dense
class used to construct the general stochastic integral. -/
theorem IsItoProcess.exists_continuousModification_of_diffusion_eq_elementaryFinsupp
    (hX : IsItoProcess X μ σ B P)
    (v : ElementaryPredictableIndex
      (Filtration.natural B hX.driver_stronglyMeasurable) P →₀ ℝ)
    (hdiffusion : hX.diffusion = elementaryFinsuppToPredictable
      (Filtration.natural B hX.driver_stronglyMeasurable) P v) :
    ∃ Y : ℝ≥0 → W → ℝ, IsContinuousProcessModification X Y P := by
  let J := elementaryFinsuppItoContinuousRepresentative B
    hX.driver_stronglyMeasurable v
  have hJ : IsContinuousProcessModification hX.integralProcess J P := by
    unfold IsItoProcess.integralProcess stochasticIntegralProcess
    rw [hdiffusion]
    exact elementaryFinsuppItoContinuousModification
      hX.driver_brownian hX.driver_stronglyMeasurable v
  exact ⟨hX.continuousRepresentative J,
    hX.continuousModification_of_integralProcess J hJ⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- On the finite elementary diffusion layer, the full separable Taylor
remainder vanishes without any additional representation hypothesis. -/
theorem IsItoProcess.generalItoRemainder_timeAddState_tendstoInMeasure_of_elementaryFinsupp
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (v : ElementaryPredictableIndex
      (Filtration.natural B hX.driver_stronglyMeasurable) P →₀ ℝ)
    (hdiffusion : hX.diffusion = elementaryFinsuppToPredictable
      (Filtration.natural B hX.driver_stronglyMeasurable) P v)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
        X t (n + 1)) Filter.atTop (fun _ => 0) := by
  obtain ⟨Y, hmod⟩ :=
    hX.exists_continuousModification_of_diffusion_eq_elementaryFinsupp
      v hdiffusion
  exact hX.generalItoRemainder_timeAddState_tendstoInMeasure
    hmod hXzero g f hg hf t

omit [CompleteSpace W] [BorelSpace W] in
/-- The displayed diffusion coefficient of an Itô process is square
integrable on time-sample product space.  This transfers the bundled `L²`
fact through the representative equality stored in `IsItoProcess`. -/
theorem IsItoProcess.integrable_sq_diffusionCoefficient
    (hX : IsItoProcess X μ σ B P) :
    Integrable (fun p : ℝ≥0 × W => (σ p.1 p.2) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) := by
  have hbundled : Integrable
      (fun p : ℝ≥0 × W =>
        ((hX.diffusion : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (hX.diffusion : TimeProcessL2 P)).integrable_sq
  apply hbundled.congr
  filter_upwards [hX.diffusion_ae_eq] with p hp
  rw [hp]
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- The displayed diffusion variance is integrable on every finite
horizon. -/
theorem IsItoProcess.integrable_integratedDiffusionVariance
    (hX : IsItoProcess X μ σ B P) (t : ℝ≥0) :
    Integrable (integratedDiffusionVariance σ t) P := by
  exact (integrable_predictableQuadraticVariation
    hX.driver_stronglyMeasurable hX.diffusion t).congr
      (predictableQuadraticVariation_diffusion_ae hX t)

omit [CompleteSpace W] [BorelSpace W] in
/-- The expected displayed diffusion variance on any finite horizon is
bounded by the squared norm of the bundled diffusion coefficient. -/
theorem IsItoProcess.integral_integratedDiffusionVariance_le_diffusion_norm_sq
    (hX : IsItoProcess X μ σ B P) (t : ℝ≥0) :
    ∫ omega, integratedDiffusionVariance σ t omega ∂P ≤
      ‖hX.diffusion‖ ^ 2 := by
  calc
    (∫ omega, integratedDiffusionVariance σ t omega ∂P) =
        ∫ omega, predictableQuadraticVariation
          hX.driver_stronglyMeasurable hX.diffusion t omega ∂P :=
      integral_congr_ae (predictableQuadraticVariation_diffusion_ae hX t).symm
    _ ≤ ‖hX.diffusion‖ ^ 2 :=
      integral_predictableQuadraticVariation_le_norm_sq
        hX.driver_stronglyMeasurable hX.diffusion t

omit [CompleteSpace W] [BorelSpace W] in
/-- The displayed diffusion coefficient is square integrable along almost
every sample path on every finite real-time interval. -/
theorem IsItoProcess.eventually_integrableOn_sq_diffusionCoefficient
    (hX : IsItoProcess X μ σ B P) (T : ℝ≥0) :
    ∀ᵐ omega ∂P, IntegrableOn
      (fun r : ℝ => (σ r.toNNReal omega) ^ 2)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  have hsections := hX.integrable_sq_diffusionCoefficient.prod_left_ae
  filter_upwards [hsections] with omega homega
  let q : ℝ → ℝ := fun r => (σ r.toNNReal omega) ^ 2
  have hsource : Integrable
      (q ∘ ((↑) : ℝ≥0 → ℝ))
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 T)) := by
    have hrestricted := homega.mono_measure
      (Measure.restrict_le_self (μ := nonnegativeLebesgueMeasure)
        (s := Set.Ioc 0 T))
    have hcomp : (q ∘ ((↑) : ℝ≥0 → ℝ)) =
        (fun s : ℝ≥0 => (σ s omega) ^ 2) := by
      funext s
      dsimp only [q, Function.comp_apply]
      rw [Real.toNNReal_coe]
    rw [hcomp]
    exact hrestricted
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 T))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (T : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,
      map_nonnegativeLebesgueMeasure_restrict_Ioc T⟩
  have htargetIoc : Integrable q
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (T : ℝ))) :=
    (hpres.integrable_comp_emb measurableEmbedding_nnrealCoe_iterated).mp hsource
  change IntegrableOn q (Set.Icc (0 : ℝ) (T : ℝ))
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact htargetIoc

omit [CompleteSpace W] [BorelSpace W] in
/-- Candidate diffusion-weighted bracket integrals inherit the uniform
weight perturbation estimate in `L¹`.  Measurability and pathwise
integrability are stated explicitly because they are exactly the remaining
representation obligations when this estimate is applied to a chosen
continuous modification. -/
theorem IsItoProcess.integral_abs_generalItoQuadraticIntegral_sub_le
    (hX : IsItoProcess X μ σ B P)
    (f g : ℝ → ℝ → ℝ) (t : ℝ≥0)
    (hfmeas : AEStronglyMeasurable
      (generalItoQuadraticIntegral f X σ t) P)
    (hgmeas : AEStronglyMeasurable
      (generalItoQuadraticIntegral g X σ t) P)
    (hfint : ∀ᵐ omega ∂P, IntegrableOn (fun s : ℝ =>
      itoSpaceSecondDerivative f s (X s.toNNReal omega) *
        (σ s.toNNReal omega) ^ 2) (Set.Icc 0 (t : ℝ)))
    (hgint : ∀ᵐ omega ∂P, IntegrableOn (fun s : ℝ =>
      itoSpaceSecondDerivative g s (X s.toNNReal omega) *
        (σ s.toNNReal omega) ^ 2) (Set.Icc 0 (t : ℝ)))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ s x,
      |itoSpaceSecondDerivative f s x -
        itoSpaceSecondDerivative g s x| ≤ K) :
    ∫ omega, |generalItoQuadraticIntegral f X σ t omega -
        generalItoQuadraticIntegral g X σ t omega| ∂P ≤
      (1 / 2 : ℝ) * K * ‖hX.diffusion‖ ^ 2 := by
  have hσint := hX.eventually_integrableOn_sq_diffusionCoefficient t
  have hpoint : ∀ᵐ omega ∂P,
      |generalItoQuadraticIntegral f X σ t omega -
          generalItoQuadraticIntegral g X σ t omega| ≤
        (1 / 2 : ℝ) * K * integratedDiffusionVariance σ t omega := by
    filter_upwards [hfint, hgint, hσint] with omega hfomega hgomega hσomega
    exact abs_generalItoQuadraticIntegral_sub_le_integratedDiffusionVariance
      f g X σ t omega K hfomega hgomega hσomega
        (fun s hs => hbound s (X s.toNNReal omega))
  have hrightInt : Integrable (fun omega =>
      (1 / 2 : ℝ) * K * integratedDiffusionVariance σ t omega) P :=
    (hX.integrable_integratedDiffusionVariance t).const_mul
      ((1 / 2 : ℝ) * K)
  have hleftInt : Integrable (fun omega =>
      |generalItoQuadraticIntegral f X σ t omega -
        generalItoQuadraticIntegral g X σ t omega|) P := by
    apply hrightInt.mono' ((hfmeas.sub hgmeas).norm)
    filter_upwards [hpoint] with omega homega
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_abs] using homega
  calc
    (∫ omega, |generalItoQuadraticIntegral f X σ t omega -
        generalItoQuadraticIntegral g X σ t omega| ∂P) ≤
        ∫ omega, (1 / 2 : ℝ) * K *
          integratedDiffusionVariance σ t omega ∂P :=
      integral_mono_ae hleftInt hrightInt hpoint
    _ = (1 / 2 : ℝ) * K *
        ∫ omega, integratedDiffusionVariance σ t omega ∂P := by
      rw [integral_const_mul]
    _ ≤ (1 / 2 : ℝ) * K * ‖hX.diffusion‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (hX.integral_integratedDiffusionVariance_le_diffusion_norm_sq t)
        (mul_nonneg (by norm_num) hK)

omit [CompleteSpace W] [BorelSpace W] in
/-- On every finite horizon, the integrated diffusion variance has continuous
sample paths almost everywhere.  This supplies the path regularity of the
target bracket even though the current quadratic-variation theorem is stated
only at each fixed terminal time. -/
theorem IsItoProcess.eventually_continuousOn_integratedDiffusionVariance
    (hX : IsItoProcess X μ σ B P) (T : ℝ≥0) :
    ∀ᵐ omega ∂P, ContinuousOn
      (fun t => integratedDiffusionVariance σ t omega)
      (Set.Icc (0 : ℝ≥0) T) := by
  filter_upwards [hX.eventually_integrableOn_sq_diffusionCoefficient T]
    with omega homega
  let q : ℝ → ℝ := fun r => (σ r.toNNReal omega) ^ 2
  have hcontinuous := continuousOn_nnrealIntegralPrimitive homega
  change ContinuousOn (nnrealIntegralPrimitive q) (Set.Icc (0 : ℝ≥0) T)
  exact hcontinuous

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Itô's formula for an arbitrary `C²` state function of a deterministic
affine transform of Brownian motion.  This is the complementary projection to
the general-process quadratic theorem: state regularity is unrestricted here,
while the diffusion is the deterministic constant `c`. -/
theorem ito_formula_affineBrownian
    (hB : IsBrownianMotion B P) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => affineBrownianItoSpaceApprox f x₀ c B t (n + 1))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        f (affineBrownianProcess x₀ c B t omega) = f x₀ + I omega +
          (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv (deriv f)
                (affineBrownianProcess x₀ c B s.toNNReal omega) * c ^ 2 := by
  let g : ℝ → ℝ := fun y => f (x₀ + c * y)
  have hg : ContDiff ℝ 2 g := by
    dsimp only [g]
    fun_prop
  have hfirst : deriv g = fun y => deriv f (x₀ + c * y) * c := by
    funext y
    exact deriv_comp_const_add_const_mul f
      (hf.differentiable (by norm_num)) x₀ c y
  have hsecond : deriv (deriv g) =
      fun y => deriv (deriv f) (x₀ + c * y) * c ^ 2 := by
    funext y
    exact secondDeriv_comp_const_add_const_mul f hf x₀ c y
  obtain ⟨I, hlimit, hformula⟩ := ito_formula_brownianMotion hB hg t
  rw [hfirst] at hlimit
  rw [hsecond] at hformula
  refine ⟨I, ?_, ?_⟩
  · apply hlimit.congr_left
    intro n
    filter_upwards with omega
    unfold affineBrownianItoSpaceApprox affineBrownianProcess
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · simpa only [g, affineBrownianProcess, mul_zero, add_zero] using hformula

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The time-dependent Itô formula for a `C¹_t + C²_x` separable function of
a deterministic affine Brownian state.  Both regularity axes are unrestricted;
what remains for the full target is their interaction with a variable
diffusion and a general Itô-process representative. -/
theorem ito_formula_timeAddState_affineBrownian
    (hB : IsBrownianMotion B P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => affineBrownianItoSpaceApprox f x₀ c B t (n + 1))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddStateFunction g f t
            (affineBrownianProcess x₀ c B t omega) =
          timeAddStateFunction g f 0 x₀ +
            (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) + I omega +
            (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv (deriv f)
                  (affineBrownianProcess x₀ c B s.toNNReal omega) * c ^ 2 := by
  have hFTC : (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) =
      g t - g 0 := by
    calc
      _ = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), deriv g s :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ s in (0 : ℝ)..(t : ℝ), deriv g s :=
        (intervalIntegral.integral_of_le (NNReal.coe_nonneg t)).symm
      _ = g t - g 0 :=
        intervalIntegral.integral_deriv_eq_sub
          (fun _ _ => hg.differentiable (by norm_num) |>.differentiableAt)
          ((hg.continuous_deriv (by norm_num)).intervalIntegrable 0 t)
  obtain ⟨I, hlimit, hformula⟩ :=
    ito_formula_affineBrownian hB f hf x₀ c t
  refine ⟨I, hlimit, ?_⟩
  filter_upwards [hformula] with omega homega
  unfold timeAddStateFunction
  rw [homega, hFTC]
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Every analytic input of the generic uniform-partition reduction is
available for separable `C¹_t + C²_x` functions along affine Brownian states.
This theorem ties the abstract reduction to the concrete Brownian theory. -/
theorem generalIto_uniformPartition_limits_timeAddState_affineBrownian
    (hB : IsBrownianMotion B P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoTimeApprox (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t (n + 1))
        Filter.atTop
        (generalItoTimeIntegral (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t) ∧
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t (n + 1))
        Filter.atTop I ∧
      TendstoInMeasure P
        (fun n => generalItoQuadraticApprox (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t (n + 1))
        Filter.atTop
        (generalItoQuadraticIntegral (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B)
          (fun _ : ℝ≥0 => fun _ : W => c) t) ∧
      TendstoInMeasure P
        (fun n => generalItoRemainderApprox (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t (n + 1))
        Filter.atTop (fun _ => 0) := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hspaceSpecialized, _hformula⟩ :=
    ito_formula_affineBrownian hB f hf x₀ c t
  have htime :=
    generalItoTimeApprox_timeAddStateFunction_tendstoInMeasure
      (P := P) g f hg (affineBrownianProcess x₀ c B) t
  have htime' : TendstoInMeasure P
      (fun n => generalItoTimeApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop
      (generalItoTimeIntegral (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t) := by
    rw [show
      generalItoTimeIntegral (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t =
        (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) by
      funext omega
      exact generalItoTimeIntegral_timeAddStateFunction g f
        (hg.differentiable (by norm_num))
        (affineBrownianProcess x₀ c B) t omega]
    exact htime
  have hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1))
      Filter.atTop I := by
    rw [show
      (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
        (affineBrownianProcess x₀ c B) t (n + 1)) =
      (fun n => affineBrownianItoSpaceApprox f x₀ c B t (n + 1)) by
      funext n omega
      exact generalItoSpaceApprox_timeAddState_affineBrownian g f
        (hf.differentiable (by norm_num)) x₀ c B t (n + 1) omega]
    exact hspaceSpecialized
  exact ⟨I, htime', hspace,
    generalItoQuadraticApprox_timeAddState_affineBrownian_tendstoInMeasure
      hB g f hf x₀ c t,
    generalItoRemainderApprox_timeAddState_affineBrownian_tendstoInMeasure_zero
      hB g f hg hf x₀ c t⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The separable affine-Brownian Itô formula obtained specifically through
the generic four-limit partition interface.  Unlike the earlier streamlined
statement, this version keeps the abstract time and quadratic integrals
visible and therefore verifies that the general reduction is wired
correctly. -/
theorem ito_formula_timeAddState_affineBrownian_via_partition_limits
    (hB : IsBrownianMotion B P)
    (g f : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (x₀ c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox (timeAddStateFunction g f)
          (affineBrownianProcess x₀ c B) t (n + 1))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddStateFunction g f t
            (affineBrownianProcess x₀ c B t omega) =
          timeAddStateFunction g f 0
              (affineBrownianProcess x₀ c B 0 omega) +
            generalItoTimeIntegral (timeAddStateFunction g f)
              (affineBrownianProcess x₀ c B) t omega + I omega +
            generalItoQuadraticIntegral (timeAddStateFunction g f)
              (affineBrownianProcess x₀ c B)
              (fun _ : ℝ≥0 => fun _ : W => c) t omega := by
  let hpre := hB.toIsPreBrownianReal
  let _ : IsProbabilityMeasure P :=
    hpre.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, htime, hspace, hquadratic, hremainder⟩ :=
    generalIto_uniformPartition_limits_timeAddState_affineBrownian
      hB g f hg hf x₀ c t
  have hYmeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (affineBrownianProcess x₀ c B s) P := by
    intro s
    unfold affineBrownianProcess
    exact aestronglyMeasurable_const.add
      (aestronglyMeasurable_const.mul
        (hpre.aemeasurable s).aestronglyMeasurable)
  have hvalueMeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (fun omega => timeAddStateFunction g f s
        (affineBrownianProcess x₀ c B s omega)) P := by
    intro s
    unfold timeAddStateFunction
    exact aestronglyMeasurable_const.add
      (hf.continuous.measurable.comp_aemeasurable
        (hYmeas s).aemeasurable).aestronglyMeasurable
  have hendpoint : AEStronglyMeasurable
      (fun omega =>
        timeAddStateFunction g f t
            (affineBrownianProcess x₀ c B t omega) -
          timeAddStateFunction g f 0
            (affineBrownianProcess x₀ c B 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  refine ⟨I, hspace, ?_⟩
  exact generalIto_formula_ae_of_uniformPartition_convergence
    (timeAddStateFunction g f) (affineBrownianProcess x₀ c B)
    (fun _ : ℝ≥0 => fun _ : W => c) t I
    hendpoint htime hspace hquadratic hremainder

omit [CompleteSpace W] [BorelSpace W] in
/-- Itô's formula for a quadratic state function of a general Itô process.

The stochastic integral is characterized by the defining left sums against
`X`.  The correction term is the bracket `a ∫₀ᵗ σ²`, obtained from the fully
proved general-process quadratic-variation theorem. -/
theorem ito_formula_quadratic_itoProcess
    (hX : IsItoProcess X μ σ B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
          (fun n => quadraticItoSpaceApprox a b X t (n + 1))
          Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        quadraticPolynomial a b c (X t omega) =
          quadraticPolynomial a b c (X 0 omega) + I omega +
            a * integratedDiffusionVariance σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let F : W → ℝ := fun omega =>
    quadraticPolynomial a b c (X t omega) -
      quadraticPolynomial a b c (X 0 omega)
  let I : W → ℝ := fun omega =>
    F omega - a * integratedDiffusionVariance σ t omega
  have hpolyMeas : ∀ s, AEStronglyMeasurable
      (fun omega => quadraticPolynomial a b c (X s omega)) P := by
    intro s
    unfold quadraticPolynomial
    exact ((aestronglyMeasurable_const.mul ((hXmeas s).pow 2)).add
      (aestronglyMeasurable_const.mul (hXmeas s))).add
        aestronglyMeasurable_const
  have hFMeas : AEStronglyMeasurable F P := by
    exact (hpolyMeas t).sub (hpolyMeas 0)
  have hvarianceMeas : AEStronglyMeasurable
      (integratedDiffusionVariance σ t) P := by
    have hcanonical := (integrable_predictableQuadraticVariation
      hX.driver_stronglyMeasurable hX.diffusion t).aestronglyMeasurable
    exact hcanonical.congr (predictableQuadraticVariation_diffusion_ae hX t)
  have hIMeas : AEStronglyMeasurable I P := by
    exact hFMeas.sub (aestronglyMeasurable_const.mul hvarianceMeas)
  have hconstant : TendstoInMeasure P (fun _ : ℕ => F) Filter.atTop F :=
    tendstoInMeasure_of_tendsto_ae (fun _ => hFMeas) (by
      filter_upwards with omega
      exact tendsto_const_nhds)
  have hqv : TendstoInMeasure P
      (fun n => quadraticVariationApprox X t (n + 1)) Filter.atTop
      (integratedDiffusionVariance σ t) :=
    quadraticVariation_itoProcess hX t
  have hscaled := hqv.const_mul_real_noMeas a
  have hresidual : TendstoInMeasure P
      (fun n omega => F omega -
        a * quadraticVariationApprox X t (n + 1) omega)
      Filter.atTop I := by
    simpa only [I] using hconstant.sub_real_noMeas hscaled
  have hlimit : TendstoInMeasure P
      (fun n => quadraticItoSpaceApprox a b X t (n + 1))
      Filter.atTop I := by
    apply hresidual.congr_left
    intro n
    filter_upwards with omega
    have hdecomp :=
      quadraticPolynomial_uniformPartition_decomposition a b c X t n omega
    dsimp only [F]
    linarith
  refine ⟨I, hIMeas, hlimit, ?_⟩
  filter_upwards with omega
  dsimp only [I, F]
  ring

omit [CompleteSpace W] [BorelSpace W] in
/-- A genuinely time-dependent general-process Itô formula for every function
that is affine in time and quadratic in the state.  The time integral is the
explicit value `tau * t`, the `dX` term is the limit of the left sums, and the
second-order correction follows from the bracket of `X`. -/
theorem ito_formula_timeAffineQuadratic_itoProcess
    (hX : IsItoProcess X μ σ B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (tau a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
          (fun n => quadraticItoSpaceApprox a b X t (n + 1))
          Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAffineQuadraticPolynomial tau a b c t (X t omega) =
          timeAffineQuadraticPolynomial tau a b c 0 (X 0 omega) +
            tau * (t : ℝ) + I omega +
              a * integratedDiffusionVariance σ t omega := by
  obtain ⟨I, hImeas, hlimit, hformula⟩ :=
    ito_formula_quadratic_itoProcess hX hXmeas a b c t
  refine ⟨I, hImeas, hlimit, ?_⟩
  filter_upwards [hformula] with omega homega
  unfold timeAffineQuadraticPolynomial
  rw [homega]
  ring

omit [CompleteSpace W] [BorelSpace W] in
/-- Itô's formula for arbitrary `C¹` time dependence and quadratic state
dependence.  This discharges the full time-derivative term by the fundamental
theorem of calculus while retaining the genuine general-process bracket and
left-sum stochastic term. -/
theorem ito_formula_timeAddQuadratic_itoProcess
    (hX : IsItoProcess X μ σ B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
          (fun n => quadraticItoSpaceApprox a b X t (n + 1))
          Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddQuadraticPolynomial g a b c t (X t omega) =
          timeAddQuadraticPolynomial g a b c 0 (X 0 omega) +
            (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) + I omega +
              a * integratedDiffusionVariance σ t omega := by
  have hFTC : (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) =
      g t - g 0 := by
    calc
      _ = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), deriv g s :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ s in (0 : ℝ)..(t : ℝ), deriv g s :=
        (intervalIntegral.integral_of_le (NNReal.coe_nonneg t)).symm
      _ = g t - g 0 :=
        intervalIntegral.integral_deriv_eq_sub
          (fun _ _ => hg.differentiable (by norm_num) |>.differentiableAt)
          ((hg.continuous_deriv (by norm_num)).intervalIntegrable 0 t)
  obtain ⟨I, hImeas, hlimit, hformula⟩ :=
    ito_formula_quadratic_itoProcess hX hXmeas a b c t
  refine ⟨I, hImeas, hlimit, ?_⟩
  filter_upwards [hformula] with omega homega
  unfold timeAddQuadraticPolynomial
  rw [homega, hFTC]
  ring

omit [CompleteSpace W] [BorelSpace W] in
/-- All four concrete partition limits required by the generic reduction are
discharged for arbitrary `C¹` time dependence and quadratic state dependence
along a general Itô process. -/
theorem generalIto_uniformPartition_limits_timeAddQuadratic_itoProcess
    (hX : IsItoProcess X μ σ B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
        (fun n => generalItoTimeApprox
          (timeAddQuadraticPolynomial g a b c) X t (n + 1))
        Filter.atTop
        (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) ∧
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox
          (timeAddQuadraticPolynomial g a b c) X t (n + 1))
        Filter.atTop I ∧
      TendstoInMeasure P
        (fun n => generalItoQuadraticApprox
          (timeAddQuadraticPolynomial g a b c) X t (n + 1))
        Filter.atTop
        (fun omega => a * integratedDiffusionVariance σ t omega) ∧
      TendstoInMeasure P
        (fun n => generalItoRemainderApprox
          (timeAddQuadraticPolynomial g a b c) X t (n + 1))
        Filter.atTop (fun _ => 0) := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hImeas, hspaceSpecialized, _hformula⟩ :=
    ito_formula_quadratic_itoProcess hX hXmeas a b c t
  have htime : TendstoInMeasure P
      (fun n => generalItoTimeApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1))
      Filter.atTop
      (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) := by
    change TendstoInMeasure P
      (fun n => generalItoTimeApprox
        (timeAddStateFunction g (quadraticPolynomial a b c))
        X t (n + 1)) Filter.atTop _
    exact generalItoTimeApprox_timeAddStateFunction_tendstoInMeasure
      (P := P) g (quadraticPolynomial a b c) hg X t
  have hspace : TendstoInMeasure P
      (fun n => generalItoSpaceApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1))
      Filter.atTop I := by
    rw [show
      (fun n => generalItoSpaceApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1)) =
      (fun n => quadraticItoSpaceApprox a b X t (n + 1)) by
      funext n omega
      exact generalItoSpaceApprox_timeAddQuadraticPolynomial
        g a b c X t (n + 1) omega]
    exact hspaceSpecialized
  have hquadratic : TendstoInMeasure P
      (fun n => generalItoQuadraticApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1))
      Filter.atTop
      (fun omega => a * integratedDiffusionVariance σ t omega) := by
    have hscaled :=
      (quadraticVariation_itoProcess hX t).const_mul_real_noMeas a
    rw [show
      (fun n => generalItoQuadraticApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1)) =
      (fun n omega => a * quadraticVariationApprox X t (n + 1) omega) by
      funext n omega
      exact generalItoQuadraticApprox_timeAddQuadraticPolynomial
        g a b c X t (n + 1) omega]
    exact hscaled
  have hremainder : TendstoInMeasure P
      (fun n => generalItoRemainderApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1))
      Filter.atTop (fun _ => 0) := by
    rw [show
      (fun n => generalItoRemainderApprox
        (timeAddQuadraticPolynomial g a b c) X t (n + 1)) =
      (fun n _ => itoTimeTaylorRemainderApprox g t (n + 1)) by
      funext n omega
      exact generalItoRemainderApprox_timeAddQuadraticPolynomial
        g (hg.differentiable (by norm_num)) a b c X t (n + 1) omega]
    exact itoTimeTaylorRemainderApprox_tendstoInMeasure_zero
      (P := P) g hg t
  exact ⟨I, hImeas, htime, hspace, hquadratic, hremainder⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- The arbitrary-time, quadratic-state general-process formula obtained by
feeding the preceding concrete limits through the generic partition theorem. -/
theorem ito_formula_timeAddQuadratic_itoProcess_via_partition_limits
    (hX : IsItoProcess X μ σ B P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
        (fun n => generalItoSpaceApprox
          (timeAddQuadraticPolynomial g a b c) X t (n + 1))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddQuadraticPolynomial g a b c t (X t omega) =
          timeAddQuadraticPolynomial g a b c 0 (X 0 omega) +
            (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) + I omega +
              a * integratedDiffusionVariance σ t omega := by
  let _ : IsProbabilityMeasure P :=
    hX.driver_brownian.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hImeas, htime, hspace, hquadratic, hremainder⟩ :=
    generalIto_uniformPartition_limits_timeAddQuadratic_itoProcess
      hX hXmeas g hg a b c t
  have hpolyMeas : ∀ s, AEStronglyMeasurable
      (fun omega => quadraticPolynomial a b c (X s omega)) P := by
    intro s
    unfold quadraticPolynomial
    exact ((aestronglyMeasurable_const.mul ((hXmeas s).pow 2)).add
      (aestronglyMeasurable_const.mul (hXmeas s))).add
        aestronglyMeasurable_const
  have hvalueMeas : ∀ s : ℝ≥0, AEStronglyMeasurable
      (fun omega => timeAddQuadraticPolynomial g a b c s (X s omega)) P := by
    intro s
    unfold timeAddQuadraticPolynomial
    exact aestronglyMeasurable_const.add (hpolyMeas s)
  have hendpoint : AEStronglyMeasurable
      (fun omega =>
        timeAddQuadraticPolynomial g a b c t (X t omega) -
          timeAddQuadraticPolynomial g a b c 0 (X 0 omega)) P :=
    (hvalueMeas t).sub (hvalueMeas 0)
  refine ⟨I, hImeas, hspace, ?_⟩
  exact generalIto_formula_ae_of_partition_limits
    (timeAddQuadraticPolynomial g a b c) X t
    (fun _ => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s)
    I (fun omega => a * integratedDiffusionVariance σ t omega)
    hendpoint htime hspace hquadratic hremainder

omit [CompleteSpace W] [BorelSpace W] in
/-- Initial-value measurability is enough for the preceding formula; all later
fixed-time measurability follows from the Itô-process equation. -/
theorem ito_formula_timeAddQuadratic_itoProcess_of_initialMeasurable
    (hX : IsItoProcess X μ σ B P)
    (hXzero : AEStronglyMeasurable (X 0) P)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (a b c : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      AEStronglyMeasurable I P ∧
      TendstoInMeasure P
          (fun n => quadraticItoSpaceApprox a b X t (n + 1))
          Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        timeAddQuadraticPolynomial g a b c t (X t omega) =
          timeAddQuadraticPolynomial g a b c 0 (X 0 omega) +
            (∫ s in Set.Icc (0 : ℝ) (t : ℝ), deriv g s) + I omega +
              a * integratedDiffusionVariance σ t omega := by
  exact ito_formula_timeAddQuadratic_itoProcess hX
    (hX.aestronglyMeasurable_of_initial hXzero) g hg a b c t

end StochasticCalculus
