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

variable [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian P]

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

end StochasticCalculus
