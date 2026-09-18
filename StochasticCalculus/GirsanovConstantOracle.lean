/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Moments.Tilted

/-!
# Constant-drift terminal Girsanov calculation

This file proves the fixed-horizon, constant-drift Gaussian change of measure.
The capstone identifies the stopped-drift shift as pre-Brownian under one
equivalent terminal measure. This independent Gaussian-law regression oracle was copied from
lean-pipeline/girsanov, commit 93c77028edae070a11cff3a77b2c0f19f662d4e6.
It is kept separate from the predictable Girsanov proof.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace StochasticCalculus.Girsanov

/-- The constant-drift exponential density at one Brownian terminal time. -/
def constantExponentialDensity {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (theta : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-theta * B t ω - theta ^ 2 * (t : ℝ) / 2)

/-- The normalized terminal Esscher measure with tilt `-theta * B_t`. -/
def constantGirsanovMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (theta : ℝ) (t : ℝ≥0) : Measure Ω :=
  P.tilted (fun ω ↦ -theta * B t ω)

/-- The terminal coordinate after cancelling the constant drift `-theta`. -/
def driftShiftedTerminal {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (theta : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω + theta * (t : ℝ)

/-- The Brownian coordinate shifted by the constant drift up to a fixed
horizon, and left with no further drift after that horizon. -/
def horizonDriftShifted {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (theta : ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω + theta * (min t T : ℝ≥0)

/-- A finite real measure is determined by its moment generating function
when the comparison law is Gaussian. -/
private theorem eq_gaussianReal_of_mgf_eq
    (ν : Measure ℝ) [IsFiniteMeasure ν] (mean : ℝ) (variance : ℝ≥0)
    (hmgf : mgf id ν = mgf id (gaussianReal mean variance)) :
    ν = gaussianReal mean variance := by
  have heqOn := eqOn_complexMGF_of_mgf hmgf.symm
  have hcomplex : complexMGF id (gaussianReal mean variance) = complexMGF id ν := by
    funext z
    apply heqOn
    simp only [integrableExpSet_id_gaussianReal, interior_univ, Set.mem_univ,
      Set.ofPred_true]
  simpa only [Measure.map_id] using
    (Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id hcomplex).symm

/-- Exponential tilting of a real Gaussian shifts its mean by
`variance * c` and preserves its variance. -/
theorem tilted_gaussianReal (mean : ℝ) (variance : ℝ≥0) (c : ℝ) :
    (gaussianReal mean variance).tilted (fun x ↦ c * x) =
      gaussianReal (mean + (variance : ℝ) * c) variance := by
  let ν : Measure ℝ := (gaussianReal mean variance).tilted (fun x ↦ c * x)
  have hint : Integrable (fun x : ℝ ↦ Real.exp (c * x))
      (gaussianReal mean variance) := integrable_exp_mul_gaussianReal c
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hint
  apply eq_gaussianReal_of_mgf_eq ν (mean + (variance : ℝ) * c) variance
  funext t
  change (∫ x, Real.exp (t * x) ∂ν) = _
  rw [show ν = (gaussianReal mean variance).tilted (fun x ↦ c * x) from rfl,
    integral_exp_tilted]
  have hnum := mgf_gaussianReal
    (p := gaussianReal mean variance) (X := id) (μ := mean) (v := variance)
    (by simp) (c + t)
  have hden := mgf_gaussianReal
    (p := gaussianReal mean variance) (X := id) (μ := mean) (v := variance)
    (by simp) c
  have htarget := mgf_gaussianReal
    (p := gaussianReal (mean + (variance : ℝ) * c) variance)
    (X := id) (μ := mean + (variance : ℝ) * c) (v := variance)
    (by simp) t
  rw [show (∫ x, Real.exp (((fun x ↦ c * x) + fun x ↦ t * x) x)
      ∂gaussianReal mean variance) =
        Real.exp (mean * (c + t) + (variance : ℝ) * (c + t) ^ 2 / 2) by
      simpa [mgf, id_eq, add_mul] using hnum,
    show (∫ x, Real.exp (c * x) ∂gaussianReal mean variance) =
        Real.exp (mean * c + (variance : ℝ) * c ^ 2 / 2) by
      simpa [mgf, id_eq] using hden,
    div_eq_iff (Real.exp_ne_zero _), htarget, ← Real.exp_add]
  congr 1
  ring

/-- A Gaussian random variable remains Gaussian under its sample-space
Esscher transform, with the expected shifted mean. -/
theorem hasLaw_gaussian_tilted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {mean : ℝ} {variance : ℝ≥0}
    (hX : HasLaw X (gaussianReal mean variance) P) (c : ℝ) :
    HasLaw X (gaussianReal (mean + (variance : ℝ) * c) variance)
      (P.tilted (fun ω ↦ c * X ω)) := by
  let Q : Measure Ω := P.tilted (fun ω ↦ c * X ω)
  have hintP : Integrable (fun ω ↦ Real.exp (c * X ω)) P := by
    have hmapped : Integrable (fun x : ℝ ↦ Real.exp (c * x)) (P.map X) := by
      rw [hX.map_eq]
      exact integrable_exp_mul_gaussianReal c
    have hcomp := (integrable_map_measure hmapped.aestronglyMeasurable
      hX.aemeasurable).mp hmapped
    simpa only [Function.comp_def] using hcomp
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hintP
  have hXQ : AEMeasurable X Q :=
    hX.aemeasurable.mono_ac (tilted_absolutelyContinuous P (fun ω ↦ c * X ω))
  let ν : Measure ℝ := Q.map X
  let _ : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hXQ
  refine ⟨hXQ, ?_⟩
  change ν = gaussianReal (mean + (variance : ℝ) * c) variance
  apply eq_gaussianReal_of_mgf_eq ν (mean + (variance : ℝ) * c) variance
  funext t
  change (∫ x, Real.exp (t * x) ∂ν) = _
  rw [show ν = Q.map X from rfl,
    integral_map hXQ (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (t * x)) (Q.map X)),
    show Q = P.tilted (fun ω ↦ c * X ω) from rfl,
    integral_exp_tilted]
  have hnumP :
      (∫ ω, Real.exp ((c + t) * X ω) ∂P) =
        Real.exp (mean * (c + t) + (variance : ℝ) * (c + t) ^ 2 / 2) := by
    have htransport := hX.integral_comp (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp ((c + t) * x)) (gaussianReal mean variance))
    simp only [Function.comp_apply] at htransport
    rw [htransport]
    have hmgf := mgf_gaussianReal
      (p := gaussianReal mean variance) (X := id) (μ := mean) (v := variance)
      (by simp) (c + t)
    simpa [mgf, id_eq] using hmgf
  have hdenP :
      (∫ ω, Real.exp (c * X ω) ∂P) =
        Real.exp (mean * c + (variance : ℝ) * c ^ 2 / 2) := by
    have htransport := hX.integral_comp (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (c * x)) (gaussianReal mean variance))
    simp only [Function.comp_apply] at htransport
    rw [htransport]
    have hmgf := mgf_gaussianReal
      (p := gaussianReal mean variance) (X := id) (μ := mean) (v := variance)
      (by simp) c
    simpa [mgf, id_eq] using hmgf
  have htarget := mgf_gaussianReal
    (p := gaussianReal (mean + (variance : ℝ) * c) variance)
    (X := id) (μ := mean + (variance : ℝ) * c) (v := variance)
    (by simp) t
  rw [show (∫ ω, Real.exp
      (((fun ω ↦ c * X ω) + fun ω ↦ t * X ω) ω) ∂P) =
        Real.exp (mean * (c + t) + (variance : ℝ) * (c + t) ^ 2 / 2) by
      simpa only [Pi.add_apply, add_mul] using hnumP,
    hdenP, div_eq_iff (Real.exp_ne_zero _), htarget, ← Real.exp_add]
  congr 1
  ring

/-- If `X` and `Y` are jointly Gaussian, exponentially tilting by `c * Y`
shifts the mean of `X` by `c * cov(X,Y)` and preserves its variance. -/
theorem hasLaw_gaussian_tilted_of_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (c : ℝ) :
    HasLaw X
      (gaussianReal (P[X] + c * cov[X, Y; P]) Var[X; P].toNNReal)
      (P.tilted (fun ω ↦ c * Y ω)) := by
  let Q : Measure Ω := P.tilted (fun ω ↦ c * Y ω)
  have hX : HasGaussianLaw X P := hXY.fst
  have hY : HasGaussianLaw Y P := hXY.snd
  have hintP : Integrable (fun ω ↦ Real.exp (c * Y ω)) P := by
    have hmapped : Integrable (fun y : ℝ ↦ Real.exp (c * y)) (P.map Y) := by
      rw [hY.map_eq_gaussianReal]
      exact integrable_exp_mul_gaussianReal c
    have hcomp := (integrable_map_measure hmapped.aestronglyMeasurable
      hY.aemeasurable).mp hmapped
    simpa only [Function.comp_def] using hcomp
  let _ : IsProbabilityMeasure P := hXY.isProbabilityMeasure
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hintP
  have hXQ : AEMeasurable X Q :=
    hX.aemeasurable.mono_ac (tilted_absolutelyContinuous P (fun ω ↦ c * Y ω))
  let ν : Measure ℝ := Q.map X
  let _ : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hXQ
  refine ⟨hXQ, ?_⟩
  change ν = gaussianReal (P[X] + c * cov[X, Y; P]) Var[X; P].toNNReal
  apply eq_gaussianReal_of_mgf_eq ν
    (P[X] + c * cov[X, Y; P]) Var[X; P].toNNReal
  funext u
  change (∫ x, Real.exp (u * x) ∂ν) = _
  rw [show ν = Q.map X from rfl,
    integral_map hXQ (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (u * x)) (Q.map X)),
    show Q = P.tilted (fun ω ↦ c * Y ω) from rfl,
    integral_exp_tilted]
  have hlin : HasGaussianLaw (fun ω ↦ c * Y ω + u * X ω) P := by
    let L : ℝ × ℝ →L[ℝ] ℝ :=
      c • ContinuousLinearMap.snd ℝ ℝ ℝ + u • ContinuousLinearMap.fst ℝ ℝ ℝ
    have hmap := hXY.map_fun L
    simpa [L] using hmap
  have hmean :
      P[fun ω ↦ c * Y ω + u * X ω] = c * P[Y] + u * P[X] := by
    rw [integral_add ((hY.memLp_two.const_mul c).integrable one_le_two)
        ((hX.memLp_two.const_mul u).integrable one_le_two),
      integral_const_mul, integral_const_mul]
  have hvar :
      Var[fun ω ↦ c * Y ω + u * X ω; P] =
        c ^ 2 * Var[Y; P] + u ^ 2 * Var[X; P] +
          2 * c * u * cov[X, Y; P] := by
    change Var[(fun ω ↦ c * Y ω) + (fun ω ↦ u * X ω); P] = _
    rw [variance_add (hY.memLp_two.const_mul c) (hX.memLp_two.const_mul u),
      variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right,
      covariance_comm]
    ring
  have hvar_nonneg :
      0 ≤ c ^ 2 * Var[Y; P] + u ^ 2 * Var[X; P] +
        2 * c * u * cov[X, Y; P] := by
    rw [← hvar]
    exact variance_nonneg _ _
  have hnum := mgf_gaussianReal hlin.map_eq_gaussianReal 1
  have hden := mgf_gaussianReal hY.map_eq_gaussianReal c
  have htarget := mgf_gaussianReal
    (p := gaussianReal (P[X] + c * cov[X, Y; P]) Var[X; P].toNNReal)
    (X := id) (μ := P[X] + c * cov[X, Y; P])
    (v := Var[X; P].toNNReal) (by simp) u
  rw [show (∫ ω, Real.exp
      (((fun ω ↦ c * Y ω) + fun ω ↦ u * X ω) ω) ∂P) =
        Real.exp (c * P[Y] + u * P[X] +
          (c ^ 2 * Var[Y; P] + u ^ 2 * Var[X; P] +
            2 * c * u * cov[X, Y; P]) / 2) by
      simpa [mgf, hmean, hvar, Real.coe_toNNReal',
        max_eq_left hvar_nonneg] using hnum,
    show (∫ ω, Real.exp (c * Y ω) ∂P) =
        Real.exp (P[Y] * c + Var[Y; P] * c ^ 2 / 2) by
      simpa [mgf, Real.coe_toNNReal',
        max_eq_left (variance_nonneg _ _)] using hden,
    div_eq_iff (Real.exp_ne_zero _), htarget, ← Real.exp_add]
  congr 1
  simp only [Real.coe_toNNReal', max_eq_left (variance_nonneg _ _)]
  ring

/-- A finite-dimensional Gaussian random variable remains Gaussian after an
exponential tilt by a jointly Gaussian real coordinate. -/
theorem hasGaussianLaw_tilted_of_joint
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {P : Measure Ω} {X : Ω → E} {Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (c : ℝ) :
    HasGaussianLaw X (P.tilted (fun ω ↦ c * Y ω)) := by
  let Q : Measure Ω := P.tilted (fun ω ↦ c * Y ω)
  have hX : HasGaussianLaw X P := hXY.fst
  have hXQ : AEMeasurable X Q :=
    hX.aemeasurable.mono_ac (tilted_absolutelyContinuous P (fun ω ↦ c * Y ω))
  refine ⟨isGaussian_of_map_eq_gaussianReal fun L ↦ ?_⟩
  let K : E × ℝ →L[ℝ] ℝ × ℝ :=
    (L.comp (ContinuousLinearMap.fst ℝ E ℝ)).prod
      (ContinuousLinearMap.snd ℝ E ℝ)
  have hLY : HasGaussianLaw (fun ω ↦ (L (X ω), Y ω)) P := by
    have hmap := hXY.map_fun K
    simpa [K] using hmap
  have hlaw := hasLaw_gaussian_tilted_of_joint hLY c
  refine ⟨P[fun ω ↦ L (X ω)] + c * cov[fun ω ↦ L (X ω), Y; P],
    Var[fun ω ↦ L (X ω); P].toNNReal, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXQ]
  simpa only [Function.comp_def] using hlaw.map_eq

/-- Translating a finite-dimensional Gaussian random variable by a
deterministic vector preserves Gaussianity. -/
theorem hasGaussianLaw_add_const
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {X : Ω → E} (hX : HasGaussianLaw X P) (c : E) :
    HasGaussianLaw (fun ω ↦ X ω + c) P := by
  refine ⟨?_⟩
  rw [show (fun ω ↦ X ω + c) = (fun x ↦ x + c) ∘ X from rfl,
    ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable]
  let _ : IsGaussian (P.map X) := hX.isGaussian_map
  infer_instance

/-- Exponential tilting by one coordinate of a jointly Gaussian triple
preserves the covariance of the other two coordinates. -/
theorem covariance_gaussian_tilted_of_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y Z : Ω → ℝ}
    (hXYZ : HasGaussianLaw (fun ω ↦ ((X ω, Y ω), Z ω)) P) (c : ℝ) :
    cov[X, Y; P.tilted (fun ω ↦ c * Z ω)] = cov[X, Y; P] := by
  let Q : Measure Ω := P.tilted (fun ω ↦ c * Z ω)
  let LXZ : (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ :=
    { toFun p := (p.1.1, p.2)
      map_add' x y := by ext <;> simp
      map_smul' a x := by ext <;> simp }
  let LYZ : (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ :=
    { toFun p := (p.1.2, p.2)
      map_add' x y := by ext <;> simp
      map_smul' a x := by ext <;> simp }
  let LsumZ : (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ :=
    { toFun p := (p.1.1 + p.1.2, p.2)
      map_add' x y := by ext <;> simp [add_left_comm, add_comm]
      map_smul' a x := by ext <;> simp [mul_add] }
  have hXZ : HasGaussianLaw (fun ω ↦ (X ω, Z ω)) P := by
    simpa [LXZ] using hXYZ.map_fun LXZ
  have hYZ : HasGaussianLaw (fun ω ↦ (Y ω, Z ω)) P := by
    simpa [LYZ] using hXYZ.map_fun LYZ
  have hsumZ : HasGaussianLaw (fun ω ↦ (X ω + Y ω, Z ω)) P := by
    simpa [LsumZ] using hXYZ.map_fun LsumZ
  have hXQ := hasLaw_gaussian_tilted_of_joint hXZ c
  have hYQ := hasLaw_gaussian_tilted_of_joint hYZ c
  have hsumQ := hasLaw_gaussian_tilted_of_joint hsumZ c
  let _ : IsProbabilityMeasure P := hXYZ.isProbabilityMeasure
  let _ : IsProbabilityMeasure Q := hXQ.isProbabilityMeasure
  have hvX : Var[X; Q] = Var[X; P] := by
    rw [hXQ.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal',
      max_eq_left (variance_nonneg _ _)]
  have hvY : Var[Y; Q] = Var[Y; P] := by
    rw [hYQ.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal',
      max_eq_left (variance_nonneg _ _)]
  have hvsum : Var[fun ω ↦ X ω + Y ω; Q] =
      Var[fun ω ↦ X ω + Y ω; P] := by
    rw [hsumQ.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal',
      max_eq_left (variance_nonneg _ _)]
  have hvarQ :=
    variance_add hXQ.hasGaussianLaw.memLp_two hYQ.hasGaussianLaw.memLp_two
  change Var[fun ω ↦ X ω + Y ω; Q] =
    Var[X; Q] + 2 * cov[X, Y; Q] + Var[Y; Q] at hvarQ
  have hvarP := variance_add hXZ.fst.memLp_two hYZ.fst.memLp_two
  change Var[fun ω ↦ X ω + Y ω; P] =
    Var[X; P] + 2 * cov[X, Y; P] + Var[Y; P] at hvarP
  rw [hvsum, hvX, hvY] at hvarQ
  linarith

/-- A Brownian process remains a Gaussian process after a terminal
constant-drift tilt. Its mean changes, but Gaussianity is preserved jointly
at every finite set of times. -/
theorem isGaussianProcess_brownian_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T : ℝ≥0) :
    IsGaussianProcess B (constantGirsanovMeasure P B theta T) := by
  refine ⟨fun I ↦ ?_⟩
  let J : Finset ℝ≥0 := insert T I
  let L : (J → ℝ) →L[ℝ] (I → ℝ) × ℝ :=
    { toFun x := (fun i ↦ x ⟨i, by simp [J]⟩, x ⟨T, by simp [J]⟩)
      map_add' x y := by ext <;> simp
      map_smul' c x := by ext <;> simp }
  have hpair :
      HasGaussianLaw
        (fun ω ↦ (I.restrict (B · ω), B T ω)) P := by
    have hmap := (hB.isGaussianProcess.hasGaussianLaw J).map_fun L
    simpa [J, L, Finset.restrict_def] using hmap
  exact hasGaussianLaw_tilted_of_joint hpair (-theta)

/-- Under a tilt at horizon `T`, the Brownian coordinate at any time `t`
has mean `-theta * min t T` and its original variance. -/
theorem hasLaw_brownian_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T t : ℝ≥0) :
    HasLaw (B t) (gaussianReal (-theta * (min t T : ℝ≥0)) t)
      (constantGirsanovMeasure P B theta T) := by
  have hpair := hB.isGaussianProcess.hasGaussianLaw_prodMk (s := t) (t := T)
  have hlaw := hasLaw_gaussian_tilted_of_joint hpair (-theta)
  simpa [constantGirsanovMeasure, neg_mul, hB.integral_eval, hB.covariance_eval,
    (hB.hasLaw_eval t).variance_eq, variance_id_gaussianReal] using hlaw

/-- The stopped constant drift cancels the mean introduced by the terminal
tilt, at every time before and after the horizon. -/
theorem hasLaw_horizonDriftShifted_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T t : ℝ≥0) :
    HasLaw (horizonDriftShifted B theta T t) (gaussianReal 0 t)
      (constantGirsanovMeasure P B theta T) := by
  change HasLaw (fun ω ↦ B t ω + theta * (min t T : ℝ≥0))
    (gaussianReal 0 t) (constantGirsanovMeasure P B theta T)
  have hlaw := hasLaw_brownian_constantGirsanovMeasure hB theta T t
  have hadd := gaussianReal_add_const hlaw (theta * (min t T : ℝ≥0))
  have hmean :
      -theta * (min t T : ℝ≥0) + theta * (min t T : ℝ≥0) = 0 := by
    ring
  simpa only [hmean] using hadd

set_option backward.isDefEq.respectTransparency false in
/-- The stopped-drift shift is jointly Gaussian under the terminal measure,
not merely Gaussian at each individual time. -/
theorem isGaussianProcess_horizonDriftShifted_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T : ℝ≥0) :
    IsGaussianProcess (horizonDriftShifted B theta T)
      (constantGirsanovMeasure P B theta T) := by
  refine ⟨fun I ↦ ?_⟩
  let Q : Measure Ω := constantGirsanovMeasure P B theta T
  let base : Ω → I → ℝ := fun ω ↦ I.restrict (B · ω)
  let shift : I → ℝ := fun i ↦ theta * (min (i : ℝ≥0) T : ℝ≥0)
  let W : Ω → I → ℝ := fun ω i ↦ base ω i + shift i
  change HasGaussianLaw W Q
  have hbase : HasGaussianLaw base Q :=
    (isGaussianProcess_brownian_constantGirsanovMeasure hB theta T).hasGaussianLaw I
  have hbase_ae : AEMeasurable base Q := hbase.aemeasurable
  have hW_ae : AEMeasurable W Q := by
    exact hbase_ae.add aemeasurable_const
  refine ⟨isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  have hmap :
      (Q.map W).map L =
        ((Q.map base).map L).map (fun x ↦ x + L shift) := by
    calc
      (Q.map W).map L = Q.map (L ∘ W) :=
        AEMeasurable.map_map_of_aemeasurable (by fun_prop) hW_ae
      _ = Q.map ((fun x ↦ x + L shift) ∘ (L ∘ base)) := by
        congr 1
        funext ω
        simp only [Function.comp_apply, W]
        change L (base ω + shift) = L (base ω) + L shift
        rw [L.map_add]
      _ = (Q.map (L ∘ base)).map (fun x ↦ x + L shift) :=
        (AEMeasurable.map_map_of_aemeasurable (by fun_prop)
          ((by fun_prop : AEMeasurable L (Q.map base)).comp_aemeasurable hbase_ae)).symm
      _ = ((Q.map base).map L).map (fun x ↦ x + L shift) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hbase_ae]
  rw [hmap]
  have hscalar : IsGaussian ((Q.map base).map L) := by
    rw [hbase.isGaussian_map.map_eq_gaussianReal L]
    infer_instance
  let _ : IsGaussian ((Q.map base).map L) := hscalar
  infer_instance

/-- A terminal constant-drift tilt preserves the Brownian covariance at all
time pairs, including pairs extending beyond the terminal horizon. -/
theorem covariance_brownian_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T s t : ℝ≥0) :
    cov[B s, B t; constantGirsanovMeasure P B theta T] = min s t := by
  let I : Finset ℝ≥0 := {s, t, T}
  let L : (I → ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
    { toFun x :=
        ((x ⟨s, by simp [I]⟩, x ⟨t, by simp [I]⟩), x ⟨T, by simp [I]⟩)
      map_add' x y := by ext <;> simp
      map_smul' c x := by ext <;> simp }
  have htriple :
      HasGaussianLaw (fun ω ↦ ((B s ω, B t ω), B T ω)) P := by
    have hmap := (hB.isGaussianProcess.hasGaussianLaw I).map_fun L
    simpa [I, L, Finset.restrict_def] using hmap
  have hcov := covariance_gaussian_tilted_of_joint htriple (-theta)
  simpa [constantGirsanovMeasure, neg_mul, hB.covariance_eval] using hcov

/-- Constant-drift Girsanov at a fixed horizon: under the equivalent terminal
measure, adding `theta * t` up to `T` (and keeping that shift constant
after `T`) yields a pre-Brownian process. Thus all finite-dimensional laws
and independent-increment consequences hold under the one measure `Q_T`. -/
theorem isPreBrownianReal_horizonDriftShifted_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (T : ℝ≥0) :
    IsPreBrownianReal (horizonDriftShifted B theta T)
      (constantGirsanovMeasure P B theta T) := by
  let Q : Measure Ω := constantGirsanovMeasure P B theta T
  have hGaussian :=
    isGaussianProcess_horizonDriftShifted_constantGirsanovMeasure hB theta T
  let _ : IsProbabilityMeasure Q := hGaussian.isProbabilityMeasure
  refine hGaussian.isPreBrownianReal_of_covariance (fun t ↦ ?_)
    (fun s t hst ↦ ?_)
  · rw [(hasLaw_horizonDriftShifted_constantGirsanovMeasure
      hB theta T t).integral_eq, integral_id_gaussianReal]
  · have hBs := hasLaw_brownian_constantGirsanovMeasure hB theta T s
    have hBt := hasLaw_brownian_constantGirsanovMeasure hB theta T t
    change cov[
      fun ω ↦ B s ω + theta * (min s T : ℝ≥0),
      fun ω ↦ B t ω + theta * (min t T : ℝ≥0); Q] = (s : ℝ)
    rw [covariance_add_const_left hBs.hasGaussianLaw.integrable,
      covariance_add_const_right hBt.hasGaussianLaw.integrable,
      covariance_brownian_constantGirsanovMeasure hB theta T s t,
      min_eq_left hst]

/-- The exponential moment of an arbitrary two-time Brownian linear
combination. This is the finite-dimensional input for a horizon-consistent
constant-drift tilt. -/
theorem integral_exp_brownian_linearCombination
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (a b : ℝ) (s t : ℝ≥0) :
    (∫ ω, Real.exp (a * B s ω + b * B t ω) ∂P) =
      Real.exp ((a ^ 2 * (s : ℝ) + b ^ 2 * (t : ℝ) +
        2 * a * b * min (s : ℝ) (t : ℝ)) / 2) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hpair := hB.isGaussianProcess.hasGaussianLaw_prodMk (s := s) (t := t)
  have hgauss : HasGaussianLaw (fun ω ↦ a * B s ω + b * B t ω) P := by
    have hmap := hpair.map_fun L
    simpa [L, mul_comm] using hmap
  have hsLp := (hB.hasLaw_eval s).hasGaussianLaw.memLp_two
  have htLp := (hB.hasLaw_eval t).hasGaussianLaw.memLp_two
  have hmean : P[fun ω ↦ a * B s ω + b * B t ω] = 0 := by
    rw [integral_add ((hsLp.const_mul a).integrable one_le_two)
        ((htLp.const_mul b).integrable one_le_two),
      integral_const_mul, integral_const_mul, hB.integral_eval, hB.integral_eval]
    ring
  have hvar : Var[fun ω ↦ a * B s ω + b * B t ω; P] =
      a ^ 2 * (s : ℝ) + b ^ 2 * (t : ℝ) +
        2 * a * b * min (s : ℝ) (t : ℝ) := by
    change Var[(fun ω ↦ a * B s ω) + (fun ω ↦ b * B t ω); P] = _
    rw [variance_add (hsLp.const_mul a) (htLp.const_mul b),
      variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right,
      (hB.hasLaw_eval s).variance_eq, (hB.hasLaw_eval t).variance_eq,
      variance_id_gaussianReal, variance_id_gaussianReal,
      hB.covariance_eval]
    norm_num
    ring
  have hnonneg : 0 ≤ a ^ 2 * (s : ℝ) + b ^ 2 * (t : ℝ) +
      2 * a * b * min (s : ℝ) (t : ℝ) := by
    rw [← hvar]
    exact variance_nonneg _ _
  have hmgf := mgf_gaussianReal hgauss.map_eq_gaussianReal 1
  simpa [mgf, hmean, hvar, Real.coe_toNNReal', max_eq_left hnonneg] using hmgf

private theorem integrable_exp_neg_mul_brownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ Real.exp (-theta * B t ω)) P := by
  have hmapped : Integrable (fun x : ℝ ↦ Real.exp (-theta * x))
      (P.map (B t)) := by
    rw [(hB.hasLaw_eval t).map_eq]
    exact integrable_exp_mul_gaussianReal (-theta)
  have hcomp := (integrable_map_measure hmapped.aestronglyMeasurable
    (hB.hasLaw_eval t).aemeasurable).mp hmapped
  simpa only [Function.comp_def] using hcomp

/-- Tilting at a terminal horizon `T` shifts every earlier one-time Brownian
marginal by `-theta * s`. The single measure in this statement is the first
horizon-consistent part of the constant-drift Girsanov calculation. -/
theorem hasLaw_brownian_under_constantGirsanovMeasure_of_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) {s T : ℝ≥0} (hsT : s ≤ T) :
    HasLaw (B s) (gaussianReal (-theta * (s : ℝ)) s)
      (constantGirsanovMeasure P B theta T) := by
  let Q : Measure Ω := constantGirsanovMeasure P B theta T
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let _ : IsProbabilityMeasure Q :=
    isProbabilityMeasure_tilted (integrable_exp_neg_mul_brownian hB theta T)
  have hBsQ : AEMeasurable (B s) Q :=
    (hB.hasLaw_eval s).aemeasurable.mono_ac
      (tilted_absolutelyContinuous P (fun ω ↦ -theta * B T ω))
  let ν : Measure ℝ := Q.map (B s)
  let _ : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hBsQ
  refine ⟨hBsQ, ?_⟩
  change ν = gaussianReal (-theta * (s : ℝ)) s
  apply eq_gaussianReal_of_mgf_eq ν (-theta * (s : ℝ)) s
  funext u
  change (∫ x, Real.exp (u * x) ∂ν) = _
  rw [show ν = Q.map (B s) from rfl,
    integral_map hBsQ (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (u * x)) (Q.map (B s))),
    show Q = P.tilted (fun ω ↦ -theta * B T ω) from rfl,
    integral_exp_tilted]
  have hsTR : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
  have hnum := integral_exp_brownian_linearCombination hB u (-theta) s T
  rw [min_eq_left hsTR] at hnum
  have hden := integral_exp_brownian_linearCombination hB 0 (-theta) s T
  have htarget := mgf_gaussianReal
    (p := gaussianReal (-theta * (s : ℝ)) s) (X := id)
    (μ := -theta * (s : ℝ)) (v := s) (by simp) u
  rw [show (∫ ω, Real.exp
      (((fun ω ↦ -theta * B T ω) + fun ω ↦ u * B s ω) ω) ∂P) =
        Real.exp ((u ^ 2 * (s : ℝ) + (-theta) ^ 2 * (T : ℝ) +
          2 * u * (-theta) * (s : ℝ)) / 2) by
      simpa only [Pi.add_apply, add_comm] using hnum,
    show (∫ ω, Real.exp (-theta * B T ω) ∂P) =
        Real.exp (theta ^ 2 * (T : ℝ) / 2) by
      simpa using hden,
    div_eq_iff (Real.exp_ne_zero _), htarget, ← Real.exp_add]
  congr 1
  ring

/-- The classical constant-drift exponential density has expectation one. -/
theorem integral_constantExponentialDensity_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (t : ℝ≥0) :
    ∫ ω, constantExponentialDensity B theta t ω ∂P = 1 := by
  have htransport := (hB.hasLaw_eval t).integral_comp
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.exp (-theta * x - theta ^ 2 * (t : ℝ) / 2))
        (gaussianReal 0 t))
  simp only [Function.comp_apply] at htransport
  change (∫ ω, Real.exp
    (-theta * B t ω - theta ^ 2 * (t : ℝ) / 2) ∂P) = 1
  rw [htransport]
  have hfun :
      (fun x : ℝ ↦ Real.exp (-theta * x - theta ^ 2 * (t : ℝ) / 2)) =
        fun x ↦ Real.exp (-theta ^ 2 * (t : ℝ) / 2) * Real.exp (-theta * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_const_mul]
  have hmgf := mgf_gaussianReal
    (p := gaussianReal 0 t) (X := id) (μ := (0 : ℝ)) (v := t)
    (by simp) (-theta)
  rw [show (∫ x, Real.exp (-theta * x) ∂gaussianReal 0 t) =
      Real.exp ((t : ℝ) * theta ^ 2 / 2) by
    simpa [mgf, id_eq] using hmgf,
    ← Real.exp_add]
  rw [show -theta ^ 2 * (t : ℝ) / 2 + (t : ℝ) * theta ^ 2 / 2 = 0 by ring,
    Real.exp_zero]

/-- The terminal Esscher transform is a probability measure. -/
theorem isProbabilityMeasure_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (constantGirsanovMeasure P B theta t) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold constantGirsanovMeasure
  exact isProbabilityMeasure_tilted (integrable_exp_neg_mul_brownian hB theta t)

/-- The original and constant-drift terminal measures have identical null sets. -/
theorem constantGirsanovMeasure_mutuallyAbsolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (t : ℝ≥0) :
    constantGirsanovMeasure P B theta t ≪ P ∧
      P ≪ constantGirsanovMeasure P B theta t := by
  unfold constantGirsanovMeasure
  exact ⟨tilted_absolutelyContinuous P _,
    absolutelyContinuous_tilted (integrable_exp_neg_mul_brownian hB theta t)⟩

/-- Under the terminal tilt, the drift-shifted coordinate is again centered Gaussian. -/
theorem hasLaw_driftShiftedTerminal_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) (t : ℝ≥0) :
    HasLaw (driftShiftedTerminal B theta t) (gaussianReal 0 t)
      (constantGirsanovMeasure P B theta t) := by
  change HasLaw (fun ω ↦ B t ω + theta * (t : ℝ)) (gaussianReal 0 t)
    (P.tilted (fun ω ↦ -theta * B t ω))
  have htilt := hasLaw_gaussian_tilted (hB.hasLaw_eval t) (-theta)
  have hadd := gaussianReal_add_const htilt (theta * (t : ℝ))
  have hmean : (0 + (t : ℝ) * (-theta)) + theta * (t : ℝ) = 0 := by ring
  simpa only [hmean] using hadd

/-- Under a single terminal-horizon tilt, every earlier drift-shifted
coordinate has the correct centered Brownian marginal. This still does not
assert joint laws or independent increments under the tilted measure. -/
  theorem hasLaw_driftShifted_of_le_constantGirsanovMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (theta : ℝ) {s T : ℝ≥0} (hsT : s ≤ T) :
    HasLaw (driftShiftedTerminal B theta s) (gaussianReal 0 s)
      (constantGirsanovMeasure P B theta T) := by
  change HasLaw (fun ω ↦ B s ω + theta * (s : ℝ)) (gaussianReal 0 s)
    (constantGirsanovMeasure P B theta T)
  have htilt := hasLaw_brownian_under_constantGirsanovMeasure_of_le
    hB theta hsT
  have hadd := gaussianReal_add_const htilt (theta * (s : ℝ))
  have hmean : -theta * (s : ℝ) + theta * (s : ℝ) = 0 := by ring
  simpa only [hmean] using hadd

end StochasticCalculus.Girsanov
