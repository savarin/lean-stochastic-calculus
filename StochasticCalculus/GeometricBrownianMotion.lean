/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.WeightedBracketRiemann
import Mathlib.Analysis.ODE.Gronwall

/-!
# Geometric Brownian motion and the linear SDE

This file defines the explicit geometric Brownian process and proves its
fixed-time integral SDE identity from the general time-dependent Itô formula.
The stochastic integral is pinned by concrete uniform Brownian left sums.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace StochasticCalculus

/-- Uniform Lipschitz condition on a pair of scalar SDE coefficients. -/
def IsLipschitzCoeff (b sigma : ℝ≥0 → ℝ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ t x y,
    |b t x - b t y| ≤ K * |x - y| ∧
      |sigma t x - sigma t y| ≤ K * |x - y|

/-- Linear growth bound on a pair of scalar SDE coefficients. -/
def HasLinearGrowth (b sigma : ℝ≥0 → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t x,
    |b t x| ≤ C * (1 + |x|) ∧
      |sigma t x| ≤ C * (1 + |x|)

/-- The linear drift coefficient `x ↦ μx`. -/
def linearDriftCoefficient (drift : ℝ) : ℝ≥0 → ℝ → ℝ :=
  fun _ x => drift * x

/-- The linear diffusion coefficient `x ↦ σx`. -/
def linearDiffusionCoefficient (volatility : ℝ) : ℝ≥0 → ℝ → ℝ :=
  fun _ x => volatility * x

/-- Linear SDE coefficients are uniformly Lipschitz. -/
theorem isLipschitzCoeff_linear
    (drift volatility : ℝ) :
    IsLipschitzCoeff (linearDriftCoefficient drift)
      (linearDiffusionCoefficient volatility) := by
  refine ⟨|drift| + |volatility|, by positivity, fun t x y => ⟨?_, ?_⟩⟩
  · unfold linearDriftCoefficient
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (abs_nonneg volatility)) (abs_nonneg _)
  · unfold linearDiffusionCoefficient
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (abs_nonneg drift)) (abs_nonneg _)

/-- Linear SDE coefficients have a uniform linear-growth bound. -/
theorem hasLinearGrowth_linear
    (drift volatility : ℝ) :
    HasLinearGrowth (linearDriftCoefficient drift)
      (linearDiffusionCoefficient volatility) := by
  refine ⟨|drift| + |volatility|, by positivity, fun t x => ⟨?_, ?_⟩⟩
  · unfold linearDriftCoefficient
    rw [abs_mul]
    calc
      |drift| * |x| ≤ (|drift| + |volatility|) * |x| := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (abs_nonneg volatility)) (abs_nonneg x)
      _ ≤ (|drift| + |volatility|) * (1 + |x|) := by
        exact mul_le_mul_of_nonneg_left
          (by linarith [abs_nonneg x]) (by positivity)
  · unfold linearDiffusionCoefficient
    rw [abs_mul]
    calc
      |volatility| * |x| ≤ (|drift| + |volatility|) * |x| := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (abs_nonneg drift)) (abs_nonneg x)
      _ ≤ (|drift| + |volatility|) * (1 + |x|) := by
        exact mul_le_mul_of_nonneg_left
          (by linarith [abs_nonneg x]) (by positivity)

/-- Integral Grönwall at zero: a continuous scalar error controlled by the
integral of its absolute value vanishes on the whole time interval.  This is
the deterministic endpoint needed after a stochastic difference estimate. -/
theorem eq_zero_of_abs_le_mul_integral_abs
    {u : ℝ → ℝ} {a b K : ℝ}
    (hu : Continuous u)
    (hbound : ∀ t ∈ Icc a b,
      |u t| ≤ K * ∫ s in a..t, |u s|) :
    ∀ t ∈ Icc a b, u t = 0 := by
  let F : ℝ → ℝ := fun t ↦ ∫ s in a..t, |u s|
  have habs : Continuous (fun s ↦ |u s|) := hu.abs
  have hFcont : ContinuousOn F (Icc a b) :=
    (intervalIntegral.differentiable_integral_of_continuous habs).continuous.continuousOn
  have hFderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt F |u t| (Ici t) t := by
    intro t ht
    exact (intervalIntegral.integral_hasDerivAt_right
      (habs.intervalIntegrable a t)
      habs.aestronglyMeasurable.stronglyMeasurableAtFilter
      habs.continuousAt).hasDerivWithinAt
  have hFzero : ∀ t ∈ Icc a b, F t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      hFcont hFderiv
    · simp [F]
    · intro t ht
      have htIcc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
      have hFnonneg : 0 ≤ F t := by
        dsimp only [F]
        exact intervalIntegral.integral_nonneg ht.1
          (fun s _ ↦ abs_nonneg (u s))
      simpa [Real.norm_eq_abs, abs_of_nonneg hFnonneg] using hbound t htIcc
  intro t ht
  have hut := hbound t ht
  rw [show (∫ s in a..t, |u s|) = F t by rfl, hFzero t ht] at hut
  simpa only [mul_zero, abs_nonpos_iff] using hut

/-- Cauchy--Schwarz for the integral of a real `L²` function on a finite
measure space, stated directly in second-moment form. -/
theorem sq_integral_le_measure_mul_integral_sq
    {A : Type*} [MeasurableSpace A] {mu : Measure A}
    [IsFiniteMeasure mu] {f : A → ℝ} (hf : MemLp f 2 mu) :
    (∫ x, f x ∂mu) ^ 2 ≤ mu.real univ * ∫ x, f x ^ 2 ∂mu := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by
    norm_num
    exact hf
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hf' (memLp_const (1 : ℝ))
  have habs : |∫ x, f x ∂mu| ≤ ∫ x, |f x| ∂mu := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
  have hsquare_nonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
    integral_nonneg fun x ↦ sq_nonneg (f x)
  have hmeasure_nonneg : 0 ≤ mu.real univ := measureReal_nonneg
  have hroot : ∫ x, |f x| ∂mu ≤
      (∫ x, f x ^ 2 ∂mu) ^ (1 / (2 : ℝ)) *
        (mu.real univ) ^ (1 / (2 : ℝ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using hholder
  have htotal : |∫ x, f x ∂mu| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂mu) * Real.sqrt (mu.real univ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact habs.trans hroot
  have htotal_nonneg : 0 ≤
      Real.sqrt (∫ x, f x ^ 2 ∂mu) * Real.sqrt (mu.real univ) := by
    positivity
  have hsquared := (sq_le_sq₀ (abs_nonneg _) htotal_nonneg).mpr htotal
  rw [sq_abs, mul_pow, Real.sq_sqrt hsquare_nonneg,
    Real.sq_sqrt hmeasure_nonneg] at hsquared
  nlinarith

/-- The product-measure form of Cauchy--Schwarz and Fubini: the second
moment of an integral in the first variable is controlled by the measure of
that variable times the iterated second moment. -/
theorem integral_sq_integral_le_measure_mul_integral_integral_sq
    {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    {mu : Measure A} {P : Measure W} [SFinite mu] [SFinite P]
    [IsFiniteMeasure mu] [IsFiniteMeasure P]
    {f : A → W → ℝ}
    (hfmeas : AEStronglyMeasurable (Function.uncurry f) (mu.prod P))
    (hfsq : Integrable (Function.uncurry (fun a omega ↦ (f a omega) ^ 2))
      (mu.prod P)) :
    ∫ omega, (∫ a, f a omega ∂mu) ^ 2 ∂P ≤
      mu.real univ * ∫ a, ∫ omega, (f a omega) ^ 2 ∂P ∂mu := by
  have hfmem : MemLp (Function.uncurry f) 2 (mu.prod P) :=
    (memLp_two_iff_integrable_sq hfmeas).2 hfsq
  have hfint : Integrable (Function.uncurry f) (mu.prod P) :=
    hfmem.integrable (by norm_num)
  have hsection_meas := hfmeas.prodMk_right
  have hsection_sq := hfsq.prod_left_ae
  have hpoint : ∀ᵐ omega ∂P,
      (∫ a, f a omega ∂mu) ^ 2 ≤
        mu.real univ * ∫ a, (f a omega) ^ 2 ∂mu := by
    filter_upwards [hsection_meas, hsection_sq] with omega hmeas hsquare
    exact sq_integral_le_measure_mul_integral_sq
      ((memLp_two_iff_integrable_sq hmeas).2 hsquare)
  have hDmeas : AEStronglyMeasurable (fun omega ↦ ∫ a, f a omega ∂mu) P :=
    hfmeas.prod_swap.integral_prod_right'
  have hDsqmeas : AEStronglyMeasurable
      (fun omega ↦ (∫ a, f a omega ∂mu) ^ 2) P := hDmeas.pow 2
  have hinnerint : Integrable (fun omega ↦ ∫ a, (f a omega) ^ 2 ∂mu) P :=
    hfsq.integral_prod_right
  have hRint : Integrable
      (fun omega ↦ mu.real univ * ∫ a, (f a omega) ^ 2 ∂mu) P :=
    hinnerint.const_mul _
  have hDsqint : Integrable
      (fun omega ↦ (∫ a, f a omega ∂mu) ^ 2) P :=
    hRint.mono_nonneg hDsqmeas
      (Eventually.of_forall fun omega ↦ sq_nonneg _)
      hpoint
  calc
    ∫ omega, (∫ a, f a omega ∂mu) ^ 2 ∂P ≤
        ∫ omega, mu.real univ * ∫ a, (f a omega) ^ 2 ∂mu ∂P :=
      integral_mono_ae hDsqint hRint hpoint
    _ = mu.real univ * ∫ omega, ∫ a, (f a omega) ^ 2 ∂mu ∂P := by
      rw [integral_const_mul]
    _ = mu.real univ * ∫ a, ∫ omega, (f a omega) ^ 2 ∂P ∂mu := by
      rw [integral_integral_swap hfsq]

/-- Cauchy--Schwarz--Fubini specialized to a nonnegative compact time
interval. -/
theorem integral_sq_setIntegral_Icc_le
    {W : Type*} [MeasurableSpace W]
    {P : Measure W} [SFinite P] [IsFiniteMeasure P]
    {f : ℝ → W → ℝ} (t : ℝ≥0)
    (hfmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P))
    (hfsq : Integrable (Function.uncurry (fun s omega ↦ (f s omega) ^ 2))
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P)) :
    ∫ omega, (∫ s in Icc (0 : ℝ) (t : ℝ), f s omega) ^ 2 ∂P ≤
      (t : ℝ) * ∫ s in Icc (0 : ℝ) (t : ℝ),
        ∫ omega, (f s omega) ^ 2 ∂P := by
  have h := integral_sq_integral_le_measure_mul_integral_integral_sq
    hfmeas hfsq
  simpa [Measure.real_def, NNReal.coe_nonneg] using h

/-- The elementary `L²` estimate for a sum of two real random variables. -/
theorem integral_sq_add_le_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f g : W → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ omega, (f omega + g omega) ^ 2 ∂P ≤
      2 * ∫ omega, f omega ^ 2 ∂P +
        2 * ∫ omega, g omega ^ 2 ∂P := by
  have hfsq : Integrable (fun omega ↦ f omega ^ 2) P :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hgsq : Integrable (fun omega ↦ g omega ^ 2) P :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hsum : Integrable (fun omega ↦ (f omega + g omega) ^ 2) P :=
    (memLp_two_iff_integrable_sq
      (hf.add hg).aestronglyMeasurable).1 (hf.add hg)
  calc
    ∫ omega, (f omega + g omega) ^ 2 ∂P ≤
        ∫ omega, 2 * f omega ^ 2 + 2 * g omega ^ 2 ∂P := by
      apply integral_mono hsum (hfsq.const_mul 2 |>.add (hgsq.const_mul 2))
      intro omega
      change (f omega + g omega) ^ 2 ≤
        2 * f omega ^ 2 + 2 * g omega ^ 2
      nlinarith [sq_nonneg (f omega - g omega)]
    _ = 2 * ∫ omega, f omega ^ 2 ∂P +
        2 * ∫ omega, g omega ^ 2 ∂P := by
      rw [integral_add (hfsq.const_mul 2) (hgsq.const_mul 2),
        integral_const_mul, integral_const_mul]

/-- Fixed-time almost-everywhere equality of two processes with almost
everywhere continuous paths upgrades to indistinguishability. -/
theorem ae_all_eq_of_continuous_processes
    {T W E : Type*} [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T]
    [TopologicalSpace E] [T2Space E] [MeasurableSpace W]
    {P : Measure W} {X Y : T → W → E}
    (hX : ∀ᵐ omega ∂P, Continuous (fun t ↦ X t omega))
    (hY : ∀ᵐ omega ∂P, Continuous (fun t ↦ Y t omega))
    (hfixed : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ omega ∂P, ∀ t, X t omega = Y t omega := by
  obtain ⟨s : Set T, hscount, hsdense⟩ :=
    TopologicalSpace.exists_countable_dense T
  let _ : Countable s := hscount.to_subtype
  have hsEq : ∀ᵐ omega ∂P, ∀ t : s, X t omega = Y t omega := by
    rw [ae_all_iff]
    intro t
    exact hfixed t
  filter_upwards [hX, hY, hsEq] with omega hXomega hYomega hsomega
  have heqOn : Set.EqOn (fun t ↦ X t omega) (fun t ↦ Y t omega) s := by
    intro t ht
    exact hsomega ⟨t, ht⟩
  have heq := hXomega.ext_on hsdense hYomega heqOn
  intro t
  exact congrFun heq t

/-- The time-dependent exponential used to construct geometric Brownian
motion from its Brownian driver. -/
def geometricBrownianFunction
    (spot drift volatility s x : ℝ) : ℝ :=
  spot * Real.exp
    ((drift - volatility ^ 2 / 2) * s + volatility * x)

/-- Geometric Brownian motion with spot, drift, and volatility parameters. -/
def geometricBrownianMotion
    {W : Type*} (spot drift volatility : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  geometricBrownianFunction spot drift volatility t (B t omega)

/-- Exponential moments of a Brownian coordinate are finite. -/
theorem integrable_exp_mul_brownian_eval
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    Integrable (fun omega ↦ Real.exp (c * B t omega)) P := by
  have hgauss := integrable_exp_mul_gaussianReal
    (μ := (0 : ℝ)) (v := t) c
  rw [← (hB.hasLaw_eval t).map_eq] at hgauss
  change Integrable ((fun x : ℝ ↦ Real.exp (c * x)) ∘ B t) P
  exact hgauss.comp_aemeasurable (hB.aemeasurable t)

/-- The Brownian exponential moment has its exact Gaussian value. -/
theorem integral_exp_mul_brownian_eval
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    ∫ omega, Real.exp (c * B t omega) ∂P =
      Real.exp ((t : ℝ) * c ^ 2 / 2) := by
  simpa only [mgf, zero_mul, zero_add] using
    mgf_gaussianReal (hB.hasLaw_eval t).map_eq c

/-- Brownian exponential coordinates are square-integrable. -/
theorem memLp_exp_mul_brownian_eval_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) (t : ℝ≥0) :
    MemLp (fun omega ↦ Real.exp (c * B t omega)) 2 P := by
  have hgauss : MemLp (fun x : ℝ ↦ Real.exp (c * x)) 2
      (gaussianReal 0 t) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    have hint := integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := t) (2 * c)
    convert hint using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← (hB.hasLaw_eval t).map_eq] at hgauss
  change MemLp ((fun x : ℝ ↦ Real.exp (c * x)) ∘ B t) 2 P
  exact hgauss.comp_of_map (hB.aemeasurable t)

/-- A positive initial spot gives a pointwise positive GBM. -/
theorem geometricBrownianMotion_pos
    {W : Type*} {B : ℝ≥0 → W → ℝ}
    {spot : ℝ} (hspot : 0 < spot) (drift volatility : ℝ)
    (t : ℝ≥0) (omega : W) :
    0 < geometricBrownianMotion spot drift volatility B t omega := by
  unfold geometricBrownianMotion geometricBrownianFunction
  exact mul_pos hspot (Real.exp_pos _)

/-- Every fixed-time GBM coordinate is square-integrable. -/
theorem memLp_geometricBrownianMotion_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (spot drift volatility : ℝ) (t : ℝ≥0) :
    MemLp (geometricBrownianMotion spot drift volatility B t) 2 P := by
  rw [show geometricBrownianMotion spot drift volatility B t =
      fun omega ↦
        (spot * Real.exp ((drift - volatility ^ 2 / 2) * (t : ℝ))) *
          Real.exp (volatility * B t omega) by
    funext omega
    unfold geometricBrownianMotion geometricBrownianFunction
    rw [Real.exp_add]
    ring]
  exact (memLp_exp_mul_brownian_eval_two hB volatility t).const_mul _

/-- The explicit GBM has expectation `spot * exp (drift * t)`. -/
theorem integral_geometricBrownianMotion
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (spot drift volatility : ℝ) (t : ℝ≥0) :
    ∫ omega, geometricBrownianMotion spot drift volatility B t omega ∂P =
      spot * Real.exp (drift * (t : ℝ)) := by
  rw [show (fun omega ↦
      geometricBrownianMotion spot drift volatility B t omega) =
      fun omega ↦
        (spot * Real.exp ((drift - volatility ^ 2 / 2) * (t : ℝ))) *
          Real.exp (volatility * B t omega) by
    funext omega
    unfold geometricBrownianMotion geometricBrownianFunction
    rw [Real.exp_add]
    ring]
  rw [integral_const_mul, integral_exp_mul_brownian_eval hB]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- The exact second moment of GBM.  In particular, the volatility contributes
the additional exponential factor `exp (σ²t)` beyond the squared mean. -/
theorem integral_sq_geometricBrownianMotion
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (spot drift volatility : ℝ) (t : ℝ≥0) :
    ∫ omega, (geometricBrownianMotion spot drift volatility B t omega) ^ 2 ∂P =
      spot ^ 2 * Real.exp ((2 * drift + volatility ^ 2) * (t : ℝ)) := by
  rw [show (fun omega ↦
      (geometricBrownianMotion spot drift volatility B t omega) ^ 2) =
      fun omega ↦
        (spot ^ 2 * Real.exp
          (2 * ((drift - volatility ^ 2 / 2) * (t : ℝ)))) *
          Real.exp ((2 * volatility) * B t omega) by
    funext omega
    unfold geometricBrownianMotion geometricBrownianFunction
    rw [Real.exp_add]
    let A : ℝ := (drift - volatility ^ 2 / 2) * (t : ℝ)
    let C : ℝ := volatility * B t omega
    change (spot * (Real.exp A * Real.exp C)) ^ 2 = _
    rw [pow_two]
    calc
      (spot * (Real.exp A * Real.exp C)) *
          (spot * (Real.exp A * Real.exp C)) =
          (spot ^ 2 * (Real.exp A * Real.exp A)) *
            (Real.exp C * Real.exp C) := by ring
      _ = (spot ^ 2 * Real.exp (A + A)) * Real.exp (C + C) := by
        rw [Real.exp_add, Real.exp_add]
      _ = (spot ^ 2 * Real.exp
          (2 * ((drift - volatility ^ 2 / 2) * (t : ℝ)))) *
          Real.exp ((2 * volatility) * B t omega) := by
        congr 2 <;> dsimp only [A, C] <;> ring_nf]
  rw [integral_const_mul, integral_exp_mul_brownian_eval hB]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- Uniform predictable left sums for the diffusion coefficient `σ X`. -/
def linearSDESpaceApprox
    {W : Type*} (volatility : ℝ) (X B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    volatility * X (uniformPartitionTime t n i) omega *
      (B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega)

/-- A uniform Brownian left sum whose coefficient may depend on the mesh
index.  This form is useful for discrete exit-time localization, where the
coefficient at index `i` remembers whether an earlier grid point has crossed
the localization level. -/
def uniformBrownianLeftSum
    {W : Type*} (C : ℕ → W → ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n, C i omega *
    (B (uniformPartitionTime t n (i + 1)) omega -
      B (uniformPartitionTime t n i) omega)

/-- Samples have remained inside `[-R,R]` through grid index `i`. -/
def uniformGridStaySet
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n i : ℕ) : Set W :=
  ⋂ j ∈ Finset.range (i + 1),
    {omega | |X (uniformPartitionTime t n j) omega| ≤ (R : ℝ)}

/-- The linear diffusion coefficient, switched off permanently after the
first sampled exit from `[-R,R]`. -/
def uniformGridExitCoefficient
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) : W → ℝ :=
  (uniformGridStaySet R X t n i).indicator fun omega ↦
    volatility * X (uniformPartitionTime t n i) omega

/-- The Brownian left sum stopped at the first grid exit of its coefficient
process. -/
def gridExitLinearSDESpaceApprox
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) : W → ℝ :=
  uniformBrownianLeftSum
    (uniformGridExitCoefficient volatility R X t n) B t n

/-- The countably measurable event that every positive uniform mesh up to
`t` remains inside `[-R,R]`. -/
def uniformGridPathStaySet
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) : Set W :=
  ⋂ n : ℕ, uniformGridStaySet R X t (n + 1) (n + 1)

/-- A process switched off after its path has left `[-R,R]`, expressed using
the countably measurable all-mesh event. -/
def pathExitCoefficient
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun t ↦ (uniformGridPathStaySet R X t).indicator (X t)

/-- An ambient `L²` random variable measurable at time `a`, multiplied by a
future Brownian increment, remains in `L²`.  This function-level version of
the elementary Itô construction avoids choosing an `Lp` representative. -/
theorem memLp_two_natural_adapted_mul_brownianIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZmeas : AEStronglyMeasurable[(Filtration.natural B hsm) a] Z P)
    (hZmem : MemLp Z 2 P) :
    MemLp (fun omega ↦ Z omega * (B b omega - B a omega)) 2 P := by
  have hDelta : MemLp (fun omega ↦ B b omega - B a omega) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := indep_increment_of_natural_adapted
    hB hsm rfl hab hZmeas
  have hindSq : IndepFun (fun omega ↦ (B b omega - B a omega) ^ 2)
      (fun omega ↦ Z omega ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hint : Integrable
      ((fun omega ↦ (B b omega - B a omega) ^ 2) *
        fun omega ↦ Z omega ^ 2) P :=
    hindSq.integrable_mul hDelta.integrable_sq hZmem.integrable_sq
  have hZamb : AEStronglyMeasurable Z P :=
    hZmeas.mono ((Filtration.natural B hsm).le a)
  have hprodMeas : AEStronglyMeasurable
      (fun omega ↦ Z omega * (B b omega - B a omega)) P :=
    hZamb.mul hDelta.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hprodMeas).2
  refine hint.congr (Filter.Eventually.of_forall fun omega ↦ ?_)
  simp only [Pi.mul_apply]
  ring

/-- Every square-integrable natural-filtration coefficient times a future
Brownian increment is centered. -/
theorem integral_natural_adapted_mul_brownianIncrement_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZmeas : AEStronglyMeasurable[(Filtration.natural B hsm) a] Z P)
    (_hZmem : MemLp Z 2 P) :
    ∫ omega, Z omega * (B b omega - B a omega) ∂P = 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  have hDelta : MemLp (fun omega ↦ B b omega - B a omega) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hZamb : AEStronglyMeasurable Z P :=
    hZmeas.mono ((Filtration.natural B hsm).le a)
  have hfactor := (indep_increment_of_natural_adapted
    hB hsm rfl hab hZmeas).symm.integral_mul_eq_mul_integral
      hZamb hDelta.aestronglyMeasurable
  change ∫ omega, (Z * fun w ↦ B b w - B a w) omega ∂P = 0
  rw [hfactor]
  rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
    hB.integral_eval, hB.integral_eval, sub_zero, mul_zero]

/-- Exact diagonal Itô isometry for one adapted coefficient and one future
Brownian increment. -/
theorem integral_sq_natural_adapted_mul_brownianIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b) {Z : W → ℝ}
    (hZmeas : AEStronglyMeasurable[(Filtration.natural B hsm) a] Z P)
    (hZmem : MemLp Z 2 P) :
    ∫ omega, (Z omega * (B b omega - B a omega)) ^ 2 ∂P =
      ((b : ℝ) - a) * ∫ omega, Z omega ^ 2 ∂P := by
  have hDelta : MemLp (fun omega ↦ B b omega - B a omega) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := indep_increment_of_natural_adapted
    hB hsm rfl hab hZmeas
  have hindSq : IndepFun (fun omega ↦ (B b omega - B a omega) ^ 2)
      (fun omega ↦ Z omega ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hDelta.integrable_sq.aestronglyMeasurable
    hZmem.integrable_sq.aestronglyMeasurable
  calc
    (∫ omega, (Z omega * (B b omega - B a omega)) ^ 2 ∂P) =
        ∫ omega, (B b omega - B a omega) ^ 2 * Z omega ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with omega
      ring
    _ = (∫ omega, (B b omega - B a omega) ^ 2 ∂P) *
        ∫ omega, Z omega ^ 2 ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = ((b : ℝ) - a) * ∫ omega, Z omega ^ 2 ∂P := by
      rw [integral_incr_sq hB hab]

/-- Adapted Brownian integral terms carried by chronologically disjoint
intervals are orthogonal. -/
theorem integral_mul_natural_adapted_brownianIncrements_eq_zero_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {Z Y : W → ℝ}
    (hZmeas : AEStronglyMeasurable[(Filtration.natural B hsm) a] Z P)
    (hYmeas : AEStronglyMeasurable[(Filtration.natural B hsm) c] Y P)
    (hZmem : MemLp Z 2 P) (hYmem : MemLp Y 2 P) :
    ∫ omega,
        (Z omega * (B b omega - B a omega)) *
          (Y omega * (B d omega - B c omega)) ∂P = 0 := by
  let naturalF := Filtration.natural B hsm
  have hac : a ≤ c := hab.trans hbc
  have hBadapted : StronglyAdapted naturalF B :=
    Filtration.stronglyAdapted_natural hsm
  have hZc : AEStronglyMeasurable[naturalF c] Z P :=
    hZmeas.mono (naturalF.mono hac)
  have hDeltaAB : AEStronglyMeasurable[naturalF c]
      (fun omega ↦ B b omega - B a omega) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[naturalF c]
      (fun omega ↦ (Z omega * (B b omega - B a omega)) * Y omega) P :=
    (hZc.mul hDeltaAB).mul hYmeas
  have hDeltaCD : MemLp (fun omega ↦ B d omega - B c omega) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfirstMem := memLp_two_natural_adapted_mul_brownianIncrement
    hB hsm hab hZmeas hZmem
  have hsecondMem := memLp_two_natural_adapted_mul_brownianIncrement
    hB hsm hcd hYmeas hYmem
  have _hproductIntegrable := hfirstMem.integrable_mul hsecondMem
  have hfactor := (indep_increment_of_natural_adapted
    hB hsm rfl hcd hG).symm.integral_mul_eq_mul_integral
      (hG.mono (naturalF.le c)) hDeltaCD.aestronglyMeasurable
  calc
    (∫ omega,
        (Z omega * (B b omega - B a omega)) *
          (Y omega * (B d omega - B c omega)) ∂P) =
        ∫ omega,
          ((Z omega * (B b omega - B a omega)) * Y omega) *
            (B d omega - B c omega) ∂P := by
      apply integral_congr_ae
      filter_upwards with omega
      ring
    _ = (∫ omega,
          (Z omega * (B b omega - B a omega)) * Y omega ∂P) *
        ∫ omega, B d omega - B c omega ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval d) (hB.integrable_eval c),
        hB.integral_eval, hB.integral_eval, sub_zero, mul_zero]

/-- The second moment of a finite sum of pairwise orthogonal real `L²`
random variables is the sum of their second moments. -/
theorem integral_sq_finsetSum_of_pairwise_integral_mul_eq_zero
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    (s : Finset I) (Y : I → W → ℝ)
    (hYmem : ∀ i, MemLp (Y i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ omega, Y i omega * Y j omega ∂P = 0) :
    ∫ omega, (∑ i ∈ s, Y i omega) ^ 2 ∂P =
      ∑ i ∈ s, ∫ omega, (Y i omega) ^ 2 ∂P := by
  classical
  have htermInt (i j : I) :
      Integrable (fun omega ↦ Y i omega * Y j omega) P :=
    (hYmem i).integrable_mul (hYmem j)
  have hexpand (omega : W) :
      (∑ i ∈ s, Y i omega) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, Y i omega * Y j omega := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  rw [integral_finsetSum s (fun i _hi ↦
    integrable_finsetSum s (fun j _hj ↦ htermInt i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j _hj ↦ htermInt i j)]
  rw [Finset.sum_eq_single i]
  · apply integral_congr_ae
    filter_upwards with omega
    rw [pow_two]
  · intro j hj hji
    exact horth i hi j hj hji.symm
  · exact fun hni ↦ (hni hi).elim

/-- A grid-indexed adapted Brownian left sum is square-integrable whenever
each coefficient used by the grid is square-integrable. -/
theorem memLp_two_uniformBrownianLeftSum
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {C : ℕ → W → ℝ} {t : ℝ≥0} {n : ℕ}
    (hCmeas : ∀ i,
      AEStronglyMeasurable[(Filtration.natural B hsm)
        (uniformPartitionTime t n i)] (C i) P)
    (hCmem : ∀ i, MemLp (C i) 2 P) :
    MemLp (uniformBrownianLeftSum C B t n) 2 P := by
  unfold uniformBrownianLeftSum
  apply memLp_finsetSum (Finset.range n)
  intro i hi
  have hle : uniformPartitionTime t n i ≤
      uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  exact memLp_two_natural_adapted_mul_brownianIncrement
    hB hsm hle (hCmeas i) (hCmem i)

/-- A grid-indexed adapted Brownian left sum is centered. -/
theorem integral_uniformBrownianLeftSum_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {C : ℕ → W → ℝ} {t : ℝ≥0} {n : ℕ}
    (hCmeas : ∀ i,
      AEStronglyMeasurable[(Filtration.natural B hsm)
        (uniformPartitionTime t n i)] (C i) P)
    (hCmem : ∀ i, MemLp (C i) 2 P) :
    ∫ omega, uniformBrownianLeftSum C B t n omega ∂P = 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  unfold uniformBrownianLeftSum
  rw [integral_finsetSum (Finset.range n)]
  · apply Finset.sum_eq_zero
    intro i hi
    have hle : uniformPartitionTime t n i ≤
        uniformPartitionTime t n (i + 1) := by
      unfold uniformPartitionTime
      gcongr
      omega
    exact integral_natural_adapted_mul_brownianIncrement_eq_zero
      hB hsm hle (hCmeas i) (hCmem i)
  · intro i hi
    have hle : uniformPartitionTime t n i ≤
        uniformPartitionTime t n (i + 1) := by
      unfold uniformPartitionTime
      gcongr
      omega
    exact (memLp_two_natural_adapted_mul_brownianIncrement
      hB hsm hle (hCmeas i) (hCmem i)).integrable (by norm_num)

/-- Exact discrete Itô isometry for grid-indexed adapted coefficients. -/
theorem integral_sq_uniformBrownianLeftSum
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {C : ℕ → W → ℝ} {t : ℝ≥0} {n : ℕ}
    (hCmeas : ∀ i,
      AEStronglyMeasurable[(Filtration.natural B hsm)
        (uniformPartitionTime t n i)] (C i) P)
    (hCmem : ∀ i, MemLp (C i) 2 P) :
    ∫ omega, (uniformBrownianLeftSum C B t n omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) *
          ∫ omega, (C i omega) ^ 2 ∂P := by
  classical
  let Y : ℕ → W → ℝ := fun i omega ↦
    C i omega *
      (B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega)
  have htimeStep (i : ℕ) : uniformPartitionTime t n i ≤
      uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  have hYmem (i : ℕ) : MemLp (Y i) 2 P :=
    memLp_two_natural_adapted_mul_brownianIncrement
      hB hsm (htimeStep i) (hCmeas i) (hCmem i)
  have horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → ∫ omega, Y i omega * Y j omega ∂P = 0 := by
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt
    · have hbetween : uniformPartitionTime t n (i + 1) ≤
          uniformPartitionTime t n j := by
        unfold uniformPartitionTime
        gcongr
        omega
      exact integral_mul_natural_adapted_brownianIncrements_eq_zero_of_le
        hB hsm (htimeStep i) hbetween (htimeStep j)
          (hCmeas i) (hCmeas j) (hCmem i) (hCmem j)
    · have hbetween : uniformPartitionTime t n (j + 1) ≤
          uniformPartitionTime t n i := by
        unfold uniformPartitionTime
        gcongr
        omega
      calc
        (∫ omega, Y i omega * Y j omega ∂P) =
            ∫ omega, Y j omega * Y i omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = 0 :=
          integral_mul_natural_adapted_brownianIncrements_eq_zero_of_le
            hB hsm (htimeStep j) hbetween (htimeStep i)
              (hCmeas j) (hCmeas i) (hCmem j) (hCmem i)
  unfold uniformBrownianLeftSum
  change (∫ omega, (∑ i ∈ Finset.range n, Y i omega) ^ 2 ∂P) = _
  rw [integral_sq_finsetSum_of_pairwise_integral_mul_eq_zero
    (Finset.range n) Y (fun i ↦ hYmem i) horth]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_sq_natural_adapted_mul_brownianIncrement
    hB hsm (htimeStep i) (hCmeas i) (hCmem i)

/-- The finite grid stay event through index `i` is measurable at the
corresponding grid time. -/
theorem measurableSet_uniformGridStaySet
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (R : ℝ≥0) (t : ℝ≥0) (n i : ℕ) :
    MeasurableSet[V (uniformPartitionTime t n i)]
      (uniformGridStaySet R X t n i) := by
  unfold uniformGridStaySet
  apply Finset.measurableSet_biInter
  intro j hj
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have htime : uniformPartitionTime t n j ≤
      uniformPartitionTime t n i :=
    monotone_uniformPartitionTime_general t n hji
  simpa only [Real.norm_eq_abs] using
    (hX.stronglyMeasurable_le htime).norm.measurableSet_le
      stronglyMeasurable_const

/-- Requiring the path to stay inside through a later grid index implies
the corresponding requirement at every earlier index. -/
theorem uniformGridStaySet_anti
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    uniformGridStaySet R X t n j ⊆ uniformGridStaySet R X t n i := by
  intro omega homega
  simp only [uniformGridStaySet, Set.mem_iInter, Set.mem_ofPred_eq] at homega ⊢
  intro k hk
  exact homega k (Finset.mem_range.mpr
    ((Finset.mem_range.mp hk).trans_le (Nat.succ_le_succ hij)))

/-- Grid stay events grow with the localization level. -/
theorem uniformGridStaySet_mono_level
    {W : Type*} {R S : ℝ≥0} (hRS : R ≤ S)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) :
    uniformGridStaySet R X t n i ⊆ uniformGridStaySet S X t n i := by
  intro omega homega
  simp only [uniformGridStaySet, Set.mem_iInter, Set.mem_ofPred_eq] at homega ⊢
  intro j hj
  exact (homega j hj).trans (by exact_mod_cast hRS)

/-- All-mesh path stay events grow with the localization level. -/
theorem uniformGridPathStaySet_mono_level
    {W : Type*} {R S : ℝ≥0} (hRS : R ≤ S)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) :
    uniformGridPathStaySet R X t ⊆ uniformGridPathStaySet S X t := by
  intro omega homega
  simp only [uniformGridPathStaySet, Set.mem_iInter] at homega ⊢
  intro n
  exact uniformGridStaySet_mono_level hRS X t (n + 1) (n + 1)
    (homega n)

/-- A pointwise bound on the whole deterministic interval implies every
finite-grid stay event. -/
theorem mem_uniformGridStaySet_of_bound
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) (omega : W)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ≥0) t, |X s omega| ≤ (R : ℝ)) :
    omega ∈ uniformGridStaySet R X t n i := by
  simp only [uniformGridStaySet, Set.mem_iInter, Set.mem_ofPred_eq]
  intro j hj
  exact hbound _ (uniformPartitionTime_mem_Icc_of_le t hn
    ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hi))

/-- For a positive mesh size, the full grid stay event is measurable at its
horizon. -/
theorem measurableSet_uniformGridStaySet_horizon
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (R : ℝ≥0) (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    MeasurableSet[V t] (uniformGridStaySet R X t n n) := by
  have hmeas := measurableSet_uniformGridStaySet hX R t n n
  have hn0 : (n : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hend : uniformPartitionTime t n n = t := by
    unfold uniformPartitionTime
    exact mul_div_cancel_right₀ t hn0
  rwa [hend] at hmeas

/-- The all-mesh path stay event is measurable at the deterministic
horizon. -/
theorem measurableSet_uniformGridPathStaySet
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (R : ℝ≥0) (t : ℝ≥0) :
    MeasurableSet[V t] (uniformGridPathStaySet R X t) := by
  unfold uniformGridPathStaySet
  exact MeasurableSet.iInter fun n ↦
    measurableSet_uniformGridStaySet_horizon hX R t (Nat.zero_lt_succ n)

/-- The path-exit coefficient is strongly adapted. -/
theorem stronglyAdapted_pathExitCoefficient
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (R : ℝ≥0) : StronglyAdapted V (pathExitCoefficient R X) := by
  intro t
  exact (hX t).indicator (measurableSet_uniformGridPathStaySet hX R t)

/-- Membership in the all-mesh stay event controls the endpoint value. -/
theorem abs_le_of_mem_uniformGridPathStaySet
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W)
    (hstay : omega ∈ uniformGridPathStaySet R X t) :
    |X t omega| ≤ (R : ℝ) := by
  have hmesh := Set.mem_iInter.mp hstay 0
  have hend : uniformPartitionTime t 1 1 = t := by
    norm_num [uniformPartitionTime]
  have hendpoint := Set.mem_iInter₂.mp hmesh 1 (by simp)
  simpa only [Set.mem_ofPred_eq, hend] using hendpoint

/-- The path-exit coefficient is bounded by its localization level. -/
theorem norm_pathExitCoefficient_le
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    ‖pathExitCoefficient R X t omega‖ ≤ (R : ℝ) := by
  classical
  by_cases hstay : omega ∈ uniformGridPathStaySet R X t
  · rw [pathExitCoefficient, Set.indicator_of_mem hstay, Real.norm_eq_abs]
    exact abs_le_of_mem_uniformGridPathStaySet R X t omega hstay
  · rw [pathExitCoefficient, Set.indicator_of_notMem hstay, norm_zero]
    exact NNReal.coe_nonneg R

/-- Every section of the bounded path-exit coefficient is in `L²`. -/
theorem memLp_two_pathExitCoefficient
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (R : ℝ≥0) (t : ℝ≥0) : MemLp (pathExitCoefficient R X t) 2 P := by
  apply MemLp.of_bound (p := (2 : ℝ≥0∞)) (μ := P)
    (((stronglyAdapted_pathExitCoefficient hX R t).mono
      (V.le t)).aestronglyMeasurable) (R : ℝ)
  exact Filter.Eventually.of_forall fun omega ↦
    norm_pathExitCoefficient_le R X t omega

/-- Almost every continuous path belongs to some integer-level all-mesh stay
event on each fixed compact horizon. -/
theorem ae_mem_iUnion_uniformGridPathStaySet
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℝ≥0 → W → ℝ}
    (hXcont : ∀ᵐ omega ∂P, Continuous (fun t ↦ X t omega))
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P,
      omega ∈ ⋃ R : ℕ, uniformGridPathStaySet (R : ℝ≥0) X t := by
  let hmod : IsContinuousProcessModification X X P :=
    ⟨fun _ ↦ Filter.EventuallyEq.rfl, hXcont⟩
  have hgrid := hmod.uniformPartition_bounded t
  filter_upwards [hgrid] with omega homega
  obtain ⟨K, hK⟩ := homega
  obtain ⟨R : ℕ, hKR⟩ := exists_nat_ge K
  apply Set.mem_iUnion.mpr
  refine ⟨R, ?_⟩
  simp only [uniformGridPathStaySet, uniformGridStaySet,
    Set.mem_iInter, Set.mem_ofPred_eq]
  intro n j hj
  have hjle : j ≤ n + 1 :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hK n j hjle).trans (by simpa using hKR)

/-- For a continuous path, the countable all-mesh event is exactly the
usual compact-horizon uniform bound. -/
theorem mem_uniformGridPathStaySet_iff_of_continuous
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W)
    (hXcont : Continuous (fun s ↦ X s omega)) :
    omega ∈ uniformGridPathStaySet R X t ↔
      ∀ s ∈ Set.Icc (0 : ℝ≥0) t, |X s omega| ≤ (R : ℝ) := by
  constructor
  · intro hstay s hs
    have htime := tendsto_uniformPartitionTime_dyadicApproxIndex hs.2
    have habs : Tendsto
        (fun n ↦ |X
          (uniformPartitionTime t (2 ^ n) (dyadicApproxIndex s t n))
          omega|) Filter.atTop (nhds |X s omega|) :=
      (hXcont.abs.tendsto s).comp htime
    apply le_of_tendsto habs
    exact Filter.Eventually.of_forall fun n ↦ by
      let k : ℕ := 2 ^ n
      have hk : 0 < k := by
        dsimp only [k]
        positivity
      have hmesh : omega ∈ uniformGridStaySet R X t k k := by
        have hpred := Set.mem_iInter.mp hstay (Nat.pred k)
        have hsucc : Nat.pred k + 1 = k := Nat.succ_pred_eq_of_pos hk
        simpa only [hsucc] using hpred
      exact Set.mem_iInter₂.mp hmesh (dyadicApproxIndex s t n)
        (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (dyadicApproxIndex_le_pow hs.2 n)))
  · intro hbound
    simp only [uniformGridPathStaySet, Set.mem_iInter]
    intro n
    exact mem_uniformGridStaySet_of_bound R X t
      (Nat.zero_lt_succ n) le_rfl omega hbound

/-- Before a continuous path exits its localization interval, the path-exit
coefficient agrees with the original process. -/
theorem pathExitCoefficient_eq_of_continuous_of_bound
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W)
    (hXcont : Continuous (fun s ↦ X s omega))
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ≥0) t, |X s omega| ≤ (R : ℝ)) :
    pathExitCoefficient R X t omega = X t omega := by
  rw [pathExitCoefficient, Set.indicator_of_mem]
  exact (mem_uniformGridPathStaySet_iff_of_continuous
    R X t omega hXcont).2 hbound

/-- After a continuous path has exceeded its localization interval, the
path-exit coefficient is zero. -/
theorem pathExitCoefficient_eq_zero_of_continuous_of_exists_abs_gt
    {W : Type*} (R : ℝ≥0) (X : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W)
    (hXcont : Continuous (fun s ↦ X s omega))
    (hexit : ∃ s ∈ Set.Icc (0 : ℝ≥0) t, (R : ℝ) < |X s omega|) :
    pathExitCoefficient R X t omega = 0 := by
  rw [pathExitCoefficient, Set.indicator_of_notMem]
  intro hstay
  obtain ⟨s, hs, hlarge⟩ := hexit
  exact (not_lt_of_ge
    ((mem_uniformGridPathStaySet_iff_of_continuous
      R X t omega hXcont).1 hstay s hs)) hlarge

/-- On the full stay event for one mesh, exit gating does not change its
Brownian left sum. -/
theorem gridExitLinearSDESpaceApprox_eq_of_mem_gridStaySet
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W)
    (hstay : omega ∈ uniformGridStaySet R X t n n) :
    gridExitLinearSDESpaceApprox volatility R X B t n omega =
      linearSDESpaceApprox volatility X B t n omega := by
  classical
  unfold gridExitLinearSDESpaceApprox uniformBrownianLeftSum
    uniformGridExitCoefficient linearSDESpaceApprox
  apply Finset.sum_congr rfl
  intro i hi
  rw [Set.indicator_of_mem
    (uniformGridStaySet_anti R X t n
      (Nat.le_of_lt (Finset.mem_range.mp hi)) hstay)]

/-- On the all-mesh path stay event, every positive exit-gated approximation
agrees with the original SDE approximation. -/
theorem gridExitLinearSDESpaceApprox_eq_of_mem_pathStaySet
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X B : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (omega : W)
    (hstay : omega ∈ uniformGridPathStaySet R X t) :
    gridExitLinearSDESpaceApprox volatility R X B t (n + 1) omega =
      linearSDESpaceApprox volatility X B t (n + 1) omega := by
  apply gridExitLinearSDESpaceApprox_eq_of_mem_gridStaySet
  exact Set.mem_iInter.mp hstay n

/-- The grid-exit coefficient is adapted at its left endpoint. -/
theorem stronglyMeasurable_uniformGridExitCoefficient
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) (n i : ℕ) :
    StronglyMeasurable[V (uniformPartitionTime t n i)]
      (uniformGridExitCoefficient volatility R X t n i) := by
  unfold uniformGridExitCoefficient
  exact ((hX _).const_mul volatility).indicator
    (measurableSet_uniformGridStaySet hX R t n i)

/-- The exit-gated coefficient has the deterministic localization bound. -/
theorem norm_uniformGridExitCoefficient_le
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) (omega : W) :
    ‖uniformGridExitCoefficient volatility R X t n i omega‖ ≤
      |volatility| * (R : ℝ) := by
  classical
  by_cases hstay : omega ∈ uniformGridStaySet R X t n i
  · rw [uniformGridExitCoefficient, Set.indicator_of_mem hstay,
      Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg volatility)
    have hi : i ∈ Finset.range (i + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_self i)
    exact Set.mem_iInter₂.mp hstay i hi
  · rw [uniformGridExitCoefficient, Set.indicator_of_notMem hstay,
      norm_zero]
    positivity

/-- Once an earlier grid stay condition fails, every later exit coefficient
on the same mesh is zero. -/
theorem uniformGridExitCoefficient_eq_zero_of_not_mem
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ)
    {i j : ℕ} (hij : i ≤ j) (omega : W)
    (hexit : omega ∉ uniformGridStaySet R X t n i) :
    uniformGridExitCoefficient volatility R X t n j omega = 0 := by
  unfold uniformGridExitCoefficient
  rw [Set.indicator_of_notMem]
  intro hstay
  exact hexit (uniformGridStaySet_anti R X t n hij hstay)

/-- Squaring an exit coefficient is the indicator of the corresponding
coefficient square. -/
theorem sq_uniformGridExitCoefficient
    {W : Type*} (volatility : ℝ) (R : ℝ≥0)
    (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n i : ℕ) (omega : W) :
    (uniformGridExitCoefficient volatility R X t n i omega) ^ 2 =
      (uniformGridStaySet R X t n i).indicator
        (fun omega ↦
          (volatility * X (uniformPartitionTime t n i) omega) ^ 2) omega := by
  classical
  by_cases hstay : omega ∈ uniformGridStaySet R X t n i
  · rw [uniformGridExitCoefficient, Set.indicator_of_mem hstay,
      Set.indicator_of_mem hstay]
  · rw [uniformGridExitCoefficient, Set.indicator_of_notMem hstay,
      Set.indicator_of_notMem hstay, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Every exit-gated grid coefficient is square-integrable. -/
theorem memLp_two_uniformGridExitCoefficient
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : StronglyAdapted V X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) (n i : ℕ) :
    MemLp (uniformGridExitCoefficient volatility R X t n i) 2 P := by
  apply MemLp.of_bound (p := (2 : ℝ≥0∞)) (μ := P)
    ((stronglyMeasurable_uniformGridExitCoefficient
      hX volatility R t n i).mono
        (V.le (uniformPartitionTime t n i))).aestronglyMeasurable
    (|volatility| * (R : ℝ))
  exact Filter.Eventually.of_forall fun omega ↦
    norm_uniformGridExitCoefficient_le volatility R X t n i omega

/-- Exit-gated uniform Brownian sums are square-integrable. -/
theorem memLp_two_gridExitLinearSDESpaceApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    MemLp (gridExitLinearSDESpaceApprox volatility R X B t n) 2 P := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  exact memLp_two_uniformBrownianLeftSum hB hsm
    (fun i ↦ (stronglyMeasurable_uniformGridExitCoefficient
      hX volatility R t n i).aestronglyMeasurable)
    (fun i ↦ memLp_two_uniformGridExitCoefficient
      hX volatility R t n i)

/-- Exact discrete Itô isometry for the exit-gated SDE approximation. -/
theorem integral_sq_gridExitLinearSDESpaceApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ∫ omega,
        (gridExitLinearSDESpaceApprox volatility R X B t n omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) *
          ∫ omega,
            (uniformGridStaySet R X t n i).indicator
              (fun omega ↦
                (volatility *
                  X (uniformPartitionTime t n i) omega) ^ 2) omega ∂P := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  rw [show gridExitLinearSDESpaceApprox volatility R X B t n =
      uniformBrownianLeftSum
        (uniformGridExitCoefficient volatility R X t n) B t n by rfl,
    integral_sq_uniformBrownianLeftSum hB hsm
      (fun i ↦ (stronglyMeasurable_uniformGridExitCoefficient
        hX volatility R t n i).aestronglyMeasurable)
      (fun i ↦ memLp_two_uniformGridExitCoefficient
        hX volatility R t n i)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply integral_congr_ae
  filter_upwards with omega
  exact sq_uniformGridExitCoefficient volatility R X t n i omega

/-- Exit-gated uniform Brownian sums are centered. -/
theorem integral_gridExitLinearSDESpaceApprox_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ∫ omega, gridExitLinearSDESpaceApprox volatility R X B t n omega ∂P = 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  exact integral_uniformBrownianLeftSum_eq_zero hB hsm
    (fun i ↦ (stronglyMeasurable_uniformGridExitCoefficient
      hX volatility R t n i).aestronglyMeasurable)
    (fun i ↦ memLp_two_uniformGridExitCoefficient
      hX volatility R t n i)

/-- The exit-gated Brownian sum has the uniform localization-level second
moment bound. -/
theorem integral_sq_gridExitLinearSDESpaceApprox_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0)
    {n : ℕ} (hn : 0 < n) :
    ∫ omega,
        (gridExitLinearSDESpaceApprox volatility R X B t n omega) ^ 2 ∂P ≤
      (|volatility| * (R : ℝ)) ^ 2 * (t : ℝ) := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  let C : ℕ → W → ℝ := uniformGridExitCoefficient volatility R X t n
  have hCmeas (i : ℕ) :
      AEStronglyMeasurable[(Filtration.natural B hsm)
        (uniformPartitionTime t n i)] (C i) P :=
    (stronglyMeasurable_uniformGridExitCoefficient
      hX volatility R t n i).aestronglyMeasurable
  have hCmem (i : ℕ) : MemLp (C i) 2 P :=
    memLp_two_uniformGridExitCoefficient hX volatility R t n i
  have hCsq (i : ℕ) : ∫ omega, (C i omega) ^ 2 ∂P ≤
      (|volatility| * (R : ℝ)) ^ 2 := by
    have hpoint : ∀ omega, (C i omega) ^ 2 ≤
        (|volatility| * (R : ℝ)) ^ 2 := by
      intro omega
      have habs : |C i omega| ≤ |volatility| * (R : ℝ) := by
        simpa only [C, Real.norm_eq_abs] using
        norm_uniformGridExitCoefficient_le volatility R X t n i omega
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (C i omega)) (by positivity)).mpr habs
    calc
      (∫ omega, (C i omega) ^ 2 ∂P) ≤
          ∫ _omega : W, (|volatility| * (R : ℝ)) ^ 2 ∂P := by
        exact integral_mono (hCmem i).integrable_sq (integrable_const _)
          hpoint
      _ = (|volatility| * (R : ℝ)) ^ 2 := by simp
  rw [show gridExitLinearSDESpaceApprox volatility R X B t n =
      uniformBrownianLeftSum C B t n by rfl,
    integral_sq_uniformBrownianLeftSum hB hsm hCmeas hCmem]
  calc
    (∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) *
          ∫ omega, (C i omega) ^ 2 ∂P) ≤
        ∑ i ∈ Finset.range n,
          ((uniformPartitionTime t n (i + 1) : ℝ) -
            (uniformPartitionTime t n i : ℝ)) *
            (|volatility| * (R : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (hCsq i)
      exact sub_nonneg.mpr (by
        exact_mod_cast monotone_uniformPartitionTime_general t n
          (Nat.le_succ i))
    _ = (|volatility| * (R : ℝ)) ^ 2 *
        ∑ i ∈ Finset.range n,
          ((uniformPartitionTime t n (i + 1) : ℝ) -
            (uniformPartitionTime t n i : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (|volatility| * (R : ℝ)) ^ 2 * (t : ℝ) := by
      congr 1
      have hmono : Monotone
          (fun i ↦ (uniformPartitionTime t n i : ℝ)) := by
        intro i j hij
        exact_mod_cast monotone_uniformPartitionTime_general t n hij
      rw [Finset.sum_range_tsub hmono]
      have hn0 : (n : ℝ≥0) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn
      simp [uniformPartitionTime, hn0]

/-- Seminorm form of the uniform exit-gated second-moment estimate. -/
theorem eLpNorm_gridExitLinearSDESpaceApprox_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0)
    {n : ℕ} (hn : 0 < n) :
    eLpNorm (gridExitLinearSDESpaceApprox volatility R X B t n) 2 P ≤
      ENNReal.ofReal
        ((|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ)) := by
  have hmem := memLp_two_gridExitLinearSDESpaceApprox
    hB hsm hX volatility R t n
  have hsq := integral_sq_gridExitLinearSDESpaceApprox_le
    hB hsm hX volatility R t hn
  have hsqeq :
      (∫ omega,
        (gridExitLinearSDESpaceApprox volatility R X B t n omega) ^ 2 ∂P) =
        (eLpNorm
          (gridExitLinearSDESpaceApprox volatility R X B t n) 2 P).toReal ^ 2 := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have hnonneg : 0 ≤ ∫ omega,
        (gridExitLinearSDESpaceApprox volatility R X B t n omega) ^ 2 ∂P :=
      integral_nonneg fun omega ↦ sq_nonneg _
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt hnonneg]
  rw [hsqeq] at hsq
  have hCnonneg :
      0 ≤ (|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ) := by
    positivity
  apply (ENNReal.toReal_le_toReal hmem.eLpNorm_lt_top.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hCnonneg]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).mp
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
  exact hsq

/-- On an all-mesh path-stay event, any probability limit of the original
SDE sums is locally square-integrable.  This is the first stopping-compatible
bridge from the Challenge's unbounded left-sum contract to the global `L²`
estimates. -/
theorem memLp_two_indicator_of_linearSDESpaceApprox_limit_on_pathStaySet
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hX : StronglyAdapted (Filtration.natural B hsm) X)
    (volatility : ℝ) (R : ℝ≥0) (t : ℝ≥0) {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop I) :
    let A := uniformGridPathStaySet R X t
    MemLp (A.indicator I) 2 P ∧
      eLpNorm (A.indicator I) 2 P ≤ ENNReal.ofReal
        ((|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ)) := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  let A := uniformGridPathStaySet R X t
  let S : ℕ → W → ℝ := fun n ↦
    gridExitLinearSDESpaceApprox volatility R X B t (n + 1)
  have hAfil : MeasurableSet[(Filtration.natural B hsm) t] A :=
    measurableSet_uniformGridPathStaySet hX R t
  have hA : MeasurableSet A :=
    (Filtration.natural B hsm).le t A hAfil
  have hSmem (n : ℕ) : MemLp (S n) 2 P :=
    memLp_two_gridExitLinearSDESpaceApprox
      hB hsm hX volatility R t (n + 1)
  have hSbound (n : ℕ) : eLpNorm (S n) 2 P ≤ ENNReal.ofReal
      ((|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ)) := by
    exact eLpNorm_gridExitLinearSDESpaceApprox_le
      hB hsm hX volatility R t (Nat.zero_lt_succ n)
  have hlimit : TendstoInMeasure P
      (fun n ↦ A.indicator (S n)) Filter.atTop (A.indicator I) := by
    have hraw := hI.indicator A
    apply hraw.congr_left
    intro n
    filter_upwards with omega
    by_cases hstay : omega ∈ A
    · rw [Set.indicator_of_mem hstay, Set.indicator_of_mem hstay]
      exact (gridExitLinearSDESpaceApprox_eq_of_mem_pathStaySet
        volatility R X B t n omega hstay).symm
    · rw [Set.indicator_of_notMem hstay, Set.indicator_of_notMem hstay]
  have hindMeas (n : ℕ) : AEStronglyMeasurable (A.indicator (S n)) P :=
    (hSmem n).aestronglyMeasurable.indicator hA
  have hnorm : eLpNorm (A.indicator I) 2 P ≤ ENNReal.ofReal
      ((|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ)) :=
    eLpNorm_le_of_tendstoInMeasure
      (Filter.Eventually.of_forall fun n ↦
        (eLpNorm_indicator_le (S n)).trans (hSbound n))
      hlimit hindMeas
  exact ⟨⟨hlimit.aestronglyMeasurable hindMeas,
    hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

/-- For a real square-integrable function, its second moment is the square
of the real-valued `L²` seminorm. -/
theorem integral_sq_eq_eLpNorm_two_toReal_sq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : W → ℝ} (hf : MemLp f 2 P) :
    ∫ omega, f omega ^ 2 ∂P = (eLpNorm f 2 P).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hnonneg : 0 ≤ ∫ omega, f omega ^ 2 ∂P :=
    integral_nonneg (fun omega ↦ sq_nonneg (f omega))
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt hnonneg]

/-- Uniform left sums of an adapted, pointwise square-integrable process are
themselves square-integrable. -/
theorem memLp_two_linearSDESpaceApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (n : ℕ) :
    MemLp (linearSDESpaceApprox volatility X B t n) 2 P := by
  unfold linearSDESpaceApprox
  apply memLp_finsetSum (Finset.range n)
  intro i _hi
  have hle : uniformPartitionTime t n i ≤
      uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  exact memLp_two_natural_adapted_mul_brownianIncrement
    hB hsm hle
      ((hXadapted (uniformPartitionTime t n i)).const_mul
        volatility).aestronglyMeasurable
      ((hXmem _).const_mul volatility)

/-- Exact discrete Itô isometry for the uniform left sum of a pointwise
`L²`, natural-filtration adapted process. -/
theorem integral_sq_linearSDESpaceApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (n : ℕ) :
    ∫ omega, (linearSDESpaceApprox volatility X B t n omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) *
          ∫ omega,
            (volatility * X (uniformPartitionTime t n i) omega) ^ 2 ∂P := by
  classical
  let Y : ℕ → W → ℝ := fun i omega ↦
    volatility * X (uniformPartitionTime t n i) omega *
      (B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega)
  have htimeStep (i : ℕ) : uniformPartitionTime t n i ≤
      uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  have hYmem (i : ℕ) : MemLp (Y i) 2 P := by
    exact memLp_two_natural_adapted_mul_brownianIncrement
      hB hsm (htimeStep i)
        ((hXadapted (uniformPartitionTime t n i)).const_mul
          volatility).aestronglyMeasurable
        ((hXmem _).const_mul volatility)
  have horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → ∫ omega, Y i omega * Y j omega ∂P = 0 := by
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt
    · have hbetween : uniformPartitionTime t n (i + 1) ≤
          uniformPartitionTime t n j := by
        unfold uniformPartitionTime
        gcongr
        omega
      exact integral_mul_natural_adapted_brownianIncrements_eq_zero_of_le
        hB hsm (htimeStep i) hbetween (htimeStep j)
          ((hXadapted (uniformPartitionTime t n i)).const_mul
            volatility).aestronglyMeasurable
          ((hXadapted (uniformPartitionTime t n j)).const_mul
            volatility).aestronglyMeasurable
          ((hXmem _).const_mul volatility)
          ((hXmem _).const_mul volatility)
    · have hbetween : uniformPartitionTime t n (j + 1) ≤
          uniformPartitionTime t n i := by
        unfold uniformPartitionTime
        gcongr
        omega
      calc
        (∫ omega, Y i omega * Y j omega ∂P) =
            ∫ omega, Y j omega * Y i omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = 0 :=
          integral_mul_natural_adapted_brownianIncrements_eq_zero_of_le
            hB hsm (htimeStep j) hbetween (htimeStep i)
              ((hXadapted (uniformPartitionTime t n j)).const_mul
                volatility).aestronglyMeasurable
              ((hXadapted (uniformPartitionTime t n i)).const_mul
                volatility).aestronglyMeasurable
              ((hXmem _).const_mul volatility)
              ((hXmem _).const_mul volatility)
  unfold linearSDESpaceApprox
  change (∫ omega, (∑ i ∈ Finset.range n, Y i omega) ^ 2 ∂P) = _
  rw [integral_sq_finsetSum_of_pairwise_integral_mul_eq_zero
    (Finset.range n) Y hYmem horth]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_sq_natural_adapted_mul_brownianIncrement
    hB hsm (htimeStep i)
      ((hXadapted (uniformPartitionTime t n i)).const_mul
        volatility).aestronglyMeasurable
      ((hXmem _).const_mul volatility)

/-- A uniform bound on the fixed-time second moments of the coefficient
gives the standard `K² t` bound for every positive uniform left sum. -/
theorem integral_sq_linearSDESpaceApprox_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2)
    {n : ℕ} (hn : 0 < n) :
    ∫ omega, (linearSDESpaceApprox volatility X B t n omega) ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * (t : ℝ) := by
  rw [integral_sq_linearSDESpaceApprox
    hB hsm hXadapted hXmem volatility t n]
  have htimeStep (i : ℕ) : uniformPartitionTime t n i ≤
      uniformPartitionTime t n (i + 1) := by
    unfold uniformPartitionTime
    gcongr
    omega
  calc
    (∑ i ∈ Finset.range n,
        ((uniformPartitionTime t n (i + 1) : ℝ) -
          (uniformPartitionTime t n i : ℝ)) *
          ∫ omega,
            (volatility * X (uniformPartitionTime t n i) omega) ^ 2 ∂P) ≤
        ∑ i ∈ Finset.range n,
          ((uniformPartitionTime t n (i + 1) : ℝ) -
            (uniformPartitionTime t n i : ℝ)) * (K : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact hbound _ (uniformPartitionTime_mem_Icc_of_le
          t hn (Nat.le_of_lt (Finset.mem_range.mp hi)))
      · exact sub_nonneg.mpr (by exact_mod_cast htimeStep i)
    _ = (K : ℝ) ^ 2 *
        ∑ i ∈ Finset.range n,
          ((uniformPartitionTime t n (i + 1) : ℝ) -
            (uniformPartitionTime t n i : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (K : ℝ) ^ 2 * (t : ℝ) := by
      congr 1
      have hmono : Monotone
          (fun i ↦ (uniformPartitionTime t n i : ℝ)) := by
        intro i j hij
        exact_mod_cast show uniformPartitionTime t n i ≤
          uniformPartitionTime t n j by
            unfold uniformPartitionTime
            gcongr
      rw [Finset.sum_range_tsub hmono]
      have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      simp [uniformPartitionTime, hn0]

/-- The `L²` seminorm form of the uniform left-sum bound. -/
theorem eLpNorm_linearSDESpaceApprox_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2)
    {n : ℕ} (hn : 0 < n) :
    eLpNorm (linearSDESpaceApprox volatility X B t n) 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hmem := memLp_two_linearSDESpaceApprox
    hB hsm hXadapted hXmem volatility t n
  have hsq := integral_sq_linearSDESpaceApprox_le
    hB hsm hXadapted hXmem volatility t K hbound hn
  rw [integral_sq_eq_eLpNorm_two_toReal_sq hmem] at hsq
  have hCnonneg : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  apply (ENNReal.toReal_le_toReal hmem.eLpNorm_lt_top.ne
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hCnonneg]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).mp
  rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
  exact hsq

/-- The full sequence of positive uniform Brownian left sums is uniformly
integrable in `L¹` under a uniform fixed-time second-moment bound. -/
theorem unifIntegrable_linearSDESpaceApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2) :
    UniformIntegrable
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1)) 1 P := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  let C : ℝ≥0 := ⟨(K : ℝ) * Real.sqrt (t : ℝ),
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)⟩
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (linearSDESpaceApprox volatility X B t (n + 1)) P :=
    (memLp_two_linearSDESpaceApprox
      hB hsm hXadapted hXmem volatility t (n + 1)).aestronglyMeasurable
  have htwo (n : ℕ) : eLpNorm
      (linearSDESpaceApprox volatility X B t (n + 1)) 2 P ≤
        (C : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact eLpNorm_linearSDESpaceApprox_le
      hB hsm hXadapted hXmem volatility t K hbound (Nat.zero_lt_succ n)
  refine ⟨hmeas, ?_, ⟨C, fun n ↦ ?_⟩⟩
  · exact unifIntegrable_of_eLpNorm_two_bounded_of_lt_two
      (P := P) (by norm_num) (by norm_num) hmeas C htwo
  · exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hmeas n)).trans
      (htwo n)

/-- Every square-integrable adapted uniform Brownian left sum has mean zero. -/
theorem integral_linearSDESpaceApprox_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (n : ℕ) :
    ∫ omega, linearSDESpaceApprox volatility X B t n omega ∂P = 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  unfold linearSDESpaceApprox
  rw [integral_finsetSum (Finset.range n)]
  · apply Finset.sum_eq_zero
    intro i hi
    have hle : uniformPartitionTime t n i ≤
        uniformPartitionTime t n (i + 1) := by
      unfold uniformPartitionTime
      gcongr
      omega
    exact integral_natural_adapted_mul_brownianIncrement_eq_zero
      hB hsm hle
        ((hXadapted (uniformPartitionTime t n i)).const_mul
          volatility).aestronglyMeasurable
        ((hXmem _).const_mul volatility)
  · intro i hi
    have hle : uniformPartitionTime t n i ≤
        uniformPartitionTime t n (i + 1) := by
      unfold uniformPartitionTime
      gcongr
      omega
    exact (memLp_two_natural_adapted_mul_brownianIncrement
      hB hsm hle
        ((hXadapted (uniformPartitionTime t n i)).const_mul
          volatility).aestronglyMeasurable
        ((hXmem _).const_mul volatility)).integrable (by norm_num)

/-- A probability limit of uniformly `L²`-bounded adapted Brownian left
sums remains in `L²`, with the same seminorm bound. -/
theorem memLp_two_linearSDESpaceApprox_limit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2)
    {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop I) :
    MemLp I 2 P ∧
      eLpNorm I 2 P ≤ ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (linearSDESpaceApprox volatility X B t (n + 1)) P :=
    (memLp_two_linearSDESpaceApprox
      hB hsm hXadapted hXmem volatility t (n + 1)).aestronglyMeasurable
  have hnorm : eLpNorm I 2 P ≤
      ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) :=
    eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n ↦ eLpNorm_linearSDESpaceApprox_le
        hB hsm hXadapted hXmem volatility t K hbound (Nat.zero_lt_succ n))
      hI hmeas
  exact ⟨⟨hI.aestronglyMeasurable hmeas,
    hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

/-- The second-moment form of the bound for a probability limit of adapted
Brownian left sums. -/
theorem integral_sq_linearSDESpaceApprox_limit_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2)
    {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop I) :
    ∫ omega, I omega ^ 2 ∂P ≤ (K : ℝ) ^ 2 * (t : ℝ) := by
  obtain ⟨hImem, hInorm⟩ := memLp_two_linearSDESpaceApprox_limit
    hB hsm hXadapted hXmem volatility t K hbound hI
  rw [integral_sq_eq_eLpNorm_two_toReal_sq hImem]
  have hCnonneg : 0 ≤ (K : ℝ) * Real.sqrt (t : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm I 2 P).toReal ≤
      (K : ℝ) * Real.sqrt (t : ℝ) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hInorm
    simpa [ENNReal.toReal_ofReal hCnonneg] using this
  calc
    (eLpNorm I 2 P).toReal ^ 2 ≤
        ((K : ℝ) * Real.sqrt (t : ℝ)) ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg hCnonneg).mpr hreal
    _ = (K : ℝ) ^ 2 * (t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]

/-- With a continuous coefficient second-moment profile, the limiting
stochastic integral satisfies the sharp Itô-isometry upper bound.  The proof
uses the exact discrete isometry, deterministic Riemann convergence, and
lower semicontinuity of the `L²` seminorm under convergence in probability. -/
theorem integral_sq_linearSDESpaceApprox_limit_le_integral
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0)
    (hmoment : Continuous (fun s : ℝ ↦
      ∫ omega, (volatility * X s.toNNReal omega) ^ 2 ∂P))
    {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop I) :
    MemLp I 2 P ∧
      ∫ omega, I omega ^ 2 ∂P ≤
        ∫ s in Icc (0 : ℝ) (t : ℝ),
          ∫ omega, (volatility * X s.toNNReal omega) ^ 2 ∂P := by
  let S : ℕ → W → ℝ := fun n ↦
    linearSDESpaceApprox volatility X B t (n + 1)
  let L : ℝ := ∫ s in Icc (0 : ℝ) (t : ℝ),
    ∫ omega, (volatility * X s.toNNReal omega) ^ 2 ∂P
  have hSmem (n : ℕ) : MemLp (S n) 2 P := by
    simpa only [S] using memLp_two_linearSDESpaceApprox
      hB hsm hXadapted hXmem volatility t (n + 1)
  have hsecond : Tendsto (fun n ↦ ∫ omega, (S n omega) ^ 2 ∂P)
      Filter.atTop (nhds L) := by
    have hRiemann := tendsto_uniformPartition_leftRiemann
      (fun s : ℝ ↦ ∫ omega,
        (volatility * X s.toNNReal omega) ^ 2 ∂P) hmoment t
    simpa only [S, L, Real.toNNReal_coe, mul_comm,
      integral_sq_linearSDESpaceApprox
        hB hsm hXadapted hXmem volatility] using hRiemann
  have hLnonneg : 0 ≤ L := by
    dsimp only [L]
    exact integral_nonneg fun s ↦ integral_nonneg fun omega ↦
      sq_nonneg (volatility * X s.toNNReal omega)
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
    hI.aestronglyMeasurable (fun n ↦ (hSmem n).aestronglyMeasurable)
  have hInorm : eLpNorm I 2 P ≤ ENNReal.ofReal (Real.sqrt L) := by
    have hlower := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (2 : ℝ≥0∞))
      (fun n ↦ (hSmem (ns n)).aestronglyMeasurable) I (by
        simpa only [S] using hnsae)
    rwa [hennnorm.liminf_eq] at hlower
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

/-- A probability limit of uniformly `L²`-bounded adapted Brownian left
sums is integrable and centered.  This is the Vitali-convergence bridge from
the concrete sums in `IsStrongLinearSDESolution` to their stochastic limit. -/
theorem integrable_and_integral_linearSDESpaceApprox_limit_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (hXadapted : StronglyAdapted (Filtration.natural B hsm) X)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (volatility : ℝ) (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2)
    {I : W → ℝ}
    (hI : TendstoInMeasure P
      (fun n ↦ linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop I) :
    Integrable I P ∧ ∫ omega, I omega ∂P = 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  have hui := unifIntegrable_linearSDESpaceApprox
    hB hsm hXadapted hXmem volatility t K hbound
  have hIint : Integrable I P := hui.integrable_of_tendstoInMeasure hI
  refine ⟨hIint, ?_⟩
  have hLp : Tendsto
      (fun n ↦ eLpNorm
        (linearSDESpaceApprox volatility X B t (n + 1) - I) 1 P)
      Filter.atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (p := (1 : ℝ≥0∞))
      le_rfl ENNReal.one_ne_top
      (fun n ↦ (memLp_two_linearSDESpaceApprox
        hB hsm hXadapted hXmem volatility t (n + 1)).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hIint) hui.unifIntegrable hI
  have hLpReal : Tendsto
      (fun n ↦ (eLpNorm
        (linearSDESpaceApprox volatility X B t (n + 1) - I) 1 P).toReal)
      Filter.atTop (nhds 0) := by
    change Tendsto
      (ENNReal.toReal ∘ fun n ↦ eLpNorm
        (linearSDESpaceApprox volatility X B t (n + 1) - I) 1 P)
      Filter.atTop (nhds 0)
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp
  have hnormle (n : ℕ) : ‖∫ omega, I omega ∂P‖ ≤
      (eLpNorm
        (linearSDESpaceApprox volatility X B t (n + 1) - I) 1 P).toReal := by
    let S := linearSDESpaceApprox volatility X B t (n + 1)
    have hSmem : MemLp S 2 P := memLp_two_linearSDESpaceApprox
      hB hsm hXadapted hXmem volatility t (n + 1)
    have hSint : Integrable S P := hSmem.integrable (by norm_num)
    have hSmean : ∫ omega, S omega ∂P = 0 :=
      integral_linearSDESpaceApprox_eq_zero
        hB hsm hXadapted hXmem volatility t (n + 1)
    have hdiff : Integrable (fun omega ↦ S omega - I omega) P :=
      hSint.sub hIint
    calc
      ‖∫ omega, I omega ∂P‖ =
          ‖(∫ omega, S omega ∂P) - ∫ omega, I omega ∂P‖ := by
            rw [hSmean, zero_sub, norm_neg]
      _ = ‖∫ omega, S omega - I omega ∂P‖ := by
        rw [integral_sub hSint hIint]
      _ ≤ ∫ omega, ‖S omega - I omega‖ ∂P :=
        norm_integral_le_integral_norm _
      _ = (eLpNorm (S - I) 1 P).toReal := by
        change (∫ omega, ‖S omega - I omega‖ ∂P) =
          (eLpNorm (fun omega ↦ S omega - I omega) 1 P).toReal
        simpa only [eLpNorm_one_eq_lintegral_enorm] using
          integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable
  have hnormzero : ‖∫ omega, I omega ∂P‖ ≤ 0 :=
    ge_of_tendsto hLpReal (Eventually.of_forall hnormle)
  exact norm_eq_zero.mp (le_antisymm hnormzero (norm_nonneg _))

/-- The stochastic residual in the integral form of `dX = μX dt + σX dB`. -/
def linearSDEResidual
    {W : Type*} (drift : ℝ) (X : ℝ≥0 → W → ℝ)
    (spot : ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  X t omega - spot -
    ∫ s in Icc (0 : ℝ) (t : ℝ), drift * X s.toNNReal omega

/-- Strong solutions of the scalar linear Brownian SDE, with the stochastic
integral pinned by concrete left-sum convergence in probability. -/
structure IsStrongLinearSDESolution
    {W : Type*} [MeasurableSpace W]
    (X B : ℝ≥0 → W → ℝ) (P : Measure W)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (spot drift volatility : ℝ) : Prop where
  adapted : StronglyAdapted (Filtration.natural B hsm) X
  continuous_paths : ∀ᵐ omega ∂P, Continuous (fun t => X t omega)
  initial : X 0 =ᵐ[P] fun _ => spot
  drift_integrable : ∀ t, ∀ᵐ omega ∂P,
    IntegrableOn (fun s : ℝ => drift * X s.toNNReal omega)
      (Icc 0 (t : ℝ))
  integral_equation : ∀ t,
    TendstoInMeasure P
      (fun n => linearSDESpaceApprox volatility X B t (n + 1))
      Filter.atTop (linearSDEResidual drift X spot t)

/-- A strong linear-SDE solution has an `L²` stochastic residual whenever
its diffusion coefficient has uniformly bounded second moments up to the
specified time. -/
theorem IsStrongLinearSDESolution.residual_memLp_two
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2) :
    MemLp (linearSDEResidual drift X spot t) 2 P ∧
      eLpNorm (linearSDEResidual drift X spot t) 2 P ≤
        ENNReal.ofReal ((K : ℝ) * Real.sqrt (t : ℝ)) :=
  memLp_two_linearSDESpaceApprox_limit
    hB hsm hX.adapted hXmem volatility t K hbound (hX.integral_equation t)

/-- Every strong solution has a locally square-integrable stochastic
residual on each all-mesh path-stay event, without any global moment
assumption on the solution. -/
theorem IsStrongLinearSDESolution.residual_indicator_memLp_two_on_pathStaySet
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (R : ℝ≥0) (t : ℝ≥0) :
    let A := uniformGridPathStaySet R X t
    MemLp (A.indicator (linearSDEResidual drift X spot t)) 2 P ∧
      eLpNorm (A.indicator (linearSDEResidual drift X spot t)) 2 P ≤
        ENNReal.ofReal
          ((|volatility| * (R : ℝ)) * Real.sqrt (t : ℝ)) :=
  memLp_two_indicator_of_linearSDESpaceApprox_limit_on_pathStaySet
    hB hsm hX.adapted volatility R t (hX.integral_equation t)

/-- The stochastic residual of a strong solution satisfies the usual local
Itô second-moment estimate. -/
theorem IsStrongLinearSDESolution.integral_sq_residual_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2) :
    ∫ omega, (linearSDEResidual drift X spot t omega) ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * (t : ℝ) :=
  integral_sq_linearSDESpaceApprox_limit_le
    hB hsm hX.adapted hXmem volatility t K hbound (hX.integral_equation t)

/-- If the diffusion-coefficient second moment is continuous in time, a
strong solution's stochastic residual obeys the sharp integral estimate. -/
theorem IsStrongLinearSDESolution.integral_sq_residual_le_integral
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (hmoment : Continuous (fun s : ℝ ↦
      ∫ omega, (volatility * X s.toNNReal omega) ^ 2 ∂P))
    (t : ℝ≥0) :
    MemLp (linearSDEResidual drift X spot t) 2 P ∧
      ∫ omega, (linearSDEResidual drift X spot t omega) ^ 2 ∂P ≤
        ∫ s in Icc (0 : ℝ) (t : ℝ),
          ∫ omega, (volatility * X s.toNNReal omega) ^ 2 ∂P :=
  integral_sq_linearSDESpaceApprox_limit_le_integral
    hB hsm hX.adapted hXmem volatility t hmoment (hX.integral_equation t)

/-- An `L²` zero-initial strong solution of the linear SDE vanishes at every
fixed time.  The hypotheses record precisely the time-continuity and product
integrability needed for the Cauchy--Schwarz--Fubini step; no uniqueness
conclusion is assumed. -/
theorem IsStrongLinearSDESolution.ae_eq_zero_of_l2
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B Z : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)} {drift volatility : ℝ}
    (hZ : IsStrongLinearSDESolution Z B P hsm 0 drift volatility)
    (hZmem : ∀ t, MemLp (Z t) 2 P)
    (hu : Continuous (fun s : ℝ ↦ ∫ omega, (Z s.toNNReal omega) ^ 2 ∂P))
    (hjointMeas : ∀ t : ℝ≥0,
      AEStronglyMeasurable
        (Function.uncurry (fun s : ℝ ↦ fun omega ↦
          drift * Z s.toNNReal omega))
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P))
    (hjointSq : ∀ t : ℝ≥0,
      Integrable
        (Function.uncurry (fun s : ℝ ↦ fun omega ↦
          (drift * Z s.toNNReal omega) ^ 2))
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P)) :
    ∀ t, Z t =ᵐ[P] fun _ ↦ 0 := by
  let _ : IsProbabilityMeasure P :=
    hB.isGaussianProcess.isProbabilityMeasure
  let u : ℝ → ℝ := fun s ↦ ∫ omega, (Z s.toNNReal omega) ^ 2 ∂P
  have hu' : Continuous u := hu
  have hunonneg (s : ℝ) : 0 ≤ u s :=
    integral_nonneg fun omega ↦ sq_nonneg (Z s.toNNReal omega)
  have hcoeff (c : ℝ) (q : ℝ≥0) :
      (∫ s in Icc (0 : ℝ) (q : ℝ),
        ∫ omega, (c * Z s.toNNReal omega) ^ 2 ∂P) =
        c ^ 2 * ∫ s in Icc (0 : ℝ) (q : ℝ), u s := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s _hs
    dsimp only [u]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with omega
    ring
  have hvolmoment : Continuous (fun s : ℝ ↦
      ∫ omega, (volatility * Z s.toNNReal omega) ^ 2 ∂P) := by
    have hc : Continuous (fun s ↦ volatility ^ 2 * u s) :=
      continuous_const.mul hu'
    convert hc using 1
    funext s
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with omega
    ring
  have hmoment_le (q : ℝ≥0) : u q ≤
      (2 * (q : ℝ) * drift ^ 2 + 2 * volatility ^ 2) *
        ∫ s in Icc (0 : ℝ) (q : ℝ), u s := by
    let D : W → ℝ := fun omega ↦
      ∫ s in Icc (0 : ℝ) (q : ℝ), drift * Z s.toNNReal omega
    let R : W → ℝ := linearSDEResidual drift Z 0 q
    obtain ⟨hRmem, hRbound⟩ :=
      hZ.integral_sq_residual_le_integral hB hZmem hvolmoment q
    have hDfun : D = Z q - R := by
      funext omega
      simp only [D, R, Pi.sub_apply]
      unfold linearSDEResidual
      ring
    have hDmem : MemLp D 2 P := by
      rw [hDfun]
      exact (hZmem q).sub hRmem
    have hZfun : Z q = D + R := by
      rw [hDfun]
      ext omega
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have hsum := integral_sq_add_le_two hDmem hRmem
    have hZbound : ∫ omega, (Z q omega) ^ 2 ∂P ≤
        2 * ∫ omega, (D omega) ^ 2 ∂P +
          2 * ∫ omega, (R omega) ^ 2 ∂P := by
      rw [hZfun]
      exact hsum
    have hDbound := integral_sq_setIntegral_Icc_le q
      (hjointMeas q) (hjointSq q)
    calc
      u q = ∫ omega, (Z q omega) ^ 2 ∂P := by
        simp only [u, Real.toNNReal_coe]
      _ ≤ 2 * ∫ omega, (D omega) ^ 2 ∂P +
          2 * ∫ omega, (R omega) ^ 2 ∂P := hZbound
      _ ≤ 2 * ((q : ℝ) *
            ∫ s in Icc (0 : ℝ) (q : ℝ),
              ∫ omega, (drift * Z s.toNNReal omega) ^ 2 ∂P) +
          2 * (∫ s in Icc (0 : ℝ) (q : ℝ),
            ∫ omega, (volatility * Z s.toNNReal omega) ^ 2 ∂P) := by
        gcongr
      _ = (2 * (q : ℝ) * drift ^ 2 + 2 * volatility ^ 2) *
          ∫ s in Icc (0 : ℝ) (q : ℝ), u s := by
        rw [hcoeff drift q, hcoeff volatility q]
        ring
  intro T
  let K : ℝ := 2 * (T : ℝ) * drift ^ 2 + 2 * volatility ^ 2
  have hgronwall : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), u s = 0 := by
    exact eq_zero_of_abs_le_mul_integral_abs hu' (fun s hs ↦ by
      have hm := hmoment_le s.toNNReal
      rw [Real.coe_toNNReal s hs.1] at hm
      have hintnonneg : 0 ≤ ∫ r in Icc (0 : ℝ) s, u r :=
        integral_nonneg fun r ↦ hunonneg r
      have hcoef : 2 * s * drift ^ 2 + 2 * volatility ^ 2 ≤ K := by
        dsimp only [K]
        have hmul : s * drift ^ 2 ≤ (T : ℝ) * drift ^ 2 :=
          mul_le_mul_of_nonneg_right hs.2 (sq_nonneg drift)
        linarith
      have hmain : u s ≤ K * ∫ r in Icc (0 : ℝ) s, u r :=
        hm.trans (mul_le_mul_of_nonneg_right hcoef hintnonneg)
      rw [abs_of_nonneg (hunonneg s)]
      have habsIntegral : (∫ r in (0 : ℝ)..s, |u r|) =
          ∫ r in Icc (0 : ℝ) s, u r := by
        rw [intervalIntegral.integral_of_le hs.1,
          ← integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _hr
        exact abs_of_nonneg (hunonneg r)
      rw [habsIntegral]
      exact hmain)
  have hmomentZero : ∫ omega, (Z T omega) ^ 2 ∂P = 0 := by
    simpa only [u, Real.toNNReal_coe] using
      hgronwall T ⟨NNReal.coe_nonneg T, le_rfl⟩
  have hsqint : Integrable (fun omega ↦ (Z T omega) ^ 2) P :=
    (memLp_two_iff_integrable_sq (hZmem T).aestronglyMeasurable).1 (hZmem T)
  have hsqzero : (fun omega ↦ (Z T omega) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun omega ↦ sq_nonneg (Z T omega)) hsqint).1 hmomentZero
  filter_upwards [hsqzero] with omega homega
  simpa using (sq_eq_zero_iff.mp homega)

/-- Under the same local second-moment bound, the stochastic residual of a
strong linear-SDE solution is integrable and has expectation zero. -/
theorem IsStrongLinearSDESolution.integrable_residual_and_integral_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hXmem : ∀ t, MemLp (X t) 2 P)
    (t : ℝ≥0) (K : ℝ≥0)
    (hbound : ∀ s ∈ Icc 0 t,
      ∫ omega, (volatility * X s omega) ^ 2 ∂P ≤ (K : ℝ) ^ 2) :
    Integrable (linearSDEResidual drift X spot t) P ∧
      ∫ omega, linearSDEResidual drift X spot t omega ∂P = 0 :=
  integrable_and_integral_linearSDESpaceApprox_limit_eq_zero
    hB hsm hX.adapted hXmem volatility t K hbound (hX.integral_equation t)

/-- The uniform diffusion sum is linear in its candidate solution. -/
theorem linearSDESpaceApprox_sub
    {W : Type*} (volatility : ℝ) (X Y B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) :
    linearSDESpaceApprox volatility
        (fun s omega ↦ X s omega - Y s omega) B t n omega =
      linearSDESpaceApprox volatility X B t n omega -
        linearSDESpaceApprox volatility Y B t n omega := by
  unfold linearSDESpaceApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Subtracting two integrable linear-SDE residuals with the same initial
value produces the zero-initial residual of the difference process. -/
theorem linearSDEResidual_sub
    {W : Type*} (drift : ℝ) (X Y : ℝ≥0 → W → ℝ)
    (spot : ℝ) (t : ℝ≥0) (omega : W)
    (hX : IntegrableOn (fun s : ℝ ↦ drift * X s.toNNReal omega)
      (Icc 0 (t : ℝ)))
    (hY : IntegrableOn (fun s : ℝ ↦ drift * Y s.toNNReal omega)
      (Icc 0 (t : ℝ))) :
    linearSDEResidual drift (fun s omega ↦ X s omega - Y s omega)
        0 t omega =
      linearSDEResidual drift X spot t omega -
        linearSDEResidual drift Y spot t omega := by
  unfold linearSDEResidual
  rw [show (∫ s in Icc (0 : ℝ) (t : ℝ),
      drift * (X s.toNNReal omega - Y s.toNNReal omega)) =
      (∫ s in Icc (0 : ℝ) (t : ℝ), drift * X s.toNNReal omega) -
        ∫ s in Icc (0 : ℝ) (t : ℝ), drift * Y s.toNNReal omega by
    rw [← MeasureTheory.integral_sub hX hY]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s _hs
    ring]
  ring

/-- The difference of two strong solutions driven by the same Brownian
motion is a zero-initial strong solution of the same homogeneous equation. -/
theorem IsStrongLinearSDESolution.sub
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X Y : ℝ≥0 → W → ℝ} {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hY : IsStrongLinearSDESolution Y B P hsm spot drift volatility) :
    IsStrongLinearSDESolution
      (fun t omega ↦ X t omega - Y t omega) B P hsm
      0 drift volatility := by
  refine ⟨hX.adapted.sub hY.adapted, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hX.continuous_paths, hY.continuous_paths]
      with omega hXomega hYomega
    exact hXomega.sub hYomega
  · filter_upwards [hX.initial, hY.initial] with omega hXzero hYzero
    linarith
  · intro t
    filter_upwards [hX.drift_integrable t, hY.drift_integrable t]
      with omega hXint hYint
    rw [show (fun s : ℝ ↦
        drift * (X s.toNNReal omega - Y s.toNNReal omega)) =
        (fun s ↦ drift * X s.toNNReal omega) -
          fun s ↦ drift * Y s.toNNReal omega by
      funext s
      simp only [Pi.sub_apply, mul_sub]]
    exact hXint.sub hYint
  · intro t
    have hraw := (hX.integral_equation t).sub_real_noMeas
      (hY.integral_equation t)
    have hleft : TendstoInMeasure P
        (fun n ↦ linearSDESpaceApprox volatility
          (fun s omega ↦ X s omega - Y s omega) B t (n + 1))
        Filter.atTop
        (fun omega ↦ linearSDEResidual drift X spot t omega -
          linearSDEResidual drift Y spot t omega) := by
      apply hraw.congr_left
      intro n
      filter_upwards with omega
      exact (linearSDESpaceApprox_sub volatility X Y B
        t (n + 1) omega).symm
    apply hleft.congr_right
    filter_upwards [hX.drift_integrable t, hY.drift_integrable t]
      with omega hXint hYint
    exact (linearSDEResidual_sub drift X Y spot t omega
      hXint hYint).symm

/-- Two strong linear-SDE solutions are indistinguishable under the explicit
`L²` continuity and product-integrability conditions used by the standard
Gronwall uniqueness proof. -/
theorem IsStrongLinearSDESolution.indistinguishable_of_l2
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X Y : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {hsm : ∀ t, StronglyMeasurable (B t)}
    {spot drift volatility : ℝ}
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility)
    (hY : IsStrongLinearSDESolution Y B P hsm spot drift volatility)
    (hXmem : ∀ t, MemLp (X t) 2 P) (hYmem : ∀ t, MemLp (Y t) 2 P)
    (hu : Continuous (fun s : ℝ ↦
      ∫ omega, (X s.toNNReal omega - Y s.toNNReal omega) ^ 2 ∂P))
    (hjointMeas : ∀ t : ℝ≥0,
      AEStronglyMeasurable
        (Function.uncurry (fun s : ℝ ↦ fun omega ↦
          drift * (X s.toNNReal omega - Y s.toNNReal omega)))
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P))
    (hjointSq : ∀ t : ℝ≥0,
      Integrable
        (Function.uncurry (fun s : ℝ ↦ fun omega ↦
          (drift * (X s.toNNReal omega - Y s.toNNReal omega)) ^ 2))
        ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P)) :
    ∀ᵐ omega ∂P, ∀ t, X t omega = Y t omega := by
  let Z : ℝ≥0 → W → ℝ := fun t omega ↦ X t omega - Y t omega
  have hZ : IsStrongLinearSDESolution Z B P hsm 0 drift volatility :=
    hX.sub hY
  have hZmem (t : ℝ≥0) : MemLp (Z t) 2 P :=
    (hXmem t).sub (hYmem t)
  have hZfixed : ∀ t, Z t =ᵐ[P] fun _ ↦ 0 :=
    hZ.ae_eq_zero_of_l2 hB hZmem hu hjointMeas hjointSq
  apply ae_all_eq_of_continuous_processes
    hX.continuous_paths hY.continuous_paths
  intro t
  filter_upwards [hZfixed t] with omega hzero
  exact sub_eq_zero.mp hzero

/-- The time derivative of the GBM exponential. -/
theorem itoTimeDerivative_geometricBrownianFunction
    (spot drift volatility s x : ℝ) :
    itoTimeDerivative (geometricBrownianFunction spot drift volatility) s x =
      (drift - volatility ^ 2 / 2) *
        geometricBrownianFunction spot drift volatility s x := by
  unfold itoTimeDerivative geometricBrownianFunction
  have hinner : HasDerivAt
      (fun r => (drift - volatility ^ 2 / 2) * r + volatility * x)
      (drift - volatility ^ 2 / 2) s := by
    exact (hasDerivAt_const_mul (x := s)
      (drift - volatility ^ 2 / 2)).add_const (volatility * x)
  rw [(hinner.exp.const_mul spot).deriv]
  ring

/-- The state derivative of the GBM exponential. -/
theorem itoSpaceDerivative_geometricBrownianFunction
    (spot drift volatility s x : ℝ) :
    itoSpaceDerivative (geometricBrownianFunction spot drift volatility) s x =
      volatility * geometricBrownianFunction spot drift volatility s x := by
  unfold itoSpaceDerivative geometricBrownianFunction
  have hinner : HasDerivAt
      (fun y => (drift - volatility ^ 2 / 2) * s + volatility * y)
      volatility x := by
    exact (hasDerivAt_const_mul (x := x) volatility).const_add
      ((drift - volatility ^ 2 / 2) * s)
  rw [(hinner.exp.const_mul spot).deriv]
  ring

/-- The second state derivative of the GBM exponential. -/
theorem itoSpaceSecondDerivative_geometricBrownianFunction
    (spot drift volatility s x : ℝ) :
    itoSpaceSecondDerivative
        (geometricBrownianFunction spot drift volatility) s x =
      volatility ^ 2 *
        geometricBrownianFunction spot drift volatility s x := by
  unfold itoSpaceSecondDerivative
  have hfirst : deriv (geometricBrownianFunction spot drift volatility s) =
      fun y => volatility *
        geometricBrownianFunction spot drift volatility s y := by
    funext y
    exact itoSpaceDerivative_geometricBrownianFunction
      spot drift volatility s y
  rw [hfirst]
  have hinner : HasDerivAt
      (fun y => (drift - volatility ^ 2 / 2) * s + volatility * y)
      volatility x :=
    (hasDerivAt_const_mul (x := x) volatility).const_add
      ((drift - volatility ^ 2 / 2) * s)
  have hderiv := (hinner.exp.const_mul spot).const_mul volatility
  unfold geometricBrownianFunction at hderiv ⊢
  rw [hderiv.deriv]
  ring

/-- Brownian completed-cell quadratic sums before an arbitrary deterministic
cutoff converge in probability to the stopped clock. -/
theorem quadraticVariationBeforeStop_brownian_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (t a : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox B t (n + 1) a)
      Filter.atTop (fun _ => ((min t a : ℝ≥0) : ℝ)) := by
  by_cases ha : a ≤ t
  · let hmod : IsContinuousProcessModification B B P :=
      ⟨fun _ => Filter.EventuallyEq.rfl, hB.cont⟩
    exact hmod.quadraticVariationBeforeStopApprox_tendstoInMeasure
      (fun s => (hB.toIsPreBrownianReal.aemeasurable s).aestronglyMeasurable)
      t a ⟨bot_le, ha⟩ (fun _ => ((min t a : ℝ≥0) : ℝ))
      (quadraticVariation_stopped_brownian_inProbability hB a t)
  · have hta : t ≤ a := le_of_not_ge ha
    have hfull : TendstoInMeasure P
        (fun n => quadraticVariationApprox B t (n + 1)) Filter.atTop
        (fun _ => (t : ℝ)) :=
      quadraticVariation_brownianMotion_inProbability hB t
    refine (hfull.congr_left (fun n => ?_)).congr_right ?_
    · filter_upwards with omega
      unfold quadraticVariationBeforeStopApprox quadraticVariationApprox
      apply Finset.sum_congr rfl
      intro i hi
      have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
      rw [if_pos ((uniformPartitionTime_mem_Icc_of_le t
        (Nat.zero_lt_succ n) hi1).2.trans hta)]
    · filter_upwards with omega
      rw [min_eq_left hta]

/-- The Brownian completed-cell clock is the integral of the constant
diffusion density one over the stopped interval. -/
theorem quadraticVariationBeforeStop_brownian_characteristic
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P) (t a : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox B t (n + 1) a)
      Filter.atTop (fun _ => ∫ _s in Ioc (0 : ℝ≥0) (min t a),
        (1 : ℝ) ^ 2 ∂nonnegativeLebesgueMeasure) := by
  apply (quadraticVariationBeforeStop_brownian_tendstoInMeasure
    hB t a).congr_right
  filter_upwards with omega
  rw [one_pow, setIntegral_const, Measure.real_def,
    nonnegativeLebesgueMeasure_Ioc]
  simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (min t a : ℝ))]

/-- The general time-dependent Itô formula gives the integral equation for
the explicit geometric Brownian process at every fixed time. -/
theorem exists_geometricBrownianMotion_linearSDE_identity
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (spot drift volatility : ℝ) (t : ℝ≥0) :
    ∃ I : W → ℝ,
      TendstoInMeasure P
        (fun n => linearSDESpaceApprox volatility
          (geometricBrownianMotion spot drift volatility B) B t (n + 1))
        Filter.atTop I ∧
      ∀ᵐ omega ∂P,
        geometricBrownianMotion spot drift volatility B t omega =
          spot +
            (∫ s in Icc (0 : ℝ) (t : ℝ),
              drift * geometricBrownianMotion spot drift volatility B
                s.toNNReal omega) + I omega := by
  let f : ℝ → ℝ → ℝ := geometricBrownianFunction spot drift volatility
  have hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    dsimp only [f, geometricBrownianFunction]
    fun_prop
  have htdiff : ∀ x, Differentiable ℝ (fun s => f s x) := by
    intro x
    dsimp only [f, geometricBrownianFunction]
    fun_prop
  have hslice : ∀ s, ContDiff ℝ 2 (f s) := by
    intro s
    change ContDiff ℝ 2 (fun x => spot * Real.exp
      ((drift - volatility ^ 2 / 2) * s + volatility * x))
    fun_prop
  have hdt : Continuous (fun p : ℝ × ℝ =>
      itoTimeDerivative f p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => itoTimeDerivative f p.1 p.2) =
        fun p => (drift - volatility ^ 2 / 2) * f p.1 p.2 by
      funext p
      exact itoTimeDerivative_geometricBrownianFunction
        spot drift volatility p.1 p.2]
    exact continuous_const.mul hf
  have hdx : Continuous (fun p : ℝ × ℝ =>
      itoSpaceDerivative f p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => itoSpaceDerivative f p.1 p.2) =
        fun p => volatility * f p.1 p.2 by
      funext p
      exact itoSpaceDerivative_geometricBrownianFunction
        spot drift volatility p.1 p.2]
    exact continuous_const.mul hf
  have hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => itoSpaceSecondDerivative f p.1 p.2) =
        fun p => volatility ^ 2 * f p.1 p.2 by
      funext p
      exact itoSpaceSecondDerivative_geometricBrownianFunction
        spot drift volatility p.1 p.2]
    exact continuous_const.mul hf
  have hmod : IsContinuousProcessModification B B P :=
    ⟨fun _ => Filter.EventuallyEq.rfl, hB.cont⟩
  have hdecomp : ∀ s, B s =ᵐ[P] fun omega =>
      B 0 omega + integratedDrift (fun _ _ => (0 : ℝ)) s omega + B s omega := by
    intro s
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero]
      with omega hzero
    simp only [integratedDrift, integral_zero, add_zero,
      hzero, zero_add]
  have hsigmaInt : ∀ T, ∀ᵐ omega ∂P, IntegrableOn
      (fun _s : ℝ≥0 => ((1 : ℝ) ^ 2)) (Ioc 0 T)
      nonnegativeLebesgueMeasure := by
    intro T
    filter_upwards with omega
    exact integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)
  obtain ⟨I, hI, hformula⟩ := exists_ito_formula_of_characteristics
    B (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ)) B B
    (fun s => (hB.toIsPreBrownianReal.aemeasurable s).aestronglyMeasurable)
    (fun s => (hB.toIsPreBrownianReal.aemeasurable s).aestronglyMeasurable)
    measurable_const (fun _ _ =>
      integrableOn_const (μ := volume) measure_Icc_lt_top.ne) hmod hdecomp
    (quadraticVariationBeforeStop_brownian_characteristic hB) hsigmaInt
    f hf htdiff hslice hdt hdx hsecond t
  refine ⟨I, ?_, ?_⟩
  · apply hI.congr_left
    intro n
    filter_upwards with omega
    unfold generalItoSpaceApprox linearSDESpaceApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [itoSpaceDerivative_geometricBrownianFunction]
    rfl
  · filter_upwards [hformula,
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with omega homega hzero
    have htime : generalItoTimeIntegral f B t omega =
        (drift - volatility ^ 2 / 2) *
          ∫ s in Icc (0 : ℝ) (t : ℝ),
            geometricBrownianMotion spot drift volatility B s.toNNReal omega := by
      unfold generalItoTimeIntegral
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only [f]
      rw [itoTimeDerivative_geometricBrownianFunction]
      unfold geometricBrownianMotion
      rw [Real.coe_toNNReal s hs.1]
    have hquad : generalItoQuadraticIntegral f B (fun _ _ => (1 : ℝ))
          t omega =
        (1 / 2 : ℝ) * volatility ^ 2 *
          ∫ s in Icc (0 : ℝ) (t : ℝ),
            geometricBrownianMotion spot drift volatility B s.toNNReal omega := by
      unfold generalItoQuadraticIntegral
      rw [show (∫ s in Icc (0 : ℝ) (t : ℝ),
          itoSpaceSecondDerivative f s (B s.toNNReal omega) *
            (1 : ℝ) ^ 2) =
          volatility ^ 2 * ∫ s in Icc (0 : ℝ) (t : ℝ),
            geometricBrownianMotion spot drift volatility B
              s.toNNReal omega by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only [f]
        rw [itoSpaceSecondDerivative_geometricBrownianFunction]
        simp only [one_pow]
        unfold geometricBrownianMotion
        rw [Real.coe_toNNReal s hs.1]
        ring]
      ring
    rw [hzero, htime, hquad] at homega
    dsimp only [f] at homega
    simp only [geometricBrownianFunction, mul_zero, zero_add,
      Real.exp_zero, mul_one] at homega
    change geometricBrownianMotion spot drift volatility B t omega =
        (spot + (drift - volatility ^ 2 / 2) *
          ∫ s in Icc (0 : ℝ) (t : ℝ),
            geometricBrownianMotion spot drift volatility B
              s.toNNReal omega) + I omega +
          (1 / 2 : ℝ) * volatility ^ 2 *
            ∫ s in Icc (0 : ℝ) (t : ℝ),
              geometricBrownianMotion spot drift volatility B
                s.toNNReal omega at homega
    rw [integral_const_mul]
    nlinarith [homega]

/-- Geometric Brownian motion satisfies the scalar linear SDE in the strong
left-sum sense. -/
theorem geometricBrownianMotion_isStrongLinearSDESolution
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (spot drift volatility : ℝ) :
    IsStrongLinearSDESolution
      (geometricBrownianMotion spot drift volatility B) B P hsm
      spot drift volatility := by
  have hcontinuous : ∀ᵐ omega ∂P,
      Continuous (fun t =>
        geometricBrownianMotion spot drift volatility B t omega) := by
    filter_upwards [hB.cont] with omega hBomega
    unfold geometricBrownianMotion geometricBrownianFunction
    fun_prop
  refine ⟨?_, hcontinuous, ?_, ?_, ?_⟩
  · intro t
    have hBt : StronglyMeasurable[(Filtration.natural B hsm) t] (B t) :=
      Filtration.stronglyAdapted_natural hsm t
    unfold geometricBrownianMotion geometricBrownianFunction
    exact stronglyMeasurable_const.mul
      (Real.continuous_exp.comp_stronglyMeasurable
        (stronglyMeasurable_const.add (hBt.const_mul volatility)))
  · filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero]
      with omega hzero
    simp only [geometricBrownianMotion, geometricBrownianFunction,
      NNReal.coe_zero, mul_zero, hzero, add_zero, Real.exp_zero, mul_one]
  · intro t
    filter_upwards [hcontinuous] with omega hSomega
    exact ((continuous_const.mul
      (hSomega.comp continuous_real_toNNReal)).continuousOn).integrableOn_compact
        isCompact_Icc
  · intro t
    obtain ⟨I, hI, hEq⟩ :=
      exists_geometricBrownianMotion_linearSDE_identity
        hB spot drift volatility t
    apply hI.congr_right
    filter_upwards [hEq] with omega homega
    unfold linearSDEResidual
    linarith

/-- Geometric Brownian motion is the unique strong solution among candidates
satisfying the explicit `L²` regularity conditions needed by the formal
Gronwall argument. -/
theorem geometricBrownianMotion_unique_strong_solution_of_l2
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ}
    (hB : IsBrownianMotion B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (spot drift volatility : ℝ) :
    IsStrongLinearSDESolution
        (geometricBrownianMotion spot drift volatility B) B P hsm
        spot drift volatility ∧
      ∀ X, IsStrongLinearSDESolution X B P hsm spot drift volatility →
        (∀ t, MemLp (X t) 2 P) →
        Continuous (fun s : ℝ ↦ ∫ omega,
          (X s.toNNReal omega -
            geometricBrownianMotion spot drift volatility B
              s.toNNReal omega) ^ 2 ∂P) →
        (∀ t : ℝ≥0,
          AEStronglyMeasurable
            (Function.uncurry (fun s : ℝ ↦ fun omega ↦
              drift * (X s.toNNReal omega -
                geometricBrownianMotion spot drift volatility B
                  s.toNNReal omega)))
            ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P)) →
        (∀ t : ℝ≥0,
          Integrable
            (Function.uncurry (fun s : ℝ ↦ fun omega ↦
              (drift * (X s.toNNReal omega -
                geometricBrownianMotion spot drift volatility B
                  s.toNNReal omega)) ^ 2))
            ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod P)) →
        ∀ᵐ omega ∂P, ∀ t,
          X t omega =
            geometricBrownianMotion spot drift volatility B t omega := by
  have hGBM := geometricBrownianMotion_isStrongLinearSDESolution
    hB hsm spot drift volatility
  refine ⟨hGBM, fun X hX hXmem hu hjointMeas hjointSq ↦ ?_⟩
  exact hX.indistinguishable_of_l2 hB.toIsPreBrownianReal hGBM
    hXmem (memLp_geometricBrownianMotion_two
      hB.toIsPreBrownianReal spot drift volatility)
    hu hjointMeas hjointSq

end StochasticCalculus
