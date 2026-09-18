/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.ItoProcess

/-!
# Itô processes

This file connects the pointwise process notation used by the quadratic-
variation development to the natural-filtration `L²` Itô integral.  In
particular, the stochastic term below is not an abstract placeholder: it is
the strongly measurable representative constructed in `Ito.ItoProcess`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B X μ σ : ℝ≥0 → W → ℝ}

/-- Brownian motion with Mathlib's canonical finite-dimensional laws and
almost-everywhere continuous paths. -/
abbrev IsBrownianMotion (B : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  IsBrownianReal B P

/-- The selected pointwise representative of the natural Itô integral
process.  Its fixed-time `L²(P)` class is `naturalItoProcess`. -/
noncomputable def stochasticIntegralProcess
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ℝ≥0 → W → ℝ :=
  naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U

/-- `X` is an Itô process driven by `B`, with drift `μ` and diffusion `σ`.

The bundled predictable `L²` value pins the stochastic integral to the
actual construction in this library.  `diffusion_ae_eq` records that its
product-space representative is the displayed coefficient `σ`; this is the
right representative-sensitive datum for the bracket `∫ σ²`.
-/
structure IsItoProcess
    (X μ σ B : ℝ≥0 → W → ℝ) (P : Measure W) [IsGaussian P] where
  /-- The named driver is Brownian under `P`. -/
  driver_brownian : IsBrownianMotion B P
  /-- A strongly measurable representative of every Brownian coordinate. -/
  driver_stronglyMeasurable : ∀ t, StronglyMeasurable (B t)
  /-- The drift is jointly measurable in time and sample. -/
  drift_measurable : Measurable (Function.uncurry μ)
  /-- Every drift path is integrable on each finite horizon. -/
  drift_integrable (t : ℝ≥0) (ω : W) :
    IntegrableOn (fun s : ℝ => μ s.toNNReal ω)
      (Set.Icc (0 : ℝ) (t : ℝ))
  /-- The diffusion as an actual predictable product-`L²` value. -/
  diffusion :
    PredictableProcessL2
      (Filtration.natural B driver_stronglyMeasurable) P
  /-- The bundled diffusion has `σ` as its selected product-space
  representative. -/
  diffusion_ae_eq :
    (diffusion : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      Function.uncurry σ
  /-- The defining integral equation, almost everywhere at every fixed
  time. -/
  integral_eq (t : ℝ≥0) :
    ∀ᵐ ω ∂P, X t ω = X 0 ω +
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), μ s.toNNReal ω) +
      stochasticIntegralProcess driver_brownian driver_stronglyMeasurable
        diffusion t ω

/-- The stochastic-integral component bundled by an Itô-process witness. -/
noncomputable def IsItoProcess.integralProcess
    (hX : IsItoProcess X μ σ B P) : ℝ≥0 → W → ℝ :=
  stochasticIntegralProcess hX.driver_brownian
    hX.driver_stronglyMeasurable hX.diffusion

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem IsItoProcess.integralProcess_apply
    (hX : IsItoProcess X μ σ B P) (t : ℝ≥0) (ω : W) :
    hX.integralProcess t ω =
      stochasticIntegralProcess hX.driver_brownian
        hX.driver_stronglyMeasurable hX.diffusion t ω :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- The defining equation expressed through the public integral-process
accessor. -/
theorem IsItoProcess.integral_eq_integralProcess
    (hX : IsItoProcess X μ σ B P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, X t ω = X 0 ω +
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), μ s.toNNReal ω) +
      hX.integralProcess t ω := by
  simpa only [IsItoProcess.integralProcess] using hX.integral_eq t

end StochasticCalculus
