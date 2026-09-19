/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus

/-! # Black–Scholes pricing (Solution)

Restates each challenge definition with bodies delegating to the library,
then discharges the main theorem. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace PalomarBlackScholes

universe u

def uniformPartitionTime (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  StochasticCalculus.uniformPartitionTime t n i

def geometricBrownianMotion
    {W : Type u} (spot drift volatility : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.geometricBrownianMotion spot drift volatility B t omega

def linearSDESpaceApprox
    {W : Type u} (volatility : ℝ) (X B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  StochasticCalculus.linearSDESpaceApprox volatility X B t n omega

def linearSDEResidual
    {W : Type u} (drift : ℝ) (X : ℝ≥0 → W → ℝ)
    (spot : ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.linearSDEResidual drift X spot t omega

structure IsStrongLinearSolution
    {W : Type u} [MeasurableSpace W]
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
      atTop (linearSDEResidual drift X spot t)

def marketPriceOfRisk (drift rate volatility : ℝ) : ℝ :=
  StochasticCalculus.BlackScholes.marketPriceOfRisk drift rate volatility

def riskNeutralMeasure {W : Type*} [MeasurableSpace W]
    (P : Measure W) (B : ℝ≥0 → W → ℝ) (drift rate volatility : ℝ) (T : ℝ≥0) : Measure W :=
  StochasticCalculus.BlackScholes.riskNeutralMeasure P B drift rate volatility T

def riskNeutralBrownian {W : Type*} (B : ℝ≥0 → W → ℝ)
    (drift rate volatility : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.BlackScholes.riskNeutralBrownian B drift rate volatility T t omega

def discountedStoppedAsset {W : Type*} (X : ℝ≥0 → W → ℝ)
    (rate : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.BlackScholes.discountedStoppedAsset X rate T t omega

def blackScholesCall (spot strike rate volatility maturity : ℝ) : ℝ :=
  StochasticCalculus.BlackScholes.blackScholesCall spot strike rate volatility maturity

theorem black_scholes
    {W : Type u} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot strike drift rate volatility : ℝ} {T : ℝ≥0}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hsigma : 0 < volatility) (hT : 0 < T)
    (hX : IsStrongLinearSolution X B P hsm spot drift volatility) :
    let Q := riskNeutralMeasure P B drift rate volatility T
    IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      IsBrownianReal (riskNeutralBrownian B drift rate volatility T) Q ∧
      Martingale (discountedStoppedAsset X rate T) (Filtration.natural B hsm) Q ∧
      Integrable (fun omega ↦ max (X T omega - strike) 0) Q ∧
      Real.exp (-rate * (T : ℝ)) *
        (∫ omega, max (X T omega - strike) 0 ∂Q) =
        blackScholesCall spot strike rate volatility (T : ℝ) :=
  StochasticCalculus.BlackScholes.black_scholes hB hsm hspot hstrike hsigma hT
    ⟨hX.adapted, hX.continuous_paths, hX.initial, hX.drift_integrable,
      hX.integral_equation⟩

end PalomarBlackScholes
