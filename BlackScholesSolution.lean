/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.CDF

/-! # Black–Scholes pricing (Solution)

Restates every Challenge definition with the same body, so that the
Comparator sees identical constants, and discharges the main theorem by
the library theorem `StochasticCalculus.BlackScholes.black_scholes`, whose
statement unfolds to the one below. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace PalomarBlackScholes

universe u

/-- The `i`-th point of the uniform `n`-partition of `[0,t]`. -/
def uniformPartitionTime (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  t * (i : ℝ≥0) / (n : ℝ≥0)

/-- Geometric Brownian motion with spot, drift, and volatility parameters. -/
def geometricBrownianMotion
    {W : Type u} (spot drift volatility : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  spot * Real.exp
    ((drift - volatility ^ 2 / 2) * (t : ℝ) + volatility * B t omega)

/-- Uniform predictable left sums for the diffusion coefficient `σ X`. -/
def linearSDESpaceApprox
    {W : Type u} (volatility : ℝ) (X B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    volatility * X (uniformPartitionTime t n i) omega *
      (B (uniformPartitionTime t n (i + 1)) omega -
        B (uniformPartitionTime t n i) omega)

/-- The stochastic residual in the integral form of `dX = μX dt + σX dB`. -/
def linearSDEResidual
    {W : Type u} (drift : ℝ) (X : ℝ≥0 → W → ℝ)
    (spot : ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  X t omega - spot -
    ∫ s in Icc (0 : ℝ) (t : ℝ), drift * X s.toNNReal omega

/-- Strong solutions of the scalar linear Brownian SDE, with the stochastic
integral pinned by concrete left-sum convergence in probability. -/
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

/-- The market price of Brownian risk. -/
def marketPriceOfRisk (drift rate volatility : ℝ) : ℝ := (drift - rate) / volatility

/-- The exact finite-horizon Girsanov density measure. -/
def riskNeutralMeasure {W : Type*} [MeasurableSpace W]
    (P : Measure W) (B : ℝ≥0 → W → ℝ) (drift rate volatility : ℝ) (T : ℝ≥0) : Measure W :=
  let theta := marketPriceOfRisk drift rate volatility
  P.withDensity (fun omega ↦ ENNReal.ofReal
    (Real.exp (-theta * B T omega - theta ^ 2 * (T : ℝ) / 2)))

/-- The Brownian driver under the terminal measure, continued after T. -/
def riskNeutralBrownian {W : Type*} (B : ℝ≥0 → W → ℝ)
    (drift rate volatility : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  B t omega + marketPriceOfRisk drift rate volatility * ((min t T : ℝ≥0) : ℝ)

/-- Discount and then stop at maturity. -/
def discountedStoppedAsset {W : Type*} (X : ℝ≥0 → W → ℝ)
    (rate : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (-rate * ((min t T : ℝ≥0) : ℝ)) * X (min t T) omega

/-- The Black--Scholes expression, with d2 = d1 - sigma sqrt T. -/
def blackScholesCall (spot strike rate volatility maturity : ℝ) : ℝ :=
  let d1 := (Real.log (spot / strike) + (rate + volatility ^ 2 / 2) * maturity) /
    (volatility * Real.sqrt maturity)
  let d2 := d1 - volatility * Real.sqrt maturity
  spot * cdf (gaussianReal 0 1) d1 -
    strike * Real.exp (-rate * maturity) * cdf (gaussianReal 0 1) d2

/-- The exact Girsanov measure prices every strong solution of the GBM SDE.
The discounted process is stopped at maturity, so the martingale assertion
is a finite-horizon assertion under one fixed terminal measure. -/
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
        blackScholesCall spot strike rate volatility (T : ℝ) := by
  exact StochasticCalculus.BlackScholes.black_scholes hB hsm hspot hstrike hsigma hT
    ⟨hX.adapted, hX.continuous_paths, hX.initial, hX.drift_integrable,
      hX.integral_equation⟩

end PalomarBlackScholes
