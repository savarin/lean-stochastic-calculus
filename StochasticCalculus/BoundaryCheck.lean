import StochasticCalculus.BlackScholes
import StochasticCalculus.GeometricBrownianMotion
import StochasticCalculus.QuadraticVariation

/-!
Manifest-driven boundary for the landed Black–Scholes surface.

The declarations below have explicit types and delegate to the production
declarations. A changed source signature therefore breaks elaboration.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators NNReal ENNReal

namespace BlackScholesBoundary

noncomputable def uniformPartitionTime_boundary
    (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  StochasticCalculus.uniformPartitionTime t n i

noncomputable def geometricBrownianMotion_boundary
    {W : Type*} (spot drift volatility : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.geometricBrownianMotion spot drift volatility B t omega

noncomputable def linearSDESpaceApprox_boundary
    {W : Type*} (volatility : ℝ) (X B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  StochasticCalculus.linearSDESpaceApprox volatility X B t n omega

noncomputable def linearSDEResidual_boundary
    {W : Type*} (drift : ℝ) (X : ℝ≥0 → W → ℝ)
    (spot : ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.linearSDEResidual drift X spot t omega

def IsStrongLinearSDESolution_boundary
    {W : Type*} [MeasurableSpace W]
    (X B : ℝ≥0 → W → ℝ) (P : Measure W)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (spot drift volatility : ℝ) : Prop :=
  StochasticCalculus.IsStrongLinearSDESolution X B P hsm spot drift volatility

noncomputable def marketPriceOfRisk_boundary
    (drift rate volatility : ℝ) : ℝ :=
  StochasticCalculus.BlackScholes.marketPriceOfRisk drift rate volatility

noncomputable def riskNeutralMeasure_boundary
    {W : Type*} [MeasurableSpace W]
    (P : Measure W) (B : ℝ≥0 → W → ℝ) (drift rate volatility : ℝ) (T : ℝ≥0) : Measure W :=
  StochasticCalculus.BlackScholes.riskNeutralMeasure P B drift rate volatility T

noncomputable def riskNeutralBrownian_boundary
    {W : Type*} (B : ℝ≥0 → W → ℝ)
    (drift rate volatility : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.BlackScholes.riskNeutralBrownian B drift rate volatility T t omega

noncomputable def discountedStoppedAsset_boundary
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (rate : ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  StochasticCalculus.BlackScholes.discountedStoppedAsset X rate T t omega

noncomputable def blackScholesCall_boundary
    (spot strike rate volatility maturity : ℝ) : ℝ :=
  StochasticCalculus.BlackScholes.blackScholesCall spot strike rate volatility maturity

theorem black_scholes_boundary
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot strike drift rate volatility : ℝ} {T : ℝ≥0}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hsigma : 0 < volatility) (hT : 0 < T)
    (hX : StochasticCalculus.IsStrongLinearSDESolution X B P hsm spot drift volatility) :
    let Q := StochasticCalculus.BlackScholes.riskNeutralMeasure P B drift rate volatility T
    IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      IsBrownianReal (StochasticCalculus.BlackScholes.riskNeutralBrownian B drift rate volatility T) Q ∧
      Martingale (StochasticCalculus.BlackScholes.discountedStoppedAsset X rate T)
        (Filtration.natural B hsm) Q ∧
      Integrable (fun omega ↦ max (X T omega - strike) 0) Q ∧
      Real.exp (-rate * (T : ℝ)) *
        (∫ omega, max (X T omega - strike) 0 ∂Q) =
        StochasticCalculus.BlackScholes.blackScholesCall spot strike rate volatility (T : ℝ) :=
  StochasticCalculus.BlackScholes.black_scholes hB hsm hspot hstrike hsigma hT hX

end BlackScholesBoundary
