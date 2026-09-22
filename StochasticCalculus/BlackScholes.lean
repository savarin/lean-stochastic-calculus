/-
Copyright (c) 2026 The lean-ito contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-ito contributors
-/
import StochasticCalculus.GBMLocalization
import StochasticCalculus.GirsanovConstantDrift
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.CDF
import Mathlib.Probability.Moments.Tilted

/-!
# The Black–Scholes formula

This file develops the Black–Scholes call-price formula from two routes that
converge on the same closed-form expression.

**Gaussian route (Sections 1–3).** The risk-neutral lognormal model defines
`gaussianCallPrice` as a discounted Gaussian expectation and evaluates it
analytically to the Black–Scholes formula `S Φ(d₁) − K e^{−rT} Φ(d₂)`.

**SDE route (Section 4).** The risk-neutral measure is constructed via the
Girsanov density `Z_T`, the shifted driver is proved Brownian under the new
measure by the predictable Girsanov theorem at the constant market price of
risk (`GirsanovConstantDrift`), the discounted asset is a martingale, and the
terminal payoff expectation is identified with the Gaussian calculation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace StochasticCalculus.BlackScholes

/-- The standard normal cumulative distribution function. -/
def normalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The terminal value of geometric Brownian motion, written as a function of a standard normal
coordinate. -/
def geometricBrownianTerminal (spot rate volatility maturity z : ℝ) : ℝ :=
  spot * Real.exp ((rate - volatility ^ 2 / 2) * maturity +
    volatility * Real.sqrt maturity * z)

/-- The payoff of a European call with strike `strike`. -/
def callPayoff (strike terminalValue : ℝ) : ℝ := max (terminalValue - strike) 0

/-- The two dimensionless parameters in the Black--Scholes call formula. -/
def dOne (spot strike rate volatility maturity : ℝ) : ℝ :=
  (Real.log (spot / strike) + (rate + volatility ^ 2 / 2) * maturity) /
    (volatility * Real.sqrt maturity)

def dTwo (spot strike rate volatility maturity : ℝ) : ℝ :=
  dOne spot strike rate volatility maturity - volatility * Real.sqrt maturity

/-- The discounted Gaussian expectation defining the European call price in the risk-neutral
lognormal model. -/
def gaussianCallPrice (spot strike rate volatility maturity : ℝ) : ℝ :=
  Real.exp (-rate * maturity) *
    ∫ z, callPayoff strike
      (geometricBrownianTerminal spot rate volatility maturity z)
      ∂gaussianReal 0 1

/-- The closed-form Black--Scholes expression. -/
def blackScholesCall (spot strike rate volatility maturity : ℝ) : ℝ :=
  spot * normalCDF (dOne spot strike rate volatility maturity) -
    strike * Real.exp (-rate * maturity) *
      normalCDF (dTwo spot strike rate volatility maturity)


/-- By symmetry, an upper tail of the standard Gaussian is its CDF at the reflected endpoint. -/
theorem measureReal_Ici_standardGaussian (x : ℝ) :
    (gaussianReal 0 1).real (Set.Ici (-x)) = normalCDF x := by
  have hmap := map_measureReal_apply
    (μ := gaussianReal 0 1) (f := fun y : ℝ ↦ -y)
    (by fun_prop) (measurableSet_Iic : MeasurableSet (Set.Iic x))
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Set.Iic x = Set.Ici (-x) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  rw [gaussianReal_map_neg, neg_zero, hpre] at hmap
  rw [normalCDF, cdf_eq_real]
  exact hmap.symm

/-- An upper tail of a unit-variance Gaussian with mean `c` is the standard normal CDF at the
standardized reflected endpoint. -/
theorem measureReal_Ici_gaussianMean (c a : ℝ) :
    (gaussianReal c 1).real (Set.Ici a) = normalCDF (c - a) := by
  have hshift : (gaussianReal 0 1).map (fun y : ℝ ↦ y + c) = gaussianReal c 1 := by
    simpa using gaussianReal_map_add_const (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) c
  rw [← hshift, map_measureReal_apply (by fun_prop) measurableSet_Ici]
  have hpre : (fun y : ℝ ↦ y + c) ⁻¹' Set.Ici a = Set.Ici (-(c - a)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hpre, measureReal_Ici_standardGaussian]

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

/-- Completing the square through the normalized Esscher transform: the exponential martingale
density integrated over a measurable set equals the probability of that set under the shifted
Gaussian law. -/
theorem setIntegral_exp_sub_half_sq_standardGaussian (c : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (∫ x in s, Real.exp (c * x - c ^ 2 / 2) ∂gaussianReal 0 1) =
      (gaussianReal c 1).real s := by
  have hint : Integrable (fun x : ℝ ↦ Real.exp (c * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal c
  have hcgf := cgf_gaussianReal
    (p := gaussianReal 0 1) (X := id) (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    (by simp) c
  have h := setIntegral_tilted_mul_eq_cgf'
    (μ := gaussianReal 0 1) (X := id) (t := c)
    (g := fun _ : ℝ ↦ (1 : ℝ)) hs hint
  have h' :
      (∫ x in s, (1 : ℝ) ∂(gaussianReal 0 1).tilted (fun x ↦ c * x)) =
        ∫ x in s, Real.exp (c * x - cgf id (gaussianReal 0 1) c) • (1 : ℝ)
          ∂gaussianReal 0 1 := by
    simpa only [id_eq] using h
  rw [tilted_gaussianReal 0 1 c, hcgf] at h'
  simp only [zero_add, NNReal.coe_one, one_mul] at h'
  simpa only [id_eq, zero_mul, zero_add, NNReal.coe_one, one_mul, smul_eq_mul,
    mul_one, setIntegral_one_eq_measureReal, one_smul] using h'.symm

private theorem drift_add_scale_neg_dTwo
    {spot strike rate volatility maturity : ℝ}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hvolatility : 0 < volatility) (hmaturity : 0 < maturity) :
    (rate - volatility ^ 2 / 2) * maturity +
        (volatility * Real.sqrt maturity) *
          (-dTwo spot strike rate volatility maturity) =
      Real.log (strike / spot) := by
  have hsqrt : (Real.sqrt maturity) ^ 2 = maturity := Real.sq_sqrt hmaturity.le
  have hscale : volatility * Real.sqrt maturity ≠ 0 :=
    (mul_pos hvolatility (Real.sqrt_pos.2 hmaturity)).ne'
  have hlog : Real.log (spot / strike) = -Real.log (strike / spot) := by
    rw [Real.log_div hspot.ne' hstrike.ne', Real.log_div hstrike.ne' hspot.ne']
    ring
  unfold dTwo dOne
  rw [hlog]
  field_simp
  nlinarith

private theorem callPayoff_region
    {spot strike rate volatility maturity : ℝ}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hvolatility : 0 < volatility) (hmaturity : 0 < maturity) (z : ℝ) :
    callPayoff strike (geometricBrownianTerminal spot rate volatility maturity z) =
      (Set.Ici (-dTwo spot strike rate volatility maturity)).indicator
        (fun z ↦ geometricBrownianTerminal spot rate volatility maturity z - strike) z := by
  have hscale : 0 < volatility * Real.sqrt maturity :=
    mul_pos hvolatility (Real.sqrt_pos.2 hmaturity)
  have hthreshold := drift_add_scale_neg_dTwo
    (rate := rate) hspot hstrike hvolatility hmaturity
  have hterminal :
      strike ≤ geometricBrownianTerminal spot rate volatility maturity z ↔
        -dTwo spot strike rate volatility maturity ≤ z := by
    have hratio : 0 < strike / spot := div_pos hstrike hspot
    have hmul :
        strike ≤ spot * Real.exp
            ((rate - volatility ^ 2 / 2) * maturity +
              volatility * Real.sqrt maturity * z) ↔
          strike / spot ≤ Real.exp
            ((rate - volatility ^ 2 / 2) * maturity +
              volatility * Real.sqrt maturity * z) := by
      rw [div_le_iff₀ hspot]
      ring_nf
    rw [geometricBrownianTerminal, hmul, ← Real.log_le_iff_le_exp hratio]
    rw [← hthreshold]
    constructor <;> intro h
    · exact (mul_le_mul_iff_left₀ hscale).mp (by linarith)
    · have := (mul_le_mul_iff_left₀ hscale).mpr h
      linarith
  rw [callPayoff]
  by_cases hz : z ∈ Set.Ici (-dTwo spot strike rate volatility maturity)
  · rw [Set.indicator_of_mem hz, max_eq_left]
    exact sub_nonneg.mpr (hterminal.mpr hz)
  · rw [Set.indicator_of_notMem hz, max_eq_right]
    exact le_of_not_ge (fun h ↦ hz (hterminal.mp (sub_nonneg.mp h)))

/-- Evaluation of the discounted European-call expectation in the risk-neutral lognormal model.
This is the analytic Black--Scholes formula, including the truncated Gaussian calculation rather
than assuming it as a pricing axiom. -/
theorem gaussianCallPrice_eq_blackScholes
    {spot strike rate volatility maturity : ℝ}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hvolatility : 0 < volatility) (hmaturity : 0 < maturity) :
    gaussianCallPrice spot strike rate volatility maturity =
      blackScholesCall spot strike rate volatility maturity := by
  let c : ℝ := volatility * Real.sqrt maturity
  let cutoff : Set ℝ := Set.Ici (-dTwo spot strike rate volatility maturity)
  have hc_sq : c ^ 2 = volatility ^ 2 * maturity := by
    rw [show c = volatility * Real.sqrt maturity from rfl, mul_pow,
      Real.sq_sqrt hmaturity.le]
  have hgeom : Integrable
      (fun z ↦ geometricBrownianTerminal spot rate volatility maturity z)
      (gaussianReal 0 1) := by
    have h := (integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) c).const_mul
      (spot * Real.exp ((rate - volatility ^ 2 / 2) * maturity))
    simpa only [geometricBrownianTerminal, c, Real.exp_add, mul_assoc] using h
  have hterminal :
      (∫ z in cutoff, geometricBrownianTerminal spot rate volatility maturity z
          ∂gaussianReal 0 1) =
        spot * Real.exp (rate * maturity) *
          normalCDF (dOne spot strike rate volatility maturity) := by
    calc
      (∫ z in cutoff, geometricBrownianTerminal spot rate volatility maturity z
          ∂gaussianReal 0 1) =
          ∫ z in cutoff, (spot * Real.exp (rate * maturity)) *
            Real.exp (c * z - c ^ 2 / 2) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with z
        rw [geometricBrownianTerminal]
        calc
          spot * Real.exp
              ((rate - volatility ^ 2 / 2) * maturity +
                volatility * Real.sqrt maturity * z) =
              spot * Real.exp
                (rate * maturity + (c * z - c ^ 2 / 2)) := by
            congr 2
            rw [show c = volatility * Real.sqrt maturity from rfl, hc_sq]
            ring
          _ = spot * (Real.exp (rate * maturity) *
              Real.exp (c * z - c ^ 2 / 2)) := by rw [Real.exp_add]
          _ = spot * Real.exp (rate * maturity) *
              Real.exp (c * z - c ^ 2 / 2) := by ring
      _ = (spot * Real.exp (rate * maturity)) *
          ∫ z in cutoff, Real.exp (c * z - c ^ 2 / 2)
            ∂gaussianReal 0 1 := by
        rw [integral_const_mul]
      _ = (spot * Real.exp (rate * maturity)) *
          (gaussianReal c 1).real cutoff := by
        rw [setIntegral_exp_sub_half_sq_standardGaussian c measurableSet_Ici]
      _ = spot * Real.exp (rate * maturity) *
          normalCDF (dOne spot strike rate volatility maturity) := by
        rw [measureReal_Ici_gaussianMean]
        congr 2
        dsimp only [c]
        unfold dTwo
        ring
  have hstrikeIntegral :
      (∫ _z in cutoff, strike ∂gaussianReal 0 1) =
        strike * normalCDF (dTwo spot strike rate volatility maturity) := by
    rw [integral_const, measureReal_restrict_apply_univ]
    change (gaussianReal 0 1).real cutoff * strike = _
    rw [show cutoff = Set.Ici (-dTwo spot strike rate volatility maturity) from rfl,
      measureReal_Ici_standardGaussian]
    ring
  have hpayoff :
      (∫ z, callPayoff strike
          (geometricBrownianTerminal spot rate volatility maturity z)
          ∂gaussianReal 0 1) =
        spot * Real.exp (rate * maturity) *
            normalCDF (dOne spot strike rate volatility maturity) -
          strike * normalCDF (dTwo spot strike rate volatility maturity) := by
    calc
      _ = ∫ z, cutoff.indicator
          (fun z ↦ geometricBrownianTerminal spot rate volatility maturity z - strike) z
          ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards with z
        exact callPayoff_region hspot hstrike hvolatility hmaturity z
      _ = ∫ z in cutoff,
          geometricBrownianTerminal spot rate volatility maturity z - strike
          ∂gaussianReal 0 1 := integral_indicator measurableSet_Ici
      _ = (∫ z in cutoff,
            geometricBrownianTerminal spot rate volatility maturity z
            ∂gaussianReal 0 1) -
          ∫ _z in cutoff, strike ∂gaussianReal 0 1 := by
        rw [integral_sub hgeom.integrableOn (integrable_const strike)]
      _ = _ := by rw [hterminal, hstrikeIntegral]
  rw [gaussianCallPrice, hpayoff, blackScholesCall]
  have hcancel : Real.exp (-rate * maturity) * Real.exp (rate * maturity) = 1 := by
    rw [← Real.exp_add]
    have hz : -rate * maturity + rate * maturity = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [mul_sub]
  calc
    Real.exp (-rate * maturity) *
          (spot * Real.exp (rate * maturity) *
            normalCDF (dOne spot strike rate volatility maturity)) -
        Real.exp (-rate * maturity) *
          (strike * normalCDF (dTwo spot strike rate volatility maturity)) =
        (Real.exp (-rate * maturity) * Real.exp (rate * maturity)) * spot *
            normalCDF (dOne spot strike rate volatility maturity) -
          strike * Real.exp (-rate * maturity) *
            normalCDF (dTwo spot strike rate volatility maturity) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- The same call-price formula for any random coordinate whose law is standard Gaussian.  This
separates the probabilistic input (`HasLaw`) from the analytic Gaussian evaluation above. -/
theorem callPrice_of_hasLaw_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P)
    {spot strike rate volatility maturity : ℝ}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hvolatility : 0 < volatility) (hmaturity : 0 < maturity) :
    Real.exp (-rate * maturity) *
        ∫ ω, callPayoff strike
          (geometricBrownianTerminal spot rate volatility maturity (Z ω)) ∂P =
      blackScholesCall spot strike rate volatility maturity := by
  have hcontinuous : Continuous (fun z ↦ callPayoff strike
      (geometricBrownianTerminal spot rate volatility maturity z)) := by
    unfold callPayoff geometricBrownianTerminal
    fun_prop
  have htransport := hZ.integral_comp hcontinuous.aestronglyMeasurable
  simp only [Function.comp_apply] at htransport
  rw [htransport]
  exact gaussianCallPrice_eq_blackScholes hspot hstrike hvolatility hmaturity

/-- A positive-time Brownian observation, divided by the square root of its time, is standard
Gaussian. -/
theorem hasLaw_standardizedBrownianTerminal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {maturity : ℝ≥0} (hmaturity : 0 < maturity) :
    HasLaw (fun ω ↦ B maturity ω / Real.sqrt (maturity : ℝ))
      (gaussianReal 0 1) P := by
  have h := gaussianReal_div_const (hB.hasLaw_eval maturity)
    (Real.sqrt (maturity : ℝ))
  convert h using 1
  norm_num [Real.sq_sqrt maturity.2, div_self hmaturity.ne']

/-- The discounted call expectation evaluated on a positive-time Brownian observation.  The
Brownian input is used through its proved terminal Gaussian law; no pricing identity is assumed. -/
theorem brownianCallPrice_eq_blackScholes
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {spot strike rate volatility : ℝ} {maturity : ℝ≥0}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hvolatility : 0 < volatility) (hmaturity : 0 < maturity) :
    Real.exp (-rate * (maturity : ℝ)) *
        ∫ ω, callPayoff strike
          (geometricBrownianTerminal spot rate volatility (maturity : ℝ)
            (B maturity ω / Real.sqrt (maturity : ℝ))) ∂P =
      blackScholesCall spot strike rate volatility (maturity : ℝ) := by
  exact callPrice_of_hasLaw_standardGaussian
    (hasLaw_standardizedBrownianTerminal hB hmaturity)
    hspot hstrike hvolatility (by exact_mod_cast hmaturity)

end StochasticCalculus.BlackScholes

/-! ## Section 4 — SDE pricing via Girsanov -/

open Filter Topology Set
open scoped NNReal ENNReal

namespace StochasticCalculus.BlackScholes

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

/-- The risk-neutral measure is the exact terminal density measure of the dynamic
Girsanov theorem at the market price of risk. -/
private theorem riskNeutralMeasure_eq_girsanovMeasure
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (B : ℝ≥0 → W → ℝ) (drift rate volatility : ℝ) (T : ℝ≥0) :
    riskNeutralMeasure P B drift rate volatility T =
      girsanovMeasure P
        (fun t omega ↦ -(marketPriceOfRisk drift rate volatility) * B (min t T) omega)
        (fun t _ ↦ (marketPriceOfRisk drift rate volatility) ^ 2 * ((min t T : ℝ≥0) : ℝ)) T := by
  simp only [riskNeutralMeasure, girsanovMeasure, girsanovDensity, doleansDadeExponential,
    doleansDadeLog, min_self]
  congr 1
  funext omega
  congr 2
  ring

theorem riskNeutralMeasure_equivalent
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (drift rate volatility : ℝ) (T : ℝ≥0) :
    riskNeutralMeasure P B drift rate volatility T ≪ P ∧
      P ≪ riskNeutralMeasure P B drift rate volatility T := by
  rw [riskNeutralMeasure_eq_girsanovMeasure]
  exact girsanovMeasure_const_mutuallyAbsolutelyContinuous hB hsm _ T

theorem isPreBrownianReal_riskNeutralBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (drift rate volatility : ℝ) (T : ℝ≥0) :
    IsPreBrownianReal (riskNeutralBrownian B drift rate volatility T)
      (riskNeutralMeasure P B drift rate volatility T) := by
  rw [riskNeutralMeasure_eq_girsanovMeasure]
  have h := isPreBrownianReal_girsanovShiftedBrownian_const_dynamic hB hsm
    (marketPriceOfRisk drift rate volatility) T
  rw [girsanovShiftedBrownian_const] at h
  exact h

/-- Deterministic drift shifts leave the entire natural filtration unchanged. -/
theorem natural_add_deterministic
    {W : Type*} [MeasurableSpace W] (B : ℝ≥0 → W → ℝ)
    (hsm : ∀ t, StronglyMeasurable (B t)) (f : ℝ≥0 → ℝ) :
    Filtration.natural (fun t omega ↦ B t omega + f t)
      (fun t ↦ (hsm t).add stronglyMeasurable_const) = Filtration.natural B hsm := by
  apply Filtration.ext
  funext t
  change (⨆ j ≤ t, MeasurableSpace.comap (fun omega ↦ B j omega + f j) inferInstance) =
    ⨆ j ≤ t, MeasurableSpace.comap (B j) inferInstance
  apply iSup_congr
  intro j
  apply iSup_congr
  intro hj
  apply le_antisymm
  · apply measurable_iff_comap_le.mp
    exact (measurable_iff_comap_le.mpr le_rfl).add_const (f j)
  · apply measurable_iff_comap_le.mp
    have hm : Measurable[MeasurableSpace.comap (fun omega ↦ B j omega + f j) inferInstance]
        (fun omega ↦ B j omega + f j) := measurable_iff_comap_le.mpr le_rfl
    simpa using hm.sub_const (f j)

/-- Exact algebraic drift cancellation at every time through maturity. -/
theorem discounted_gbm_eq_exponential
    {W : Type*} (B : ℝ≥0 → W → ℝ) (spot drift rate volatility : ℝ)
    (hsigma : volatility ≠ 0) (T t : ℝ≥0) (omega : W) :
    discountedStoppedAsset (geometricBrownianMotion spot drift volatility B) rate T t omega =
      spot * scaledBrownianDoleansDadeExponential volatility
        (riskNeutralBrownian B drift rate volatility T) (min t T) omega := by
  unfold discountedStoppedAsset geometricBrownianMotion geometricBrownianFunction
    scaledBrownianDoleansDadeExponential doleansDadeExponential doleansDadeLog
    riskNeutralBrownian marketPriceOfRisk
  dsimp only
  rw [min_eq_left (min_le_right t T)]
  rw [← mul_assoc, mul_comm (Real.exp _) spot, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The shifted driver has continuous paths under the equivalent measure. -/
theorem isBrownianReal_riskNeutralBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (drift rate volatility : ℝ) (T : ℝ≥0) :
    IsBrownianReal (riskNeutralBrownian B drift rate volatility T)
      (riskNeutralMeasure P B drift rate volatility T) := by
  refine ⟨isPreBrownianReal_riskNeutralBrownian hB hsm drift rate volatility T, ?_⟩
  have hcont := hB.cont.filter_mono
    (riskNeutralMeasure_equivalent hB hsm drift rate volatility T).1.ae_le
  filter_upwards [hcont] with omega homega
  unfold riskNeutralBrownian
  fun_prop

/-- Every strong solution has a discounted martingale under the same terminal Q. -/
theorem martingale_discountedStoppedAsset
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot drift rate volatility : ℝ} (hsigma : volatility ≠ 0) (T : ℝ≥0)
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility) :
    Martingale (discountedStoppedAsset X rate T) (Filtration.natural B hsm)
      (riskNeutralMeasure P B drift rate volatility T) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Q := riskNeutralMeasure P B drift rate volatility T
  let WQ := riskNeutralBrownian B drift rate volatility T
  have hW := isPreBrownianReal_riskNeutralBrownian hB hsm drift rate volatility T
  let _ : IsProbabilityMeasure Q := hW.isGaussianProcess.isProbabilityMeasure
  have hWsm : ∀ t, StronglyMeasurable (WQ t) := fun t ↦ (hsm t).add stronglyMeasurable_const
  have hfil : Filtration.natural WQ hWsm = Filtration.natural B hsm :=
    natural_add_deterministic B hsm _
  have hmart := (martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements
    hW hWsm volatility).smul spot
  rw [hfil] at hmart
  have hstop := StochasticCalculus.Martingale.stopAt hmart T
  have hsameP := (geometricBrownianMotion_unique_strong_solution hB hsm
    spot drift volatility).2 X hX
  have hsameQ := hsameP.filter_mono
    (riskNeutralMeasure_equivalent hB hsm drift rate volatility T).1.ae_le
  apply hstop.congr
  · intro t
    have hm := (hX.adapted (min t T)).mono
      ((Filtration.natural B hsm).mono (min_le_left t T))
    exact stronglyMeasurable_const.mul hm
  · intro t
    filter_upwards [hsameQ] with omega homega
    change spot * scaledBrownianDoleansDadeExponential volatility WQ (min t T) omega = _
    rw [← discounted_gbm_eq_exponential B spot drift rate volatility hsigma T t omega]
    exact congrArg (Real.exp (-rate * ((min t T : ℝ≥0) : ℝ)) * ·)
      (homega (min t T)).symm

/-- The physical and risk-neutral terminal lognormal expressions agree pointwise. -/
theorem gbm_terminal_eq_riskNeutralGaussian
    {W : Type*} (B : ℝ≥0 → W → ℝ) (spot drift rate volatility : ℝ)
    (hsigma : volatility ≠ 0) {T : ℝ≥0} (hT : 0 < T) (omega : W) :
    geometricBrownianMotion spot drift volatility B T omega =
      BlackScholes.geometricBrownianTerminal spot rate volatility (T : ℝ)
        (riskNeutralBrownian B drift rate volatility T T omega / Real.sqrt (T : ℝ)) := by
  have hsqrt : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hT))
  unfold geometricBrownianMotion geometricBrownianFunction
    BlackScholes.geometricBrownianTerminal riskNeutralBrownian marketPriceOfRisk
  rw [min_self]
  congr 2
  field_simp
  ring

/-- Girsanov, strong-SDE uniqueness, and Gaussian integration give the price. -/
theorem call_expectation_eq_blackScholes
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot strike drift rate volatility : ℝ} {T : ℝ≥0}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hsigma : 0 < volatility) (hT : 0 < T)
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility) :
    Real.exp (-rate * (T : ℝ)) *
      (∫ omega, max (X T omega - strike) 0
        ∂riskNeutralMeasure P B drift rate volatility T) =
      BlackScholes.blackScholesCall spot strike rate volatility (T : ℝ) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hsameP := (geometricBrownianMotion_unique_strong_solution hB hsm
    spot drift volatility).2 X hX
  have hsameQ := hsameP.filter_mono
    (riskNeutralMeasure_equivalent hB hsm drift rate volatility T).1.ae_le
  have hW := isPreBrownianReal_riskNeutralBrownian hB hsm drift rate volatility T
  rw [← BlackScholes.brownianCallPrice_eq_blackScholes hW hspot hstrike hsigma hT]
  congr 1
  apply integral_congr_ae
  filter_upwards [hsameQ] with omega homega
  rw [homega T, gbm_terminal_eq_riskNeutralGaussian B spot drift rate volatility hsigma.ne' hT]
  rfl

/-- The risk-neutral payoff is genuinely Bochner integrable. -/
theorem integrable_callPayoff
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot drift rate volatility : ℝ} (hsigma : volatility ≠ 0) (T : ℝ≥0)
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility) (strike : ℝ) :
    Integrable (fun omega ↦ max (X T omega - strike) 0)
      (riskNeutralMeasure P B drift rate volatility T) := by
  have hW := isPreBrownianReal_riskNeutralBrownian hB hsm drift rate volatility T
  let _ := hW.isGaussianProcess.isProbabilityMeasure
  have hm := martingale_discountedStoppedAsset hB hsm (rate := rate) hsigma T hX
  have hXT : Integrable (X T) (riskNeutralMeasure P B drift rate volatility T) := by
    apply (integrable_const_mul_iff (IsUnit.mk0 _ (Real.exp_ne_zero (-rate * (T : ℝ)))) (X T)).mp
    have hh := hm.integrable T
    change Integrable (fun omega ↦ Real.exp (-rate * ((min T T : ℝ≥0) : ℝ)) *
      X (min T T) omega) _ at hh
    simpa only [min_self] using hh
  exact (hXT.sub (integrable_const strike)).sup (integrable_const 0)

/-- Full finite-horizon pricing package for any strong GBM SDE solution. -/
theorem black_scholes
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B X : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {spot strike drift rate volatility : ℝ} {T : ℝ≥0}
    (hspot : 0 < spot) (hstrike : 0 < strike)
    (hsigma : 0 < volatility) (hT : 0 < T)
    (hX : IsStrongLinearSDESolution X B P hsm spot drift volatility) :
    let Q := riskNeutralMeasure P B drift rate volatility T
    IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      IsBrownianReal (riskNeutralBrownian B drift rate volatility T) Q ∧
      Martingale (discountedStoppedAsset X rate T) (Filtration.natural B hsm) Q ∧
      Integrable (fun omega ↦ max (X T omega - strike) 0) Q ∧
      Real.exp (-rate * (T : ℝ)) *
        (∫ omega, max (X T omega - strike) 0 ∂Q) =
        BlackScholes.blackScholesCall spot strike rate volatility (T : ℝ) := by
  have hW := isBrownianReal_riskNeutralBrownian hB hsm drift rate volatility T
  have hQ := riskNeutralMeasure_equivalent hB hsm drift rate volatility T
  exact ⟨hW.isGaussianProcess.isProbabilityMeasure, hQ.1, hQ.2, hW,
    martingale_discountedStoppedAsset hB hsm hsigma.ne' T hX,
    integrable_callPayoff hB hsm hsigma.ne' T hX strike,
    call_expectation_eq_blackScholes hB hsm hspot hstrike hsigma hT hX⟩

end StochasticCalculus.BlackScholes
