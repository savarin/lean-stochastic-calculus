/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.Girsanov
import StochasticCalculus.GirsanovConstantDrift

/-!
# Girsanov density data from a predictable `L²` integrand

`ItoGirsanovDensityData` packages the input of the Novikov density
construction for the natural Itô integral of a predictable `L²` integrand
`U`.  An earlier packaging stated its bracket fields pointwise for
`predictableQuadraticVariation hsm U`, which integrates the selected
product-space representative of `U`; that representative is fixed only up
to a null set, so those fields could not be established for any integrand,
and the packaging was removed.

Here the bracket is a free representative `A`, tied to
`predictableQuadraticVariation hsm U` by an almost-everywhere modification
field, exactly as the martingale `M` is tied to the natural Itô
representative.  The passage to `GirsanovDensityData` survives the change
because the quadratic-variation contract is a convergence in probability at
fixed times.

The constant integrand on `(0, T]` instantiates the repaired contract on the
continuous version of the driver: its natural Itô integral is the stopped
scaled driver and its bracket is deterministic.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-! ## The contract with a free bracket representative -/

/-- Predictable-integral data with a free bracket representative.  Both the
martingale `M` and the bracket `A` are tied to the natural Itô construction
by almost-everywhere modification fields; every pointwise field concerns the
free representatives only. -/
structure ItoGirsanovDensityData
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (M A : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop where
  modification : IsContinuousProcessModification
    (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P
  adapted : StronglyAdapted (Filtration.natural B hsm) M
  continuous_path : ∀ omega, Continuous (fun t => M t omega)
  bracket_ae_eq : ∀ t, A t =ᵐ[P] predictableQuadraticVariation hsm U t
  bracket_adapted : StronglyAdapted (Filtration.natural B hsm) A
  bracket_continuous_monotone : ∀ omega,
    Continuous (fun t => A t omega) ∧ Monotone (fun t => A t omega)
  martingale_zero : ∀ omega, M 0 omega = 0
  bracket_zero : ∀ omega, A 0 omega = 0
  novikov : NovikovCondition A P T

/-- The repaired data produces the generic normalized Girsanov density
contract. -/
theorem ItoGirsanovDensityData.toGirsanovDensityData
    {hB : IsBrownianMotion B P} {hsm : ∀ t, StronglyMeasurable (B t)}
    [IsProbabilityMeasure P]
    {U : PredictableProcessL2 (Filtration.natural B hsm) P}
    {M A : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : ItoGirsanovDensityData hB hsm U M A T) :
    GirsanovDensityData P (Filtration.natural B hsm) M A T where
  novikov := h.novikov
  localQuadraticVariation := by
    have hmart : Martingale M (Filtration.natural B hsm) P :=
      (martingale_naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U).congr
        h.adapted h.modification.fixedTime_ae_eq
    have hqv : HasQuadraticVariationBeforeStopProcessInProbability M A P := by
      intro t a
      exact (h.modification.hasQuadraticVariationBeforeStop_naturalIto hB hsm U t a).congr_right
        (h.bracket_ae_eq (min t a)).symm
    have hlocM : localizingStoppedProcess M (fun _ => ⊤) = M := by
      funext t omega
      simp [localizingStoppedProcess]
    have hlocA : localizingStoppedProcess A (fun _ => ⊤) = A := by
      funext t omega
      simp [localizingStoppedProcess]
    refine ⟨fun _ _ => ⊤, isLocalizingSequence_const_top _ _, ?_, ?_⟩
    · intro _
      rw [hlocM]
      exact hmart
    · intro _
      rw [hlocM, hlocA]
      exact hqv
  continuous_martingale_path := h.continuous_path
  adapted_martingale := h.adapted
  adapted_bracket := h.bracket_adapted
  continuous_monotone_bracket := h.bracket_continuous_monotone
  martingale_zero := h.martingale_zero
  bracket_zero := h.bracket_zero

/-! ## The constant integrand instance -/

/-- A constant, regarded as an `𝓕_a`-measurable `L²(P)` random variable. -/
def adaptedConst (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0) (r : ℝ) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨Lp.const 2 P r, aestronglyMeasurable_const.congr (Lp.coeFn_const 2 P r).symm⟩

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem adaptedConst_coeFn (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0) (r : ℝ) :
    ((adaptedConst (P := P) 𝓕 a r : lpMeas ℝ ℝ (𝓕 a) 2 P) : W → ℝ) =ᵐ[P] fun _ => r :=
  Lp.coeFn_const 2 P r

/-- The clipped covariation of the interval `(0, T]` with itself is `t ∧ T`. -/
theorem clippedIntervalCovariation_zero_self (T t : ℝ≥0) :
    clippedIntervalCovariation 0 T 0 T t = ((min t T : ℝ≥0) : ℝ) := by
  simp only [clippedIntervalCovariation, min_self, min_eq_right (zero_le : (0 : ℝ≥0) ≤ T),
    min_eq_left (zero_le : (0 : ℝ≥0) ≤ T), min_eq_right (zero_le : (0 : ℝ≥0) ≤ t),
    NNReal.coe_zero, sub_zero, add_zero]

/-- The constant integrand `r · 1_(0,T]` over the continuous version of the driver. -/
def constantIntegrand (hsm : ∀ t, StronglyMeasurable (B t)) (r : ℝ) (T : ℝ≥0) :
    PredictableProcessL2 (Filtration.natural (continuousBrownianVersion B P)
      (stronglyMeasurable_continuousBrownianVersion P hsm)) P :=
  elementaryPredictable _ 0 T (adaptedConst _ 0 r)

omit [CompleteSpace W] [BorelSpace W] in
/-- The constant integrand instantiates the repaired contract: the natural Itô
integral of `-c · 1_(0,T]` is `-c · B_{t ∧ T}` and its bracket is `c² (t ∧ T)`. -/
theorem itoGirsanovDensityData_constantIntegrand
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    ItoGirsanovDensityData (isBrownianReal_continuousBrownianVersion hB)
      (stronglyMeasurable_continuousBrownianVersion P hsm) (constantIntegrand hsm (-c) T)
      (fun t omega => -c * continuousBrownianVersion B P (min t T) omega)
      (fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T := by
  have hsm' := stronglyMeasurable_continuousBrownianVersion P hsm
  have hBpre : IsPreBrownianReal (continuousBrownianVersion B P) P :=
    (isBrownianReal_continuousBrownianVersion hB).toIsPreBrownianReal
  have hZ := adaptedConst_coeFn (P := P) (Filtration.natural (continuousBrownianVersion B P) hsm')
    0 (-c)
  refine
    { modification := ?_
      adapted := stronglyAdapted_neg_mul_stopped hsm' c T
      continuous_path := continuous_neg_mul_stopped (continuous_continuousBrownianVersion B P) c T
      bracket_ae_eq := ?_
      bracket_adapted := fun _ => stronglyMeasurable_const
      bracket_continuous_monotone := fun _ => continuous_monotone_constantBracket c T
      martingale_zero := neg_mul_stopped_zero (continuousBrownianVersion_zero B P) c T
      bracket_zero := fun _ => by
        rw [min_eq_left zero_le]
        simp
      novikov := novikovCondition_deterministic (fun t => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T }
  · refine ⟨fun s => ?_, Filter.Eventually.of_forall
      (continuous_neg_mul_stopped (continuous_continuousBrownianVersion B P) c T)⟩
    have hrep := naturalItoProcessRepresentative_elementaryPredictable_ae_eq hBpre hsm'
      (zero_le : (0 : ℝ≥0) ≤ T) (adaptedConst _ 0 (-c)) s
    unfold constantIntegrand
    filter_upwards [hrep, hZ] with omega h1 h2
    rw [h1, h2, min_eq_right (zero_le : (0 : ℝ≥0) ≤ s), continuousBrownianVersion_zero, sub_zero]
  · intro t
    let x : ElementaryPredictableIndex
        (Filtration.natural (continuousBrownianVersion B P) hsm') P :=
      ⟨0, ⟨T, zero_le⟩, adaptedConst _ 0 (-c)⟩
    have hU : constantIntegrand hsm (-c) T = elementaryFinsuppToPredictable
        (Filtration.natural (continuousBrownianVersion B P) hsm') P (Finsupp.single x 1) := by
      rw [elementaryFinsuppToPredictable_single, one_smul]
      rfl
    have hqv := predictableQuadraticVariation_elementaryFinsuppToPredictable hsm'
      (Finsupp.single x (1 : ℝ)) t
    rw [← hU, Finsupp.support_single x one_ne_zero] at hqv
    simp only [Finset.sum_singleton, Finsupp.single_eq_same, one_mul] at hqv
    refine (hqv.trans ?_).symm
    filter_upwards [hZ] with omega h2
    change _ * _ * clippedIntervalCovariation 0 T 0 T t = _
    rw [h2, clippedIntervalCovariation_zero_self]
    ring

end StochasticCalculus
