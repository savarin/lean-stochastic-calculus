/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.GirsanovTheorem
public import StochasticCalculus.BrownianContinuousVersion

/-!
# Constant-drift Girsanov through the dynamic theorem

The predictable Girsanov theorem is instantiated at a constant drift `c`.
The continuous local martingale is `-c · B_{t ∧ T}`, its bracket is the
deterministic function `c² (t ∧ T)`, and Novikov's condition is automatic.
The density contract needs every path continuous and starting at zero, so
the theorem is applied to `continuousBrownianVersion B P` and the
conclusion is transported back to `B`, which agrees with the version almost
surely at every fixed time.

The main results are stated for the exact terminal density measure
`girsanovMeasure P (-c · B_{· ∧ T}) (c² (· ∧ T)) T`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-! ## The constant drift as a predictable integrand -/

/-- The literal predictable drift specializes to the stopped linear drift. -/
theorem girsanovIntegratedDrift_const {W : Type*} (c : ℝ) (T t : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift (fun _ _ ↦ c) T t omega = c * ((min t T : ℝ≥0) : ℝ) := by
  have hmass : nonnegativeLebesgueMeasure.real (Set.Ioc (0 : ℝ≥0) (min t T)) =
      ((min t T : ℝ≥0) : ℝ) := by
    rw [measureReal_def, nonnegativeLebesgueMeasure_Ioc, NNReal.coe_zero,
      sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  unfold girsanovIntegratedDrift
  rw [setIntegral_const, hmass, smul_eq_mul, mul_comm]

/-- The shifted driver at a constant drift is the driver plus the stopped linear drift. -/
theorem girsanovShiftedBrownian_const {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0) :
    girsanovShiftedBrownian B (fun _ _ ↦ c) T =
      fun t omega ↦ B t omega + c * ((min t T : ℝ≥0) : ℝ) := by
  funext t omega
  simp only [girsanovShiftedBrownian, girsanovIntegratedDrift_const]

/-! ## The stopped scaled driver and its deterministic bracket -/

/-- Path continuity of the stopped scaled driver. -/
theorem continuous_neg_mul_stopped {W : Type*} {B : ℝ≥0 → W → ℝ}
    (hcont : ∀ omega, Continuous (fun t => B t omega)) (c : ℝ) (T : ℝ≥0) (omega : W) :
    Continuous (fun t => -c * B (min t T) omega) :=
  continuous_const.mul ((hcont omega).comp (continuous_id.min continuous_const))

/-- The stopped scaled driver starts at zero when the driver does. -/
theorem neg_mul_stopped_zero {W : Type*} {B : ℝ≥0 → W → ℝ}
    (hzero : ∀ omega, B 0 omega = 0) (c : ℝ) (T : ℝ≥0) (omega : W) :
    -c * B (min 0 T) omega = 0 := by
  rw [min_eq_left zero_le, hzero omega, mul_zero]

/-- The stopped scaled driver is adapted to the natural filtration. -/
theorem stronglyAdapted_neg_mul_stopped {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    StronglyAdapted (Filtration.natural B hsm) (fun t omega => -c * B (min t T) omega) :=
  fun t => ((Filtration.stronglyAdapted_natural hsm (min t T)).mono
    ((Filtration.natural B hsm).mono (min_le_left t T))).const_mul (-c)

/-- The deterministic bracket `c² (t ∧ T)` is continuous and monotone. -/
theorem continuous_monotone_constantBracket (c : ℝ) (T : ℝ≥0) :
    Continuous (fun t : ℝ≥0 => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) ∧
      Monotone (fun t : ℝ≥0 => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) := by
  refine ⟨continuous_const.mul (NNReal.continuous_coe.comp (continuous_id.min continuous_const)),
    fun s t hst => ?_⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_min_right T hst) (sq_nonneg c)

/-- The deterministic bracket is the integrated square of the constant drift. -/
theorem constantBracket_eq_integral (c : ℝ) (T t : ℝ≥0) :
    c ^ 2 * ((min t T : ℝ≥0) : ℝ) =
      ∫ _ in Set.Ioc (0 : ℝ≥0) (min t T), c ^ 2 ∂nonnegativeLebesgueMeasure := by
  have hmass : nonnegativeLebesgueMeasure.real (Set.Ioc (0 : ℝ≥0) (min t T)) =
      ((min t T : ℝ≥0) : ℝ) := by
    rw [measureReal_def, nonnegativeLebesgueMeasure_Ioc, NNReal.coe_zero,
      sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  rw [setIntegral_const, hmass, smul_eq_mul, mul_comm]

/-- The stopped scaled driver is a martingale in the natural filtration. -/
theorem martingale_neg_mul_stopped_natural {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    Martingale (fun t omega => -c * B (min t T) omega) (Filtration.natural B hsm) P := by
  have h := (StochasticCalculus.Martingale.stopAt (martingale_brownian_natural hB hsm) T).smul (-c)
  refine h.congr (stronglyAdapted_neg_mul_stopped hsm c T)
    fun t => Filter.Eventually.of_forall fun omega => ?_
  simp [Pi.smul_apply, smul_eq_mul]

/-- The stopped scaled driver has the before-stop quadratic variation `c² (t ∧ T)`. -/
theorem hasQuadraticVariationBeforeStop_neg_mul_stopped {W : Type*} [MeasurableSpace W]
    {P : Measure W} [IsFiniteMeasure P] {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ omega, Continuous (fun t => B t omega))
    (c : ℝ) (T : ℝ≥0) :
    HasQuadraticVariationBeforeStopProcessInProbability
      (fun t omega => -c * B (min t T) omega)
      (fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) P := by
  have h := ((hasQuadraticVariationBeforeStop_preBrownianReal hB).stop
    (fun s => (hsm s).aestronglyMeasurable) (Filter.Eventually.of_forall hcont) T).const_mul (-c)
  simpa only [neg_sq] using h

/-! ## The Girsanov density contract at a constant drift -/

/-- A Brownian motion with every path continuous and starting at zero carries
the Girsanov density contract at every constant drift and finite horizon. -/
theorem girsanovDensityData_neg_mul_stopped {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ omega, Continuous (fun t => B t omega))
    (hzero : ∀ omega, B 0 omega = 0) (c : ℝ) (T : ℝ≥0) :
    GirsanovDensityData P (Filtration.natural B hsm)
      (fun t omega => -c * B (min t T) omega)
      (fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T where
  novikov := novikovCondition_deterministic (fun t => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T
  localQuadraticVariation := by
    have hlocM : localizingStoppedProcess (fun t omega => -c * B (min t T) omega)
        (fun _ => ⊤) = fun t omega => -c * B (min t T) omega := by
      funext t omega
      simp [localizingStoppedProcess]
    have hlocA : localizingStoppedProcess (fun t (_ : W) => c ^ 2 * ((min t T : ℝ≥0) : ℝ))
        (fun _ => ⊤) = fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ) := by
      funext t omega
      simp [localizingStoppedProcess]
    refine ⟨fun _ _ => ⊤, isLocalizingSequence_const_top _ _, ?_, ?_⟩
    · intro _
      rw [hlocM]
      exact martingale_neg_mul_stopped_natural hB hsm c T
    · intro _
      rw [hlocM, hlocA]
      exact hasQuadraticVariationBeforeStop_neg_mul_stopped hB hsm hcont c T
  continuous_martingale_path := continuous_neg_mul_stopped hcont c T
  adapted_martingale := stronglyAdapted_neg_mul_stopped hsm c T
  adapted_bracket := fun _ => stronglyMeasurable_const
  continuous_monotone_bracket := fun _ => continuous_monotone_constantBracket c T
  martingale_zero := neg_mul_stopped_zero hzero c T
  bracket_zero := fun _ => by
    rw [min_eq_left zero_le]
    simp

/-! ## Transport from the continuous version to the original driver -/

/-- The terminal densities of the version and of the original driver agree
almost surely. -/
theorem girsanovDensity_continuousBrownianVersion_ae_eq {W : Type*} [MeasurableSpace W]
    {P : Measure W} {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P) (c : ℝ) (T : ℝ≥0) :
    girsanovDensity (fun t omega => -c * continuousBrownianVersion B P (min t T) omega)
        (fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T =ᵐ[P]
      girsanovDensity (fun t omega => -c * B (min t T) omega)
        (fun t _ => c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T := by
  filter_upwards [continuousBrownianVersion_ae_eq hB (min T T)] with omega h
  simp only [girsanovDensity, doleansDadeExponential, doleansDadeLog, h]

/-- The dynamic Girsanov theorem at a constant drift: the shifted driver is
pre-Brownian under the exact terminal density measure. -/
theorem isPreBrownianReal_girsanovShiftedBrownian_const_dynamic {W : Type*} [MeasurableSpace W]
    {P : Measure W} {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    IsPreBrownianReal (girsanovShiftedBrownian B (fun _ _ ↦ c) T)
      (girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
        (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  set B' := continuousBrownianVersion B P with hB'
  have hsm' := stronglyMeasurable_continuousBrownianVersion P hsm
  have hBrownian' := isBrownianReal_continuousBrownianVersion hB
  have hdata := girsanovDensityData_neg_mul_stopped hBrownian'.toIsPreBrownianReal hsm'
    (continuous_continuousBrownianVersion B P) (continuousBrownianVersion_zero B P) c T
  have htheta : IsStronglyPredictable (Filtration.natural B' hsm') (fun _ _ ↦ c) :=
    stronglyMeasurable_const
  have hbracketTheta : ∀ t (omega : W), c ^ 2 * ((min t T : ℝ≥0) : ℝ) =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), ((fun _ _ ↦ c) s omega) ^ 2
        ∂nonnegativeLebesgueMeasure :=
    fun t _ => constantBracket_eq_integral c T t
  have hcross : HasCrossVariationProcessInProbability
      (fun t omega ↦ -c * B' (min t T) omega) B'
      (fun t omega ↦ -girsanovIntegratedDrift (fun _ _ ↦ c) T t omega) P := by
    intro t
    have hbase := (tendstoInMeasure_stopped_brownian_brownian_covariation hBrownian' T t)
      |>.const_mul_real_noMeas (-c)
    refine hbase.congr (fun n => Filter.Eventually.of_forall fun omega => ?_)
      (Filter.Eventually.of_forall fun omega => ?_)
    · have h := quadraticCovariationApprox_timeConstant_mul (fun _ => -c) (fun _ => (1 : ℝ))
        (fun s omega => B' (min s T) omega) B' t (n + 1) omega
      simp only [one_mul, mul_one] at h
      exact h.symm
    · simp only [girsanovIntegratedDrift_const, neg_mul]
  have hshift := hdata.isPreBrownianReal_girsanovShiftedBrownian_predictable hsm'
    hBrownian'.toIsPreBrownianReal htheta hbracketTheta hcross
  have hmeasure : girsanovMeasure P (fun t omega ↦ -c * B' (min t T) omega)
      (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T =
      girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
        (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T := by
    unfold girsanovMeasure
    refine withDensity_congr_ae ?_
    filter_upwards [girsanovDensity_continuousBrownianVersion_ae_eq hB c T] with omega h
    rw [h]
  rw [hmeasure] at hshift
  refine hshift.congr fun t => ?_
  refine (girsanovMeasure_absolutelyContinuous P _ _ T).ae_eq ?_
  filter_upwards [continuousBrownianVersion_ae_eq hB t] with omega h
  simp only [girsanovShiftedBrownian, h]

/-- The exact terminal density at a constant drift is integrable. -/
theorem integrable_girsanovDensity_const {W : Type*} [MeasurableSpace W]
    {P : Measure W} {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    Integrable (girsanovDensity (fun t omega ↦ -c * B (min t T) omega)
      (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T) P := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hdata := (girsanovDensityData_neg_mul_stopped
    (isBrownianReal_continuousBrownianVersion hB).toIsPreBrownianReal
    (stronglyMeasurable_continuousBrownianVersion P hsm)
    (continuous_continuousBrownianVersion B P) (continuousBrownianVersion_zero B P) c T).rightCont
  exact hdata.integrable.congr (girsanovDensity_continuousBrownianVersion_ae_eq hB c T)

/-- The exact terminal density measure at a constant drift is equivalent to `P`. -/
theorem girsanovMeasure_const_mutuallyAbsolutelyContinuous {W : Type*} [MeasurableSpace W]
    {P : Measure W} {B : ℝ≥0 → W → ℝ} (hB : IsBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (T : ℝ≥0) :
    girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
        (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T ≪ P ∧
      P ≪ girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
        (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T :=
  girsanovMeasure_mutuallyAbsolutelyContinuous P _ _ T (integrable_girsanovDensity_const hB hsm c T)

end StochasticCalculus
