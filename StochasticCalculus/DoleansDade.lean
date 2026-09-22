/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.DoleansDadeMartingale

/-!
# Doléans--Dade exponential of Gaussian increments

Processes with independent centered Gaussian increments and their
exponential martingales, the Brownian specialization with its
natural-filtration martingale property, and the exponential of a constant
multiple of Brownian motion used by the pricing chain.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The exponentially normalized value of a centered Gaussian random
variable is integrable. -/
theorem integrable_gaussianNormalizedExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : W → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    Integrable (fun omega =>
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))) P := by
  have hexp : Integrable (fun x : ℝ => Real.exp (1 * x))
      (gaussianReal 0 v) := integrable_exp_mul_gaussianReal 1
  rw [← hX.map_eq] at hexp
  have hcomp := hexp.comp_aemeasurable hX.aemeasurable
  have hraw : Integrable (fun omega => Real.exp (X omega)) P := by
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => by simp)
  have hscaled := hraw.const_mul (Real.exp (-(1 / 2 : ℝ) * (v : ℝ)))
  exact hscaled.congr (Filter.Eventually.of_forall fun omega => by
    change Real.exp (-(1 / 2 : ℝ) * (v : ℝ)) * Real.exp (X omega) =
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))
    rw [← Real.exp_add]
    congr 1
    ring)

/-- The exponential normalizer of a centered Gaussian random variable has
expectation one. -/
theorem integral_gaussianNormalizedExponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : W → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ omega, Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ)) ∂P = 1 := by
  have hmgf : ∫ omega, Real.exp (X omega) ∂P =
      Real.exp ((v : ℝ) / 2) := by
    have h := mgf_gaussianReal hX.map_eq 1
    simpa [mgf] using h
  have heq : (fun omega =>
      Real.exp (X omega - (1 / 2 : ℝ) * (v : ℝ))) =
      fun omega => Real.exp (-(1 / 2 : ℝ) * (v : ℝ)) *
        Real.exp (X omega) := by
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, hmgf, ← Real.exp_add]
  convert Real.exp_zero using 1
  ring_nf

/-- A centered Gaussian process with independent increments relative to a
filtration and deterministic nondecreasing variance clock. -/
structure IsCenteredGaussianIndependentIncrements
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (variance : ℝ≥0 → ℝ≥0) (P : Measure W) : Prop where
  stronglyAdapted : StronglyAdapted 𝓕 M
  variance_mono : Monotone variance
  hasLaw_eval (t : ℝ≥0) : HasLaw (M t) (gaussianReal 0 (variance t)) P
  hasLaw_increment {a b : ℝ≥0} (hab : a ≤ b) :
    HasLaw (fun omega => M b omega - M a omega)
      (gaussianReal 0 (variance b - variance a)) P
  indep_increment {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap (fun omega => M b omega - M a omega)
        inferInstance)
      (𝓕 a) P

/-- A real square bundled as a nonnegative real variance. -/
def realSquareNNReal (c : ℝ) : ℝ≥0 :=
  ⟨c ^ 2, sq_nonneg c⟩

@[simp]
theorem coe_realSquareNNReal (c : ℝ) :
    (realSquareNNReal c : ℝ) = c ^ 2 :=
  rfl

/-- Centered Gaussian independent-increment processes are closed under
deterministic scalar multiplication; their variance clock scales by `c²`. -/
theorem IsCenteredGaussianIndependentIncrements.const_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P) (c : ℝ) :
    IsCenteredGaussianIndependentIncrements
      (fun t omega => c * M t omega) 𝓕
      (fun t => realSquareNNReal c * variance t) P where
  stronglyAdapted := by
    change StronglyAdapted 𝓕 (c • M)
    exact hM.stronglyAdapted.smul c
  variance_mono := by
    intro a b hab
    simpa only [mul_comm] using
      mul_le_mul_left (hM.variance_mono hab) (realSquareNNReal c)
  hasLaw_eval := by
    intro t
    have hsquare : NNReal.mk (c ^ 2) (sq_nonneg c) = realSquareNNReal c := by
      apply NNReal.eq
      rfl
    rw [← hsquare]
    simpa only [mul_zero] using gaussianReal_const_mul (hM.hasLaw_eval t) c
  hasLaw_increment := by
    intro a b hab
    have hsquare : NNReal.mk (c ^ 2) (sq_nonneg c) = realSquareNNReal c := by
      apply NNReal.eq
      rfl
    have hLaw := gaussianReal_const_mul (hM.hasLaw_increment hab) c
    change HasLaw (fun omega => c * M b omega - c * M a omega)
      (gaussianReal 0
        (realSquareNNReal c * variance b -
          realSquareNNReal c * variance a)) P
    rw [← mul_tsub]
    rw [← hsquare]
    apply HasLaw.congr
    · simpa only [mul_zero] using hLaw
    filter_upwards with omega
    ring
  indep_increment := by
    intro a b hab
    let increment : W → ℝ := fun omega => M b omega - M a omega
    have hraw : Indep (MeasurableSpace.comap increment inferInstance)
        (𝓕 a) P := hM.indep_increment hab
    have hincMeas : @Measurable W ℝ
        (MeasurableSpace.comap increment inferInstance) inferInstance increment :=
      measurable_iff_comap_le.mpr le_rfl
    have hscaledMeas : @Measurable W ℝ
        (MeasurableSpace.comap increment inferInstance) inferInstance
        (fun omega => c * M b omega - c * M a omega) := by
      have hcomp : @Measurable W ℝ
          (MeasurableSpace.comap increment inferInstance) inferInstance
          (fun omega => c * increment omega) := by
        fun_prop
      convert hcomp using 1
      funext omega
      dsimp only [increment]
      ring
    exact indep_of_indep_of_le_left hraw hscaledMeas.comap_le

/-- The stochastic exponential associated to a centered Gaussian process and
its deterministic variance clock. -/
def centeredGaussianDoleansDadeExponential
    {W : Type*} (M : ℝ≥0 → W → ℝ) (variance : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential M (fun s _ => (variance s : ℝ)) t omega

/-- The normalized exponential of one increment of a centered Gaussian
process with deterministic variance clock. -/
def centeredGaussianDoleansDadeIncrement
    {W : Type*} (M : ℝ≥0 → W → ℝ) (variance : ℝ≥0 → ℝ≥0)
    (a b : ℝ≥0) (omega : W) : ℝ :=
  Real.exp ((M b omega - M a omega) -
    (1 / 2 : ℝ) * ((variance b - variance a : ℝ≥0) : ℝ))

/-- Every fixed-time centered Gaussian stochastic exponential is
integrable. -/
theorem IsCenteredGaussianIndependentIncrements.integrable_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    (t : ℝ≥0) :
    Integrable (centeredGaussianDoleansDadeExponential M variance t) P := by
  exact integrable_gaussianNormalizedExponential (hM.hasLaw_eval t)

/-- The normalized exponential of a centered Gaussian increment is
integrable. -/
theorem IsCenteredGaussianIndependentIncrements.integrable_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Integrable (centeredGaussianDoleansDadeIncrement M variance a b) P :=
  integrable_gaussianNormalizedExponential (hM.hasLaw_increment hab)

/-- The normalized exponential of a centered Gaussian increment has mean
one. -/
theorem IsCenteredGaussianIndependentIncrements.integral_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    (∫ omega,
      centeredGaussianDoleansDadeIncrement M variance a b omega ∂P) = 1 :=
  integral_gaussianNormalizedExponential (hM.hasLaw_increment hab)

/-- The centered Gaussian stochastic exponential factors into its current
value and the normalized future increment. -/
theorem IsCenteredGaussianIndependentIncrements.exponential_factor
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    centeredGaussianDoleansDadeExponential M variance b =
      centeredGaussianDoleansDadeExponential M variance a *
        centeredGaussianDoleansDadeIncrement M variance a b := by
  funext omega
  unfold centeredGaussianDoleansDadeExponential
    centeredGaussianDoleansDadeIncrement doleansDadeExponential doleansDadeLog
  simp only [Pi.mul_apply]
  rw [← Real.exp_add, NNReal.coe_sub (hM.variance_mono hab)]
  congr 1
  ring

/-- A normalized future Gaussian exponential increment is independent of
the filtration at the left endpoint. -/
theorem IsCenteredGaussianIndependentIncrements.indep_increment_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap
        (centeredGaussianDoleansDadeIncrement M variance a b) inferInstance)
      (𝓕 a) P := by
  have hincMeas : @Measurable W ℝ
      (MeasurableSpace.comap (fun omega => M b omega - M a omega)
        inferInstance) inferInstance
      (fun omega => M b omega - M a omega) :=
    measurable_iff_comap_le.mpr le_rfl
  apply indep_of_indep_of_le_left (hM.indep_increment hab)
  apply Measurable.comap_le
  exact (show Measurable (fun x : ℝ => Real.exp
    (x - (1 / 2 : ℝ) * ((variance b - variance a : ℝ≥0) : ℝ))) by
      fun_prop).comp hincMeas

/-- A centered Gaussian independent-increment process has a martingale
stochastic exponential. -/
theorem IsCenteredGaussianIndependentIncrements.martingale_exponential
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {variance : ℝ≥0 → ℝ≥0}
    (hM : IsCenteredGaussianIndependentIncrements M 𝓕 variance P) :
    Martingale (centeredGaussianDoleansDadeExponential M variance) 𝓕 P := by
  let _ : IsProbabilityMeasure P := (hM.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨fun t => ?_, fun a b hab => ?_⟩
  · change StronglyMeasurable[𝓕 t] (fun omega =>
      Real.exp (M t omega - (1 / 2 : ℝ) * (variance t : ℝ)))
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hM.stronglyAdapted t).sub stronglyMeasurable_const)
  · let future : W → ℝ :=
      centeredGaussianDoleansDadeIncrement M variance a b
    have hfutureInt : Integrable future P :=
      hM.integrable_increment_exponential hab
    have hcurrentMeas : StronglyMeasurable[𝓕 a]
        (centeredGaussianDoleansDadeExponential M variance a) := by
      change StronglyMeasurable[𝓕 a] (fun omega =>
        Real.exp (M a omega - (1 / 2 : ℝ) * (variance a : ℝ)))
      exact Real.continuous_exp.comp_stronglyMeasurable
        ((hM.stronglyAdapted a).sub stronglyMeasurable_const)
    have hind : Indep (MeasurableSpace.comap future inferInstance) (𝓕 a) P :=
      hM.indep_increment_exponential hab
    have hfutureMeas : StronglyMeasurable future := by
      have hb := (hM.stronglyAdapted b).mono (𝓕.le b)
      have ha := (hM.stronglyAdapted a).mono (𝓕.le a)
      exact Real.continuous_exp.comp_stronglyMeasurable
        ((hb.sub ha).sub stronglyMeasurable_const)
    have hcondFuture : P[future | 𝓕 a] =ᵐ[P]
        fun _ => ∫ omega, future omega ∂P := by
      exact condExp_indep_eq hfutureMeas.measurable.comap_le (𝓕.le a)
        (Measurable.stronglyMeasurable
          (measurable_iff_comap_le.mpr le_rfl)) hind
    have hfactor : centeredGaussianDoleansDadeExponential M variance b =
        centeredGaussianDoleansDadeExponential M variance a * future :=
      hM.exponential_factor hab
    have hproductInt : Integrable
        (centeredGaussianDoleansDadeExponential M variance a * future) P := by
      rw [← hfactor]
      exact hM.integrable_exponential b
    calc
      P[centeredGaussianDoleansDadeExponential M variance b | 𝓕 a] =
          P[centeredGaussianDoleansDadeExponential M variance a * future |
            𝓕 a] := by rw [hfactor]
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a *
          P[future | 𝓕 a] :=
        condExp_mul_of_stronglyMeasurable_left hcurrentMeas
          hproductInt hfutureInt
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a *
          (fun _ => ∫ omega, future omega ∂P) :=
        Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
      _ =ᵐ[P] centeredGaussianDoleansDadeExponential M variance a := by
        have hmean : (∫ omega, future omega ∂P) = 1 :=
          hM.integral_increment_exponential hab
        filter_upwards with omega
        simp only [Pi.mul_apply, hmean, mul_one]

/-! ## Brownian specialization -/

/-- A future Brownian increment is independent of the natural filtration at
its left endpoint. -/
theorem indep_brownianIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) {a b : ℝ≥0} (hab : a ≤ b) :
    Indep
      (MeasurableSpace.comap (fun omega => B b omega - B a omega)
        inferInstance)
      (Filtration.natural B hsm a) P := by
  have hshift := hB.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ => x (b - a)) :=
    measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hincPast : IndepFun (fun omega => B b omega - B a omega)
      (fun omega (t : Set.Iic a) => B t omega) P := by
    convert hfuturePast using 1
    · funext omega
      change B b omega - B a omega = B (a + (b - a)) omega - B a omega
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hincPast
  have hnat : Filtration.natural B hsm a =
      MeasurableSpace.comap (fun omega (t : Set.Iic a) => B t omega)
        inferInstance := by
    rw [Filtration.natural_eq_comap]
  rw [hnat]
  exact hind

/-- Brownian motion is a centered Gaussian independent-increment process
with variance clock `t`. -/
theorem isCenteredGaussianIndependentIncrements_brownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    IsCenteredGaussianIndependentIncrements B
      (Filtration.natural B hsm) (fun t => t) P where
  stronglyAdapted := Filtration.stronglyAdapted_natural hsm
  variance_mono := fun _ _ hab => hab
  hasLaw_eval := hB.hasLaw_eval
  hasLaw_increment := by
    intro a b hab
    refine ((hB.shift a).hasLaw_eval (b - a)).congr ?_
    filter_upwards with omega
    rw [add_comm, tsub_add_cancel_of_le hab]
  indep_increment := indep_brownianIncrement_natural hB hsm

/-- A constant multiple of Brownian motion is a centered Gaussian
independent-increment process with variance clock `c²t`. -/
theorem isCenteredGaussianIndependentIncrements_scaledBrownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    IsCenteredGaussianIndependentIncrements
      (fun t omega => c * B t omega) (Filtration.natural B hsm)
      (fun t => realSquareNNReal c * t) P :=
  (isCenteredGaussianIndependentIncrements_brownian_natural hB hsm).const_mul c

/-- A pre-Brownian process with strongly measurable coordinates is a
martingale in its natural filtration. -/
theorem martingale_brownian_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale B (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨Filtration.stronglyAdapted_natural hsm, fun a b hab => ?_⟩
  have hincMeas : StronglyMeasurable (fun omega => B b omega - B a omega) :=
    (hsm b).sub (hsm a)
  have hind := indep_brownianIncrement_natural hB hsm hab
  have hcondInc : P[(fun omega => B b omega - B a omega) |
      Filtration.natural B hsm a] =ᵐ[P]
      fun _ => ∫ omega, B b omega - B a omega ∂P := by
    exact condExp_indep_eq hincMeas.measurable.comap_le
      ((Filtration.natural B hsm).le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl)) hind
  have hmean : (∫ omega, B b omega - B a omega ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
      hB.integral_eval b, hB.integral_eval a, sub_zero]
  have hcurrent : StronglyMeasurable[Filtration.natural B hsm a] (B a) :=
    Filtration.stronglyAdapted_natural hsm a
  have hsplit : B b = (fun omega => B b omega - B a omega) + B a := by
    funext omega
    change B b omega = (B b omega - B a omega) + B a omega
    ring
  calc
    P[B b | Filtration.natural B hsm a] =
        P[(fun omega => B b omega - B a omega) + B a |
          Filtration.natural B hsm a] := by rw [← hsplit]
    _ =ᵐ[P] P[(fun omega => B b omega - B a omega) |
          Filtration.natural B hsm a] +
        P[B a | Filtration.natural B hsm a] :=
      condExp_add
        ((hB.integrable_eval b).sub (hB.integrable_eval a))
        (hB.integrable_eval a) _
    _ =ᵐ[P] (fun _ => (0 : ℝ)) + B a := by
      refine Filter.EventuallyEq.add (hcondInc.trans ?_) ?_
      · filter_upwards with omega
        simp only [hmean]
      · exact Filter.EventuallyEq.of_eq <|
          condExp_of_stronglyMeasurable
            ((Filtration.natural B hsm).le a) hcurrent
            (hB.integrable_eval a)
    _ =ᵐ[P] B a := by
      filter_upwards with omega
      simp

/-! ## Constant multiples of Brownian motion -/

/-- The Doléans–Dade exponential associated to `c B`, whose bracket is
`c² t`. -/
def scaledBrownianDoleansDadeExponential
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential
    (fun s omega => c * B s omega)
    (fun s _ => c ^ 2 * (s : ℝ)) t omega

/-- The generic Gaussian exponential specializes definitionally to the
scaled Brownian exponential. -/
theorem centeredGaussianDoleansDadeExponential_scaledBrownian
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ) :
    centeredGaussianDoleansDadeExponential
        (fun t omega => c * B t omega)
        (fun t => realSquareNNReal c * t) =
      scaledBrownianDoleansDadeExponential c B := by
  rfl

/-- The scaled Brownian stochastic exponential is a martingale by the
generic centered Gaussian independent-increment theorem. -/
theorem martingale_scaledBrownianDoleansDadeExponential_via_gaussianIncrements
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) :
    Martingale (scaledBrownianDoleansDadeExponential c B)
      (Filtration.natural B hsm) P := by
  rw [← centeredGaussianDoleansDadeExponential_scaledBrownian]
  exact (isCenteredGaussianIndependentIncrements_scaledBrownian_natural
    hB hsm c).martingale_exponential
@[simp]
theorem scaledBrownianDoleansDadeExponential_apply
    {W : Type*} (c : ℝ) (B : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) :
    scaledBrownianDoleansDadeExponential c B t omega =
      Real.exp (c * B t omega - (1 / 2 : ℝ) * (c ^ 2 * (t : ℝ))) :=
  rfl

end StochasticCalculus
