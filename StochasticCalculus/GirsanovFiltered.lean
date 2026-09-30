/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.GirsanovTheorem

/-!
# Predictable Girsanov in an arbitrary Brownian filtration

The driver is adapted and each future increment is independent of the
supplied filtration at its left endpoint. Right continuity is obtained
internally; predictability need not refer to the natural filtration.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Adaptation and independence from the supplied past imply martingality. -/
theorem martingale_brownian_filtration
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hBadapt : StronglyAdapted V B)
    (hBpast : ∀ {a b : ℝ≥0}, a ≤ b →
      Indep (MeasurableSpace.comap (fun omega ↦ B b omega - B a omega)
        inferInstance) (V a) P) :
    Martingale B (V) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hsm (t : ℝ≥0) : StronglyMeasurable (B t) := hBadapt.stronglyMeasurable
  refine ⟨hBadapt, fun a b hab => ?_⟩
  have hincMeas : StronglyMeasurable (fun omega => B b omega - B a omega) :=
    (hsm b).sub (hsm a)
  have hind := hBpast hab
  have hcondInc : P[(fun omega => B b omega - B a omega) |
      V a] =ᵐ[P]
      fun _ => ∫ omega, B b omega - B a omega ∂P := by
    exact condExp_indep_eq hincMeas.measurable.comap_le
      ((V).le a)
      (Measurable.stronglyMeasurable
        (measurable_iff_comap_le.mpr le_rfl)) hind
  have hmean : (∫ omega, B b omega - B a omega ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
      hB.integral_eval b, hB.integral_eval a, sub_zero]
  have hcurrent : StronglyMeasurable[V a] (B a) :=
    hBadapt a
  have hsplit : B b = (fun omega => B b omega - B a omega) + B a := by
    funext omega
    change B b omega = (B b omega - B a omega) + B a omega
    ring
  calc
    P[B b | V a] =
        P[(fun omega => B b omega - B a omega) + B a |
          V a] := by rw [← hsplit]
    _ =ᵐ[P] P[(fun omega => B b omega - B a omega) |
          V a] +
        P[B a | V a] :=
      condExp_add
        ((hB.integrable_eval b).sub (hB.integrable_eval a))
        (hB.integrable_eval a) _
    _ =ᵐ[P] (fun _ => (0 : ℝ)) + B a := by
      refine Filter.EventuallyEq.add (hcondInc.trans ?_) ?_
      · filter_upwards with omega
        simp only [hmean]
      · exact Filter.EventuallyEq.of_eq <|
          condExp_of_stronglyMeasurable
            ((V).le a) hcurrent
            (hB.integrable_eval a)
    _ =ᵐ[P] B a := by
      filter_upwards with omega
      simp

/-- Measurable normalized characters inherit independence from the past. -/
theorem indep_brownianFourierIncrement_filtration
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B : ℝ≥0 → W → ℝ}
    (hBpast : ∀ {a b : ℝ≥0}, a ≤ b →
      Indep (MeasurableSpace.comap (fun omega ↦ B b omega - B a omega)
        inferInstance) (V a) P)
    (c : ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep (MeasurableSpace.comap (brownianFourierIncrement B c a b)
      inferInstance) (V a) P := by
  apply ProbabilityTheory.indep_of_indep_of_le_left
    (hBpast hab)
  let f : ℝ → ℂ := fun x ↦ Complex.exp
    (((c * x : ℝ) : ℂ) * Complex.I +
      (((((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hfun : brownianFourierIncrement B c a b =
      f ∘ (fun omega ↦ B b omega - B a omega) := by rfl
  rw [hfun]
  exact (hf.comp (measurable_iff_comap_le.mpr le_rfl)).comap_le

/-- Normalized Brownian characters are adapted to any filtration of the driver. -/
theorem stronglyAdapted_brownianFourierIncrementProcess_filtration
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hBadapt : StronglyAdapted V B) (s : ℝ≥0) (c : ℝ) :
    StronglyAdapted (V)
      (brownianFourierIncrementProcess B s c) := by
  intro t
  apply Complex.continuous_exp.comp_stronglyMeasurable
  have hBt : StronglyMeasurable[V t] (B t) :=
    hBadapt t
  have hBs : StronglyMeasurable[V t] (B (min t s)) :=
    (hBadapt (min t s)).mono
      ((V).mono (min_le_left _ _))
  have hinc := (hBt.sub hBs).const_mul c
  have himag := (Complex.continuous_ofReal.comp_stronglyMeasurable hinc).mul_const
    Complex.I
  exact himag.add stronglyMeasurable_const

/-- The normalized character is a true martingale in the supplied Brownian filtration. -/
theorem martingale_brownianFourierIncrementProcess_filtration
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hBadapt : StronglyAdapted V B)
    (hBpast : ∀ {a b : ℝ≥0}, a ≤ b →
      Indep (MeasurableSpace.comap (fun omega ↦ B b omega - B a omega)
        inferInstance) (V a) P)
    (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      V P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hsm (t : ℝ≥0) : StronglyMeasurable (B t) := hBadapt.stronglyMeasurable
  let E := brownianFourierIncrementProcess B s c
  have hEadapt : StronglyAdapted V E :=
    stronglyAdapted_brownianFourierIncrementProcess_filtration hBadapt s c
  have hEint (t : ℝ≥0) : Integrable (E t) P := by
    exact integrable_brownianFourierIncrement hsm c (min t s) t
  refine ⟨hEadapt, fun a b hab ↦ ?_⟩
  change P[E b | V a] =ᵐ[P] E a
  by_cases hbs : b ≤ s
  · have has : a ≤ s := hab.trans hbs
    have hEa : E a = fun _ ↦ 1 := by
      simp only [E, brownianFourierIncrementProcess, min_eq_left has,
        brownianFourierIncrement_self]
    have hEb : E b = fun _ ↦ 1 := by
      simp only [E, brownianFourierIncrementProcess, min_eq_left hbs,
        brownianFourierIncrement_self]
    rw [hEa, hEb]
    exact Filter.EventuallyEq.of_eq <| condExp_of_stronglyMeasurable
      (V.le a) (by fun_prop) (integrable_const 1)
  · have hsb : s ≤ b := le_of_not_ge hbs
    by_cases hsa : s ≤ a
    · let future : W → ℂ := brownianFourierIncrement B c a b
      have hfactor : E b = E a * future := by
        funext omega
        dsimp only [E, brownianFourierIncrementProcess, future]
        rw [min_eq_right hsb, min_eq_right hsa]
        exact (brownianFourierIncrement_mul B c hsa hab omega).symm
      have hfutureMeas : StronglyMeasurable future :=
        stronglyMeasurable_brownianFourierIncrement hsm c a b
      have hfutureInt : Integrable future P :=
        integrable_brownianFourierIncrement hsm c a b
      have hind : Indep (MeasurableSpace.comap future inferInstance) (V a) P :=
        indep_brownianFourierIncrement_filtration hBpast c hab
      have hcondFuture : P[future | V a] =ᵐ[P] fun _ ↦ ∫ omega, future omega ∂P :=
        condExp_indep_eq hfutureMeas.measurable.comap_le (V.le a)
          (Measurable.stronglyMeasurable
            (measurable_iff_comap_le.mpr le_rfl)) hind
      have hproductInt : Integrable (E a * future) P := by
        rw [← hfactor]
        exact hEint b
      rw [hfactor]
      calc
        P[E a * future | V a] =ᵐ[P] E a * P[future | V a] :=
          condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) (hEadapt a)
            hproductInt hfutureInt
        _ =ᵐ[P] E a * (fun _ ↦ ∫ omega, future omega ∂P) :=
          Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hcondFuture
        _ =ᵐ[P] E a := by
          have hmean : (∫ omega, future omega ∂P) = 1 :=
            integral_brownianFourierIncrement hB c hab
          filter_upwards with omega
          simp only [Pi.mul_apply, hmean, mul_one]
    · have has : a ≤ s := le_of_not_ge hsa
      let future : W → ℂ := brownianFourierIncrement B c s b
      have hEa : E a = fun _ ↦ 1 := by
        simp only [E, brownianFourierIncrementProcess, min_eq_left has,
          brownianFourierIncrement_self]
      have hEb : E b = future := by
        simp only [E, brownianFourierIncrementProcess, min_eq_right hsb, future]
      have hfutureMeas : StronglyMeasurable future :=
        stronglyMeasurable_brownianFourierIncrement hsm c s b
      have hindS : Indep (MeasurableSpace.comap future inferInstance) (V s) P :=
        indep_brownianFourierIncrement_filtration hBpast c hsb
      have hindA : Indep (MeasurableSpace.comap future inferInstance) (V a) P :=
        ProbabilityTheory.indep_of_indep_of_le_right hindS (V.mono has)
      have hcondFuture : P[future | V a] =ᵐ[P] fun _ ↦ ∫ omega, future omega ∂P :=
        condExp_indep_eq hfutureMeas.measurable.comap_le (V.le a)
          (Measurable.stronglyMeasurable
            (measurable_iff_comap_le.mpr le_rfl)) hindA
      rw [hEa, hEb]
      have hmean : (∫ omega, future omega ∂P) = 1 :=
        integral_brownianFourierIncrement hB c hsb
      filter_upwards [hcondFuture] with omega homega
      simp only [homega, hmean]

/-- Stochastic continuity transports Brownian martingality to right continuation. -/
theorem martingale_brownian_rightCont_filtration
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hmart : Martingale B V P) :
    Martingale B (Filtration.rightCont V) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply StochasticCalculus.Martingale.rightCont_of_tendstoInMeasure_of_uniformIntegrable_banach
    hmart
  · intro r a ha
    exact StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha
  · intro _r a ha
    obtain ⟨R, hR⟩ := ha.bddAbove_range
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic hmart R)
      (fun n => ⟨a n, by
        simpa only [Set.mem_Iic] using hR (Set.mem_range_self n)⟩)
    exact hUI

/-- Brownian Fourier martingales survive right continuation of the supplied filtration. -/
theorem martingale_brownianFourierIncrementProcess_rightCont_filtration
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hBadapt : StronglyAdapted V B)
    (hBpast : ∀ {a b : ℝ≥0}, a ≤ b →
      Indep (MeasurableSpace.comap (fun omega ↦ B b omega - B a omega)
        inferInstance) (V a) P)
    (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      (Filtration.rightCont V) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    (martingale_brownianFourierIncrementProcess_filtration hB hBadapt hBpast s c)
  · intro r a ha
    exact tendstoInMeasure_brownianFourierIncrementProcess
      hB (fun _ ↦ hBadapt.stronglyMeasurable) s c ha
  · intro R
    let K : ℝ≥0 := ⟨Real.exp ((R : ℝ) * c ^ 2 / 2),
      (Real.exp_pos _).le⟩
    refine ⟨K, fun t ht omega ↦ ?_⟩
    simp only [brownianFourierIncrementProcess]
    rw [norm_brownianFourierIncrement]
    change Real.exp (((t - min t s : ℝ≥0) : ℝ) * c ^ 2 / 2) ≤
      Real.exp ((R : ℝ) * c ^ 2 / 2)
    apply Real.exp_le_exp.mpr
    have htime : ((t - min t s : ℝ≥0) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (tsub_le_self.trans ht)
    nlinarith [sq_nonneg c]

/-- Predictable Girsanov on a supplied Brownian filtration. The conclusion
uses the exact terminal density and the literal integrated drift, with no
right-continuity, bounded-density, or approximation premise added. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_filtered
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hBadapt : StronglyAdapted V B)
    (hBpast : ∀ {a b : ℝ≥0}, a ≤ b →
      Indep (MeasurableSpace.comap (fun omega ↦ B b omega - B a omega)
        inferInstance) (V a) P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
  let X := girsanovShiftedBrownian B theta T
  have hdataR : GirsanovDensityData P (Filtration.rightCont V) M bracket T := h.rightCont
  have hBadaptR : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration hBadapt V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hX : StronglyAdapted (Filtration.rightCont V) X :=
    stronglyAdapted_girsanovShiftedBrownian hBadaptR hthetaR
  have hXeq (t : ℝ≥0) (omega : W) : X t omega = B t omega - C (min t T) omega := by
    change B t omega + girsanovIntegratedDrift theta T t omega =
      B t omega - -girsanovIntegratedDrift theta T (min t T) omega
    rw [sub_neg_eq_add]
    congr 1
    unfold girsanovIntegratedDrift
    rw [min_eq_left (min_le_right t T)]
  have hXzero : X 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simp only [X, girsanovShiftedBrownian, homega, girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure, add_zero]
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket X T := by
    apply girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
      hdataR.adapted_martingale hdataR.adapted_bracket hX hXeq hXzero
      hdataR.martingale_densityProcess
    · intro c
      exact hdataR.martingale_stopAt_complexDoleans_predictable hB
        (martingale_brownian_rightCont_filtration hB
          (martingale_brownian_filtration hB hBadapt hBpast))
        hthetaR hbracketTheta hcross c
    · intro c
      exact martingale_brownianFourierIncrementProcess_rightCont_filtration
        hB hBadapt hBpast T c
  exact hdataR.isPreBrownianReal_girsanovShiftedBrownian_of_fourierMartingale
    hBadaptR hB.eval_zero_ae_eq_zero hthetaR hmart

end StochasticCalculus
