/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.GirsanovCommonRefinement

/-!
# Brownian Fourier increments and the complex exponential

The normalised complex character of a Brownian increment, its martingale
property in the natural and right-continuous filtrations, the complex
martingale combination `M + i c B` with its bracket, the complex
Doléans--Dade exponential, and the tightness of the freezing density at left
endpoints.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The normalized complex character of a Brownian increment. -/
@[expose] def brownianFourierIncrement
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a b : ℝ≥0) : W → ℂ :=
  fun omega ↦ Complex.exp
    (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I +
      (((((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))

/-- The normalized Brownian character has a deterministic norm. -/
theorem norm_brownianFourierIncrement
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a b : ℝ≥0) (omega : W) :
    ‖brownianFourierIncrement B c a b omega‖ =
      Real.exp (((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2) := by
  rw [brownianFourierIncrement, Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

/-- Measurability of the two endpoint evaluations makes the normalized
Brownian character strongly measurable. -/
theorem stronglyMeasurable_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ) (a b : ℝ≥0) :
    StronglyMeasurable (brownianFourierIncrement B c a b) := by
  apply Complex.continuous_exp.comp_stronglyMeasurable
  have hinc := ((hsm b).sub (hsm a)).const_mul c
  have himag := (Complex.continuous_ofReal.comp_stronglyMeasurable hinc).mul_const
    Complex.I
  exact himag.add stronglyMeasurable_const

/-- Every normalized Brownian character is integrable. -/
theorem integrable_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hsm : ∀ t, StronglyMeasurable (B t))
    (c : ℝ) (a b : ℝ≥0) :
    Integrable (brownianFourierIncrement B c a b) P := by
  refine Integrable.mono' (integrable_const
    (Real.exp (((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2)))
    (stronglyMeasurable_brownianFourierIncrement hsm c a b).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun omega ↦ by
    rw [norm_brownianFourierIncrement]

/-- The Gaussian characteristic function cancels the deterministic
normalizer, so a normalized Brownian character has mean one. -/
theorem integral_brownianFourierIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (c : ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ omega, brownianFourierIncrement B c a b omega ∂P = 1 := by
  let inc : W → ℝ := fun omega ↦ B b omega - B a omega
  let v : ℝ := ((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2
  have hchar : (∫ omega, Complex.exp
      (((c * inc omega : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp (-(v : ℂ)) := by
    have hlaw := hB.hasLaw_sub b a
    have hcomp := hlaw.integral_comp (E := ℂ)
      (f := fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (by fun_prop)
    calc
      (∫ omega, Complex.exp (((c * inc omega : ℝ) : ℂ) * Complex.I) ∂P) =
          ∫ x, Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)
            ∂gaussianReal 0 (nndist (b : ℝ) (a : ℝ)) := by
        change (∫ omega, Complex.exp
          (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I) ∂P) = _
        change (∫ omega, Complex.exp
          (((c * (B b omega - B a omega) : ℝ) : ℂ) * Complex.I) ∂P) = _ at hcomp
        exact hcomp
      _ = charFun (gaussianReal 0 (nndist (b : ℝ) (a : ℝ))) c := by
        rw [charFun_apply_real]
        apply integral_congr_ae
        filter_upwards with x
        congr 1
        push_cast
        ring
      _ = Complex.exp
          (-((((nndist (b : ℝ) (a : ℝ) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) := by
        rw [charFun_gaussianReal]
        simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
        congr 1
        push_cast
        ring
      _ = Complex.exp (-(v : ℂ)) := by
        congr 1
        dsimp only [v]
        rw [show (nndist (b : ℝ) (a : ℝ) : ℝ) = (b : ℝ) - (a : ℝ) by
          rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (mod_cast hab))],
          NNReal.coe_sub hab]
  have hfactor : brownianFourierIncrement B c a b = fun omega ↦
      Complex.exp (v : ℂ) *
        Complex.exp (((c * inc omega : ℝ) : ℂ) * Complex.I) := by
    funext omega
    rw [brownianFourierIncrement, Complex.exp_add]
    dsimp only [inc, v]
    ring
  rw [hfactor, integral_const_mul, hchar, ← Complex.exp_add]
  simp

/-- A normalized Brownian character is independent of the natural
filtration at the left endpoint. -/
theorem indep_brownianFourierIncrement_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (c : ℝ)
    {a b : ℝ≥0} (hab : a ≤ b) :
    Indep (MeasurableSpace.comap (brownianFourierIncrement B c a b)
      inferInstance) (Filtration.natural B hsm a) P := by
  apply ProbabilityTheory.indep_of_indep_of_le_left
    (indep_brownianIncrement_natural hB hsm hab)
  let f : ℝ → ℂ := fun x ↦ Complex.exp
    (((c * x : ℝ) : ℂ) * Complex.I +
      (((((b - a : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hfun : brownianFourierIncrement B c a b =
      f ∘ (fun omega ↦ B b omega - B a omega) := by rfl
  rw [hfun]
  exact (hf.comp (measurable_iff_comap_le.mpr le_rfl)).comap_le

@[simp]
theorem brownianFourierIncrement_self
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ) (a : ℝ≥0) :
    brownianFourierIncrement B c a a = fun _ ↦ 1 := by
  funext omega
  simp [brownianFourierIncrement]

/-- Normalized Brownian characters multiply over adjacent intervals. -/
theorem brownianFourierIncrement_mul
    {W : Type*} (B : ℝ≥0 → W → ℝ) (c : ℝ)
    {a b d : ℝ≥0} (hab : a ≤ b) (hbd : b ≤ d) (omega : W) :
    brownianFourierIncrement B c a b omega *
        brownianFourierIncrement B c b d omega =
      brownianFourierIncrement B c a d omega := by
  rw [brownianFourierIncrement, brownianFourierIncrement,
    brownianFourierIncrement, ← Complex.exp_add]
  congr 1
  push_cast [NNReal.coe_sub hab, NNReal.coe_sub hbd,
    NNReal.coe_sub (hab.trans hbd)]
  ring

/-- The normalized Brownian character based at `s`; it is one before `s`
and accumulates the normalized character of `B_t-B_s` afterwards. -/
@[expose] def brownianFourierIncrementProcess
    {W : Type*} (B : ℝ≥0 → W → ℝ) (s : ℝ≥0) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t ↦ brownianFourierIncrement B c (min t s) t

/-- The Brownian Fourier process is strongly adapted to the natural
filtration of the supplied version. -/
theorem stronglyAdapted_brownianFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {B : ℝ≥0 → W → ℝ}
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    StronglyAdapted (Filtration.natural B hsm)
      (brownianFourierIncrementProcess B s c) := by
  intro t
  apply Complex.continuous_exp.comp_stronglyMeasurable
  have hBt : StronglyMeasurable[Filtration.natural B hsm t] (B t) :=
    Filtration.stronglyAdapted_natural hsm t
  have hBs : StronglyMeasurable[Filtration.natural B hsm t] (B (min t s)) :=
    (Filtration.stronglyAdapted_natural hsm (min t s)).mono
      ((Filtration.natural B hsm).mono (min_le_left _ _))
  have hinc := (hBt.sub hBs).const_mul c
  have himag := (Complex.continuous_ofReal.comp_stronglyMeasurable hinc).mul_const
    Complex.I
  exact himag.add stronglyMeasurable_const

/-- The normalized Brownian Fourier process is a complex martingale for
every pre-Brownian version; no sample-path continuity is used. -/
theorem martingale_brownianFourierIncrementProcess_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      (Filtration.natural B hsm) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let V := Filtration.natural B hsm
  let E := brownianFourierIncrementProcess B s c
  have hEadapt : StronglyAdapted V E :=
    stronglyAdapted_brownianFourierIncrementProcess hsm s c
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
        indep_brownianFourierIncrement_natural hB hsm c hab
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
        indep_brownianFourierIncrement_natural hB hsm c hsb
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

/-- A pre-Brownian process is a martingale in the right continuation of its
natural filtration.  Uniform integrability of bounded deterministic-time
families replaces any appeal to pathwise continuity or random-time optional
stopping. -/
theorem martingale_brownian_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) :
    Martingale B (Filtration.rightCont (Filtration.natural B hsm)) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let V := Filtration.natural B hsm
  have hmart : Martingale B V P := martingale_brownian_natural hB hsm
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
    simpa only [V] using hUI

/-- The normalized Brownian character is stochastically continuous for
every pre-Brownian version.  This follows from stochastic continuity of the
two Brownian endpoint evaluations and continuity of the complex exponential;
no sample-path regularity is used. -/
theorem tendstoInMeasure_brownianFourierIncrementProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n ↦ brownianFourierIncrementProcess B s c (a n)) atTop
      (brownianFourierIncrementProcess B s c r) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let inc : ℕ → W → ℝ := fun n omega ↦
    B (a n) omega - B (min (a n) s) omega
  let incLimit : W → ℝ := fun omega ↦ B r omega - B (min r s) omega
  have hmin : Tendsto (fun n ↦ min (a n) s) atTop (nhds (min r s)) :=
    ha.min tendsto_const_nhds
  have hinc : TendstoInMeasure P inc atTop incLimit := by
    apply TendstoInMeasure.continuous_comp₂
      (fun n ↦ (hsm (a n)).aestronglyMeasurable)
      (fun n ↦ (hsm (min (a n) s)).aestronglyMeasurable)
      (StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha)
      (StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB hmin)
    fun_prop
  have htime : TendstoInMeasure P (fun n ↦ fun _ : W ↦ a n) atTop
      (fun _ : W ↦ r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ ↦ aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ ↦ ha
  let f : ℝ → ℝ≥0 → ℂ := fun x t ↦ Complex.exp
    (((c * x : ℝ) : ℂ) * Complex.I +
      (((((t - min t s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))
  have hf : Continuous f.uncurry := by
    dsimp only [f, Function.uncurry]
    fun_prop
  have hresult := TendstoInMeasure.continuous_comp₂
    (fun n ↦ ((hsm (a n)).sub (hsm (min (a n) s))).aestronglyMeasurable)
    (fun _ ↦ aestronglyMeasurable_const) hinc htime hf
  change TendstoInMeasure P (fun n omega ↦ Complex.exp
      (((c * (B (a n) omega - B (min (a n) s) omega) : ℝ) : ℂ) *
        Complex.I +
        (((((a n - min (a n) s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))))
    atTop (fun omega ↦ Complex.exp
      (((c * (B r omega - B (min r s) omega) : ℝ) : ℂ) * Complex.I +
        (((((r - min r s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))))
  simpa only [inc, incLimit, f, Pi.sub_apply] using hresult

/-- The Brownian Fourier martingale remains a martingale after right
continuation of its natural filtration. -/
theorem martingale_brownianFourierIncrementProcess_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) (c : ℝ) :
    Martingale (brownianFourierIncrementProcess B s c)
      (Filtration.rightCont (Filtration.natural B hsm)) P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    (martingale_brownianFourierIncrementProcess_natural hB hsm s c)
  · intro r a ha
    exact tendstoInMeasure_brownianFourierIncrementProcess hB hsm s c ha
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

/-! ## Complex quadratic variation for the Fourier argument -/

/-- The complex local-martingale combination `M + i c B` used in the
Fourier proof of Girsanov's theorem. -/
@[expose] def complexMartingaleCombination
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ) : ℝ≥0 → W → ℂ :=
  fun t omega ↦ (M t omega : ℂ) + ((c * B t omega : ℝ) : ℂ) * Complex.I

/-- The complex bracket of `M + i c B`: the real Brownian quadratic term
changes sign and the real cross variation becomes the imaginary term. -/
@[expose] def complexMartingaleCombinationBracket
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (bracket t omega : ℂ) - (c ^ 2 * (t : ℝ) : ℝ) +
    ((2 * c * C t omega : ℝ) : ℂ) * Complex.I

/-- Adapted real inputs assemble into the adapted complex martingale
combination. -/
theorem stronglyAdapted_complexMartingaleCombination
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M B : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hB : StronglyAdapted V B) (c : ℝ) :
    StronglyAdapted V (complexMartingaleCombination M B c) := by
  intro t
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable (hM t)).add
    ((Complex.continuous_ofReal.comp_stronglyMeasurable
      ((hB t).const_mul c)).mul_const Complex.I)

/-- Adapted bracket and cross-variation inputs assemble into the adapted
complex bracket. -/
theorem stronglyAdapted_complexMartingaleCombinationBracket
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : StronglyAdapted V bracket)
    (hC : StronglyAdapted V C) (c : ℝ) :
    StronglyAdapted V
      (complexMartingaleCombinationBracket bracket C c) := by
  intro t
  exact ((Complex.continuous_ofReal.comp_stronglyMeasurable
    (hbracket t)).sub stronglyMeasurable_const).add
      ((Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hC t).const_mul (2 * c))).mul_const Complex.I)

/-- Algebraic complex Doléans exponential associated to a complex process
and its algebraic quadratic variation. -/
@[expose] noncomputable def complexDoleansDadeExponential
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) : ℝ≥0 → W → ℂ :=
  fun t omega ↦ Complex.exp (X t omega - Q t omega / 2)

/-- The complex stochastic exponential of `M + i c B` factors into the
real Doléans density and the normalized Fourier character of `B - C`. -/
theorem complexDoleansDadeExponential_combination_factor
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega =
      (doleansDadeExponential M bracket t omega : ℂ) *
        Complex.exp
          (((c * (B t omega - C t omega) : ℝ) : ℂ) * Complex.I +
            ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ)) := by
  unfold complexDoleansDadeExponential complexMartingaleCombination
    complexMartingaleCombinationBracket doleansDadeExponential doleansDadeLog
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The continuous factor in the complex Girsanov exponential after the
possibly discontinuous pre-Brownian Fourier character has been split off. -/
noncomputable def girsanovComplexDoleansContinuousCoefficient
    {W : Type*} (M bracket C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) : ℂ :=
  (doleansDadeExponential M bracket t omega : ℂ) *
    Complex.exp
      (((-c * C t omega : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))

theorem stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} [MeasurableSpace W] {M bracket C : ℝ≥0 → W → ℝ}
    (hM : ∀ t, StronglyMeasurable (M t))
    (hbracket : ∀ t, StronglyMeasurable (bracket t))
    (hC : ∀ t, StronglyMeasurable (C t)) (c : ℝ) :
    ∀ t, StronglyMeasurable
      (girsanovComplexDoleansContinuousCoefficient M bracket C c t) := by
  intro t
  unfold girsanovComplexDoleansContinuousCoefficient
  have hdensity : StronglyMeasurable
      (doleansDadeExponential M bracket t) := by
    unfold doleansDadeExponential doleansDadeLog
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((hM t).sub ((hbracket t).const_mul (1 / 2)))
  have hphase : StronglyMeasurable (fun omega ↦
      (((-c * C t omega : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))) := by
    exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
      ((hC t).const_mul (-c))).mul_const Complex.I).add
        stronglyMeasurable_const)
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable hdensity).mul
    (Complex.continuous_exp.comp_stronglyMeasurable hphase)

/-- The complex Doléans weight is a continuous random coefficient times
the unit-modulus Fourier character of the supplied Brownian representative. -/
theorem complexDoleansDadeExponential_combination_factor_continuous_brownian
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega =
      girsanovComplexDoleansContinuousCoefficient M bracket C c t omega *
        Complex.exp (((c * B t omega : ℝ) : ℂ) * Complex.I) := by
  rw [complexDoleansDadeExponential_combination_factor]
  unfold girsanovComplexDoleansContinuousCoefficient
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Pathwise continuity of the martingale, bracket, and cross term makes the
non-Brownian coefficient in the factorization continuous. -/
theorem continuous_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} {M bracket C : ℝ≥0 → W → ℝ}
    (hM : ∀ omega, Continuous (fun t ↦ M t omega))
    (hbracket : ∀ omega, Continuous (fun t ↦ bracket t omega))
    (hC : ∀ omega, Continuous (fun t ↦ C t omega)) (c : ℝ) :
    ∀ omega, Continuous (fun t ↦
      girsanovComplexDoleansContinuousCoefficient M bracket C c t omega) := by
  intro omega
  unfold girsanovComplexDoleansContinuousCoefficient
    doleansDadeExponential doleansDadeLog
  fun_prop

/-- Removing the Brownian Fourier character does not change the modulus of
the complex Doléans weight. -/
theorem norm_girsanovComplexDoleansContinuousCoefficient
    {W : Type*} (M bracket C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    ‖girsanovComplexDoleansContinuousCoefficient
        M bracket C c t omega‖ =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) := by
  unfold girsanovComplexDoleansContinuousCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (doleansDadeExponential_pos M bracket t omega),
    Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

/-- A real-frequency unit-circle character is Lipschitz with the absolute
frequency as constant. -/
theorem lipschitzWith_complexFourierCharacter (c : ℝ) :
    LipschitzWith (Real.toNNReal |c|)
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal |c| (abs_nonneg c), Real.dist_eq, dist_eq_norm]
  calc
    ‖Complex.exp (((c * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)‖ =
        ‖Complex.exp (((c * y : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    _ = ‖Complex.exp (((c * y : ℝ) : ℂ) * Complex.I)‖ *
        ‖Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [norm_mul]
    _ = ‖Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ ‖c * (x - y)‖ := by
      simpa only [mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := c * (x - y)))
    _ = |c| * |x - y| := by
      rw [Real.norm_eq_abs, abs_mul]

/-- Outside the Brownian block-oscillation event, freezing the full complex
Girsanov weight reduces to freezing its continuous coefficient plus the
unit-circle Fourier error. -/
theorem
    norm_complexDoleansWeightedCovariation_commonRefinement_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (M bracket B C X Y : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    {k n : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (alpha R : ℝ) (halpha : 0 ≤ alpha) (hR : 0 ≤ R)
    (delta : ℝ≥0) (hdelta : 0 < delta) {omega : W}
    (hAclose : ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
      uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T (k * n) i) omega -
        girsanovComplexDoleansContinuousCoefficient M bracket C c
          (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ∀ j ∈ Finset.range k,
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T k j) omega‖ ≤ R)
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r ↦
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ‖(∑ i ∈ Finset.range (k * n),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega *
          ((X (uniformPartitionTime T (k * n) (i + 1)) omega -
            X (uniformPartitionTime T (k * n) i) omega) *
          (Y (uniformPartitionTime T (k * n) (i + 1)) omega -
            Y (uniformPartitionTime T (k * n) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range k,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (k * n)
                (uniformPartitionTime T k (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (k * n)
                (uniformPartitionTime T k j) omega : ℂ)‖ ≤
      (alpha + R * |c| * (delta : ℝ)) *
        √(quadraticVariationApprox X T (k * n) omega *
          quadraticVariationApprox Y T (k * n) omega) := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hweight : ∀ i ∈ Finset.range (k * n),
      ‖complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime T k j <
                uniformPartitionTime T (k * n) (i + 1) ∧
              uniformPartitionTime T (k * n) (i + 1) ≤
                uniformPartitionTime T k (j + 1) then
            complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c)
              (uniformPartitionTime T k j) omega
          else 0‖ ≤ alpha + R * |c| * (delta : ℝ) := by
    intro i hi
    have hkn : 0 < k * n := Nat.mul_pos hk hn
    have hi1 : i + 1 ≤ k * n := Finset.mem_range.mp hi
    have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
    have hr0 : 0 < uniformPartitionTime T (k * n) (i + 1) := by
      have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
        intro a b hab
        unfold uniformPartitionTime
        have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast hkn
        gcongr
      have hpos := hstrict (Nat.zero_lt_succ i)
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
        using hpos
    apply norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
      T (uniformPartitionTime T (k * n) (i + 1)) k hk hr0 hrt
    intro j hj hactive
    obtain ⟨r, hr, htime⟩ :=
      uniformPartitionTime_active_block_common_refinement
        T hT hk hn hactive
    have hBclose := hosc j hj r hr
    rw [← htime] at hBclose
    rw [complexDoleansDadeExponential_combination_factor_continuous_brownian,
      complexDoleansDadeExponential_combination_factor_continuous_brownian]
    have hraw := norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
      (girsanovComplexDoleansContinuousCoefficient M bracket C c) B
      (fun x : ℝ ↦ Complex.exp (((c * x : ℝ) : ℂ) * Complex.I))
      (lipschitzWith_complexFourierCharacter c) T omega alpha R 1
      (delta : ℝ) (hAclose i hi j hj hactive) (hAbound j hj)
      (by rw [Complex.norm_exp_ofReal_mul_I]) hBclose
    simpa only [mul_one, Real.coe_toNNReal |c| (abs_nonneg c)] using hraw
  exact norm_complexWeightedQuadraticCovariation_sub_completedBlocks_le
    X Y T (k * n) k
      (fun i omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T (k * n) i) omega)
      (fun j omega ↦ complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (uniformPartitionTime T k j) omega)
      (alpha + R * |c| * (delta : ℝ))
      (add_nonneg halpha (mul_nonneg (mul_nonneg hR (abs_nonneg c))
        delta.coe_nonneg)) omega hweight

/-- The pathwise complex common-refinement estimate promotes to convergence
in measure once the coefficient-freezing error vanishes, the coefficient
and quadratic sums are tight, and the Brownian oscillation event becomes
rare.  This separates the deterministic path analysis from the eventual
diagonal selection. -/
theorem
    tendstoInMeasure_complexDoleansWeightedCovariation_sub_completedBlocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (M bracket B C X Y : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (K N : ℕ → ℕ) (hT : 0 < T) (hK : ∀ r, 0 < K r)
    (hN : ∀ r, 0 < N r)
    (alpha R : ℕ → W → ℝ) (halpha : ∀ r omega, 0 ≤ alpha r omega)
    (hR : ∀ r omega, 0 ≤ R r omega)
    (halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0))
    (hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta)
    (delta : ℕ → ℝ≥0)
    (hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0))
    (hdeltaPos : ∀ r, 0 < delta r)
    (hqtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          √(quadraticVariationApprox X T (K r * N r) omega *
            quadraticVariationApprox Y T (K r * N r) omega)} < eta)
    (hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0))
    (hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r * N r) i) omega -
          girsanovComplexDoleansContinuousCoefficient M bracket C c
            (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega)
    (hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖girsanovComplexDoleansContinuousCoefficient M bracket C c
        (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega) :
    TendstoInMeasure P (fun r omega ↦
      (∑ i ∈ Finset.range (K r * N r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r * N r) i) omega *
          ((X (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            X (uniformPartitionTime T (K r * N r) i) omega) *
          (Y (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            Y (uniformPartitionTime T (K r * N r) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range (K r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r) j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (K r * N r)
                (uniformPartitionTime T (K r) (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (K r * N r)
                (uniformPartitionTime T (K r) j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun r omega ↦
    √(quadraticVariationApprox X T (K r * N r) omega *
      quadraticVariationApprox Y T (K r * N r) omega)
  let small : ℕ → W → ℝ := fun r _ ↦ |c| * (delta r : ℝ)
  let rq : ℕ → W → ℝ := fun r omega ↦ R r omega * q r omega
  let b₁ : ℕ → W → ℝ := fun r omega ↦ alpha r omega * q r omega
  let b₂ : ℕ → W → ℝ := fun r omega ↦ small r omega * rq r omega
  let b : ℕ → W → ℝ := fun r omega ↦ b₁ r omega + b₂ r omega
  have hq_nonneg : ∀ r omega, 0 ≤ q r omega :=
    fun r omega ↦ Real.sqrt_nonneg _
  have hq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ q r omega} < eta := by
    simpa only [q] using hqtight
  have hb₁ : TendstoInMeasure P b₁ atTop (fun _ ↦ 0) := by
    apply halphaZero.of_norm_sub_le_mul_of_eventually_tight
      hq_nonneg hq_tight
    intro r omega
    simp only [b₁, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (halpha r omega), q]
    rw [abs_of_nonneg (mul_nonneg (halpha r omega) (Real.sqrt_nonneg _))]
  have hrq_nonneg : ∀ r omega, 0 ≤ rq r omega := fun r omega ↦
    mul_nonneg (hR r omega) (hq_nonneg r omega)
  have hrq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ rq r omega} < eta := by
    exact eventually_tight_mul_of_nonneg hR hq_nonneg hRtight hq_tight
  have hsmall : TendstoInMeasure P small atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro r
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ ↦ by
        simpa only [small, mul_zero] using
          hdelta.const_mul |c|
  have hsmall_nonneg : ∀ r omega, 0 ≤ small r omega := fun r omega ↦
    mul_nonneg (abs_nonneg c) (delta r).coe_nonneg
  have hb₂ : TendstoInMeasure P b₂ atTop (fun _ ↦ 0) := by
    apply hsmall.of_norm_sub_le_mul_of_eventually_tight
      hrq_nonneg hrq_tight
    intro r omega
    simp only [b₂, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hsmall_nonneg r omega)]
    rw [abs_of_nonneg
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))]
  have hbZero : TendstoInMeasure P b atTop (fun _ ↦ 0) := by
    simpa only [b, zero_add] using hb₁.add_real_noMeas hb₂
  let bad : ℕ → Set W := fun r ↦
    ⋃ j ∈ Finset.range (K r), {omega |
      ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
        Finset.nonempty_range_add_one (fun u ↦
          (B (uniformPartitionTime T (K r) j +
              uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
            B (uniformPartitionTime T (K r) j) omega) ^ 4)}
  have hbadZero : Tendsto (fun r ↦ P.real (bad r)) atTop (nhds 0) := by
    simpa only [bad] using hbad
  have hb_nonneg : ∀ r omega, 0 ≤ b r omega := fun r omega ↦
    add_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))
      (mul_nonneg (hsmall_nonneg r omega) (hrq_nonneg r omega))
  apply hbZero.of_norm_le_nonneg_outside_noMeas hb_nonneg hbadZero
  intro r omega homega
  have hraw :=
    norm_complexDoleansWeightedCovariation_commonRefinement_sub_completedBlocks_le
      M bracket B C X Y c T hT (hK r) (hN r)
      (alpha r omega) (R r omega) (halpha r omega) (hR r omega)
      (delta r) (hdeltaPos r) (hAclose r omega) (hAbound r omega) homega
  calc
    _ ≤ (alpha r omega + R r omega * |c| * (delta r : ℝ)) *
        q r omega := by simpa only [q] using hraw
    _ = b r omega := by
      dsimp only [b, b₁, b₂, small, rq]
      ring

/-- The density maximum used by the early complex-freezing layer.  A
specialized copy is kept here because the more featureful stopped-weight
controls are developed later in the file. -/
@[expose] noncomputable def complexFreezingDensityLeftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦
    doleansDadeExponential M bracket
      (min (uniformPartitionTime T (n + 1) k) T) omega

theorem complexFreezingDensityLeftMax_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    0 ≤ complexFreezingDensityLeftMax M bracket T n omega := by
  exact (doleansDadeExponential_pos M bracket
    (min (uniformPartitionTime T (n + 1) 0) T) omega).le.trans
      (Finset.le_sup' (fun k ↦ doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) k) T) omega)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem GirsanovDensityData.complexFreezingDensityLeftMax_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ n,
        P.real {omega | K ≤
          complexFreezingDensityLeftMax M bracket T n omega} < delta := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : 0 < N := by
    have honeDiv : 0 < 1 / delta := one_div_pos.mpr hdelta
    exact_mod_cast honeDiv.trans hN
  let K : ℝ≥0 := ⟨(N : ℝ), Nat.cast_nonneg N⟩
  have hKpos : (0 : ℝ) < K := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast hNpos
  refine ⟨(K : ℝ), hKpos, fun n ↦ ?_⟩
  let D : ℝ≥0 → W → ℝ := fun t omega ↦
    doleansDadeExponential M bracket (min t T) omega
  let E : Set W := {omega | (K : ℝ) ≤
    complexFreezingDensityLeftMax M bracket T n omega}
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hsample : Martingale (uniformPartitionSample D T (n + 1))
      (uniformPartitionFiltration V T (n + 1)) P :=
    martingale_uniformPartitionSample hDmart T (n + 1)
  have hnonneg : 0 ≤ uniformPartitionSample D T (n + 1) :=
    fun _k omega ↦ (doleansDadeExponential_pos M bracket _ omega).le
  have hraw := maximal_ineq hsample.submartingale hnonneg (ε := K) n
  have hset : {omega |
      (K : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
          (fun k ↦ uniformPartitionSample D T (n + 1) k omega)} = E := by
    rfl
  rw [hset] at hraw
  have hterminal :
      ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P = 1 := by
    have htime : uniformPartitionTime T (n + 1) n ≤ T :=
      (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
        (Nat.le_succ n)).2
    have heq := StochasticCalculus.Martingale.integral_eq hDmart htime
    rw [show D T = girsanovDensity M bracket T by
      funext omega
      simp only [D, girsanovDensity, min_self]] at heq
    simpa only [uniformPartitionSample, D,
      min_eq_left htime, hdata.integral_eq_one] using heq.symm
  have hsetIntegral :
      ∫ omega in E, uniformPartitionSample D T (n + 1) n omega ∂P ≤ 1 := by
    calc
      _ ≤ ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P :=
        setIntegral_le_integral (hsample.integrable n)
          (Filter.Eventually.of_forall fun omega ↦
            (doleansDadeExponential_pos M bracket _ omega).le)
      _ = 1 := hterminal
  have hbound : (K : ℝ≥0∞) * P E ≤ 1 :=
    hraw.trans ((ENNReal.ofReal_le_ofReal hsetIntegral).trans_eq (by norm_num))
  have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at hreal
  change (K : ℝ) * P.real E ≤ 1 at hreal
  have hKdelta : 1 < (K : ℝ) * delta := by
    apply (div_lt_iff₀ hdelta).mp
    change 1 / delta < (N : ℝ)
    exact hN
  have htail : P.real E < delta := by
    by_contra hnot
    have hdeltaLe : delta ≤ P.real E := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hdeltaLe
      (show 0 ≤ (K : ℝ) by positivity)
    nlinarith
  simpa only [E] using htail

/-- Girsanov density data supplies the coefficient tightness in the complex
freezing theorem.  A master sequence of inner counts is sampled along the
polynomial Brownian scale, so the pathwise coefficient modulus and the
Brownian fourth-moment estimate share one cofinal grid. -/
theorem
    GirsanovDensityData.tendstoInMeasure_complexDoleansWeightedCovariation_polynomial
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C X Y : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (hqtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          √(quadraticVariationApprox X T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega *
            quadraticVariationApprox Y T
              (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega)} < eta) :
    TendstoInMeasure P (fun r omega ↦
      let K := (r + 1) ^ 5
      let N := n (K - 1) + 1
      (∑ i ∈ Finset.range (K * N),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K * N) i) omega *
          ((X (uniformPartitionTime T (K * N) (i + 1)) omega -
            X (uniformPartitionTime T (K * N) i) omega) *
          (Y (uniformPartitionTime T (K * N) (i + 1)) omega -
            Y (uniformPartitionTime T (K * N) i) omega) : ℂ)) -
      ∑ j ∈ Finset.range K,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T K j) omega *
          (quadraticCovariationBeforeStopApprox X Y T (K * N)
                (uniformPartitionTime T K (j + 1)) omega -
              quadraticCovariationBeforeStopApprox X Y T (K * N)
                (uniformPartitionTime T K j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let s : ℕ → ℕ := fun r ↦ K r - 1
  let N : ℕ → ℕ := fun r ↦ n (s r) + 1
  let A : ℝ≥0 → W → ℂ :=
    girsanovComplexDoleansContinuousCoefficient M bracket C c
  let alpha : ℕ → W → ℝ := fun r ↦
    commonRefinementMaxComplexStepError A T (s r) (n (s r))
  let e : ℝ := Real.exp (c ^ 2 * (T : ℝ) / 2)
  let R : ℕ → W → ℝ := fun r omega ↦
    e * complexFreezingDensityLeftMax M bracket T (s r) omega
  let delta : ℕ → ℝ≥0 := fun r ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹
  have hKpos : ∀ r, 0 < K r := fun r ↦ by
    dsimp only [K]
    positivity
  have hNpos : ∀ r, 0 < N r := fun r ↦ by
    dsimp only [N]
    positivity
  have hsadd (r : ℕ) : s r + 1 = K r := by
    dsimp only [s]
    exact Nat.sub_add_cancel (hKpos r)
  have hsTop : Tendsto s atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba ↦ ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have halt : a < K a := by
      dsimp only [K]
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hAmeas : ∀ t, StronglyMeasurable (A t) := by
    intro t
    apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    · intro u
      exact (hdata.adapted_martingale u).mono (V.le u)
    · intro u
      exact (hdata.adapted_bracket u).mono (V.le u)
    · exact hCmeas
  have hAcont : ∀ omega, Continuous (fun t ↦ A t omega) := by
    exact continuous_girsanovComplexDoleansContinuousCoefficient
      hdata.continuous_martingale_path
      (fun omega ↦ (hdata.continuous_monotone_bracket omega).1)
      hCcont c
  have halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0) := by
    have hbase := commonRefinementMaxComplexStepError_tendstoInMeasure_zero
      (P := P) (A := A) hAmeas T hT hAcont n
    change TendstoInMeasure P
      ((fun k ↦ commonRefinementMaxComplexStepError A T k (n k)) ∘ s)
      atTop (fun _ ↦ 0)
    exact hbase.comp hsTop
  have halpha : ∀ r omega, 0 ≤ alpha r omega := fun r omega ↦
    commonRefinementMaxComplexStepError_nonneg A T (s r) (n (s r)) omega
  have hRnonneg : ∀ r omega, 0 ≤ R r omega := fun r omega ↦ by
    exact mul_nonneg (Real.exp_pos _).le
      (complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega)
  have hdensityTight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega} <
            eta := by
    intro eta heta
    obtain ⟨D, hD, htail⟩ :=
      hdata.complexFreezingDensityLeftMax_tight eta heta
    exact ⟨D, hD, Filter.Eventually.of_forall fun r ↦ htail (s r)⟩
  have hRtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ R r omega} < eta := by
    exact eventually_tight_const_mul_of_nonneg e (Real.exp_pos _).le
      (fun r omega ↦ complexFreezingDensityLeftMax_nonneg
        M bracket T (s r) omega) hdensityTight
  have hdelta : Tendsto (fun r ↦ (delta r : ℝ)) atTop (nhds 0) := by
    have hinv : Tendsto (fun r : ℕ ↦
        ((r + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hinv
    change Tendsto
      (NNReal.toReal ∘ fun r : ℕ ↦ ((r + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0)
    exact hcoe
  have hdeltaPos : ∀ r, 0 < delta r := fun r ↦ by
    dsimp only [delta]
    positivity
  have hbad : Tendsto (fun r ↦ P.real
      (⋃ j ∈ Finset.range (K r), {omega |
        ((delta r : ℝ) ^ 4) ≤ (Finset.range (N r + 1)).sup'
          Finset.nonempty_range_add_one (fun u ↦
            (B (uniformPartitionTime T (K r) j +
                uniformPartitionTime (T / (K r : ℝ≥0)) (N r) u) omega -
              B (uniformPartitionTime T (K r) j) omega) ^ 4)}))
      atTop (nhds 0) := by
    simpa only [K, N, s, delta] using
      tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
        hB hsm T N hNpos
  have hAclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖A (uniformPartitionTime T (K r * N r) i) omega -
          A (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega := by
    intro r omega i hi j hj hactive
    have hcounts : (s r + 1) * (n (s r) + 1) = K r * N r := by
      rw [hsadd]
    have hi' : i ∈ Finset.range ((s r + 1) * (n (s r) + 1)) := by
      simpa only [hcounts] using hi
    have hle :
        ‖A (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) i) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              A (uniformPartitionTime T (s r + 1) l) omega else 0‖ ≤
          commonRefinementMaxComplexStepError A T (s r) (n (s r)) omega := by
      unfold commonRefinementMaxComplexStepError
      exact (le_refl _).trans (Finset.le_sup' (fun u ↦
        ‖A (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) u) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              A (uniformPartitionTime T (s r + 1) l) omega else 0‖) hi')
    have hj' : j ∈ Finset.range (s r + 1) := by
      simpa only [hsadd] using hj
    have hactive' : uniformPartitionTime T (s r + 1) j <
          uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
        uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
          uniformPartitionTime T (s r + 1) (j + 1) := by
      simpa only [hsadd, hcounts] using hactive
    have hsum := uniformPartition_rightEndpoint_complexStep_sum_eq
      T (uniformPartitionTime T
        ((s r + 1) * (n (s r) + 1)) (i + 1)) (s r + 1)
      hT (by positivity)
      (fun l ↦ A (uniformPartitionTime T (s r + 1) l) omega)
      hj' hactive'
    rw [hsum] at hle
    change ‖A (uniformPartitionTime T (K r * N r) i) omega -
        A (uniformPartitionTime T (K r) j) omega‖ ≤
      commonRefinementMaxComplexStepError A T (s r) (n (s r)) omega
    simpa only [hcounts, hsadd] using hle
  have hAbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖A (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega := by
    intro r omega j hj
    have hjle : j ≤ K r := (Finset.mem_range.mp hj).le
    have ht := (uniformPartitionTime_mem_Icc_of_le T (hKpos r) hjle).2
    have hdensity : doleansDadeExponential M bracket
          (uniformPartitionTime T (K r) j) omega ≤
        complexFreezingDensityLeftMax M bracket T (s r) omega := by
      have hj' : j ∈ Finset.range (s r + 1) := by
        simpa only [hsadd] using hj
      have hmax := Finset.le_sup' (fun u ↦
        doleansDadeExponential M bracket
          (min (uniformPartitionTime T (s r + 1) u) T) omega) hj'
      simpa only [complexFreezingDensityLeftMax, hsadd, min_eq_left ht]
        using hmax
    have hexp : Real.exp
          (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤ e := by
      apply Real.exp_le_exp.mpr
      gcongr
    rw [norm_girsanovComplexDoleansContinuousCoefficient]
    calc
      doleansDadeExponential M bracket
            (uniformPartitionTime T (K r) j) omega *
          Real.exp (c ^ 2 * (uniformPartitionTime T (K r) j : ℝ) / 2) ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega * e :=
        mul_le_mul hdensity hexp (Real.exp_pos _).le
          (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
      _ = e * complexFreezingDensityLeftMax M bracket T (s r) omega :=
        mul_comm _ _
  apply tendstoInMeasure_complexDoleansWeightedCovariation_sub_completedBlocks
    M bracket B C X Y c T K N hT hKpos hNpos alpha R halpha hRnonneg
      halphaZero hRtight delta hdelta hdeltaPos
  · simpa only [K, N, s] using hqtight
  · exact hbad
  · exact hAclose
  · exact hAbound

/-- The complex Fourier exponential has the Novikov density as its random
modulus, up to the deterministic Gaussian normalization. -/
theorem norm_complexDoleansDadeExponential_combination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (t : ℝ≥0) (omega : W) :
    ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) t omega‖ =
      doleansDadeExponential M bracket t omega *
        Real.exp (c ^ 2 * (t : ℝ) / 2) := by
  rw [complexDoleansDadeExponential_combination_factor, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (doleansDadeExponential_pos M bracket t omega),
    Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
    mul_one, neg_zero, zero_add]

end StochasticCalculus
