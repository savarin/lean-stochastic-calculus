/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.NovikovCondition

/-!
# Novikov's theorem

Kazamaki's condition, uniform integrability from uniform `Lᵖ` bounds, the
scaling trick for the Doléans--Dade exponential, and the conclusion: under
Novikov's condition the stopped stochastic exponential is a uniformly
integrable martingale with expectation one on `[0, T]`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The finite-horizon form of Kazamaki's stopped exponential condition.  It
records one common integrable bound for `exp (M_τ / 2)` over every stopping
time `τ` bounded by the horizon. -/
def KazamakiCondition
    {W : Type*} [MeasurableSpace W]
    (M : ℝ≥0 → W → ℝ) (𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (P : Measure W) (T : ℝ≥0) : Prop :=
  ∃ C : ℝ, ∀ (tau : W → WithTop ℝ≥0), IsStoppingTime 𝒱 tau →
    (∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) →
      Integrable (fun omega => Real.exp (stoppedValue M tau omega / 2)) P ∧
        (∫ omega, Real.exp (stoppedValue M tau omega / 2) ∂P) ≤ C

/-- Novikov's terminal half-bracket moment supplies the exact finite-horizon
Kazamaki condition, with the square root of that moment as a common bound. -/
theorem NovikovCondition.kazamakiCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hN : NovikovCondition bracket P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    KazamakiCondition M 𝒱 P T := by
  refine ⟨Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P), ?_⟩
  intro tau htau hbound
  exact hN.integrable_stoppedValue_exp_half hlocalQV hMcont hMadapt
    hbracket hbracketPath hMzero hbracketZero htau hbound

/-- The pointwise factorization used in Kazamaki's higher-moment argument. -/
theorem kazamakiHolder_factor
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (tau : W → WithTop ℝ≥0) (omega : W)
    (q r : ℝ) (hq : 0 ≤ q) (hr : 0 < r) :
    stoppedValue (doleansDadeExponential M bracket) tau omega ^ q =
      stoppedValue (doleansDadeExponential
        (fun t omega => Real.sqrt (q * r) * M t omega)
        (fun t omega => (q * r) * bracket t omega)) tau omega ^ (1 / r) *
          Real.exp ((q - Real.sqrt (q / r)) * stoppedValue M tau omega) := by
  unfold stoppedValue doleansDadeExponential doleansDadeLog
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  have hqr : 0 ≤ q * r := mul_nonneg hq hr.le
  have hsqrtSq : Real.sqrt (q * r) ^ 2 = q * r := Real.sq_sqrt hqr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsqrtDiv : Real.sqrt (q / r) = Real.sqrt (q * r) / r := by
    rw [Real.sqrt_div hq, Real.sqrt_mul hq]
    have hsr : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    field_simp [hsr, hrne]
    rw [Real.sq_sqrt hr.le]
  rw [hsqrtDiv]
  field_simp
  nlinarith

/-- On a probability space, a uniformly bounded `L^q` family for any
`q > 1` is uniformly integrable in `L^1`. -/
theorem uniformIntegrable_one_of_uniform_eLpNorm_gt_one
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] {f : I → W → ℝ}
    (q : ℝ≥0∞) (hq : 1 < q) (hqtop : q ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) q P ≤ C) :
    UniformIntegrable f 1 P := by
  have hqReal : 1 < q.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hqtop).2 hq
  let a : ℝ := 1 - 1 / q.toReal
  have ha : 0 < a := by
    dsimp only [a]
    rw [sub_pos, div_lt_one (by positivity)]
    exact hqReal
  refine ⟨hf, ?_, ?_⟩
  · intro ε hε
    let d : ℝ := (ε / ((C : ℝ) + 1)) ^ (1 / a)
    have hbase : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
    have hd : 0 < d := Real.rpow_pos_of_pos hbase _
    refine ⟨d, hd, fun i s hs hPs ↦ ?_⟩
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    calc
      eLpNorm (f i) 1 (P.restrict s) ≤
          eLpNorm (f i) q (P.restrict s) *
            (P.restrict s) Set.univ ^ a := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
            (f := f i) hq.le ((hf i).mono_measure Measure.restrict_le_self) using 1
        dsimp only [a]
        rw [one_div]
        norm_num
      _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal d) ^ a := by
        simp only [Measure.restrict_apply_univ]
        exact mul_le_mul'
          ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i))
          (ENNReal.rpow_le_rpow hPs ha.le)
      _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_pos hd]
        have hda : d ^ a = ε / ((C : ℝ) + 1) := by
          dsimp only [d]
          rw [show 1 / a = a⁻¹ by rw [one_div],
            Real.rpow_inv_rpow hbase.le ha.ne']
        rw [hda, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (C.coe_nonneg)]
        apply ENNReal.ofReal_le_ofReal
        calc
          (C : ℝ) * (ε / ((C : ℝ) + 1)) ≤
              ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hbase.le
          _ = ε := by field_simp
  · refine ⟨C, fun i ↦ ?_⟩
    exact (eLpNorm_le_eLpNorm_of_exponent_le hq.le (hf i)).trans (hC i)

theorem integrable_rpow_doleansDade_and_integral_le_kazamaki
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (q r : ℝ) (hq : 1 < q) (hr : 1 < r)
    (hMMeas : AEStronglyMeasurable (stoppedValue M tau) P)
    (hscaledInt : Integrable (stoppedValue (doleansDadeExponential
      (fun t omega => Real.sqrt (q * r) * M t omega)
      (fun t omega => (q * r) * bracket t omega)) tau) P)
    (hexpInt : Integrable (fun omega => Real.exp
      ((q - Real.sqrt (q / r)) * (r / (r - 1)) * stoppedValue M tau omega)) P) :
    Integrable (fun omega =>
      stoppedValue (doleansDadeExponential M bracket) tau omega ^ q) P ∧
      (∫ omega, stoppedValue (doleansDadeExponential M bracket) tau omega ^ q ∂P) ≤
        (∫ omega, stoppedValue (doleansDadeExponential
          (fun t omega => Real.sqrt (q * r) * M t omega)
          (fun t omega => (q * r) * bracket t omega)) tau omega ∂P) ^ (1 / r) *
        (∫ omega, Real.exp
          ((q - Real.sqrt (q / r)) * (r / (r - 1)) *
            stoppedValue M tau omega) ∂P) ^ (1 / (r / (r - 1))) := by
  let s : ℝ := r / (r - 1)
  let X : W → ℝ := stoppedValue (doleansDadeExponential
    (fun t omega => Real.sqrt (q * r) * M t omega)
    (fun t omega => (q * r) * bracket t omega)) tau
  let f : W → ℝ := fun omega => X omega ^ (1 / r)
  let g : W → ℝ := fun omega =>
    Real.exp ((q - Real.sqrt (q / r)) * stoppedValue M tau omega)
  have hrs : r.HolderConjugate s := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hr, ?_⟩
    dsimp only [s]
    field_simp
    ring
  let _ : (ENNReal.ofReal r).HolderTriple (ENNReal.ofReal s) 1 :=
    hrs.ennrealOfReal
  have hXpos (omega : W) : 0 < X omega := by
    unfold X stoppedValue doleansDadeExponential
    exact Real.exp_pos _
  have hfMeas : AEStronglyMeasurable f P :=
    (hscaledInt.aestronglyMeasurable.aemeasurable.pow_const
      (1 / r)).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g P := by
    exact Real.continuous_exp.comp_aestronglyMeasurable
      (hMMeas.const_mul (q - Real.sqrt (q / r)))
  have hfMem : MemLp f (ENNReal.ofReal r) P := by
    apply (memLp_norm_rpow_iff (p := ENNReal.ofReal r)
      (q := ENNReal.ofReal r) hfMeas (by positivity) (by finiteness)).mp
    convert memLp_one_iff_integrable.mpr hscaledInt using 1
    · funext omega
      dsimp only [f]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hXpos omega).le _),
        ENNReal.toReal_ofReal (lt_trans zero_lt_one hr).le,
        ← Real.rpow_mul (hXpos omega).le]
      have hrne : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
      rw [show (1 / r) * r = 1 by field_simp, Real.rpow_one]
    · rw [ENNReal.div_self (by positivity) (by finiteness)]
  have hgMem : MemLp g (ENNReal.ofReal s) P := by
    apply (memLp_norm_rpow_iff (p := ENNReal.ofReal s)
      (q := ENNReal.ofReal s) hgMeas (by positivity) (by finiteness)).mp
    convert memLp_one_iff_integrable.mpr hexpInt using 1
    · funext omega
      dsimp only [g, s]
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ENNReal.toReal_ofReal hrs.symm.nonneg,
        ← Real.exp_mul]
      congr 1
      ring
    · rw [ENNReal.div_self (by positivity) (by finiteness)]
  have hproductInt : Integrable (fun omega => f omega * g omega) P :=
    hfMem.integrable_mul hgMem
  have hfr (omega : W) : f omega ^ r = X omega := by
    dsimp only [f]
    rw [← Real.rpow_mul (hXpos omega).le]
    have hrne : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
    rw [show (1 / r) * r = 1 by field_simp, Real.rpow_one]
  have hgs (omega : W) : g omega ^ s = Real.exp
      ((q - Real.sqrt (q / r)) * (r / (r - 1)) * stoppedValue M tau omega) := by
    dsimp only [g, s]
    rw [← Real.exp_mul]
    congr 1
    ring
  have hfactor : (fun omega =>
      stoppedValue (doleansDadeExponential M bracket) tau omega ^ q) =
      fun omega => f omega * g omega := by
    funext omega
    exact kazamakiHolder_factor M bracket tau omega q r
      (lt_trans zero_lt_one hq).le (lt_trans zero_lt_one hr)
  refine ⟨hfactor ▸ hproductInt, ?_⟩
  rw [hfactor]
  calc
    (∫ omega, f omega * g omega ∂P) ≤
        (∫ omega, f omega ^ r ∂P) ^ (1 / r) *
          (∫ omega, g omega ^ s ∂P) ^ (1 / s) := by
      exact integral_mul_le_Lp_mul_Lq_of_nonneg hrs
        (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hXpos omega).le _)
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
        hfMem hgMem
    _ = (∫ omega, stoppedValue (doleansDadeExponential
          (fun t omega => Real.sqrt (q * r) * M t omega)
          (fun t omega => (q * r) * bracket t omega)) tau omega ∂P) ^ (1 / r) *
        (∫ omega, Real.exp
          ((q - Real.sqrt (q / r)) * (r / (r - 1)) *
            stoppedValue M tau omega) ∂P) ^ (1 / (r / (r - 1))) := by
      congr 2
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall hfr
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall hgs

/-- A stopped exponential bound controls every smaller nonnegative
exponential coefficient, with only an additive constant. -/
theorem integrable_exp_mul_stoppedValue_of_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {M : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hMMeas : AEStronglyMeasurable (stoppedValue M tau) P)
    (k c C : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ c)
    (hbound : Integrable
        (fun omega => Real.exp (c * stoppedValue M tau omega)) P ∧
      (∫ omega, Real.exp (c * stoppedValue M tau omega) ∂P) ≤ C) :
    Integrable (fun omega => Real.exp (k * stoppedValue M tau omega)) P ∧
      (∫ omega, Real.exp (k * stoppedValue M tau omega) ∂P) ≤ 1 + C := by
  have hmeas : AEStronglyMeasurable
      (fun omega => Real.exp (k * stoppedValue M tau omega)) P :=
    Real.continuous_exp.comp_aestronglyMeasurable (hMMeas.const_mul k)
  have hpoint (omega : W) : Real.exp (k * stoppedValue M tau omega) ≤
      1 + Real.exp (c * stoppedValue M tau omega) := by
    by_cases hx : stoppedValue M tau omega < 0
    · calc
        Real.exp (k * stoppedValue M tau omega) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hk0 hx.le)
        _ ≤ 1 + Real.exp (c * stoppedValue M tau omega) := by
          linarith [Real.exp_pos (c * stoppedValue M tau omega)]
    · have hx0 : 0 ≤ stoppedValue M tau omega := le_of_not_gt hx
      calc
        Real.exp (k * stoppedValue M tau omega) ≤
            Real.exp (c * stoppedValue M tau omega) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right hk hx0
        _ ≤ 1 + Real.exp (c * stoppedValue M tau omega) :=
          le_add_of_nonneg_left zero_le_one
  have hsumInt : Integrable
      (fun omega => 1 + Real.exp (c * stoppedValue M tau omega)) P :=
    (integrable_const 1).add hbound.1
  have hint : Integrable
      (fun omega => Real.exp (k * stoppedValue M tau omega)) P :=
    hsumInt.mono' hmeas (Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint omega)
  refine ⟨hint, ?_⟩
  calc
    (∫ omega, Real.exp (k * stoppedValue M tau omega) ∂P) ≤
        ∫ omega, 1 + Real.exp (c * stoppedValue M tau omega) ∂P :=
      integral_mono hint hsumInt hpoint
    _ = 1 + ∫ omega, Real.exp (c * stoppedValue M tau omega) ∂P := by
      rw [integral_add (integrable_const 1) hbound.1, integral_const,
        Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ 1 + C := add_le_add le_rfl hbound.2

/-- A uniform integral bound on a common real power `q > 1` gives `L^1`
uniform integrability for a nonnegative family. -/
theorem uniformIntegrable_one_of_uniform_integral_rpow
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] {f : I → W → ℝ}
    (q : ℝ) (hq : 1 < q)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hnonneg : ∀ i omega, 0 ≤ f i omega)
    (hint : ∀ i, Integrable (fun omega => f i omega ^ q) P)
    (C : ℝ)
    (hC : ∀ i, (∫ omega, f i omega ^ q ∂P) ≤ C) :
    UniformIntegrable f 1 P := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hmem (i : I) : MemLp (f i) (ENNReal.ofReal q) P := by
    apply (memLp_norm_rpow_iff (p := ENNReal.ofReal q)
      (q := ENNReal.ofReal q) (hf i) (by positivity) (by finiteness)).mp
    convert memLp_one_iff_integrable.mpr (hint i) using 1
    · funext omega
      rw [Real.norm_of_nonneg (hnonneg i omega), ENNReal.toReal_ofReal hq0.le]
    · rw [ENNReal.div_self (by positivity) (by finiteness)]
  let D : ℝ≥0 := (ENNReal.ofReal (C ^ (1 / q))).toNNReal
  have hD (i : I) : eLpNorm (f i) (ENNReal.ofReal q) P ≤ D := by
    rw [(hmem i).eLpNorm_eq_integral_rpow_norm (by positivity) (by finiteness)]
    have hintegral0 : 0 ≤ ∫ omega, ‖f i omega‖ ^ (ENNReal.ofReal q).toReal ∂P :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hrpow :
        (∫ omega, ‖f i omega‖ ^ (ENNReal.ofReal q).toReal ∂P) ^
            (ENNReal.ofReal q).toReal⁻¹ ≤ C ^ (1 / q) := by
      rw [ENNReal.toReal_ofReal hq0.le]
      have hbase : (∫ omega, ‖f i omega‖ ^ q ∂P) ≤ C := by
        simpa only [Real.norm_of_nonneg (hnonneg i _)] using hC i
      simpa only [one_div] using Real.rpow_le_rpow
        (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hbase
        (inv_nonneg.2 hq0.le)
    rw [show (D : ℝ≥0∞) = ENNReal.ofReal (C ^ (1 / q)) by
      exact (ENNReal.coe_toNNReal (by finiteness)).symm]
    exact ENNReal.ofReal_le_ofReal hrpow
  exact uniformIntegrable_one_of_uniform_eLpNorm_gt_one
    (ENNReal.ofReal q) (by simpa using hq) (by finiteness) hf D hD

/-- A stopped exponential bound at a coefficient strong enough for the
chosen Hölder pair gives uniform integrability of all bounded stopped values
of the Doléans exponential. -/
theorem uniformIntegrable_stoppedValue_doleansDade_of_holder
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (c C q r : ℝ) (hq : 1 < q) (hr : 1 < r)
    (hk0 : 0 ≤ (q - Real.sqrt (q / r)) * (r / (r - 1)))
    (hkc : (q - Real.sqrt (q / r)) * (r / (r - 1)) ≤ c)
    (tau : I → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (htauBound : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0))
    (hexpBound : ∀ i,
      Integrable (fun omega => Real.exp (c * stoppedValue M (tau i) omega)) P ∧
        (∫ omega, Real.exp (c * stoppedValue M (tau i) omega) ∂P) ≤ C) :
    UniformIntegrable
      (fun i => stoppedValue (doleansDadeExponential M bracket) (tau i)) 1 P := by
  let s : ℝ := r / (r - 1)
  have hrs : r.HolderConjugate s := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hr, ?_⟩
    dsimp only [s]
    field_simp
    ring
  have hq0 : 0 ≤ q := (lt_trans zero_lt_one hq).le
  have hr0 : 0 ≤ r := (lt_trans zero_lt_one hr).le
  have hqr0 : 0 ≤ q * r := mul_nonneg hq0 hr0
  have hMprog := hMadapt.isStronglyProgressive_of_continuous hMcont
  have hEadapt : StronglyAdapted 𝒱 (doleansDadeExponential M bracket) :=
    stronglyAdapted_doleansDadeExponential hMadapt hbracket
  have hEcont (omega : W) : Continuous
      (fun t => doleansDadeExponential M bracket t omega) :=
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  let lambda : ℝ := Real.sqrt (q * r)
  have hscaledLocal : IsContinuousLocalMartingale
      (doleansDadeExponential
        (fun t omega => lambda * M t omega)
        (fun t omega => (q * r) * bracket t omega)) 𝒱 P := by
    simpa only [lambda, Real.sq_sqrt hqr0] using
      isContinuousLocalMartingale_doleansDadeExponential_const_mul_of_localQuadraticVariation
        hlocalQV hMcont hbracket hbracketPath hMzero hbracketZero lambda
  have hscaledMAdapt : StronglyAdapted 𝒱
      (fun t omega => lambda * M t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hMadapt t)
  have hscaledBracketAdapt : StronglyAdapted 𝒱
      (fun t omega => (q * r) * bracket t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hbracket t)
  have hscaledAdapt : StronglyAdapted 𝒱
      (doleansDadeExponential
        (fun t omega => lambda * M t omega)
        (fun t omega => (q * r) * bracket t omega)) :=
    stronglyAdapted_doleansDadeExponential hscaledMAdapt hscaledBracketAdapt
  have hscaledCont (omega : W) : Continuous (fun t =>
      doleansDadeExponential
        (fun t omega => lambda * M t omega)
        (fun t omega => (q * r) * bracket t omega) t omega) :=
    continuous_doleansDadeExponential _ _ omega
      (continuous_const.mul (hMcont omega))
      (continuous_const.mul (hbracketPath omega).1)
  have hscaledZero : doleansDadeExponential
      (fun t omega => lambda * M t omega)
      (fun t omega => (q * r) * bracket t omega) 0 = fun _ => 1 := by
    funext omega
    exact doleansDadeExponential_zero _ _ omega
      (by rw [hMzero omega, mul_zero])
      (by rw [hbracketZero omega, mul_zero])
  have hscaledZeroInt : Integrable (doleansDadeExponential
      (fun t omega => lambda * M t omega)
      (fun t omega => (q * r) * bracket t omega) 0) P := by
    rw [hscaledZero]
    exact integrable_const 1
  have hYMeas (i : I) : AEStronglyMeasurable
      (stoppedValue (doleansDadeExponential M bracket) (tau i)) P :=
    ((stronglyMeasurable_stoppedValue_of_le
      (hEadapt.isStronglyProgressive_of_continuous hEcont)
      (htau i) (htauBound i)).mono (𝒱.le T)).aestronglyMeasurable
  have hYnonneg (i : I) (omega : W) : 0 ≤
      stoppedValue (doleansDadeExponential M bracket) (tau i) omega := by
    unfold stoppedValue doleansDadeExponential
    exact Real.exp_nonneg _
  have hmoment (i : I) := by
    have hMstopMeas : AEStronglyMeasurable (stoppedValue M (tau i)) P :=
      ((stronglyMeasurable_stoppedValue_of_le hMprog
        (htau i) (htauBound i)).mono (𝒱.le T)).aestronglyMeasurable
    have hsmallExp := integrable_exp_mul_stoppedValue_of_bound hMstopMeas
      ((q - Real.sqrt (q / r)) * (r / (r - 1))) c C hk0 hkc (hexpBound i)
    have hscaledBound :=
      hscaledLocal.1.integrable_stoppedValue_and_integral_le_zero_of_nonneg
        hscaledAdapt hscaledCont (fun _ _ => (Real.exp_pos _).le)
        hscaledZeroInt (htau i) T (htauBound i)
    exact integrable_rpow_doleansDade_and_integral_le_kazamaki
      M bracket (tau i) q r hq hr hMstopMeas hscaledBound.1 hsmallExp.1
  have hmomentBound (i : I) :
      (∫ omega,
        stoppedValue (doleansDadeExponential M bracket) (tau i) omega ^ q ∂P) ≤
        (1 + C) ^ (1 / s) := by
    have hMstopMeas : AEStronglyMeasurable (stoppedValue M (tau i)) P :=
      ((stronglyMeasurable_stoppedValue_of_le hMprog
        (htau i) (htauBound i)).mono (𝒱.le T)).aestronglyMeasurable
    have hsmallExp := integrable_exp_mul_stoppedValue_of_bound hMstopMeas
      ((q - Real.sqrt (q / r)) * (r / (r - 1))) c C hk0 hkc (hexpBound i)
    have hscaledBound :=
      hscaledLocal.1.integrable_stoppedValue_and_integral_le_zero_of_nonneg
        hscaledAdapt hscaledCont (fun _ _ => (Real.exp_pos _).le)
        hscaledZeroInt (htau i) T (htauBound i)
    have hscaledLeOne : (∫ omega, stoppedValue (doleansDadeExponential
        (fun t omega => lambda * M t omega)
        (fun t omega => (q * r) * bracket t omega)) (tau i) omega ∂P) ≤ 1 := by
      simpa only [hscaledZero, integral_const, Measure.real, measure_univ,
        ENNReal.toReal_one, one_smul] using hscaledBound.2
    have hscaledNonneg : 0 ≤ (∫ omega, stoppedValue (doleansDadeExponential
        (fun t omega => lambda * M t omega)
        (fun t omega => (q * r) * bracket t omega)) (tau i) omega ∂P) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hsmallNonneg : 0 ≤ ∫ omega, Real.exp
        ((q - Real.sqrt (q / r)) * (r / (r - 1)) *
          stoppedValue M (tau i) omega) ∂P :=
      integral_nonneg fun _ => Real.exp_nonneg _
    calc
      (∫ omega,
          stoppedValue (doleansDadeExponential M bracket) (tau i) omega ^ q ∂P) ≤
          (∫ omega, stoppedValue (doleansDadeExponential
            (fun t omega => Real.sqrt (q * r) * M t omega)
            (fun t omega => (q * r) * bracket t omega)) (tau i) omega ∂P) ^
              (1 / r) *
            (∫ omega, Real.exp
              ((q - Real.sqrt (q / r)) * (r / (r - 1)) *
                stoppedValue M (tau i) omega) ∂P) ^ (1 / s) := hmoment i |>.2
      _ ≤ 1 ^ (1 / r) * (1 + C) ^ (1 / s) := by
        apply mul_le_mul
        · apply Real.rpow_le_rpow hscaledNonneg hscaledLeOne
          exact hrs.one_div_nonneg
        · apply Real.rpow_le_rpow hsmallNonneg hsmallExp.2
          exact hrs.symm.one_div_nonneg
        · exact Real.rpow_nonneg hsmallNonneg _
        · positivity
      _ = (1 + C) ^ (1 / s) := by simp
  exact uniformIntegrable_one_of_uniform_integral_rpow q hq hYMeas hYnonneg
    (fun i => (hmoment i).1) ((1 + C) ^ (1 / s)) hmomentBound

/-- Explicit Hölder parameters that fit the strict Kazamaki scaling range. -/
lemma exists_kazamakiHolder_parameters (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ q r : ℝ, 1 < q ∧ 1 < r ∧
      0 ≤ (q - Real.sqrt (q / r)) * (r / (r - 1)) ∧
      (q - Real.sqrt (q / r)) * (r / (r - 1)) ≤ 1 / (2 * a) := by
  let d : ℝ := 1 - a
  let b : ℝ := 1 + d ^ 4
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hb1 : 1 < b := by
    dsimp [b]
    exact lt_add_of_pos_right 1 (pow_pos hd0 4)
  have hq1 : 1 < b ^ 2 := by nlinarith [sq_nonneg (b - 1)]
  have ha_sq_pos : 0 < a ^ 2 := sq_pos_of_pos ha0
  have ha_sq_lt_one : a ^ 2 < 1 := by nlinarith [sq_nonneg (a - 1)]
  have hr1 : 1 < 1 / a ^ 2 :=
    (one_lt_div₀ ha_sq_pos).2 ha_sq_lt_one
  have hquot : b ^ 2 / (1 / a ^ 2) = (a * b) ^ 2 := by
    field_simp
  have hsqrt : Real.sqrt (b ^ 2 / (1 / a ^ 2)) = a * b := by
    rw [hquot, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos ha0 (lt_trans zero_lt_one hb1))]
  refine ⟨b ^ 2, 1 / a ^ 2, hq1, hr1, ?_, ?_⟩
  · rw [hsqrt]
    have hba : 0 < b - a := by linarith
    have hfirst : 0 ≤ b ^ 2 - a * b := by
      rw [show b ^ 2 - a * b = b * (b - a) by ring]
      exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hb1)) hba.le
    exact mul_nonneg hfirst
      (div_nonneg (by linarith) (sub_nonneg.2 hr1.le))
  · rw [hsqrt]
    have ha_ne : a ≠ 0 := ne_of_gt ha0
    have had_ne : 1 - a ≠ 0 := ne_of_gt (by linarith : 0 < 1 - a)
    have hsum_ne : 1 + a ≠ 0 := ne_of_gt (by linarith : 0 < 1 + a)
    have hone_sub_sq_ne : 1 - a ^ 2 ≠ 0 := ne_of_gt (by linarith)
    have hfrac : (1 / a ^ 2) / (1 / a ^ 2 - 1) = 1 / (1 - a ^ 2) := by
      field_simp
    have hnumfac : b ^ 2 - a * b = b * d * (1 + d ^ 3) := by
      dsimp [b, d]
      ring
    have hdenfac : 1 - a ^ 2 = d * (1 + a) := by
      dsimp [d]
      ring
    have hk_eq :
        (b ^ 2 - a * b) * ((1 / a ^ 2) / (1 / a ^ 2 - 1)) =
          b * (1 + d ^ 3) / (1 + a) := by
      rw [hfrac, hnumfac, hdenfac]
      field_simp
    rw [hk_eq]
    apply (div_le_div_iff₀ (by linarith : 0 < 1 + a) (by positivity : 0 < 2 * a)).2
    have hd4_le_hd3 : d ^ 4 ≤ d ^ 3 := by
      calc
        d ^ 4 = d ^ 3 * d := by ring
        _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd1 (pow_nonneg hd0.le 3)
        _ = d ^ 3 := by ring
    have hd4_le_one : d ^ 4 ≤ 1 := by
      simpa using pow_le_pow_left₀ hd0.le hd1 4
    have hd7_le_hd3 : d ^ 7 ≤ d ^ 3 := by
      calc
        d ^ 7 = d ^ 3 * d ^ 4 := by ring
        _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd4_le_one (pow_nonneg hd0.le 3)
        _ = d ^ 3 := by ring
    have hsum : d ^ 3 + d ^ 4 + d ^ 7 ≤ 3 * d ^ 3 := by
      nlinarith
    have hmax_nonneg : 0 ≤ (d - 2 / 3) ^ 2 * (d + 1 / 3) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have hmax : d ^ 2 * (1 - d) ≤ 4 / 27 := by
      nlinarith [hmax_nonneg]
    have hunit : 6 * (1 - d) * d ^ 2 ≤ 1 := by
      nlinarith
    have hsum_scaled :
        2 * (1 - d) * (d ^ 3 + d ^ 4 + d ^ 7) ≤
          6 * (1 - d) * d ^ 3 := by
      have hfactor : 0 ≤ 2 * (1 - d) := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hsum hfactor
      nlinarith
    have hunit_scaled : 6 * (1 - d) * d ^ 3 ≤ d := by
      have := mul_le_mul_of_nonneg_left hunit hd0.le
      nlinarith
    have hextra : 2 * (1 - d) * (d ^ 3 + d ^ 4 + d ^ 7) ≤ d :=
      le_trans hsum_scaled hunit_scaled
    dsimp [b, d] at *
    nlinarith [hextra]

/-- Kazamaki's half-exponential condition makes every strictly down-scaled
Doleans exponential uniformly integrable, for any admissible Hölder pair. -/
theorem KazamakiCondition.uniformIntegrable_stoppedValue_scaled_of_holder
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hK : KazamakiCondition M 𝒱 P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (a q r : ℝ) (ha0 : 0 < a) (hq : 1 < q) (hr : 1 < r)
    (hk0 : 0 ≤ (q - Real.sqrt (q / r)) * (r / (r - 1)))
    (hkc : (q - Real.sqrt (q / r)) * (r / (r - 1)) ≤ 1 / (2 * a))
    (tau : I → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (htauBound : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0)) :
    UniformIntegrable (fun i => stoppedValue (doleansDadeExponential
      (fun t omega => a * M t omega)
      (fun t omega => a ^ 2 * bracket t omega)) (tau i)) 1 P := by
  obtain ⟨C, hC⟩ := hK
  have hscaledMcont (omega : W) : Continuous
      (fun t => a * M t omega) := continuous_const.mul (hMcont omega)
  have hscaledMadapt : StronglyAdapted 𝒱 (fun t omega => a * M t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hMadapt t)
  have hscaledBracketAdapt : StronglyAdapted 𝒱
      (fun t omega => a ^ 2 * bracket t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hbracket t)
  have hscaledBracketPath (omega : W) :
      Continuous (fun t => a ^ 2 * bracket t omega) ∧
        Monotone (fun t => a ^ 2 * bracket t omega) := by
    refine ⟨continuous_const.mul (hbracketPath omega).1, ?_⟩
    intro s t hst
    exact mul_le_mul_of_nonneg_left ((hbracketPath omega).2 hst) (sq_nonneg a)
  apply uniformIntegrable_stoppedValue_doleansDade_of_holder
    (hlocalQV.const_mul a) hscaledMcont hscaledMadapt hscaledBracketAdapt
    hscaledBracketPath (fun omega => by rw [hMzero omega, mul_zero])
    (fun omega => by rw [hbracketZero omega, mul_zero])
    (1 / (2 * a)) C q r hq hr hk0 hkc tau htau htauBound
  intro i
  have hhalf := hC (tau i) (htau i) (htauBound i)
  have heq : (fun omega => Real.exp
      ((1 / (2 * a)) * stoppedValue (fun t omega => a * M t omega) (tau i) omega)) =
      fun omega => Real.exp (stoppedValue M (tau i) omega / 2) := by
    funext omega
    unfold stoppedValue
    congr 1
    field_simp
  simpa only [heq] using hhalf

/-- Kazamaki's condition makes every strictly down-scaled Doleans exponential
uniformly integrable over all bounded stopping times. -/
theorem KazamakiCondition.uniformIntegrable_stoppedValue_scaled
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hK : KazamakiCondition M 𝒱 P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (tau : I → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (htauBound : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0)) :
    UniformIntegrable (fun i => stoppedValue (doleansDadeExponential
      (fun t omega => a * M t omega)
      (fun t omega => a ^ 2 * bracket t omega)) (tau i)) 1 P := by
  obtain ⟨q, r, hq, hr, hk0, hkc⟩ :=
    exists_kazamakiHolder_parameters a ha0 ha1
  exact hK.uniformIntegrable_stoppedValue_scaled_of_holder hlocalQV hMcont
    hMadapt hbracket hbracketPath hMzero hbracketZero a q r ha0 hq hr hk0 hkc
    tau htau htauBound

/-- Uniform integrability is inherited by any pointwise norm-dominated
family of measurable real-valued functions. -/
lemma UniformIntegrable.mono_norm
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    {f g : I → W → ℝ} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P)
    (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hgf : ∀ i omega, ‖g i omega‖ ≤ ‖f i omega‖) :
    UniformIntegrable g p P := by
  refine ⟨hg, ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hf.2.1 hepsilon
    refine ⟨delta, hdelta, fun i s hs hPs => ?_⟩
    apply (eLpNorm_mono fun omega => ?_).trans (hbound i s hs hPs)
    by_cases homega : omega ∈ s
    · simp only [Set.indicator_of_mem homega]
      exact hgf i omega
    · simp only [Set.indicator_of_notMem homega, norm_zero]
      exact le_rfl
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun i => (eLpNorm_mono (hgf i)).trans (hC i)⟩

/-- A local martingale is genuine through `T` if its values at the canonical
localizing stopping times, truncated at each `t ≤ T`, form a uniformly
integrable family. -/
theorem IsLocalMartingale.martingale_stopAt_of_uniformIntegrable_stoppedValue
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M)
    (T : ℝ≥0)
    (hUI : ∀ t, t ≤ T → UniformIntegrable (fun n =>
      stoppedValue M (fun omega => min (hM.localSeq n omega) (t : WithTop ℝ≥0))) 1 P) :
    Martingale (fun t => M (min t T)) 𝒱 P := by
  apply hM.martingale_stopAt_of_uniformIntegrable_localizations hMadapt T
  intro t ht
  apply UniformIntegrable.mono_norm (hUI t ht)
  · intro n
    exact ((hM.stoppedProcess_localSeq n).integrable t).1
  · intro n omega
    unfold localizingStoppedProcess stoppedProcess stoppedValue
    simp only [Set.indicator_apply]
    split_ifs
    · rw [min_comm]
    · simpa only [norm_zero] using
        (norm_nonneg (M (min (hM.localSeq n omega) (t : WithTop ℝ≥0)).untopA omega))

/-- Under Kazamaki's condition, each strictly down-scaled stochastic
exponential is a true martingale through the terminal horizon. -/
theorem KazamakiCondition.martingale_stopAt_doleansDade_scaled
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hK : KazamakiCondition M 𝒱 P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Martingale (fun t => doleansDadeExponential
      (fun s omega => a * M s omega)
      (fun s omega => a ^ 2 * bracket s omega) (min t T)) 𝒱 P := by
  have hscaledLocal :=
    isContinuousLocalMartingale_doleansDadeExponential_const_mul_of_localQuadraticVariation
      hlocalQV hMcont hbracket hbracketPath hMzero hbracketZero a
  have hscaledMadapt : StronglyAdapted 𝒱 (fun t omega => a * M t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hMadapt t)
  have hscaledBracketAdapt : StronglyAdapted 𝒱
      (fun t omega => a ^ 2 * bracket t omega) := by
    intro t
    exact stronglyMeasurable_const.mul (hbracket t)
  have hscaledAdapt : StronglyAdapted 𝒱 (doleansDadeExponential
      (fun t omega => a * M t omega)
      (fun t omega => a ^ 2 * bracket t omega)) :=
    stronglyAdapted_doleansDadeExponential hscaledMadapt hscaledBracketAdapt
  apply hscaledLocal.1.martingale_stopAt_of_uniformIntegrable_stoppedValue
    hscaledAdapt T
  intro t ht
  apply hK.uniformIntegrable_stoppedValue_scaled hlocalQV hMcont hMadapt hbracket
    hbracketPath hMzero hbracketZero a ha0 ha1
  · intro n
    exact (hscaledLocal.1.isLocalizingSequence_localSeq.isStoppingTime n).min_const t
  · intro n omega
    exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr ht)

/-- Pointwise interpolation identity between a stochastic exponential and
its strict scaling. -/
theorem doleansDade_scaled_factor
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) (a : ℝ) :
    doleansDadeExponential (fun s omega => a * M s omega)
        (fun s omega => a ^ 2 * bracket s omega) t omega =
      doleansDadeExponential M bracket t omega ^ a *
        Real.exp (a * (1 - a) * bracket t omega / 2) := by
  unfold doleansDadeExponential doleansDadeLog
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Hölder interpolation bounds a scaled stochastic exponential by the
first moment of the original exponential and a bracket exponential moment. -/
theorem integrable_doleansDade_scaled_and_integral_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hEint : Integrable (doleansDadeExponential M bracket t) P)
    (hbracketMeas : AEStronglyMeasurable (bracket t) P)
    (hbracketNonneg : ∀ omega, 0 ≤ bracket t omega)
    (hbracketInt : Integrable
      (fun omega => Real.exp (bracket t omega / 2)) P) :
    Integrable (doleansDadeExponential
      (fun s omega => a * M s omega)
      (fun s omega => a ^ 2 * bracket s omega) t) P ∧
      (∫ omega, doleansDadeExponential
        (fun s omega => a * M s omega)
        (fun s omega => a ^ 2 * bracket s omega) t omega ∂P) ≤
        (∫ omega, doleansDadeExponential M bracket t omega ∂P) ^ a *
          (∫ omega, Real.exp (a * bracket t omega / 2) ∂P) ^ (1 - a) := by
  let r : ℝ := 1 / a
  let s : ℝ := 1 / (1 - a)
  have hr1 : 1 < r := by
    dsimp only [r]
    exact (one_lt_div₀ ha0).2 ha1
  have hrs : r.HolderConjugate s := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hr1, ?_⟩
    dsimp only [r, s]
    field_simp
    ring
  let _ : (ENNReal.ofReal r).HolderTriple (ENNReal.ofReal s) 1 :=
    hrs.ennrealOfReal
  let X : W → ℝ := doleansDadeExponential M bracket t
  let f : W → ℝ := fun omega => X omega ^ a
  let g : W → ℝ := fun omega =>
    Real.exp (a * (1 - a) * bracket t omega / 2)
  have hXpos (omega : W) : 0 < X omega := by
    unfold X doleansDadeExponential
    exact Real.exp_pos _
  have hfMeas : AEStronglyMeasurable f P :=
    (hEint.aestronglyMeasurable.aemeasurable.pow_const a).aestronglyMeasurable
  have hscaledBracketMeas : AEStronglyMeasurable
      (fun omega => a * bracket t omega / 2) P := by
    convert (hbracketMeas.const_mul (a / 2)) using 1
    funext omega
    ring
  have hsmallMeas : AEStronglyMeasurable
      (fun omega => Real.exp (a * bracket t omega / 2)) P :=
    Real.continuous_exp.comp_aestronglyMeasurable hscaledBracketMeas
  have hsmallInt : Integrable
      (fun omega => Real.exp (a * bracket t omega / 2)) P := by
    apply hbracketInt.mono' hsmallMeas
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith [hbracketNonneg omega]
  have hgMeas : AEStronglyMeasurable g P := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    convert hbracketMeas.const_mul (a * (1 - a) / 2) using 1
    funext omega
    ring
  have hfMem : MemLp f (ENNReal.ofReal r) P := by
    apply (memLp_norm_rpow_iff (p := ENNReal.ofReal r)
      (q := ENNReal.ofReal r) hfMeas (by positivity) (by finiteness)).mp
    convert memLp_one_iff_integrable.mpr hEint using 1
    · funext omega
      dsimp only [f]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hXpos omega).le _),
        ENNReal.toReal_ofReal hrs.nonneg, ← Real.rpow_mul (hXpos omega).le]
      have ha_ne : a ≠ 0 := ne_of_gt ha0
      rw [show a * r = 1 by dsimp [r]; field_simp, Real.rpow_one]
    · rw [ENNReal.div_self (by positivity) (by finiteness)]
  have hgMem : MemLp g (ENNReal.ofReal s) P := by
    apply (memLp_norm_rpow_iff (p := ENNReal.ofReal s)
      (q := ENNReal.ofReal s) hgMeas (by positivity) (by finiteness)).mp
    convert memLp_one_iff_integrable.mpr hsmallInt using 1
    · funext omega
      dsimp only [g, s]
      rw [Real.norm_of_nonneg (Real.exp_nonneg _), ENNReal.toReal_ofReal hrs.symm.nonneg,
        ← Real.exp_mul]
      dsimp only [s]
      congr 1
      have hne : 1 - a ≠ 0 := ne_of_gt (sub_pos.2 ha1)
      field_simp
    · rw [ENNReal.div_self (by positivity) (by finiteness)]
  have hproductInt : Integrable (fun omega => f omega * g omega) P :=
    hfMem.integrable_mul hgMem
  have hfr (omega : W) : f omega ^ r = X omega := by
    dsimp only [f]
    rw [← Real.rpow_mul (hXpos omega).le]
    have ha_ne : a ≠ 0 := ne_of_gt ha0
    rw [show a * r = 1 by dsimp [r]; field_simp, Real.rpow_one]
  have hgs (omega : W) : g omega ^ s =
      Real.exp (a * bracket t omega / 2) := by
    dsimp only [g, s]
    rw [← Real.exp_mul]
    congr 1
    have hne : 1 - a ≠ 0 := ne_of_gt (sub_pos.2 ha1)
    field_simp
  have hfactor : doleansDadeExponential
      (fun s omega => a * M s omega)
      (fun s omega => a ^ 2 * bracket s omega) t =
        fun omega => f omega * g omega := by
    funext omega
    exact doleansDade_scaled_factor M bracket t omega a
  refine ⟨hfactor ▸ hproductInt, ?_⟩
  rw [hfactor]
  calc
    (∫ omega, f omega * g omega ∂P) ≤
        (∫ omega, f omega ^ r ∂P) ^ (1 / r) *
          (∫ omega, g omega ^ s ∂P) ^ (1 / s) := by
      exact integral_mul_le_Lp_mul_Lq_of_nonneg hrs
        (Filter.Eventually.of_forall fun omega => Real.rpow_nonneg (hXpos omega).le _)
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
        hfMem hgMem
    _ = (∫ omega, doleansDadeExponential M bracket t omega ∂P) ^ a *
        (∫ omega, Real.exp (a * bracket t omega / 2) ∂P) ^ (1 - a) := by
      have hr_inv : 1 / r = a := by dsimp [r]; field_simp
      have hs_inv : 1 / s = 1 - a := by dsimp [s]; field_simp
      rw [hr_inv, hs_inv]
      congr 2
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall hfr
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall hgs

/-- Novikov's condition forces the stochastic exponential to preserve
expectation at every time up to the terminal horizon. -/
theorem NovikovCondition.integral_doleansDade_eq_one_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T t : ℝ≥0}
    (hN : NovikovCondition bracket P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (ht : t ≤ T) :
    (∫ omega, doleansDadeExponential M bracket t omega ∂P) = 1 := by
  let E := doleansDadeExponential M bracket
  have hE :=
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
      hlocalQV hMcont hbracket hbracketPath hMzero hbracketZero
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hMadapt hbracket
  have hEbound := integrable_doleansDadeExponential_and_integral_le_one
    hE.1 hEadapt hMzero hbracketZero t
  have hbracketMeas (s : ℝ≥0) : AEStronglyMeasurable (bracket s) P :=
    ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hNt : NovikovCondition bracket P t :=
    hN.mono_time hbracketMeas
      (Filter.Eventually.of_forall fun omega => (hbracketPath omega).2) ht
  have hbracketNonneg (omega : W) : 0 ≤ bracket t omega := by
    rw [← hbracketZero omega]
    exact (hbracketPath omega).2 bot_le
  let I : ℝ := ∫ omega, E t omega ∂P
  let K : ℝ := ∫ omega, Real.exp (bracket t omega / 2) ∂P
  have hI0 : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  have hK1 : 1 ≤ K := by
    calc
      1 = ∫ _ : W, (1 : ℝ) ∂P := by
        rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      _ ≤ ∫ omega, Real.exp (bracket t omega / 2) ∂P := by
        apply integral_mono (integrable_const 1) hNt
        intro omega
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (div_nonneg (hbracketNonneg omega) (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hKne : K ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  let scale : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hscale0 (n : ℕ) : 0 < scale n := by
    dsimp only [scale]
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 1 < (n : ℝ) + 2 := by linarith
    have hden0 : 0 < (n : ℝ) + 2 := zero_lt_one.trans hden
    have hone : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one hden0).2 hden
    linarith
  have hscale1 (n : ℕ) : scale n < 1 := by
    dsimp only [scale]
    have hden0 : 0 < (n : ℝ) + 2 := by positivity
    linarith [one_div_pos.mpr hden0]
  have hineq (n : ℕ) :
      1 ≤ I ^ (scale n) * K ^ (1 - scale n) := by
    let a := scale n
    have ha0 : 0 < a := hscale0 n
    have ha1 : a < 1 := hscale1 n
    have hKazamaki := hN.kazamakiCondition hlocalQV hMcont hMadapt hbracket
      hbracketPath hMzero hbracketZero
    have hscaledMart :=
      hKazamaki.martingale_stopAt_doleansDade_scaled hlocalQV hMcont
        hMadapt hbracket hbracketPath hMzero hbracketZero a ha0 ha1
    have hscaledZero : doleansDadeExponential
        (fun s omega => a * M s omega)
        (fun s omega => a ^ 2 * bracket s omega) 0 = fun _ => 1 := by
      funext omega
      exact doleansDadeExponential_zero _ _ omega
        (by rw [hMzero omega, mul_zero])
        (by rw [hbracketZero omega, mul_zero])
    have hscaledIntegral : (∫ omega, doleansDadeExponential
        (fun s omega => a * M s omega)
        (fun s omega => a ^ 2 * bracket s omega) t omega ∂P) = 1 := by
      have heq := StochasticCalculus.Martingale.integral_eq hscaledMart (bot_le : (0 : ℝ≥0) ≤ t)
      calc
        _ = ∫ omega, doleansDadeExponential
            (fun s omega => a * M s omega)
            (fun s omega => a ^ 2 * bracket s omega) 0 omega ∂P := by
          simpa [min_eq_left ht] using heq
        _ = 1 := by
          rw [hscaledZero, integral_const, Measure.real, measure_univ,
            ENNReal.toReal_one, one_smul]
    have hinter := integrable_doleansDade_scaled_and_integral_le
      M bracket t a ha0 ha1 hEbound.1 (hbracketMeas t) hbracketNonneg hNt
    have hsmallMeas : AEStronglyMeasurable
        (fun omega => Real.exp (a * bracket t omega / 2)) P := by
      apply Real.continuous_exp.comp_aestronglyMeasurable
      convert (hbracketMeas t).const_mul (a / 2) using 1
      funext omega
      ring
    have hsmallInt : Integrable
        (fun omega => Real.exp (a * bracket t omega / 2)) P := by
      apply hNt.mono' hsmallMeas
      exact Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        nlinarith [hbracketNonneg omega]
    have hsmallLe : (∫ omega, Real.exp (a * bracket t omega / 2) ∂P) ≤ K := by
      apply integral_mono hsmallInt hNt
      intro omega
      apply Real.exp_le_exp.mpr
      nlinarith [hbracketNonneg omega]
    have hsmallNonneg : 0 ≤
        ∫ omega, Real.exp (a * bracket t omega / 2) ∂P :=
      integral_nonneg fun _ => Real.exp_nonneg _
    calc
      1 = ∫ omega, doleansDadeExponential
          (fun s omega => a * M s omega)
          (fun s omega => a ^ 2 * bracket s omega) t omega ∂P :=
        hscaledIntegral.symm
      _ ≤ I ^ a *
          (∫ omega, Real.exp (a * bracket t omega / 2) ∂P) ^ (1 - a) := by
        simpa only [I, E] using hinter.2
      _ ≤ I ^ a * K ^ (1 - a) := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hsmallNonneg hsmallLe (sub_nonneg.2 ha1.le))
          (Real.rpow_nonneg hI0 a)
      _ = I ^ (scale n) * K ^ (1 - scale n) := rfl
  have hfrac : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hscale : Tendsto scale atTop (nhds 1) := by
    simpa only [scale, sub_zero] using tendsto_const_nhds.sub hfrac
  have hIpow : Tendsto (fun n => I ^ (scale n)) atTop (nhds I) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_const_rpow' (a := I) (b := 1) one_ne_zero).tendsto.comp hscale
  have hKpow : Tendsto (fun n => K ^ (1 - scale n)) atTop (nhds 1) := by
    have hexp : Tendsto (fun n => 1 - scale n) atTop (nhds 0) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      simpa only [sub_self] using hone.sub hscale
    simpa [Function.comp_def] using
      (Real.continuousAt_const_rpow hKne).tendsto.comp hexp
  have hlimit : Tendsto (fun n => I ^ (scale n) * K ^ (1 - scale n))
      atTop (nhds I) := by
    simpa only [mul_one] using hIpow.mul hKpow
  apply le_antisymm hEbound.2
  have hI1 : 1 ≤ I := ge_of_tendsto hlimit (Filter.Eventually.of_forall hineq)
  simpa only [I, E] using hI1

/-- Novikov's condition promotes the stochastic exponential to a true
martingale on the finite horizon. -/
theorem NovikovCondition.martingale_stopAt_doleansDade
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hN : NovikovCondition bracket P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    Martingale (fun t => doleansDadeExponential M bracket (min t T)) 𝒱 P := by
  let E := doleansDadeExponential M bracket
  have hE :=
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
      hlocalQV hMcont hbracket hbracketPath hMzero hbracketZero
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hMadapt hbracket
  have hEcont (omega : W) : Continuous (fun t => E t omega) :=
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hEzero : E 0 = fun _ => 1 := by
    funext omega
    exact doleansDadeExponential_zero M bracket omega
      (hMzero omega) (hbracketZero omega)
  by_cases hTzero : T = 0
  · subst T
    convert martingale_const 𝒱 P (1 : ℝ) using 1
    funext t omega
    rw [min_eq_right (zero_le : (0 : ℝ≥0) ≤ t)]
    exact congrFun hEzero omega
  · have hTpos : 0 < T := (pos_iff_ne_zero).2 hTzero
    let N : ℝ≥0 → W → ℝ := fun t => E (min t T)
    have hNlocal : IsLocalMartingale N 𝒱 P := by
      have hstop := hE.1.localizingStoppedProcess_of_bounded hEcont
        (isStoppingTime_const 𝒱 T) T (fun _ => le_rfl)
      convert hstop using 1
      funext t omega
      unfold N localizingStoppedProcess stoppedProcess
      simp only [Set.indicator_apply]
      rw [if_pos]
      · apply congrArg (fun u => E u omega)
        rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
          WithTop.untop_coe]
      · change (⊥ : WithTop ℝ≥0) < (T : WithTop ℝ≥0)
        rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
        exact WithTop.coe_lt_coe.mpr hTpos
    have hNadapt : StronglyAdapted 𝒱 N := by
      intro t
      exact (hEadapt (min t T)).mono (𝒱.mono (min_le_left t T))
    have hNcont (omega : W) : Continuous (fun t => N t omega) :=
      (hEcont omega).comp (continuous_id.min continuous_const)
    have hNnonneg (t : ℝ≥0) (omega : W) : 0 ≤ N t omega :=
      (Real.exp_pos _).le
    have hNzero : N 0 = fun _ => 1 := by
      change E (min 0 T) = fun _ => 1
      rw [min_eq_left (zero_le : (0 : ℝ≥0) ≤ T)]
      exact hEzero
    have hNzeroInt : Integrable (N 0) P := by
      rw [hNzero]
      exact integrable_const 1
    apply hNlocal.martingale_of_nonneg_of_integral_eq_zero hNadapt hNcont
      hNnonneg hNzeroInt
    intro t
    have htIntegral := hN.integral_doleansDade_eq_one_of_le hlocalQV
      hMcont hMadapt hbracket hbracketPath hMzero hbracketZero (min_le_right t T)
    calc
      (∫ omega, N t omega ∂P) = 1 := by simpa only [N, E] using htIntegral
      _ = ∫ omega, N 0 omega ∂P := by
        rw [hNzero, integral_const, Measure.real, measure_univ,
          ENNReal.toReal_one, one_smul]

/-- Under Novikov's condition, the stochastic exponential is of class D on
the finite horizon: all of its bounded stopped values are uniformly
integrable. -/
theorem NovikovCondition.uniformIntegrable_stoppedValue_doleansDade
    {W I : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hN : NovikovCondition bracket P T)
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMadapt : StronglyAdapted 𝒱 M)
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (tau : I → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (htauBound : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0)) :
    UniformIntegrable (fun i =>
      stoppedValue (doleansDadeExponential M bracket) (tau i)) 1 P := by
  let E := doleansDadeExponential M bracket
  have hmart := hN.martingale_stopAt_doleansDade hlocalQV hMcont
    hMadapt hbracket hbracketPath hMzero hbracketZero
  have hEcont (omega : W) : Continuous (fun t => E t omega) :=
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hstoppedCont : ∀ᵐ omega ∂P, Continuous (fun t => E (min t T) omega) :=
    Filter.Eventually.of_forall fun omega =>
      (hEcont omega).comp (continuous_id.min continuous_const)
  have hstopUI : UniformIntegrable
      (fun i => stoppedValue (fun t => E (min t T)) (tau i)) 1 P :=
    StochasticCalculus.Martingale.uniformIntegrable_stoppedValue_of_bounded
      hmart hstoppedCont T tau htau htauBound
  apply hstopUI.ae_eq
  intro i
  exact Filter.Eventually.of_forall fun omega => by
    unfold stoppedValue
    have hne : tau i omega ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (htauBound i omega)
    have hcoe : (((tau i omega).untopA : ℝ≥0) : WithTop ℝ≥0) =
        tau i omega := by
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop (tau i omega) hne
    have hut : (tau i omega).untopA ≤ T := by
      apply WithTop.coe_le_coe.mp
      rw [hcoe]
      exact htauBound i omega
    change E (min (tau i omega).untopA T) omega =
      E (tau i omega).untopA omega
    rw [min_eq_left hut]

end StochasticCalculus
