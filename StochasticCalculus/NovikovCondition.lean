/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.DoleansDade

/-!
# Novikov's condition and nonnegative local martingales

The condition `E[exp(½⟪M⟫_T)] < ∞`, its deterministic and earlier-time
cases, stopping of martingales at deterministic times, uniform
integrability of martingales on bounded intervals, and the passage from a
nonnegative local martingale with vanishing integral to a true martingale.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Novikov's exponential-integrability condition at a deterministic horizon.
For an adapted bracket, strong measurability makes this equivalent to
finiteness of the usual expectation of `exp (bracket_T / 2)`. -/
@[expose] def NovikovCondition
    {W : Type*} [MeasurableSpace W]
    (bracket : ℝ≥0 → W → ℝ) (P : Measure W) (T : ℝ≥0) : Prop :=
  Integrable (fun omega => Real.exp (bracket T omega / 2)) P

/-- Every deterministic finite-valued bracket satisfies Novikov's condition
on a finite measure space. -/
theorem novikovCondition_deterministic
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (bracket : ℝ≥0 → ℝ) (T : ℝ≥0) :
    NovikovCondition (fun t (_ : W) => bracket t) P T :=
  integrable_const _

/-- For a measurable increasing bracket, Novikov's condition at `T` implies
the same condition at every earlier deterministic time. -/
theorem NovikovCondition.mono_time
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hN : NovikovCondition bracket P T)
    (hmeas : ∀ t, AEStronglyMeasurable (bracket t) P)
    (hmono : ∀ᵐ omega ∂P, Monotone (fun t => bracket t omega))
    {t : ℝ≥0} (ht : t ≤ T) :
    NovikovCondition bracket P t := by
  apply hN.mono
  · have hscaled : AEStronglyMeasurable
        (fun omega => (1 / 2 : ℝ) * bracket t omega) P :=
      (hmeas t).const_mul (1 / 2 : ℝ)
    exact Real.continuous_exp.comp_aestronglyMeasurable <| by
      simpa [div_eq_mul_inv, mul_comm] using hscaled
  · filter_upwards [hmono] with omega hmonoOmega
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (hmonoOmega ht) (by norm_num)

/-- Pointwise factorization behind the Cauchy--Schwarz step from Novikov's
condition to Kazamaki's exponential bound. -/
theorem novikovKazamaki_factor
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    Real.exp (M t omega / 2) =
      doleansDadeExponential M bracket t omega ^ (1 / 2 : ℝ) *
        Real.exp (bracket t omega / 4) := by
  unfold doleansDadeExponential doleansDadeLog
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- At each deterministic time, the canonical localized values of a local
martingale eventually agree pointwise with the original value. -/
theorem IsLocalMartingale.tendsto_ae_localizations
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, Tendsto
      (fun n => localizingStoppedProcess M (hM.localSeq n) t omega)
      atTop (nhds (M t omega)) := by
  change Locally (fun N => Martingale N 𝒱 P) 𝒱 M P at hM
  filter_upwards [hM.isLocalizingSequence_localSeq.tendsto_top] with omega htau
  have hevent : ∀ᶠ n : ℕ in atTop,
      (((t + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ hM.localSeq n omega) :=
    ((tendsto_order.1 htau).1 ((t + 1 : ℝ≥0) : WithTop ℝ≥0)
      (WithTop.coe_lt_top (t + 1))).mono fun n hn => hn.le
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hevent] with n hn
  unfold localizingStoppedProcess stoppedProcess
  have htlt : (t : WithTop ℝ≥0) < hM.localSeq n omega := by
    exact (WithTop.coe_lt_coe.mpr (lt_add_one t)).trans_le hn
  have hpos : (⊥ : WithTop ℝ≥0) < hM.localSeq n omega :=
    bot_le.trans_lt htlt
  rw [min_eq_left htlt.le,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  have hne : hM.localSeq n omega ≠ 0 := ne_of_gt hpos
  simp [Set.indicator, hne]

/-- A real martingale has constant expectation. -/
theorem Martingale.integral_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ omega, M t omega ∂P) = ∫ omega, M s omega ∂P := by
  calc
    (∫ omega, M t omega ∂P) =
        ∫ omega, P[M t | 𝒱 s] omega ∂P :=
      (integral_condExp (𝒱.le s)).symm
    _ = ∫ omega, M s omega ∂P :=
      integral_congr_ae (hM.condExp_ae_eq hst)

/-- A pointwise nonnegative local martingale has integrable fixed-time values,
and its expectation cannot exceed its time-zero expectation. This is Fatou's
lemma applied to the genuine martingales in a canonical localization. -/
theorem IsLocalMartingale.integrable_and_integral_le_zero_of_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M)
    (hMnonneg : ∀ t omega, 0 ≤ M t omega)
    (hMzeroInt : Integrable (M 0) P) (t : ℝ≥0) :
    Integrable (M t) P ∧
      (∫ omega, M t omega ∂P) ≤ ∫ omega, M 0 omega ∂P := by
  change Locally (fun N => Martingale N 𝒱 P) 𝒱 M P at hM
  let X : ℕ → W → ℝ := fun n =>
    localizingStoppedProcess M (hM.localSeq n) t
  have hXmart (n : ℕ) : Martingale
      (localizingStoppedProcess M (hM.localSeq n)) 𝒱 P :=
    hM.stoppedProcess_localSeq n
  have hXint (n : ℕ) : Integrable (X n) P :=
    (hXmart n).integrable t
  have hXnonneg (n : ℕ) : ∀ omega, 0 ≤ X n omega := by
    intro omega
    unfold X localizingStoppedProcess stoppedProcess
    change 0 ≤ {omega | (⊥ : WithTop ℝ≥0) < hM.localSeq n omega}.indicator
      (M (min (t : WithTop ℝ≥0) (hM.localSeq n omega)).untopA) omega
    simp only [Set.indicator_apply]
    split_ifs
    · exact hMnonneg _ _
    · exact le_rfl
  have hXzero_le (n : ℕ) : ∀ omega,
      localizingStoppedProcess M (hM.localSeq n) 0 omega ≤ M 0 omega := by
    intro omega
    unfold localizingStoppedProcess stoppedProcess
    by_cases hpos : (0 : WithTop ℝ≥0) < hM.localSeq n omega
    · simp [hpos]
    · simpa [Set.indicator_apply, hpos] using hMnonneg 0 omega
  have hXbound (n : ℕ) :
      (∫⁻ omega, ‖X n omega‖ₑ ∂P) ≤
        ∫⁻ omega, ‖M 0 omega‖ₑ ∂P := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hXint n)]
    have hXeq : (∫ omega, ‖X n omega‖ ∂P) =
        ∫ omega, X n omega ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hXnonneg n omega)]
    rw [hXeq, StochasticCalculus.Martingale.integral_eq (hXmart n) bot_le]
    have hXzeroInt := (hXmart n).integrable 0
    have hle : (∫ omega,
        localizingStoppedProcess M (hM.localSeq n) 0 omega ∂P) ≤
        ∫ omega, M 0 omega ∂P :=
      integral_mono hXzeroInt hMzeroInt (hXzero_le n)
    calc
      ENNReal.ofReal
          (∫ omega, localizingStoppedProcess M (hM.localSeq n) 0 omega ∂P) ≤
          ENNReal.ofReal (∫ omega, M 0 omega ∂P) := ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ omega, ‖M 0 omega‖ₑ ∂P := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hMzeroInt]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hMnonneg 0 omega)]
  have hlim : ∀ᵐ omega ∂P, Tendsto (fun n => X n omega)
      atTop (nhds (M t omega)) := by
    simpa only [X] using
      IsLocalMartingale.tendsto_ae_localizations
        (show IsLocalMartingale M 𝒱 P from hM) t
  have hfatou : (∫⁻ omega, ‖M t omega‖ₑ ∂P) ≤
      ∫⁻ omega, ‖M 0 omega‖ₑ ∂P := by
    calc
      (∫⁻ omega, ‖M t omega‖ₑ ∂P) =
          ∫⁻ omega, liminf (fun n => ‖X n omega‖ₑ) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with omega homega
        exact homega.enorm.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ omega, ‖X n omega‖ₑ ∂P) atTop :=
        MeasureTheory.lintegral_liminf_le' fun n =>
          (hXint n).aestronglyMeasurable.enorm
      _ ≤ ∫⁻ omega, ‖M 0 omega‖ₑ ∂P :=
        liminf_le_of_frequently_le' (Frequently.of_forall hXbound)
  have hMtMeas : AEStronglyMeasurable (M t) P :=
    ((hMadapt t).mono (𝒱.le t)).aestronglyMeasurable
  have hMtInt : Integrable (M t) P := by
    refine ⟨hMtMeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt hfatou (hasFiniteIntegral_iff_enorm.mp hMzeroInt.2)
  refine ⟨hMtInt, ?_⟩
  have htoReal := ENNReal.toReal_mono
    (ne_top_of_lt (hasFiniteIntegral_iff_enorm.mp hMzeroInt.2)) hfatou
  rw [← integral_norm_eq_lintegral_enorm hMtInt.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hMzeroInt.aestronglyMeasurable] at htoReal
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hMnonneg _ _)] using htoReal

/-- The stopped-and-indicated value of a nonnegative continuous local
martingale at a bounded stopping time is integrable, with expectation bounded
by its stopped-and-indicated time-zero expectation. -/
theorem IsLocalMartingale.integrable_localizingStoppedProcess_and_integral_le_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMnonneg : ∀ t omega, 0 ≤ M t omega)
    (hMzeroInt : Integrable (M 0) P)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Integrable (localizingStoppedProcess M tau T) P ∧
      (∫ omega, localizingStoppedProcess M tau T omega ∂P) ≤
        ∫ omega, localizingStoppedProcess M tau 0 omega ∂P := by
  let N := localizingStoppedProcess M tau
  have hNlocal : IsLocalMartingale N 𝒱 P :=
    hM.localizingStoppedProcess_of_bounded hMcont htau T hbound
  have hNadapt : StronglyAdapted 𝒱 N :=
    stronglyAdapted_localizingStoppedProcess hMadapt hMcont htau
  have hNnonneg : ∀ t omega, 0 ≤ N t omega := by
    intro t omega
    unfold N localizingStoppedProcess stoppedProcess
    change 0 ≤ {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (M (min (t : WithTop ℝ≥0) (tau omega)).untopA) omega
    simp only [Set.indicator_apply]
    split_ifs
    · exact hMnonneg _ _
    · exact le_rfl
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[𝒱 0] A := by
    change MeasurableSet[𝒱 0] {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  have hNzero : N 0 = A.indicator (M 0) := by
    funext omega
    unfold N A localizingStoppedProcess stoppedProcess
    simp
  have hNzeroInt : Integrable (N 0) P := by
    rw [hNzero]
    exact hMzeroInt.indicator (𝒱.le 0 A hA)
  exact hNlocal.integrable_and_integral_le_zero_of_nonneg
    hNadapt hNnonneg hNzeroInt T

/-- Optional-sampling inequality for a nonnegative continuous local
martingale: every bounded stopped value is integrable and its expectation is
at most the initial expectation. -/
theorem IsLocalMartingale.integrable_stoppedValue_and_integral_le_zero_of_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMnonneg : ∀ t omega, 0 ≤ M t omega)
    (hMzeroInt : Integrable (M 0) P)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (T : ℝ≥0) (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Integrable (stoppedValue M tau) P ∧
      (∫ omega, stoppedValue M tau omega ∂P) ≤
        ∫ omega, M 0 omega ∂P := by
  let N := localizingStoppedProcess M tau
  let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau omega}
  have hA : MeasurableSet[𝒱 0] A := by
    change MeasurableSet[𝒱 0] {omega | (⊥ : WithTop ℝ≥0) < tau omega}
    rw [show (⊥ : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
    exact htau.measurableSet_gt 0
  have hAmeas : MeasurableSet A := 𝒱.le 0 A hA
  have hAcInt : Integrable (Aᶜ.indicator (M 0)) P :=
    hMzeroInt.indicator hAmeas.compl
  have hterminal : N T = A.indicator (stoppedValue M tau) := by
    funext omega
    unfold N A localizingStoppedProcess stoppedProcess stoppedValue
    change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (M (min (T : WithTop ℝ≥0) (tau omega)).untopA) omega =
      {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (M (tau omega).untopA) omega
    simp only [Set.indicator_apply]
    split_ifs
    · rw [min_eq_right (hbound omega)]
    · rfl
  have hzero : N 0 = A.indicator (M 0) := by
    funext omega
    unfold N A localizingStoppedProcess stoppedProcess
    simp
  have hdecomp : stoppedValue M tau = N T + Aᶜ.indicator (M 0) := by
    funext omega
    rw [hterminal]
    change stoppedValue M tau omega =
      A.indicator (stoppedValue M tau) omega + Aᶜ.indicator (M 0) omega
    by_cases hmem : omega ∈ A
    · have hncomp : omega ∉ Aᶜ := by simpa
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hncomp, add_zero]
    · have htauzero : tau omega = ⊥ := le_antisymm (le_of_not_gt hmem) bot_le
      have hcomp : omega ∈ Aᶜ := by simpa
      unfold stoppedValue
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem hcomp, zero_add,
        htauzero]
      simp
  have hInd := hM.integrable_localizingStoppedProcess_and_integral_le_zero
    hMadapt hMcont hMnonneg hMzeroInt htau T hbound
  have hstopInt : Integrable (stoppedValue M tau) P := by
    rw [hdecomp]
    exact hInd.1.add hAcInt
  refine ⟨hstopInt, ?_⟩
  calc
    (∫ omega, stoppedValue M tau omega ∂P) =
        (∫ omega, N T omega ∂P) +
          ∫ omega, Aᶜ.indicator (M 0) omega ∂P := by
      rw [hdecomp]
      simpa only [Pi.add_apply] using integral_add hInd.1 hAcInt
    _ ≤ (∫ omega, N 0 omega ∂P) +
          ∫ omega, Aᶜ.indicator (M 0) omega ∂P :=
      add_le_add hInd.2 le_rfl
    _ = ∫ omega, M 0 omega ∂P := by
      rw [hzero, ← integral_add (hMzeroInt.indicator hAmeas) hAcInt]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by
        change A.indicator (M 0) omega + Aᶜ.indicator (M 0) omega = M 0 omega
        by_cases hmem : omega ∈ A
        · have hncomp : omega ∉ Aᶜ := by simpa
          rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hncomp]
          simp
        · have hcomp : omega ∈ Aᶜ := by simpa
          rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem hcomp]
          simp

/-- Every fixed-time value of a normalized local Doléans exponential is
integrable and has expectation at most one. -/
theorem integrable_doleansDadeExponential_and_integral_le_one
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M bracket : ℝ≥0 → W → ℝ}
    (hE : IsLocalMartingale (doleansDadeExponential M bracket) 𝒱 P)
    (hEadapt : StronglyAdapted 𝒱 (doleansDadeExponential M bracket))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) (t : ℝ≥0) :
    Integrable (doleansDadeExponential M bracket t) P ∧
      (∫ omega, doleansDadeExponential M bracket t omega ∂P) ≤ 1 := by
  have hEzero : doleansDadeExponential M bracket 0 = fun _ => 1 := by
    funext omega
    exact doleansDadeExponential_zero M bracket omega
      (hMzero omega) (hbracketZero omega)
  have hEzeroInt : Integrable (doleansDadeExponential M bracket 0) P := by
    rw [hEzero]
    exact integrable_const 1
  have hresult := hE.integrable_and_integral_le_zero_of_nonneg hEadapt
    (fun _ _ => (Real.exp_pos _).le) hEzeroInt t
  simpa only [hEzero, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] using hresult

/-- Deterministically stopping a martingale at `T` again gives a martingale.
This is the constant finite-range case of optional stopping. -/
theorem Martingale.stopAt
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P) (T : ℝ≥0) :
    Martingale (fun t => M (min t T)) 𝒱 P := by
  have hstop := martingale_stoppedProcess_of_finiteRange hM
    (isStoppingTime_const 𝒱 T) {T} (fun omega => by
      exact ⟨T, by simp, rfl⟩)
  convert hstop using 1
  funext t omega
  unfold stoppedProcess
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
    WithTop.untop_coe, min_comm]

/-- Finite-horizon version of the local-to-true upgrade.  To prove that a
local martingale is a martingale on `[0, T]`, uniform integrability is needed
only at deterministic times at most `T`; the conclusion is expressed by
making the process constant after `T`. -/
theorem IsLocalMartingale.martingale_stopAt_of_uniformIntegrable_localizations
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M) (T : ℝ≥0)
    (hUI : ∀ t, t ≤ T → UniformIntegrable
      (fun n => localizingStoppedProcess M (hM.localSeq n) t) 1 P) :
    Martingale (fun t => M (min t T)) 𝒱 P := by
  let X : ℕ → ℝ≥0 → W → ℝ := fun n t =>
    localizingStoppedProcess M (hM.localSeq n) (min t T)
  have hX (n : ℕ) : Martingale (X n) 𝒱 P :=
    Martingale.stopAt (hM.stoppedProcess_localSeq n) T
  have hYadapt : StronglyAdapted 𝒱 (fun t => M (min t T)) := by
    intro t
    exact (hMadapt (min t T)).mono (𝒱.mono (min_le_left t T))
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable hX hYadapt
  · intro t
    exact hUI (min t T) (min_le_right t T)
  · intro t
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hX n).integrable t |>.1)
    filter_upwards [hM.isLocalizingSequence_localSeq.tendsto_top] with omega htau
    have hevent : ∀ᶠ n : ℕ in atTop,
        ((((min t T) + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ hM.localSeq n omega) :=
      ((tendsto_order.1 htau).1 (((min t T) + 1 : ℝ≥0) : WithTop ℝ≥0)
        (WithTop.coe_lt_top ((min t T) + 1))).mono fun n hn => hn.le
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hevent] with n hn
    unfold X localizingStoppedProcess stoppedProcess
    have htlt : ((min t T : ℝ≥0) : WithTop ℝ≥0) < hM.localSeq n omega := by
      exact (WithTop.coe_lt_coe.mpr (lt_add_one (min t T))).trans_le hn
    have hpos : (⊥ : WithTop ℝ≥0) < hM.localSeq n omega :=
      bot_le.trans_lt htlt
    rw [min_eq_left htlt.le,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    have hne : hM.localSeq n omega ≠ 0 := ne_of_gt hpos
    simp [Set.indicator, hne]

/-- A genuine real martingale, restricted to all deterministic times below a
fixed terminal horizon, is a uniformly integrable family.  Each value is the
conditional expectation of the single integrable terminal value. -/
theorem Martingale.uniformIntegrable_Iic
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P) (T : ℝ≥0) :
    UniformIntegrable (fun t : Set.Iic T => M t) 1 P := by
  have hUI : UniformIntegrable
      (fun t : Set.Iic T => P[M T | 𝒱 t]) 1 P :=
    (hM.integrable T).uniformIntegrable_condExp (fun t => 𝒱.le t)
  apply hUI.ae_eq
  intro t
  exact hM.condExp_ae_eq t.property

/-- The values of a genuine martingale at an arbitrary family of bounded
countable-range stopping times are uniformly integrable.  Optional sampling
identifies each stopped value with a conditional expectation of the common
terminal value `M T`. -/
theorem Martingale.uniformIntegrable_stoppedValue_of_countableRange
    {W ι : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P) (T : ℝ≥0)
    (tau : ι → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (hle : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0))
    (hrange : ∀ i, (Set.range (tau i)).Countable) :
    UniformIntegrable (fun i => stoppedValue M (tau i)) 1 P := by
  have hUI : UniformIntegrable
      (fun i => P[M T | (htau i).measurableSpace]) 1 P :=
    (hM.integrable T).uniformIntegrable_condExp
      (fun i => (htau i).measurableSpace_le_of_le (hle i))
  apply hUI.ae_eq
  intro i
  exact (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    (htau i) (hle i) (hrange i)).symm

/-- The values of a continuous-path martingale at an arbitrary family of
bounded stopping times are uniformly integrable.  Uniform-partition ceiling
approximations have finite range and converge pathwise; uniform integrability
is preserved when all their almost-everywhere limits are adjoined. -/
theorem Martingale.uniformIntegrable_stoppedValue_of_bounded
    {W ι : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun t => M t omega)) (T : ℝ≥0)
    (tau : ι → W → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime 𝒱 (tau i))
    (hle : ∀ i omega, tau i omega ≤ (T : WithTop ℝ≥0)) :
    UniformIntegrable (fun i => stoppedValue M (tau i)) 1 P := by
  let tauN : ι × ℕ → W → WithTop ℝ≥0 := fun j =>
    uniformPartitionCeilStoppingTime (tau j.1) T (j.2 + 1)
      (Nat.zero_lt_succ j.2) (hle j.1)
  have htauN (j : ι × ℕ) : IsStoppingTime 𝒱 (tauN j) :=
    isStoppingTime_uniformPartitionCeilStoppingTime
      (htau j.1) T (j.2 + 1) (Nat.zero_lt_succ j.2) (hle j.1)
  have htauNle (j : ι × ℕ) (omega : W) :
      tauN j omega ≤ (T : WithTop ℝ≥0) :=
    uniformPartitionCeilStoppingTime_le
      (tau j.1) T (j.2 + 1) (Nat.zero_lt_succ j.2) (hle j.1) omega
  have htauNrange (j : ι × ℕ) : (Set.range (tauN j)).Countable := by
    apply ((((Finset.range (j.2 + 1 + 1)).image
      (uniformPartitionTime T (j.2 + 1))).finite_toSet.image
        ((↑) : ℝ≥0 → WithTop ℝ≥0)).countable).mono
    rintro x ⟨omega, rfl⟩
    exact uniformPartitionCeilStoppingTime_mem_rangeFinset
      (tau j.1) T (j.2 + 1) (Nat.zero_lt_succ j.2) (hle j.1) omega
  have hUI : UniformIntegrable (fun j => stoppedValue M (tauN j)) 1 P :=
    StochasticCalculus.Martingale.uniformIntegrable_stoppedValue_of_countableRange hM
      T tauN htauN htauNle htauNrange
  let Limits := {g : W → ℝ | ∃ nj : ℕ → ι × ℕ,
    ∀ᵐ omega ∂P, Tendsto (fun n => stoppedValue M (tauN (nj n)) omega)
      atTop (nhds (g omega))}
  have hLimits : UniformIntegrable (fun g : Limits => g.1) 1 P := by
    exact hUI.uniformIntegrable_of_ae_tendsto atTop
  let g : ι → Limits := fun i => ⟨stoppedValue M (tau i), ⟨fun n => (i, n), by
    filter_upwards [hMcont] with omega hcont
    unfold stoppedValue
    have hne : tau i omega ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (hle i omega)
    apply hcont.continuousAt.tendsto.comp
    apply (WithTop.tendsto_untopA hne).comp
    exact tendsto_uniformPartitionCeilStoppingTime
      (tau i) T (hle i) omega⟩⟩
  change UniformIntegrable ((fun f : Limits => f.1) ∘ g) 1 P
  refine ⟨UnifIntegrable.comp g hLimits.1, ?_⟩
  · rcases hLimits.2 with ⟨C, hC⟩
    exact ⟨C, fun i => hC (g i)⟩

theorem novikovKazamaki_stoppedValue_factor
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (tau : W → WithTop ℝ≥0) (omega : W) :
    Real.exp (stoppedValue M tau omega / 2) =
      Real.sqrt (stoppedValue (doleansDadeExponential M bracket) tau omega) *
        Real.exp (stoppedValue bracket tau omega / 4) := by
  unfold stoppedValue
  rw [novikovKazamaki_factor, ← Real.sqrt_eq_rpow]

theorem integrable_stoppedValue_exp_half_and_integral_le_doleansDade_bracket
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (hEint : Integrable
      (stoppedValue (doleansDadeExponential M bracket) tau) P)
    (hbracketMeas : AEStronglyMeasurable (stoppedValue bracket tau) P)
    (hbracketInt : Integrable
      (fun omega => Real.exp (stoppedValue bracket tau omega / 2)) P) :
    Integrable (fun omega => Real.exp (stoppedValue M tau omega / 2)) P ∧
      (∫ omega, Real.exp (stoppedValue M tau omega / 2) ∂P) ≤
        (∫ omega, stoppedValue (doleansDadeExponential M bracket) tau omega ∂P) ^
            (1 / 2 : ℝ) *
          (∫ omega, Real.exp (stoppedValue bracket tau omega / 2) ∂P) ^
            (1 / 2 : ℝ) := by
  let f : W → ℝ := fun omega =>
    Real.sqrt (stoppedValue (doleansDadeExponential M bracket) tau omega)
  let g : W → ℝ := fun omega =>
    Real.exp (stoppedValue bracket tau omega / 4)
  have hfMeas : AEStronglyMeasurable f P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hEint.aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g P := by
    have hscaled : AEStronglyMeasurable
        (fun omega => (1 / 4 : ℝ) * stoppedValue bracket tau omega) P :=
      hbracketMeas.const_mul (1 / 4 : ℝ)
    exact Real.continuous_exp.comp_aestronglyMeasurable <| by
      simpa [div_eq_mul_inv, mul_comm] using hscaled
  have hfMem : MemLp f 2 P := by
    apply (memLp_two_iff_integrable_sq hfMeas).2
    apply hEint.congr
    exact Filter.Eventually.of_forall fun omega => by
      dsimp only [f]
      exact (Real.sq_sqrt (Real.exp_nonneg _)).symm
  have hgMem : MemLp g 2 P := by
    apply (memLp_two_iff_integrable_sq hgMeas).2
    apply hbracketInt.congr
    exact Filter.Eventually.of_forall fun omega => by
      dsimp only [g]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  have hproductInt : Integrable (fun omega => f omega * g omega) P :=
    hfMem.integrable_mul hgMem
  have hfactor : (fun omega => Real.exp (stoppedValue M tau omega / 2)) =
      fun omega => f omega * g omega := by
    funext omega
    exact novikovKazamaki_stoppedValue_factor M bracket tau omega
  refine ⟨hfactor ▸ hproductInt, ?_⟩
  rw [hfactor]
  calc
    (∫ omega, f omega * g omega ∂P) ≤
        (∫ omega, f omega ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
          (∫ omega, g omega ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_le_Lp_mul_Lq_of_nonneg
        Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
        (by simpa only [ENNReal.ofReal_ofNat] using hfMem)
        (by simpa only [ENNReal.ofReal_ofNat] using hgMem)
    _ = (∫ omega, stoppedValue (doleansDadeExponential M bracket) tau omega ∂P) ^
          (1 / 2 : ℝ) *
        (∫ omega, Real.exp (stoppedValue bracket tau omega / 2) ∂P) ^
          (1 / 2 : ℝ) := by
      congr 2
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => by
          dsimp only [f]
          rw [Real.rpow_two, Real.sq_sqrt]
          unfold stoppedValue doleansDadeExponential
          positivity
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => by
          dsimp only [g]
          rw [Real.rpow_two, pow_two, ← Real.exp_add]
          congr 1
          ring

theorem NovikovCondition.integrable_stoppedValue_exp_half
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
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    {tau : W → WithTop ℝ≥0} (htau : IsStoppingTime 𝒱 tau)
    (hbound : ∀ omega, tau omega ≤ (T : WithTop ℝ≥0)) :
    Integrable (fun omega => Real.exp (stoppedValue M tau omega / 2)) P ∧
      (∫ omega, Real.exp (stoppedValue M tau omega / 2) ∂P) ≤
        Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P) := by
  have hE :=
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
      hlocalQV hMcont hbracket hbracketPath hMzero hbracketZero
  have hEadapt : StronglyAdapted 𝒱 (doleansDadeExponential M bracket) :=
    stronglyAdapted_doleansDadeExponential hMadapt hbracket
  have hEcont (omega : W) : Continuous
      (fun t => doleansDadeExponential M bracket t omega) :=
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hEzero : doleansDadeExponential M bracket 0 = fun _ => 1 := by
    funext omega
    exact doleansDadeExponential_zero M bracket omega
      (hMzero omega) (hbracketZero omega)
  have hEzeroInt : Integrable (doleansDadeExponential M bracket 0) P := by
    rw [hEzero]
    exact integrable_const 1
  have hEbound := hE.1.integrable_stoppedValue_and_integral_le_zero_of_nonneg
    hEadapt hEcont (fun _ _ => (Real.exp_pos _).le) hEzeroInt htau T hbound
  have hbracketStoppedMeas :
      AEStronglyMeasurable (stoppedValue bracket tau) P := by
    exact ((stronglyMeasurable_stoppedValue_of_le
      (hbracket.isStronglyProgressive_of_continuous
        (fun omega => (hbracketPath omega).1)) htau hbound).mono
          (𝒱.le T)).aestronglyMeasurable
  have hbracketStoppedInt : Integrable
      (fun omega => Real.exp (stoppedValue bracket tau omega / 2)) P := by
    apply hN.mono'
    · have hscaled : AEStronglyMeasurable
          (fun omega => (1 / 2 : ℝ) * stoppedValue bracket tau omega) P :=
        hbracketStoppedMeas.const_mul (1 / 2 : ℝ)
      exact Real.continuous_exp.comp_aestronglyMeasurable <| by
        simpa [div_eq_mul_inv, mul_comm] using hscaled
    · exact Filter.Eventually.of_forall fun omega => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply (hbracketPath omega).2
        apply WithTop.coe_le_coe.mp
        have hne : tau omega ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top (hbound omega)
        rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop (tau omega) hne]
        exact hbound omega
  have hCS :=
    integrable_stoppedValue_exp_half_and_integral_le_doleansDade_bracket
      M bracket tau hEbound.1 hbracketStoppedMeas hbracketStoppedInt
  refine ⟨hCS.1, hCS.2.trans ?_⟩
  have hEIntegralNonneg :
      0 ≤ ∫ omega, stoppedValue (doleansDadeExponential M bracket) tau omega ∂P :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt
          (∫ omega, stoppedValue (doleansDadeExponential M bracket) tau omega ∂P) *
        Real.sqrt
          (∫ omega, Real.exp (stoppedValue bracket tau omega / 2) ∂P) ≤
      1 * Real.sqrt
          (∫ omega, Real.exp (stoppedValue bracket tau omega / 2) ∂P) :=
        mul_le_mul_of_nonneg_right
          (Real.sqrt_le_one.mpr (by simpa [hEzero] using hEbound.2))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt
          (∫ omega, Real.exp (stoppedValue bracket tau omega / 2) ∂P) := one_mul _
    _ ≤ Real.sqrt (∫ omega, Real.exp (bracket T omega / 2) ∂P) := by
      apply Real.sqrt_le_sqrt
      apply integral_mono hbracketStoppedInt hN
      intro omega
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply (hbracketPath omega).2
      apply WithTop.coe_le_coe.mp
      have hne : tau omega ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (hbound omega)
      rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop (tau omega) hne]
      exact hbound omega

/-- A nonnegative continuous local martingale whose deterministic-time
expectations equal its initial expectation is a genuine martingale. -/
theorem IsLocalMartingale.martingale_of_nonneg_of_integral_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    {M : ℝ≥0 → W → ℝ} (hM : IsLocalMartingale M 𝒱 P)
    (hMadapt : StronglyAdapted 𝒱 M)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hMnonneg : ∀ t omega, 0 ≤ M t omega)
    (hMzeroInt : Integrable (M 0) P)
    (hintegral : ∀ t, (∫ omega, M t omega ∂P) = ∫ omega, M 0 omega ∂P) :
    Martingale M 𝒱 P := by
  classical
  have hMint (t : ℝ≥0) : Integrable (M t) P :=
    (hM.integrable_and_integral_le_zero_of_nonneg
      hMadapt hMnonneg hMzeroInt t).1
  have hseteq {s t : ℝ≥0} (hst : s ≤ t) (A : Set W)
      (hA : MeasurableSet[𝒱 s] A) :
      (∫ omega in A, M s omega ∂P) = ∫ omega in A, M t omega ∂P := by
    let tau : W → WithTop ℝ≥0 :=
      Aᶜ.piecewise (fun _ => s) (fun _ => t)
    have htau : IsStoppingTime 𝒱 tau :=
      isStoppingTime_piecewise_const hst hA.compl
    have hbound : ∀ omega, tau omega ≤ (t : WithTop ℝ≥0) := by
      intro omega
      by_cases hmem : omega ∈ Aᶜ
      · simp only [tau, Set.piecewise, hmem, ite_eq_left]
        exact_mod_cast hst
      · simp only [tau, Set.piecewise, hmem]
        exact le_rfl
    have hstop := hM.integrable_stoppedValue_and_integral_le_zero_of_nonneg
      hMadapt hMcont hMnonneg hMzeroInt htau t hbound
    have hstopEq : stoppedValue M tau =
        Aᶜ.indicator (M s) + A.indicator (M t) := by
      rw [show tau = Aᶜ.piecewise
          (fun _ => (s : WithTop ℝ≥0)) (fun _ => (t : WithTop ℝ≥0)) by rfl,
        stoppedValue_piecewise_const']
      simp only [compl_compl]
    have hwholeS : (∫ omega, M s omega ∂P) =
        (∫ omega in Aᶜ, M s omega ∂P) + ∫ omega in A, M s omega ∂P := by
      calc
        (∫ omega, M s omega ∂P) = ∫ omega,
            Aᶜ.indicator (M s) omega + A.indicator (M s) omega ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun omega => by
            simp only [Set.indicator_apply]
            by_cases hmem : omega ∈ A
            · simp [hmem]
            · simp [hmem]
        _ = (∫ omega, Aᶜ.indicator (M s) omega ∂P) +
              ∫ omega, A.indicator (M s) omega ∂P :=
          integral_add ((hMint s).indicator ((𝒱.le s A hA).compl))
            ((hMint s).indicator (𝒱.le s A hA))
        _ = (∫ omega in Aᶜ, M s omega ∂P) +
              ∫ omega in A, M s omega ∂P := by
          rw [integral_indicator ((𝒱.le s A hA).compl),
            integral_indicator (𝒱.le s A hA)]
    have hstopIntegral :
        (∫ omega, stoppedValue M tau omega ∂P) =
          (∫ omega in Aᶜ, M s omega ∂P) + ∫ omega in A, M t omega ∂P := by
      calc
        (∫ omega, stoppedValue M tau omega ∂P) = ∫ omega,
            (Aᶜ.indicator (M s) + A.indicator (M t)) omega ∂P := by rw [hstopEq]
        _ = (∫ omega, Aᶜ.indicator (M s) omega ∂P) +
              ∫ omega, A.indicator (M t) omega ∂P := by
          simpa only [Pi.add_apply] using integral_add
            ((hMint s).indicator ((𝒱.le s A hA).compl))
            ((hMint t).indicator (𝒱.le s A hA))
        _ = (∫ omega in Aᶜ, M s omega ∂P) +
              ∫ omega in A, M t omega ∂P := by
          rw [integral_indicator ((𝒱.le s A hA).compl),
            integral_indicator (𝒱.le s A hA)]
    have hle : (∫ omega in A, M t omega ∂P) ≤
        ∫ omega in A, M s omega ∂P := by
      rw [hstopIntegral, ← hintegral s, hwholeS] at hstop
      exact (add_le_add_iff_left _).mp hstop.2
    have hcompl : MeasurableSet[𝒱 s] Aᶜ := hA.compl
    let sigma : W → WithTop ℝ≥0 :=
      A.piecewise (fun _ => s) (fun _ => t)
    have hsigma : IsStoppingTime 𝒱 sigma :=
      isStoppingTime_piecewise_const hst hA
    have hsigmaBound : ∀ omega, sigma omega ≤ (t : WithTop ℝ≥0) := by
      intro omega
      by_cases hmem : omega ∈ A
      · simp only [sigma, Set.piecewise, hmem, ite_eq_left]
        exact_mod_cast hst
      · simp only [sigma, Set.piecewise, hmem]
        exact le_rfl
    have hstopComp := hM.integrable_stoppedValue_and_integral_le_zero_of_nonneg
      hMadapt hMcont hMnonneg hMzeroInt hsigma t hsigmaBound
    have hstopCompEq : stoppedValue M sigma =
        A.indicator (M s) + Aᶜ.indicator (M t) := by
      rw [show sigma = A.piecewise
          (fun _ => (s : WithTop ℝ≥0)) (fun _ => (t : WithTop ℝ≥0)) by rfl,
        stoppedValue_piecewise_const']
    have hwholeT : (∫ omega, M t omega ∂P) =
        (∫ omega in A, M t omega ∂P) + ∫ omega in Aᶜ, M t omega ∂P := by
      calc
        (∫ omega, M t omega ∂P) = ∫ omega,
            A.indicator (M t) omega + Aᶜ.indicator (M t) omega ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun omega => by
            simp only [Set.indicator_apply]
            by_cases hmem : omega ∈ A
            · simp [hmem]
            · simp [hmem]
        _ = (∫ omega, A.indicator (M t) omega ∂P) +
              ∫ omega, Aᶜ.indicator (M t) omega ∂P :=
          integral_add ((hMint t).indicator (𝒱.le s A hA))
            ((hMint t).indicator ((𝒱.le s A hA).compl))
        _ = (∫ omega in A, M t omega ∂P) +
              ∫ omega in Aᶜ, M t omega ∂P := by
          rw [integral_indicator (𝒱.le s A hA),
            integral_indicator ((𝒱.le s A hA).compl)]
    have hstopCompIntegral :
        (∫ omega, stoppedValue M sigma omega ∂P) =
          (∫ omega in A, M s omega ∂P) + ∫ omega in Aᶜ, M t omega ∂P := by
      calc
        (∫ omega, stoppedValue M sigma omega ∂P) = ∫ omega,
            (A.indicator (M s) + Aᶜ.indicator (M t)) omega ∂P := by
          rw [hstopCompEq]
        _ = (∫ omega, A.indicator (M s) omega ∂P) +
              ∫ omega, Aᶜ.indicator (M t) omega ∂P := by
          simpa only [Pi.add_apply] using integral_add
            ((hMint s).indicator (𝒱.le s A hA))
            ((hMint t).indicator ((𝒱.le s A hA).compl))
        _ = (∫ omega in A, M s omega ∂P) +
              ∫ omega in Aᶜ, M t omega ∂P := by
          rw [integral_indicator (𝒱.le s A hA),
            integral_indicator ((𝒱.le s A hA).compl)]
    have hge : (∫ omega in A, M s omega ∂P) ≤
        ∫ omega in A, M t omega ∂P := by
      rw [hstopCompIntegral, ← hintegral t, hwholeT] at hstopComp
      exact (add_le_add_iff_right _).mp hstopComp.2
    exact le_antisymm hge hle
  apply martingale_iff.mpr
  constructor
  · have hnegSub : Submartingale (-M) 𝒱 P := by
      apply submartingale_of_setIntegral_le hMadapt.neg (fun t => (hMint t).neg)
      intro s t hst A hA
      simpa only [Pi.neg_apply, integral_neg, neg_le_neg_iff] using
        (hseteq hst A hA).symm.le
    simpa only [neg_neg] using hnegSub.neg
  · apply submartingale_of_setIntegral_le hMadapt hMint
    intro s t hst A hA
    exact (hseteq hst A hA).le

end StochasticCalculus
