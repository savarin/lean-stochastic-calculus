/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.DoleansDadeExponential

/-!
# Martingality of the stochastic exponential

The general Itô expansion of `exp` applied to the compensated logarithm,
convergence of the left sums to the integral candidate, and the martingale
property of the exponential localized at paired continuous exit times.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The second state derivative of the exponential test function is itself. -/
theorem itoSpaceSecondDerivative_exp_state (s x : ℝ) :
    itoSpaceSecondDerivative (fun _ x => Real.exp x) s x = Real.exp x := by
  simp [itoSpaceSecondDerivative, Real.deriv_exp]

/-- The full quadratic term in Taylor's formula for the compensated
logarithm converges to the bracket Stieltjes integral.  The proof combines
finite-variation removal with the martingale-only weighted-bracket theorem.
-/
theorem
    generalItoQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoQuadraticApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (stieltjesBracketIntegral
        (fun s omega ↦ (1 / 2 : ℝ) *
          doleansDadeExponential M bracket s omega)
        bracket t) := by
  let A : ℝ≥0 → W → ℝ :=
    fun s omega ↦ (-1 / 2 : ℝ) * bracket s omega
  have hsecond : Continuous (fun p : ℝ × ℝ ↦
      itoSpaceSecondDerivative (fun _ x ↦ Real.exp x) p.1 p.2) := by
    simp only [itoSpaceSecondDerivative_exp_state]
    fun_prop
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hAmeas : ∀ s, AEStronglyMeasurable (A s) P := fun s ↦
    aestronglyMeasurable_const.mul (hbracketMeas s)
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hAqv : ∀ᵐ omega ∂P, Filter.Tendsto
      (fun n ↦ quadraticVariationApprox A t (n + 1) omega)
      Filter.atTop (nhds 0) := by
    filter_upwards [hbracketPath] with omega homega
    have hzero :=
      tendsto_quadraticVariationApprox_zero_of_continuous_monotone
        bracket t omega homega.1 homega.2
    simpa only [A, quadraticVariationApprox_const_mul, mul_zero] using
      hzero.const_mul ((-1 / 2 : ℝ) ^ 2)
  have hlogCont : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ doleansDadeLog M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact hMomega.sub (continuous_const.mul hbracketOmega.1)
  have hself : IsContinuousProcessModification
      (doleansDadeLog M bracket) (doleansDadeLog M bracket) P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hlogCont⟩
  have herror :=
    generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero
      (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket)
      A M hlogMeas hAmeas hMmeas t (bracket t) hAqv
      (hbefore.toProcess t)
      (hself.uniformPartition_secondDerivative_bounded
        (fun _ x ↦ Real.exp x) hsecond t)
  have hsumEq : (fun s omega ↦ A s omega + M s omega) =
      doleansDadeLog M bracket := by
    funext s omega
    simp only [A, doleansDadeLog]
    ring
  rw [hsumEq] at herror
  have herrorActual : TendstoInMeasure P
      (fun n omega ↦
        generalItoQuadraticApprox (fun _ x ↦ Real.exp x)
            (doleansDadeLog M bracket) t (n + 1) omega -
          generalItoMixedQuadraticApprox (fun _ x ↦ Real.exp x)
            (doleansDadeLog M bracket) M t (n + 1) omega)
      Filter.atTop (fun _ ↦ 0) := by
    simpa only [generalItoQuadraticApprox,
      generalItoMixedQuadraticApprox] using herror
  have hmartingale :=
    generalItoMixedQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
      hM hbracket hMcont hbracketPath hbefore t
  have hsum := herrorActual.add_real_noMeas hmartingale
  apply hsum.congr
  · intro n
    filter_upwards with omega
    ring
  · filter_upwards with omega
    ring

/-- The first-order Taylor sum against the compensated logarithm converges
to the exponential endpoint increment minus its bracket correction. -/
theorem generalItoSpace_doleansDadeLog_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoSpaceApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (fun omega ↦
        doleansDadeExponential M bracket t omega -
          doleansDadeExponential M bracket 0 omega -
          stieltjesBracketIntegral
            (fun s omega ↦ (1 / 2 : ℝ) *
              doleansDadeExponential M bracket s omega)
            bracket t omega) := by
  let Q : W → ℝ := stieltjesBracketIntegral
    (fun s omega ↦ (1 / 2 : ℝ) *
      doleansDadeExponential M bracket s omega) bracket t
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hEmeas : ∀ s,
      AEStronglyMeasurable (doleansDadeExponential M bracket s) P :=
    fun s ↦ Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s)
  have hendpoint : AEStronglyMeasurable
      (fun omega ↦ Real.exp (doleansDadeLog M bracket t omega) -
        Real.exp (doleansDadeLog M bracket 0 omega)) P := by
    change AEStronglyMeasurable
      (doleansDadeExponential M bracket t -
        doleansDadeExponential M bracket 0) P
    exact (hEmeas t).sub (hEmeas 0)
  have htimeZero (n : ℕ) (omega : W) :
      generalItoTimeApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t n omega = 0 := by
    unfold generalItoTimeApprox
    simp only [itoTimeDerivative_exp_state, zero_mul, Finset.sum_const_zero]
  have htime : TendstoInMeasure P
      (fun n ↦ generalItoTimeApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_const.congr
        (Filter.Eventually.of_forall fun omega ↦ (htimeZero (n + 1) omega).symm)
    · filter_upwards with omega
      simpa only [htimeZero] using
        (tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0))
  have hquadratic : TendstoInMeasure P
      (fun n ↦ generalItoQuadraticApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1)) Filter.atTop Q := by
    simpa only [Q] using
      generalItoQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
        hM hbracket hMcont hbracketPath hbefore t
  have hstate :=
    doleansDadeLog_exp_stateTaylorRemainder_tendstoInMeasure
      hM hbracket hMcont hbracketPath hbefore t
  have hremainderEq (n : ℕ) (omega : W) :
      generalItoRemainderApprox (fun _ x ↦ Real.exp x)
          (doleansDadeLog M bracket) t n omega =
        itoStateTaylorRemainderApprox Real.exp
          (doleansDadeLog M bracket) t n omega := by
    unfold generalItoRemainderApprox itoStateTaylorRemainderApprox
    apply Finset.sum_congr rfl
    intro i _hi
    unfold generalItoRemainderIncrement itoStateTaylorRemainder
    simp only [itoTimeDerivative_exp_state, itoSpaceDerivative_exp_state,
      itoSpaceSecondDerivative_exp_state, Real.deriv_exp, zero_mul, sub_zero]
  have hremainder : TendstoInMeasure P
      (fun n ↦ generalItoRemainderApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
    apply hstate.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega ↦
      (hremainderEq (n + 1) omega).symm
  apply (generalIto_formula_ae_iff_space_limit
    (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) t
    (fun _ ↦ 0)
    (fun omega ↦
      doleansDadeExponential M bracket t omega -
        doleansDadeExponential M bracket 0 omega - Q omega)
    Q hendpoint htime hquadratic hremainder).2
  filter_upwards with omega
  simp only [doleansDadeExponential]
  ring

/-- The genuine uncapped Doléans left sums converge in probability to the
stochastic-exponential endpoint increment.  The bracket Stieltjes term from
Taylor's formula cancels exactly with the finite-variation part of the
compensated logarithm. -/
theorem doleansDadeLeftSumProcess_terminal_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket t n t)
      Filter.atTop
      (fun omega ↦ doleansDadeExponential M bracket t omega -
        doleansDadeExponential M bracket 0 omega) := by
  let H : ℝ≥0 → W → ℝ := fun s omega ↦
    (1 / 2 : ℝ) * doleansDadeExponential M bracket s omega
  let Q : W → ℝ := stieltjesBracketIntegral H bracket t
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hHmeas : ∀ s, AEStronglyMeasurable (H s) P := by
    intro s
    exact aestronglyMeasurable_const.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s))
  have hHcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ H s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact continuous_const.mul
      (continuous_doleansDadeExponential M bracket omega
        hMomega hbracketOmega.1)
  have hspace : TendstoInMeasure P
      (fun n ↦ generalItoSpaceApprox (fun _ x ↦ Real.exp x)
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop
      (fun omega ↦
        doleansDadeExponential M bracket t omega -
          doleansDadeExponential M bracket 0 omega - Q omega) := by
    simpa only [Q, H] using
      generalItoSpace_doleansDadeLog_tendstoInMeasure
        hM hbracket hMcont hbracketPath hbefore t
  have hbracketSum : TendstoInMeasure P
      (fun n ↦ bracketWeightedLeftSum H bracket t (n + 1))
      Filter.atTop Q := by
    exact bracketWeightedLeftSum_tendstoInMeasure H bracket
      hHmeas hbracketMeas hHcont hbracketPath t
  have hsum := hspace.add_real_noMeas hbracketSum
  apply hsum.congr
  · intro n
    filter_upwards with omega
    rw [doleansDadeLeftSumProcess_terminal]
    unfold generalItoSpaceApprox bracketWeightedLeftSum H
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [itoSpaceDerivative_exp_state, doleansDadeExponential,
      doleansDadeLog]
    ring
  · filter_upwards with omega
    ring

/-- With the standard zero initial conditions, the terminal left sums
converge directly to the canonical integral candidate `ℰ(M) - 1`. -/
theorem
    doleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket t n t)
      Filter.atTop (doleansDadeIntegralCandidate M bracket t) := by
  have hterminal := doleansDadeLeftSumProcess_terminal_tendstoInMeasure
    hM hbracket hMcont hbracketPath hbefore t
  apply hterminal.congr_right
  filter_upwards [hMzero, hbracketZero]
    with omega hMzeroOmega hbracketZeroOmega
  rw [doleansDadeExponential_zero M bracket omega
    hMzeroOmega hbracketZeroOmega]
  rfl

/-- On one fixed horizon, the coherent uncapped left-sum processes converge
at every observation time to the canonical integral candidate stopped at
that horizon. -/
theorem doleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ doleansDadeLeftSumProcess M bracket T n t)
      Filter.atTop
      (doleansDadeIntegralCandidate M bracket (min T t)) := by
  let Ms : ℝ≥0 → W → ℝ := fun s omega ↦ M (min s t) omega
  let As : ℝ≥0 → W → ℝ :=
    fun s omega ↦ bracket (min s t) omega
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hMsadapt : StronglyAdapted 𝒱 Ms := by
    intro s
    exact (hM (min s t)).mono (𝒱.mono (min_le_left s t))
  have hAsadapt : StronglyAdapted 𝒱 As := by
    intro s
    exact (hbracket (min s t)).mono (𝒱.mono (min_le_left s t))
  have hMscont : ∀ᵐ omega ∂P, Continuous (fun s ↦ Ms s omega) := by
    filter_upwards [hMcont] with omega homega
    exact homega.comp (continuous_id.min continuous_const)
  have hAspath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ As s omega) ∧
        Monotone (fun s ↦ As s omega) := by
    filter_upwards [hbracketPath] with omega homega
    refine ⟨homega.1.comp (continuous_id.min continuous_const), ?_⟩
    exact homega.2.comp fun _ _ hab ↦ min_le_min hab le_rfl
  have hbeforeStop : HasQuadraticVariationBeforeStopProcessInProbability
      Ms As P := by
    simpa only [Ms, As] using hbefore.stop hMmeas hMcont t
  have hMsZero : Ms 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hMzero] with omega homega
    change M (min 0 t) omega = 0
    have hz : min (0 : ℝ≥0) t = 0 :=
      min_eq_left (show (0 : ℝ≥0) ≤ t by exact bot_le)
    rw [hz]
    exact homega
  have hAsZero : As 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hbracketZero] with omega homega
    change bracket (min 0 t) omega = 0
    have hz : min (0 : ℝ≥0) t = 0 :=
      min_eq_left (show (0 : ℝ≥0) ≤ t by exact bot_le)
    rw [hz]
    exact homega
  have hterminal :=
    doleansDadeLeftSumProcess_terminal_tendstoInMeasure_integralCandidate
      hMsadapt hAsadapt hMscont hAspath hbeforeStop hMsZero hAsZero T
  have hsource := hterminal.congr_left fun n ↦
    Filter.Eventually.of_forall fun omega ↦ by
      exact (doleansDadeLeftSumProcess_eq_stopped_terminal
        M bracket T n t omega).symm
  apply hsource.congr_right
  exact Filter.Eventually.of_forall fun omega ↦ rfl

/-- The bounded diagonal Doléans approximations inherit the coherent
common-horizon convergence of the uncapped left sums. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ cappedDoleansDadeLeftSumProcess M bracket T n t)
      Filter.atTop
      (doleansDadeIntegralCandidate M bracket (min T t)) := by
  apply tendstoInMeasure_cappedDoleansDadeLeftSumProcess_of_uncapped
    hM hbracket hMcont (hbracketPath.mono fun _ h ↦ h.1) T t
  exact doleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
    hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero T t

/-- The coherent capped Doléans approximations may be evaluated at every
fixed paired dyadic exit.  This is the finite-range random-stopping form of
the general Itô convergence theorem. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedDyadicExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R : ℝ≥0) (m : ℕ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (pairedDyadicHittingTimeNNReal M
          (doleansDadeExponential M bracket) H K R m) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (pairedDyadicHittingTimeNNReal M
          (doleansDadeExponential M bracket) H K R m) t) := by
  apply tendstoInMeasure_localizingStoppedProcess_of_finiteRange
    ((Finset.range (2 ^ m + 1)).image
      (uniformPartitionTime H (2 ^ m)))
  · exact pairedDyadicHittingTimeNNReal_mem_rangeFinset M
      (doleansDadeExponential M bracket) H K R m
  · intro s
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_integralCandidate_stop
        hM hbracket hMcont hbracketPath hbefore hMzero hbracketZero T s

/-- Uniform-in-grid convergence in probability for replacing a paired
continuous exit by its dyadic approximants is sufficient for convergence at
the continuous exit.  This probability-estimate form avoids the stronger requirement of a
pointwise error majorant. -/
theorem
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ omega,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ ↦ 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ ↦ 0)
    (T H K R t : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega))
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ delta : ℝ≥0∞, 0 < delta →
        ∃ N, ∀ m, N ≤ m → ∀ n,
          P {omega | epsilon ≤
            ‖localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (fun omega => min (continuousExitTime M H K omega)
                  (continuousExitTime
                    (doleansDadeExponential M bracket) H R omega))
                t omega -
              localizingStoppedProcess
                (cappedDoleansDadeLeftSumProcess M bracket T n)
                (pairedDyadicHittingTimeNNReal M
                  (doleansDadeExponential M bracket) H K R m)
                t omega‖} ≤ delta) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let Y : ℝ≥0 → W → ℝ :=
    fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have hYadapt : StronglyAdapted 𝒱 Y := by
    intro s
    exact (stronglyAdapted_doleansDadeIntegralCandidate
      hM hbracket (min T s)).mono (𝒱.mono (min_le_right T s))
  have hYcont : ∀ omega, Continuous (fun s => Y s omega) := by
    intro omega
    exact (continuous_doleansDadeIntegralCandidate M bracket omega
      (hMcont omega) (hbracketPath omega).1).comp
        (continuous_const.min continuous_id)
  apply tendstoInMeasure_of_uniform_approximation_in_measure
    (fm := fun m n => localizingStoppedProcess
      (cappedDoleansDadeLeftSumProcess M bracket T n)
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
    (gm := fun m => localizingStoppedProcess Y
      (pairedDyadicHittingTimeNNReal M E H K R m) t)
  · exact happrox
  · intro m
    exact
      cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedDyadicExit
        hM hbracket (Filter.Eventually.of_forall hMcont)
        (Filter.Eventually.of_forall hbracketPath) hbefore hMzero
        hbracketZero T H K R m t
  · exact tendstoInMeasure_localizingStoppedProcess_pairedDyadic_of_pos
      hYadapt hYcont hM hEadapt H K R hpos t

/-- For a continuous martingale, nested continuous exits discharge the
uniform dyadic-stop approximation estimate.  The inner-to-outer capped error
vanishes in `L²`, while the event on which removing the outer cap changes the
stop has probability tending to zero. -/
theorem cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : M 0 =ᵐ[P] fun _ => 0)
    (hbracketZero : bracket 0 =ᵐ[P] fun _ => 0)
    (T H K R t : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    TendstoInMeasure P
      (fun n => localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega)) t)
      Filter.atTop
      (localizingStoppedProcess
        (fun s omega => doleansDadeIntegralCandidate M bracket (min T s) omega)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega)) t) := by
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H (K + 1) omega)
      (continuousExitTime E H (R + 1) omega)
  let sigma : ℕ → W → WithTop ℝ≥0 :=
    pairedDyadicHittingTimeNNReal M E H K R
  let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
    min (sigma m omega) (theta omega)
  let X : ℕ → ℝ≥0 → W → ℝ := fun n =>
    cappedDoleansDadeLeftSumProcess M bracket T n
  let B : ℕ → ℝ≥0∞ := fun m => (R + 1) * eLpNorm
    ((localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) T -
      (localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) 0) 2 P
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hBtend : Tendsto B Filter.atTop (nhds 0) := by
    dsimp only [B, tau, theta, rho, sigma, E]
    exact tendsto_outerCappedDyadic_doleans_error_bound
      (P := P) hM.stronglyAdapted hbracket hMcont
        (fun omega => (hbracketPath omega).1)
        H K R (K + 1) (R + 1) T
        (le_add_right le_rfl) (le_add_right le_rfl) hpos
  have hbound : ∀ m n,
      eLpNorm
        (localizingStoppedProcess (X n) tau t -
          localizingStoppedProcess (X n) (rho m) t) 2 P ≤ B m := by
    intro m n
    dsimp only [X, tau, rho, sigma, theta, B, E]
    exact eLpNorm_pairedExit_sub_outerCappedDyadic_cappedDoleans_le
      hM hMcont hbracket (fun omega => (hbracketPath omega).1)
        T H K R (K + 1) (R + 1)
        (le_add_right le_rfl) (le_add_right le_rfl) m n t
  have hcapApprox := uniform_approximation_in_measure_of_eLpNorm
    hBtend hbound
  have hexception := tendsto_measure_outerContinuousExit_lt_pairedDyadic
    (P := P) hM.stronglyAdapted hEadapt hMcont hEcont
      H K R (K + 1) (R + 1) hpos (lt_add_one K) (lt_add_one R)
  apply
    cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit_of_uniform_error
      hM.stronglyAdapted hbracket hMcont hbracketPath hbefore hMzero
        hbracketZero T H K R t hpos
  intro epsilon hepsilon delta hdelta
  have hdeltaHalf : 0 < delta / 2 :=
    ENNReal.div_pos hdelta.ne' ENNReal.ofNat_ne_top
  obtain ⟨Ncap, hNcap⟩ :=
    hcapApprox epsilon hepsilon (delta / 2) hdeltaHalf
  rw [ENNReal.tendsto_atTop_zero] at hexception
  obtain ⟨Nexception, hNexception⟩ :=
    hexception (delta / 2) hdeltaHalf
  refine ⟨max Ncap Nexception, fun m hm n => ?_⟩
  have hcap := hNcap m (le_trans (le_max_left _ _) hm) n
  have hexc := hNexception m (le_trans (le_max_right _ _) hm)
  calc
    P {omega | epsilon ≤
        ‖localizingStoppedProcess (X n) tau t omega -
          localizingStoppedProcess (X n) (sigma m) t omega‖} ≤
      P ({omega | epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖} ∪
        {omega | theta omega < sigma m omega}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_contra hnot
      push Not at hnot
      have hstop : rho m omega = sigma m omega := by
        dsimp only [rho]
        rw [min_eq_left hnot.2]
      have hlocal := localizingStoppedProcess_congr_stop_at
        (X n) (rho m) (sigma m) t omega hstop
      have hlarge : epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖ := by
        rw [hlocal]
        exact homega
      exact (not_lt_of_ge hlarge) hnot.1
    _ ≤ P {omega | epsilon ≤
          ‖localizingStoppedProcess (X n) tau t omega -
            localizingStoppedProcess (X n) (rho m) t omega‖} +
        P {omega | theta omega < sigma m omega} := measure_union_le _ _
    _ ≤ delta / 2 + delta / 2 := add_le_add hcap hexc
    _ = delta := ENNReal.add_halves delta

/-- If a positive stopping rule is bounded by `H`, localizing a process
capped at `H` gives the same result as localizing the original process. -/
theorem localizingStoppedProcess_min_horizon_eq_of_le
    {W : Type*} (X : ℝ≥0 → W → ℝ) (H : ℝ≥0)
    (tau : W → WithTop ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega)
    (hle : ∀ omega, tau omega ≤ (H : WithTop ℝ≥0)) :
    localizingStoppedProcess (fun s omega => X (min H s) omega) tau =
      localizingStoppedProcess X tau := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
    hpos omega
  let sTop := min (t : WithTop ℝ≥0) (tau omega)
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X (min H sTop.untopA)) omega =
    {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X sTop.untopA) omega
  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  have hs_ne : sTop ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hscoe : ((sTop.untopA : ℝ≥0) : WithTop ℝ≥0) = sTop := by
    rw [WithTop.untopA_eq_untop hs_ne]
    exact WithTop.coe_untop sTop hs_ne
  have hsH : sTop.untopA ≤ H := by
    apply WithTop.coe_le_coe.mp
    rw [hscoe]
    exact (min_le_right _ _).trans (hle omega)
  change X (min H sTop.untopA) omega = X sTop.untopA omega
  rw [min_eq_right hsH]

/-- At a positive pair of bounded continuous exits, the normalized
Doleans integral candidate is a genuine martingale.  Nested exit estimates
provide convergence of the capped left sums, and their uniform `L²` bound
provides the Vitali closure. -/
theorem martingale_doleansDadeIntegralCandidate_pairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (H K R : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    Martingale
      (localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega))) 𝒱 P := by
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let X : ℕ → ℝ≥0 → W → ℝ := fun n =>
    cappedDoleansDadeLeftSumProcess M bracket H n
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have htau : IsStoppingTime 𝒱 tau :=
    (isStoppingTime_continuousExitTime_of_stronglyAdapted
      hM.stronglyAdapted H K).min
      (isStoppingTime_continuousExitTime_of_stronglyAdapted hEadapt H R)
  have hXmart (n : ℕ) : Martingale (X n) 𝒱 P := by
    dsimp only [X, cappedDoleansDadeLeftSumProcess]
    exact martingale_uniformAdaptedMartingaleLeftSumProcess hM
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) (n + 1)
      (norm_cappedDoleansDadeExponential_le M bracket (n + 1)) H (n + 1)
  have hXcont (n : ℕ) : ∀ omega, Continuous (fun t => X n t omega) :=
    fun omega => continuous_uniformAdaptedMartingaleLeftSumProcess
      hMcont H (n + 1) omega
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable
    (X := fun n => localizingStoppedProcess (X n) tau)
  · intro n
    exact martingale_localizingStoppedProcess_min_continuousExitTime
      (hXmart n) (hXcont n) hM.stronglyAdapted hEadapt H K R
  · exact stronglyAdapted_localizingStoppedProcess
      (stronglyAdapted_doleansDadeIntegralCandidate
        hM.stronglyAdapted hbracket)
      (fun omega => continuous_doleansDadeIntegralCandidate M bracket omega
        (hMcont omega) (hbracketPath omega).1)
      htau
  · intro t
    have hUI :=
      uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply
        hM hMcont hbracket (fun omega => (hbracketPath omega).1)
          H H K H R t
    apply hUI.ae_eq
    intro n
    have heq := localizingStoppedProcess_localizingStoppedProcess (X n)
      (continuousExitTime M H K) (continuousExitTime E H R)
    exact Filter.Eventually.of_forall fun omega =>
      congrFun (congrFun heq t) omega
  · intro t
    have hraw := cappedDoleansDadeLeftSumProcess_tendstoInMeasure_pairedExit
      hM hMcont hbracket hbracketPath hbefore
        (Filter.Eventually.of_forall hMzero)
        (Filter.Eventually.of_forall hbracketZero)
        H H K R t hpos
    have hle : ∀ omega, tau omega ≤ (H : WithTop ℝ≥0) := by
      intro omega
      exact (min_le_left _ _).trans (continuousExitTime_le M H K omega)
    have heq := localizingStoppedProcess_min_horizon_eq_of_le
      (doleansDadeIntegralCandidate M bracket) H tau hpos hle
    exact hraw.congr (fun n => Filter.EventuallyEq.rfl)
      (Filter.Eventually.of_forall fun omega =>
        congrFun (congrFun heq t) omega)

/-- Localizing a Doléans exponential is the exponential of the two localized
inputs on the event where the stopping rule is positive, and zero elsewhere.
This records exactly the exceptional-set convention in Mathlib's `Locally`
predicate. -/
theorem localizingStoppedProcess_doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess (doleansDadeExponential M bracket) tau =
      fun t => {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
        (doleansDadeExponential
          (localizingStoppedProcess M tau)
          (localizingStoppedProcess bracket tau) t) := by
  funext t omega
  by_cases hpos : (⊥ : WithTop ℝ≥0) < tau omega
  · have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    simp only [Set.indicator_of_mem hmem]
    unfold doleansDadeExponential doleansDadeLog
    simp only [Set.indicator_of_mem hmem]
  · have hmem : omega ∉ {omega | (⊥ : WithTop ℝ≥0) < tau omega} := hpos
    unfold localizingStoppedProcess stoppedProcess
    simp only [Set.indicator_of_notMem hmem]

/-- Localization commutes with multiplication by a fixed event indicator. -/
theorem localizingStoppedProcess_indicator
    {W : Type*} (X : ℝ≥0 → W → ℝ) (A : Set W)
    (tau : W → WithTop ℝ≥0) :
    localizingStoppedProcess (fun t => A.indicator (X t)) tau =
      fun t => A.indicator (localizingStoppedProcess X tau t) := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  by_cases hA : omega ∈ A <;>
    by_cases htau : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} <;>
    simp [Set.indicator_apply, hA]

/-- Localizing `1 + X` at an everywhere-positive stopping rule is one plus
the localization of `X`. -/
theorem localizingStoppedProcess_one_add_of_pos
    {W : Type*} (X : ℝ≥0 → W → ℝ) (tau : W → WithTop ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) < tau omega) :
    localizingStoppedProcess (fun t omega => 1 + X t omega) tau =
      fun t omega => 1 + localizingStoppedProcess X tau t omega := by
  funext t omega
  unfold localizingStoppedProcess stoppedProcess
  have hmem : omega ∈ {omega | (⊥ : WithTop ℝ≥0) < tau omega} :=
    hpos omega
  let sTop := min (t : WithTop ℝ≥0) (tau omega)
  change {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (fun omega => 1 + X sTop.untopA omega) omega =
    1 + {omega | (⊥ : WithTop ℝ≥0) < tau omega}.indicator
      (X sTop.untopA) omega
  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]

/-- The stochastic exponential itself, rather than only its integral
candidate, is a genuine martingale after a positive pair of bounded exits. -/
theorem martingale_doleansDadeExponential_pairedContinuousExit
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (H K R : ℝ≥0)
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    Martingale
      (localizingStoppedProcess (doleansDadeExponential M bracket)
        (fun omega => min (continuousExitTime M H K omega)
          (continuousExitTime
            (doleansDadeExponential M bracket) H R omega))) 𝒱 P := by
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime (doleansDadeExponential M bracket) H R omega)
  have hI := martingale_doleansDadeIntegralCandidate_pairedContinuousExit
    hM hMcont hbracket hbracketPath hbefore hMzero hbracketZero
      H K R hpos
  have hone : Martingale (fun _ : ℝ≥0 => fun _ : W => (1 : ℝ)) 𝒱 P :=
    martingale_const_fun 𝒱 P stronglyMeasurable_const (integrable_const 1)
  have hadd := hone.add hI
  change Martingale ((fun _ : ℝ≥0 => fun _ : W => (1 : ℝ)) +
    localizingStoppedProcess (doleansDadeIntegralCandidate M bracket) tau) 𝒱 P
      at hadd
  have hadd' : Martingale (fun t omega =>
      1 + localizingStoppedProcess (doleansDadeIntegralCandidate M bracket)
        tau t omega) 𝒱 P := hadd
  have heq := localizingStoppedProcess_one_add_of_pos
    (doleansDadeIntegralCandidate M bracket) tau hpos
  rw [← heq] at hadd'
  change Martingale (localizingStoppedProcess
    (doleansDadeExponential M bracket) tau) 𝒱 P
  have hEeq : doleansDadeExponential M bracket =
      fun t omega => 1 + doleansDadeIntegralCandidate M bracket t omega := by
    funext t omega
    simp only [doleansDadeIntegralCandidate]
    ring
  rw [hEeq]
  exact hadd'

/-- The Doléans--Dade theorem from a common martingale/bracket localizing
sequence and the localization-stable quadratic-variation contract used by
the proof.

Along the supplied sequence, each stopped bracket must be the robust
quadratic variation of the corresponding stopped martingale.  The proof puts
a second, bounded paired-exit sequence around each stopped martingale, applies
the genuine-martingale exponential theorem there, and then diagonalizes the
two localization layers. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_common_localizedQV
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (tau : ℕ → W → WithTop ℝ≥0)
    (htau : IsLocalizingSequence 𝒱 tau P)
    (hMmart : ∀ k, Martingale
      (localizingStoppedProcess M (tau k)) 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (hlocalQV : ∀ k,
      HasQuadraticVariationBeforeStopProcessInProbability
        (localizingStoppedProcess M (tau k))
        (localizingStoppedProcess bracket (tau k)) P) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  let N : ℕ → ℝ≥0 → W → ℝ := fun k =>
    localizingStoppedProcess M (tau k)
  let Q : ℕ → ℝ≥0 → W → ℝ := fun k =>
    localizingStoppedProcess bracket (tau k)
  let E := doleansDadeExponential M bracket
  let Ek : ℕ → ℝ≥0 → W → ℝ := fun k =>
    doleansDadeExponential (N k) (Q k)
  let sigma : ℕ → ℕ → W → WithTop ℝ≥0 := fun k =>
    globalPairedContinuousExitSequence (N k) (Ek k)
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketPath omega).1
  have hNmart (k : ℕ) : Martingale (N k) 𝒱 P := by
    exact hMmart k
  have hNcont (k : ℕ) (omega : W) :
      Continuous (fun t => N k t omega) := by
    exact continuous_localizingStoppedProcess hMcont (tau k) omega
  have hQadapt (k : ℕ) : StronglyAdapted 𝒱 (Q k) := by
    exact stronglyAdapted_localizingStoppedProcess hbracket
      (fun omega => (hbracketPath omega).1) (htau.isStoppingTime k)
  have hQcont (k : ℕ) (omega : W) :
      Continuous (fun t => Q k t omega) := by
    exact continuous_localizingStoppedProcess
      (fun omega => (hbracketPath omega).1) (tau k) omega
  have hQmono (k : ℕ) (omega : W) :
      Monotone (fun t => Q k t omega) := by
    exact monotone_localizingStoppedProcess
      (fun omega => (hbracketPath omega).2) (tau k) omega
  have hNzero (k : ℕ) (omega : W) : N k 0 omega = 0 := by
    simp [N, localizingStoppedProcess, stoppedProcess,
      Set.indicator_apply, hMzero]
  have hQzero (k : ℕ) (omega : W) : Q k 0 omega = 0 := by
    simp [Q, localizingStoppedProcess, stoppedProcess,
      Set.indicator_apply, hbracketZero]
  have hEkadapt (k : ℕ) : StronglyAdapted 𝒱 (Ek k) := by
    exact stronglyAdapted_doleansDadeExponential
      (hNmart k).stronglyAdapted (hQadapt k)
  have hEkcont (k : ℕ) (omega : W) :
      Continuous (fun t => Ek k t omega) := by
    exact continuous_doleansDadeExponential (N k) (Q k) omega
      (hNcont k omega) (hQcont k omega)
  have hsigma (k : ℕ) : IsLocalizingSequence 𝒱 (sigma k) P := by
    exact isLocalizingSequence_globalPairedContinuousExit
      (hNmart k).stronglyAdapted (hEkadapt k) (hNcont k) (hEkcont k)
  have hsigmaBound (k j : ℕ) : ∃ T : ℝ≥0, ∀ omega,
      sigma k j omega ≤ (T : WithTop ℝ≥0) := by
    refine ⟨2 ^ j, fun omega => ?_⟩
    exact (min_le_left _ _).trans
      (continuousExitTime_le (N k) (2 ^ j) (j + 2) omega)
  have hmart (k j : ℕ) : Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess E (tau k)) (sigma k j)) 𝒱 P := by
    let H : ℝ≥0 := 2 ^ j
    let R : ℝ≥0 := (j : ℝ≥0) + 2
    have hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
        min (continuousExitTime (N k) H R omega)
          (continuousExitTime (Ek k) H R omega) := by
      intro omega
      apply min_continuousExitTime_pos_of_initial_lt
      · exact hNcont k omega
      · exact hEkcont k omega
      · dsimp only [H]
        positivity
      · rw [hNzero k omega]
        dsimp only [R]
        norm_num only [abs_zero]
        exact_mod_cast (show 0 < j + 2 by omega)
      · dsimp only [Ek]
        rw [doleansDadeExponential_zero (N k) (Q k) omega
          (hNzero k omega) (hQzero k omega)]
        dsimp only [R]
        exact_mod_cast (show 1 < j + 2 by omega)
    have hinner := martingale_doleansDadeExponential_pairedContinuousExit
      (hNmart k) (hNcont k) (hQadapt k)
      (fun omega => ⟨hQcont k omega, hQmono k omega⟩)
      (hlocalQV k) (hNzero k) (hQzero k) H R R hpos
    have hinner' : Martingale
        (localizingStoppedProcess (Ek k) (sigma k j)) 𝒱 P := by
      change Martingale (localizingStoppedProcess (Ek k)
        (fun omega => min (continuousExitTime (N k) H R omega)
          (continuousExitTime (Ek k) H R omega))) 𝒱 P at hinner
      change Martingale (localizingStoppedProcess (Ek k)
        (fun omega => min (continuousExitTime (N k) (2 ^ j) (j + 2) omega)
          (continuousExitTime (Ek k) (2 ^ j) (j + 2) omega))) 𝒱 P
      simpa only [H, R] using hinner
    let A : Set W := {omega | (⊥ : WithTop ℝ≥0) < tau k omega}
    have hA : MeasurableSet[𝒱 0] A := by
      change MeasurableSet[𝒱 0]
        {omega | (⊥ : WithTop ℝ≥0) < tau k omega}
      rw [show (⊥ : WithTop ℝ≥0) =
        ((0 : ℝ≥0) : WithTop ℝ≥0) by simp]
      exact (htau.isStoppingTime k).measurableSet_gt 0
    have hindicator := StochasticCalculus.Martingale.indicator_zero hinner' hA
    have houter := localizingStoppedProcess_doleansDadeExponential
      M bracket (tau k)
    have hdouble := localizingStoppedProcess_indicator
      (Ek k) A (sigma k j)
    rw [houter, hdouble]
    exact hindicator
  have hlocal : IsLocalMartingale E 𝒱 P :=
    isLocalMartingale_of_bounded_double_localization hEcont tau htau
      sigma hsigma hsigmaBound hmart
  exact ⟨hlocal, Filter.Eventually.of_forall hEcont⟩

/-- The proof-independent local-bracket formulation of the Doléans--Dade
theorem.  A pathwise-continuous process with an adapted continuous monotone
local quadratic variation has a continuous-local-martingale stochastic
exponential. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability
      M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0) :
    IsContinuousLocalMartingale
      (doleansDadeExponential M bracket) 𝒱 P := by
  obtain ⟨tau, htau, hMmart, hQV⟩ := hlocalQV
  exact
    isContinuousLocalMartingale_doleansDadeExponential_of_common_localizedQV
      tau htau hMmart hMcont hbracket hbracketPath hMzero hbracketZero hQV

/-- Every deterministic scaling of a process carrying the robust local
quadratic-variation contract has its corresponding scaled Doléans exponential
as a continuous local martingale. -/
theorem
    isContinuousLocalMartingale_doleansDadeExponential_const_mul_of_localQuadraticVariation
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hlocalQV : HasLocalQuadraticVariationProcessInProbability
      M bracket 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ omega,
      Continuous (fun t => bracket t omega) ∧
        Monotone (fun t => bracket t omega))
    (hMzero : ∀ omega, M 0 omega = 0)
    (hbracketZero : ∀ omega, bracket 0 omega = 0)
    (c : ℝ) :
    IsContinuousLocalMartingale
      (doleansDadeExponential
        (fun t omega => c * M t omega)
        (fun t omega => c ^ 2 * bracket t omega)) 𝒱 P := by
  apply
    isContinuousLocalMartingale_doleansDadeExponential_of_localQuadraticVariation
      (hlocalQV.const_mul c)
  · intro omega
    exact continuous_const.mul (hMcont omega)
  · intro t
    exact stronglyMeasurable_const.mul (hbracket t)
  · intro omega
    refine ⟨continuous_const.mul (hbracketPath omega).1, ?_⟩
    intro s t hst
    exact mul_le_mul_of_nonneg_left ((hbracketPath omega).2 hst) (sq_nonneg c)
  · intro omega
    simp only [hMzero omega, mul_zero]
  · intro omega
    simp only [hbracketZero omega, mul_zero]

/-! ## Centered Gaussian normalization -/

end StochasticCalculus
