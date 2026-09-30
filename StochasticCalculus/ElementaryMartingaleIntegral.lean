/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.ContinuousExitTime

/-!
# Elementary martingale integrals

The stochastic integral of a coefficient known at the left endpoint against
a martingale on one interval: continuity, adaptedness, martingality,
orthogonality of weighted increments, and the passage of the martingale
property through limits in `L¹` and in measure with uniform integrability.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The elementary stochastic integral with coefficient `Z` on the
half-open deterministic interval `(a, b]`.  Stopping both endpoints at
`t` makes the process identically zero before `a`, equal to the weighted
martingale increment between `a` and `t` on the interval, and constant
after `b`. -/
@[expose] def elementaryMartingaleIntegralProcess
    {W : Type*} (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  Z omega * (M (min t b) omega - M (min t a) omega)

/-- Elementary stochastic-integral processes inherit path continuity from
their integrator. -/
theorem continuous_elementaryMartingaleIntegralProcess
    {W : Type*} {M : ℝ≥0 → W → ℝ}
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (a b : ℝ≥0) (Z : W → ℝ) (omega : W) :
    Continuous (fun t =>
      elementaryMartingaleIntegralProcess M a b Z t omega) := by
  unfold elementaryMartingaleIntegralProcess
  exact continuous_const.mul
    (((hMcont omega).comp (continuous_id.min continuous_const)).sub
      ((hMcont omega).comp (continuous_id.min continuous_const)))

/-- Elementary predictable integrals preserve strong adaptation without any
integrability or martingale hypothesis on the integrator. -/
theorem stronglyAdapted_elementaryMartingaleIntegralProcess
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M : ℝ≥0 → W → ℝ} (hM : StronglyAdapted 𝓥 M)
    {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓥 a] Z) :
    StronglyAdapted 𝓥 (elementaryMartingaleIntegralProcess M a b Z) := by
  intro t
  rcases le_total t a with hta | hat
  · have hzero : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    rw [hzero]
    exact stronglyMeasurable_zero
  · exact hZ.mono (𝓥.mono hat) |>.mul
      ((hM (min t b)).mono (𝓥.mono (min_le_left _ _)) |>.sub
        ((hM (min t a)).mono (𝓥.mono (min_le_left _ _))))

/-- A bounded coefficient measurable at the left endpoint gives a
martingale when integrated over one deterministic time interval against a
martingale.  This is the first arbitrary-integrator construction needed for
the process-level stochastic integral: unlike the Gaussian specialization,
the driving martingale is completely general. -/
theorem martingale_elementaryMartingaleIntegralProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M 𝓥 P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓥 a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    Martingale (elementaryMartingaleIntegralProcess M a b Z) 𝓥 P := by
  have hInt (t : ℝ≥0) : Integrable
      (elementaryMartingaleIntegralProcess M a b Z t) P := by
    have hDelta : Integrable
        (fun omega ↦ M (min t b) omega - M (min t a) omega) P :=
      (hM.integrable _).sub (hM.integrable _)
    exact hDelta.bdd_mul (hZ.mono (𝓥.le a)).aestronglyMeasurable
      (Filter.Eventually.of_forall hZbound)
  have hadapt : StronglyAdapted 𝓥
      (elementaryMartingaleIntegralProcess M a b Z) := by
    intro t
    rcases le_total t a with hta | hat
    · have hzero : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
        funext omega
        simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
          min_eq_left (hta.trans hab)]
      rw [hzero]
      exact stronglyMeasurable_zero
    · exact hZ.mono (𝓥.mono hat) |>.mul
        ((hM.stronglyMeasurable (min t b)).mono
          (𝓥.mono (min_le_left _ _)) |>.sub
            ((hM.stronglyMeasurable (min t a)).mono
              (𝓥.mono (min_le_left _ _))))
  refine ⟨hadapt, ?_⟩
  intro s t hst
  rcases le_total t a with hta | hat
  · have hIt : elementaryMartingaleIntegralProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleIntegralProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    have hIs : elementaryMartingaleIntegralProcess M a b Z s = 0 := by
      funext omega
      have hsa : s ≤ a := hst.trans hta
      simp [elementaryMartingaleIntegralProcess, min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
    rw [hIt, hIs, condExp_zero]
  · rcases le_total s a with hsa | has
    · have hIs : elementaryMartingaleIntegralProcess M a b Z s = 0 := by
        funext omega
        simp [elementaryMartingaleIntegralProcess, min_eq_left hsa,
          min_eq_left (hsa.trans hab)]
      rw [hIs]
      have hIa : P[Z * (M (min t b) - M a) | 𝓥 a] =ᵐ[P] 0 := by
        have hamin : a ≤ min t b := le_min hat hab
        have hprod : Integrable
            (fun omega ↦ Z omega * (M (min t b) omega - M a omega)) P := by
          have hInt' := hInt t
          change Integrable (fun omega ↦
            Z omega * (M (min t b) omega - M (min t a) omega)) P at hInt'
          simpa only [min_eq_right hat] using hInt'
        have hpull := condExp_mul_of_stronglyMeasurable_left hZ
          hprod ((hM.integrable _).sub (hM.integrable a))
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (𝓥 a)
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hamin,
          Filter.Eventually.of_forall (congrFun
            (condExp_of_stronglyMeasurable (𝓥.le a)
              (hM.stronglyMeasurable a) (hM.integrable a)))]
            with omega hp hd hfuture hpast
        change P[Z * (fun xi ↦ M (min t b) xi - M a xi) | 𝓥 a] omega = 0
        have hd' : P[(fun xi ↦ M (min t b) xi - M a xi) | 𝓥 a] omega =
            (P[M (min t b) | 𝓥 a] - P[M a | 𝓥 a]) omega := by
          exact hd
        rw [hp, Pi.mul_apply, hd', Pi.sub_apply, hfuture, hpast,
          sub_self, mul_zero]
      have htower := condExp_condExp_of_le (μ := P)
        (𝓥.mono hsa) (𝓥.le a) (f := Z * (M (min t b) - M a))
      have hzeroCond : P[Z * (M (min t b) - M a) | 𝓥 s] =ᵐ[P] 0 := by
        filter_upwards [htower, condExp_congr_ae hIa,
          Filter.Eventually.of_forall (congrFun
            (condExp_zero (μ := P) (m := 𝓥 s) (E := ℝ)))]
            with omega htow hcongr hzero
        rw [← htow, hcongr, hzero]
      have hprocess : elementaryMartingaleIntegralProcess M a b Z t =
          Z * (M (min t b) - M a) := by
        funext omega
        simp only [elementaryMartingaleIntegralProcess, min_eq_right hat,
          Pi.mul_apply, Pi.sub_apply]
      rw [hprocess]
      exact hzeroCond
    · rcases le_total b s with hbs | hsb
      · have hconst : elementaryMartingaleIntegralProcess M a b Z t =
            elementaryMartingaleIntegralProcess M a b Z s := by
          funext omega
          simp [elementaryMartingaleIntegralProcess,
            min_eq_right (hbs.trans hst), min_eq_right hbs,
            min_eq_right (has.trans hst), min_eq_right has]
        rw [hconst]
        exact Filter.Eventually.of_forall (congrFun
          (condExp_of_stronglyMeasurable (𝓥.le s) (hadapt s) (hInt s)))
      · have hsmin : s ≤ min t b := le_min hst hsb
        have hprod : Integrable
            (fun omega ↦ Z omega * (M (min t b) omega - M a omega)) P := by
          have hInt' := hInt t
          change Integrable (fun omega ↦
            Z omega * (M (min t b) omega - M (min t a) omega)) P at hInt'
          simpa only [min_eq_right hat] using hInt'
        have hpull := condExp_mul_of_stronglyMeasurable_left
          (hZ.mono (𝓥.mono has)) hprod
          ((hM.integrable _).sub (hM.integrable a))
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (𝓥 s)
        have hpast := condExp_of_stronglyMeasurable (𝓥.le s)
          ((hM.stronglyMeasurable a).mono (𝓥.mono has)) (hM.integrable a)
        have hprocess : elementaryMartingaleIntegralProcess M a b Z t =
            Z * (fun xi ↦ M (min t b) xi - M a xi) := by
          funext omega
          simp only [elementaryMartingaleIntegralProcess, min_eq_right hat,
            Pi.mul_apply]
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hsmin,
          Filter.Eventually.of_forall (congrFun hpast)]
            with omega hp hd hfuture hpast'
        rw [hprocess]
        simp only [elementaryMartingaleIntegralProcess, min_eq_right has,
          min_eq_left hsb]
        have hd' : P[(fun xi ↦ M (min t b) xi - M a xi) | 𝓥 s] omega =
            (P[M (min t b) | 𝓥 s] - P[M a | 𝓥 s]) omega := by
          exact hd
        rw [hp, Pi.mul_apply, hd', Pi.sub_apply, hfuture, hpast']

/-- Bounded predictable martingale increments on disjoint ordered intervals
are orthogonal in `L²`.  This is the cross-term cancellation behind the
second-moment estimate for elementary martingale transforms. -/
theorem integral_mul_weighted_martingaleIncrements_eq_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hM2 : ∀ t, MemLp (M t) 2 P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {Z Y : W → ℝ}
    (hZ : StronglyMeasurable[𝓥 a] Z) (K : ℝ≥0)
    (hZK : ∀ omega, ‖Z omega‖ ≤ K)
    (hY : StronglyMeasurable[𝓥 c] Y) (L : ℝ≥0)
    (hYL : ∀ omega, ‖Y omega‖ ≤ L) :
    ∫ omega, (Z omega * (M b omega - M a omega)) *
      (Y omega * (M d omega - M c omega)) ∂P = 0 := by
  let A : W → ℝ := fun omega ↦ Z omega * (M b omega - M a omega)
  let D : W → ℝ := fun omega ↦ M d omega - M c omega
  have hDeltaAB2 : MemLp (fun omega ↦ M b omega - M a omega) 2 P :=
    (hM2 b).sub (hM2 a)
  have hDeltaCD2 : MemLp D 2 P := by
    change MemLp (M d - M c) 2 P
    exact (hM2 d).sub (hM2 c)
  have hAmeas : AEStronglyMeasurable A P := by
    exact (hZ.mono (𝓥.le a)).aestronglyMeasurable.mul hDeltaAB2.aestronglyMeasurable
  have hA2 : MemLp A 2 P := by
    refine hDeltaAB2.of_le_mul (c := K) hAmeas ?_
    filter_upwards with omega
    simp only [A, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hZK omega) (abs_nonneg _)
  have hYDmeas : AEStronglyMeasurable (Y * D) P :=
    (hY.mono (𝓥.le c)).aestronglyMeasurable.mul hDeltaCD2.aestronglyMeasurable
  have hYD2 : MemLp (Y * D) 2 P := by
    refine hDeltaCD2.of_le_mul (c := L) hYDmeas ?_
    filter_upwards with omega
    simp only [Pi.mul_apply, D, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hYL omega) (abs_nonneg _)
  have hprodAssoc : Integrable (A * (Y * D)) P :=
    memLp_one_iff_integrable.mp (hA2.mul hYD2)
  have hprod : Integrable ((A * Y) * D) P := by
    apply hprodAssoc.congr
    filter_upwards with omega
    simp only [Pi.mul_apply]
    ring
  have hAYmeas : StronglyMeasurable[𝓥 c] (A * Y) := by
    apply StronglyMeasurable.mul _ hY
    exact (hZ.mono (𝓥.mono (hab.trans hbc))).mul
      ((hM.stronglyMeasurable b).mono (𝓥.mono hbc) |>.sub
        ((hM.stronglyMeasurable a).mono (𝓥.mono (hab.trans hbc))))
  have hDint : Integrable D P := by
    change Integrable (M d - M c) P
    exact (hM.integrable d).sub (hM.integrable c)
  have hpull := condExp_mul_of_stronglyMeasurable_left hAYmeas hprod hDint
  have hDzero : P[D | 𝓥 c] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable d) (hM.integrable c) (𝓥 c)
    filter_upwards [hsub, hM.condExp_ae_eq hcd,
      Filter.Eventually.of_forall (congrFun
        (condExp_of_stronglyMeasurable (𝓥.le c)
          (hM.stronglyMeasurable c) (hM.integrable c)))]
        with omega hsubOmega hdOmega hcOmega
    change P[D | 𝓥 c] omega = 0
    rw [show P[D | 𝓥 c] omega =
      (P[M d | 𝓥 c] - P[M c | 𝓥 c]) omega by exact hsubOmega]
    simp only [Pi.sub_apply, hdOmega, hcOmega, sub_self]
  have hcondZero : P[(A * Y) * D | 𝓥 c] =ᵐ[P] 0 := by
    filter_upwards [hpull, hDzero] with omega hpullOmega hDOmega
    simpa only [Pi.mul_apply, Pi.zero_apply, hDOmega, mul_zero] using hpullOmega
  calc
    ∫ omega, (Z omega * (M b omega - M a omega)) *
        (Y omega * (M d omega - M c omega)) ∂P =
        ∫ omega, ((A * Y) * D) omega ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          simp only [A, D, Pi.mul_apply]
          ring
    _ = ∫ omega, P[(A * Y) * D | 𝓥 c] omega ∂P :=
      (integral_condExp (𝓥.le c)).symm
    _ = 0 := by
      rw [integral_congr_ae hcondZero]
      simp

/-- The second moment of a finite sum of pairwise orthogonal real `L²`
functions is the sum of their second moments. -/
theorem integral_sq_sum_range_of_pairwise_orthogonal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (f : ℕ → W → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    (horth : ∀ i j, i < j → ∫ omega, f i omega * f j omega ∂P = 0)
    (n : ℕ) :
    ∫ omega, (∑ i ∈ Finset.range n, f i omega) ^ 2 ∂P =
      ∑ i ∈ Finset.range n, ∫ omega, (f i omega) ^ 2 ∂P := by
  have hsq (g : W → ℝ) (hg : MemLp g 2 P) :
      Integrable (fun omega ↦ (g omega) ^ 2) P := by
    have hmul : MemLp (g * g) 1 P := hg.mul hg
    apply (memLp_one_iff_integrable.mp hmul).congr
    filter_upwards with omega
    simp only [Pi.mul_apply, pow_two]
  induction n with
  | zero => simp
  | succ n ih =>
      let S : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range n, f i omega
      have hS2 : MemLp S 2 P := by
        exact memLp_finsetSum (Finset.range n) (fun i _ ↦ hf i)
      have hSn : Integrable (S * f n) P :=
        memLp_one_iff_integrable.mp (hS2.mul (hf n))
      have hcross : ∫ omega, S omega * f n omega ∂P = 0 := by
        simp only [S, Finset.sum_mul]
        rw [integral_finsetSum]
        · apply Finset.sum_eq_zero
          intro i hi
          exact horth i n (Finset.mem_range.mp hi)
        · intro i _
          exact memLp_one_iff_integrable.mp ((hf i).mul (hf n))
      simp_rw [Finset.sum_range_succ]
      change ∫ omega, (S omega + f n omega) ^ 2 ∂P =
        (∑ i ∈ Finset.range n, ∫ omega, f i omega ^ 2 ∂P) +
          ∫ omega, f n omega ^ 2 ∂P
      calc
        ∫ omega, (S omega + f n omega) ^ 2 ∂P =
            ∫ omega, S omega ^ 2 +
              (2 * (S omega * f n omega) + f n omega ^ 2) ∂P := by
          apply integral_congr_ae
          filter_upwards with omega
          ring
        _ = (∫ omega, S omega ^ 2 ∂P) +
            ((∫ omega, 2 * (S omega * f n omega) ∂P) +
              ∫ omega, f n omega ^ 2 ∂P) := by
          rw [integral_add (hsq S hS2)]
          · rw [integral_add]
            · exact hSn.const_mul 2
            · exact hsq (f n) (hf n)
          · exact (hSn.const_mul 2).add (hsq (f n) (hf n))
        _ = (∫ omega, S omega ^ 2 ∂P) +
            ∫ omega, f n omega ^ 2 ∂P := by
          rw [integral_const_mul, hcross]
          ring
        _ = (∑ i ∈ Finset.range n, ∫ omega, f i omega ^ 2 ∂P) +
            ∫ omega, f n omega ^ 2 ∂P := by rw [ih]

/-- Forming a single elementary integral commutes exactly with Mathlib's
stopped-process convention and its exceptional-event indicator.  This
identity is the stopping compatibility needed to reuse an integrator's
localizing sequence. -/
theorem stoppedProcess_indicator_elementaryMartingaleIntegralProcess
    {W : Type*} (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → ℝ)
    (A : Set W) (tau : W → WithTop ℝ≥0) :
    stoppedProcess
        (fun i ↦ A.indicator
          (elementaryMartingaleIntegralProcess M a b Z i)) tau =
      elementaryMartingaleIntegralProcess
        (stoppedProcess (fun i ↦ A.indicator (M i)) tau) a b Z := by
  funext t omega
  simp only [elementaryMartingaleIntegralProcess, stoppedProcess]
  by_cases hA : omega ∈ A
  · simp only [Set.indicator_of_mem hA]
    simp only [elementaryMartingaleIntegralProcess]
    congr 1
    have hcoe_untopA (x : WithTop ℝ≥0) (hx : x ≠ ⊤) :
        ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
      rw [WithTop.untopA_eq_untop hx, WithTop.coe_untop]
    have hcoe_min (x y : ℝ≥0) :
        ((min x y : ℝ≥0) : WithTop ℝ≥0) =
          min (x : WithTop ℝ≥0) (y : WithTop ℝ≥0) := by
      norm_cast
    have hstopmin (c : ℝ≥0) :
        min (min (t : WithTop ℝ≥0) (tau omega)).untopA c =
          (min ((min t c : ℝ≥0) : WithTop ℝ≥0) (tau omega)).untopA := by
      apply WithTop.coe_injective
      rw [hcoe_min, hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)),
        hcoe_untopA _
          (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)), hcoe_min]
      ac_rfl
    rw [hstopmin b, hstopmin a]
  · simp only [Set.indicator_of_notMem hA, sub_self, mul_zero]

/-- A finite sum of martingales is a martingale.  The pointwise finite-sum
form is convenient for assembling elementary stochastic integrals without
introducing an artificial ordering on their interval index type. -/
theorem Martingale.finset_sum
    {W I : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : I → ℝ≥0 → W → ℝ} (S : Finset I)
    (hX : ∀ i ∈ S, Martingale (X i) 𝓥 P) :
    Martingale (∑ i ∈ S, X i) 𝓥 P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using martingale_zero ℝ 𝓥 P
  | @insert i S hi ih =>
      have hhead : Martingale (X i) 𝓥 P :=
        hX i (Finset.mem_insert_self i S)
      have htail : Martingale (∑ j ∈ S, X j) 𝓥 P :=
        ih fun j hj ↦ hX j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using hhead.add htail

/-- Finite pointwise sums preserve strong adaptation. -/
theorem StronglyAdapted.finset_sum
    {W I : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : I → ℝ≥0 → W → ℝ} (S : Finset I)
    (hX : ∀ i ∈ S, StronglyAdapted 𝓥 (X i)) :
    StronglyAdapted 𝓥 (∑ i ∈ S, X i) := by
  intro t
  simpa only [Finset.sum_apply] using
    S.stronglyMeasurable_sum fun i hi ↦ hX i hi t

/-- An `L¹`-norm limit of integrable
functions is integrable.  Convergence to zero makes one difference have
finite `L¹` norm, after which integrability follows by adding back the
corresponding approximant. -/
theorem integrable_of_tendsto_eLpNorm_one_sub
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {f : ℕ → W → ℝ} {g : W → ℝ}
    (hf : ∀ n, Integrable (f n) P)
    (hconv : Tendsto (fun n ↦ eLpNorm (g - f n) 1 P)
      Filter.atTop (𝓝 0)) :
    Integrable g P := by
  have hlt : ∀ᶠ n in Filter.atTop,
      eLpNorm (g - f n) 1 P < 1 :=
    (tendsto_order.1 hconv).2 1 (by simp)
  rcases hlt.exists with ⟨n, hn⟩
  have hdiff : Integrable (g - f n) P :=
    memLp_one_iff_integrable.mp (hn.trans (by simp))
  simpa only [sub_add_cancel] using hdiff.add (hf n)

/-- A uniformly `L²`-bounded family on a probability space is uniformly
integrable in `L¹`.  This is the standard higher-moment route to the Vitali
hypothesis used below: the remaining probabilistic obligation can therefore
be discharged by a uniform second-moment estimate for the explicit
martingale-transform approximations. -/
theorem uniformIntegrable_one_of_uniform_eLpNorm_two
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} [IsProbabilityMeasure P] {f : I → W → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (f i) 2 P ≤ C) :
    UniformIntegrable f 1 P := by
  refine ⟨unifIntegrable_iff'.2 ?_, ⟨C, fun i ↦ ?_⟩⟩
  · intro ε₀ hε₀
    obtain ⟨ε, _, hε, hεlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε₀
    have hε : 0 < ε := ENNReal.ofReal_pos.1 hε
    let d : ℝ := ε / ((C : ℝ) + 1)
    have hd : 0 < d := div_pos hε (by positivity)
    refine ⟨ENNReal.ofReal (d ^ 2), ENNReal.ofReal_pos.2 (sq_pos_of_pos hd),
      fun i s _hs hPs ↦ ?_⟩
    apply le_trans ?_ hεlt.le
    calc
      eLpNorm (f i) 1 (P.restrict s) ≤
          eLpNorm (f i) 2 (P.restrict s) *
            (P.restrict s) Set.univ ^ (1 / 2 : ℝ) := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
            (f := f i) (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
            ((hf i).mono_measure Measure.restrict_le_self) using 1;
          norm_num
      _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (d ^ 2)) ^ (1 / 2 : ℝ) := by
        simp only [Measure.restrict_apply_univ]
        exact mul_le_mul'
          ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i))
          (ENNReal.rpow_le_rpow hPs (by norm_num))
      _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_pos (sq_pos_of_pos hd)]
        rw [show (d ^ 2) ^ (1 / 2 : ℝ) = d by
          rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast hd.le
            (show (2 : ℕ) ≠ 0 by norm_num)]
        rw [← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (C.coe_nonneg)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [d]
        calc
          (C : ℝ) * (ε / ((C : ℝ) + 1)) ≤
              ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
            gcongr
            norm_num
          _ = ε := by field_simp
  · exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans
      (hC i)

/-- A strongly adapted pointwise-in-time `L¹`-norm limit of martingales is a
martingale.  Integrability of the limit follows from convergence, and
conditional expectation is an `L¹` contraction, so the martingale identities
pass to the limit at every pair of times. -/
theorem martingale_of_tendsto_eLpNorm_one
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓥 P)
    (hYadapt : StronglyAdapted 𝓥 Y)
    (hconv : ∀ t, Tendsto
      (fun n ↦ eLpNorm (Y t - X n t) 1 P) Filter.atTop (𝓝 0)) :
    Martingale Y 𝓥 P := by
  have hYint : ∀ t, Integrable (Y t) P := fun t ↦
    integrable_of_tendsto_eLpNorm_one_sub
      (fun n ↦ (hX n).integrable t)
      (hconv t)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff one_ne_zero]
  apply le_antisymm
  · have hconvS : Tendsto (fun n ↦ eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (𝓝 0) := by
      convert hconv s using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Tendsto (fun n ↦
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (𝓝 0) := by
      simpa only [add_zero] using (hconv t).add hconvS
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hdecomp :
        P[Y t | 𝓥 s] - Y s =ᵐ[P]
          P[Y t - X n t | 𝓥 s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (𝓥 s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      ring
    calc
      eLpNorm (P[Y t | 𝓥 s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | 𝓥 s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | 𝓥 s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- Vitali closure for martingales: a strongly adapted limit in measure of a
uniformly integrable sequence of martingales is a martingale. -/
theorem martingale_of_tendstoInMeasure_of_uniformIntegrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {X : ℕ → ℝ≥0 → W → ℝ} {Y : ℝ≥0 → W → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓥 P)
    (hYadapt : StronglyAdapted 𝓥 Y)
    (hUI : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ X n t)
      Filter.atTop (Y t)) :
    Martingale Y 𝓥 P := by
  apply martingale_of_tendsto_eLpNorm_one hX hYadapt
  intro t
  have hYmem : MemLp (Y t) 1 P :=
    (hUI t).memLp_of_tendstoInMeasure (hconv t)
  have hLp : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P)
      Filter.atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (by simp) (by simp)
      (fun n ↦ ((hX n).integrable t).1) hYmem
      (hUI t).unifIntegrable (hconv t)
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- Stopping a continuous-path martingale at its bounded continuous exit
time preserves the martingale property.  The proof closes the dyadic
finite-range martingales under convergence in measure.  Uniform
integrability follows from optional sampling: at each deterministic time
the approximants are conditional expectations of the original martingale. -/
theorem martingale_stoppedProcess_continuousExitTime_of_adapted
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M Z : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hZ : StronglyAdapted 𝓥 Z)
    (T R : ℝ≥0) :
    Martingale (stoppedProcess M (continuousExitTime Z T R)) 𝓥 P := by
  let tau : W → WithTop ℝ≥0 := continuousExitTime Z T R
  let tauN : ℕ → W → WithTop ℝ≥0 :=
    fun n => dyadicHittingTimeNNReal Z T R n
  let X : ℕ → ℝ≥0 → W → ℝ := fun n => stoppedProcess M (tauN n)
  have htau : IsStoppingTime 𝓥 tau :=
    isStoppingTime_continuousExitTime_of_stronglyAdapted hZ T R
  have hX (n : ℕ) : Martingale (X n) 𝓥 P := by
    dsimp only [X, tauN]
    exact
      martingale_stoppedProcess_uniformPartitionHittingTimeNNReal_of_adapted
        hM hZ T (2 ^ n) (measurableSet_outsideClosedBall R)
  have hYadapt : StronglyAdapted 𝓥 (stoppedProcess M tau) :=
    hM.stronglyAdapted.stoppedProcess hMcont htau
  apply martingale_of_tendstoInMeasure_of_uniformIntegrable hX hYadapt
  · intro t
    let sigma : ℕ → W → WithTop ℝ≥0 := fun n omega =>
      min (t : WithTop ℝ≥0) (tauN n omega)
    have hsigma (n : ℕ) : IsStoppingTime 𝓥 (sigma n) :=
      (isStoppingTime_const 𝓥 t).min
        (isStoppingTime_uniformPartitionHittingTimeNNReal_of_stronglyAdapted
          hZ T (2 ^ n) (measurableSet_outsideClosedBall R))
    have hsigma_le (n : ℕ) (omega : W) : sigma n omega ≤ t :=
      min_le_left _ _
    have hsigma_range (n : ℕ) : (Set.range (sigma n)).Countable := by
      have heq : Set.range (sigma n) =
          (fun x : WithTop ℝ≥0 => min (t : WithTop ℝ≥0) x) ''
            Set.range (tauN n) := by
        rw [← Set.range_comp]
        rfl
      rw [heq]
      apply Set.Countable.image
      apply ((((Finset.range (2 ^ n + 1)).image
        (uniformPartitionTime T (2 ^ n))).finite_toSet.image
          ((↑) : ℝ≥0 → WithTop ℝ≥0)).countable).mono
      rintro x ⟨omega, rfl⟩
      exact uniformPartitionHittingTimeNNReal_mem_rangeFinset Z T (2 ^ n)
        (outsideClosedBall R) omega
    have hae (n : ℕ) : X n t =ᵐ[P]
        P[M t | (hsigma n).measurableSpace] := by
      exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
        (hsigma n) (hsigma_le n) (hsigma_range n)
    have hUI : UniformIntegrable
        (fun n => P[M t | (hsigma n).measurableSpace]) 1 P :=
      (hM.integrable t).uniformIntegrable_condExp
        (fun n => (hsigma n).measurableSpace_le)
    exact hUI.ae_eq (fun n => (hae n).symm)
  · intro t
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hX n).integrable t).1
    · exact Filter.Eventually.of_forall fun omega =>
        tendsto_stoppedProcess_dyadicHittingTime_continuousExitTime_of_continuous
          hMcont T R t omega

end StochasticCalculus
