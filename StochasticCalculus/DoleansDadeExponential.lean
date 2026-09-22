/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.MartingaleLeftSum

/-!
# The Doléans--Dade exponential and its left sums

The compensated logarithm `M - ½⟪M⟫`, the stochastic exponential, its capped
version and integral candidate, the left-sum processes, the Stieltjes
bracket integral of continuous weights, and the quadratic variation and
Taylor expansion of the logarithm along uniform partitions.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- The compensated logarithm `M - (1/2) ⟪M⟫` used in the stochastic
exponential.  The second argument is kept abstract until a bracket API is
available at the process level. -/
def doleansDadeLog
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  M t omega - (1 / 2 : ℝ) * bracket t omega

/-- The real Doléans–Dade exponential associated to a process and a selected
bracket process. -/
def doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (doleansDadeLog M bracket t omega)

/-- Adaptedness of both the martingale and bracket processes makes the
selected Doléans–Dade exponential adapted. -/
theorem stronglyAdapted_doleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket) :
    StronglyAdapted 𝓥 (doleansDadeExponential M bracket) := by
  intro t
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hM t).sub (stronglyMeasurable_const.mul (hbracket t)))

/-- The canonical stochastic-integral candidate in the Doléans--Dade
identity: the stochastic exponential minus its initial constant.  Naming
this process lets the approximation endpoint state its sole analytic input
without quantifying over an otherwise arbitrary integral process. -/
def doleansDadeIntegralCandidate
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  doleansDadeExponential M bracket t omega - 1

/-- The canonical Doléans--Dade integral candidate is adapted whenever the
martingale and selected bracket are adapted. -/
theorem stronglyAdapted_doleansDadeIntegralCandidate
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket) :
    StronglyAdapted 𝓥 (doleansDadeIntegralCandidate M bracket) := by
  intro t
  exact (stronglyAdapted_doleansDadeExponential hM hbracket t).sub
    stronglyMeasurable_const

/-- Continuous martingale and bracket paths give a continuous canonical
Doléans--Dade integral-candidate path. -/
theorem continuous_doleansDadeIntegralCandidate
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    Continuous (fun t ↦ doleansDadeIntegralCandidate M bracket t omega) := by
  exact (Real.continuous_exp.comp
    (hM.sub (continuous_const.mul hbracket))).sub continuous_const

/-- The stochastic exponential capped above at a deterministic nonnegative
level.  Positivity of the exponential makes this a bounded adapted
integrand suitable for the elementary arbitrary-integrator construction. -/
def cappedDoleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (R : ℝ≥0)
    (t : ℝ≥0) (omega : W) : ℝ :=
  min (doleansDadeExponential M bracket t omega) R

/-- Deterministic capping preserves adaptedness of the stochastic
exponential. -/
theorem stronglyAdapted_cappedDoleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (R : ℝ≥0) :
    StronglyAdapted 𝓥 (cappedDoleansDadeExponential M bracket R) := by
  intro t
  exact (continuous_id.min continuous_const).comp_stronglyMeasurable
    (stronglyAdapted_doleansDadeExponential hM hbracket t)

/-- The capped stochastic exponential has its advertised deterministic
bound. -/
theorem norm_cappedDoleansDadeExponential_le
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (R : ℝ≥0)
    (t : ℝ≥0) (omega : W) :
    ‖cappedDoleansDadeExponential M bracket R t omega‖ ≤ (R : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact min_le_right _ _
  · exact le_min (Real.exp_pos _).le R.coe_nonneg

/-- On a compact time interval, continuous sample paths make the integer
caps eventually inactive uniformly over the whole interval. -/
theorem eventually_cappedDoleansDadeExponential_eq_on_Icc
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      cappedDoleansDadeExponential M bracket n t omega =
        doleansDadeExponential M bracket t omega := by
  have hE : Continuous
      (fun t ↦ doleansDadeExponential M bracket t omega) :=
    Real.continuous_exp.comp
      (hM.sub (continuous_const.mul hbracket))
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hE.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht
  unfold cappedDoleansDadeExponential
  rw [min_eq_left]
  exact (hC ⟨t, ht, rfl⟩).trans (hN.trans (by exact_mod_cast hn))

/-- A diagonal approximation to `∫ E(M) dM`: at stage `n`, cap the
Doléans integrand at `n + 1` and use an `n + 1` point uniform grid. -/
def cappedDoleansDadeLeftSumProcess
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  uniformAdaptedMartingaleLeftSumProcess M
    (cappedDoleansDadeExponential M bracket (n + 1)) T (n + 1)

/-- The matching uncapped uniform left-sum process for the stochastic
integral `∫ E(M) dM`. -/
def doleansDadeLeftSumProcess
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℝ :=
  uniformAdaptedMartingaleLeftSumProcess M
    (doleansDadeExponential M bracket) T (n + 1)

/-- Along continuous input paths, the capped diagonal and uncapped left-sum
sample paths are eventually identical.  Thus the caps introduce no
pathwise compact-horizon error. -/
theorem eventually_cappedDoleansDadeLeftSumProcess_eq
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (omega : W)
    (hM : Continuous (fun t ↦ M t omega))
    (hbracket : Continuous (fun t ↦ bracket t omega)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (fun t ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega) =
        fun t ↦ doleansDadeLeftSumProcess M bracket T n t omega := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_cappedDoleansDadeExponential_eq_on_Icc
      M bracket T omega hM hbracket)
  filter_upwards [eventually_ge_atTop N] with n hn
  funext t
  simp only [cappedDoleansDadeLeftSumProcess, doleansDadeLeftSumProcess,
    uniformAdaptedMartingaleLeftSumProcess,
    elementaryMartingaleIntegralSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := Finset.mem_range.mp hi |>.le
  have htime := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hcap := hN (n + 1) (hn.trans (Nat.le_succ n)) _ htime
  simp only [elementaryMartingaleIntegralProcess]
  rw [show cappedDoleansDadeExponential M bracket (n + 1)
      (uniformPartitionTime T (n + 1) i) omega =
        doleansDadeExponential M bracket
          (uniformPartitionTime T (n + 1) i) omega by
    simpa only [Nat.cast_add, Nat.cast_one] using hcap]

/-- Almost-everywhere continuous paths make the capped and uncapped
left-sum sample paths eventually identical almost surely. -/
theorem ae_eventually_cappedDoleansDadeLeftSumProcess_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hM : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracket : ∀ᵐ omega ∂P, Continuous (fun t ↦ bracket t omega)) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop,
      (fun t ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega) =
        fun t ↦ doleansDadeLeftSumProcess M bracket T n t omega := by
  filter_upwards [hM, hbracket] with omega hMomega hbracketOmega
  exact eventually_cappedDoleansDadeLeftSumProcess_eq
    M bracket T omega hMomega hbracketOmega

/-- At every observation time, the capped-minus-uncapped diagonal left sums
converge to zero in measure.  This turns compact-path eventual equality into
the probabilistic convergence interface used elsewhere in the library. -/
theorem tendstoInMeasure_cappedDoleansDadeLeftSumProcess_sub
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracketCont : ∀ᵐ omega ∂P,
      Continuous (fun t ↦ bracket t omega))
    (T t : ℝ≥0) :
    TendstoInMeasure P
      (fun n omega ↦
        cappedDoleansDadeLeftSumProcess M bracket T n t omega -
          doleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hcap : StronglyAdapted 𝓥
        (cappedDoleansDadeLeftSumProcess M bracket T n) := by
      unfold cappedDoleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_cappedDoleansDadeExponential
          hM hbracket (n + 1)) T (n + 1)
    have huncap : StronglyAdapted 𝓥
        (doleansDadeLeftSumProcess M bracket T n) := by
      unfold doleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_doleansDadeExponential hM hbracket) T (n + 1)
    exact ((hcap t).mono (𝓥.le t)).aestronglyMeasurable.sub
      ((huncap t).mono (𝓥.le t)).aestronglyMeasurable
  · filter_upwards
      [ae_eventually_cappedDoleansDadeLeftSumProcess_eq
        M bracket T hMcont hbracketCont] with omega homega
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [homega] with n hn
    rw [congrFun hn t, sub_self]

/-- Any fixed-time convergence-in-measure result for the classical uncapped
Doléans left sums transfers to the bounded diagonal approximation. -/
theorem tendstoInMeasure_cappedDoleansDadeLeftSumProcess_of_uncapped
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun t ↦ M t omega))
    (hbracketCont : ∀ᵐ omega ∂P,
      Continuous (fun t ↦ bracket t omega))
    (T t : ℝ≥0) {I : W → ℝ}
    (huncap : TendstoInMeasure P
      (fun n omega ↦ doleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop I) :
    TendstoInMeasure P
      (fun n omega ↦ cappedDoleansDadeLeftSumProcess M bracket T n t omega)
      Filter.atTop I := by
  have hcapMeas (n : ℕ) : AEStronglyMeasurable
      (cappedDoleansDadeLeftSumProcess M bracket T n t) P := by
    have hcap : StronglyAdapted 𝓥
        (cappedDoleansDadeLeftSumProcess M bracket T n) := by
      unfold cappedDoleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_cappedDoleansDadeExponential
          hM hbracket (n + 1)) T (n + 1)
    exact ((hcap t).mono (𝓥.le t)).aestronglyMeasurable
  have huncapMeas (n : ℕ) : AEStronglyMeasurable
      (doleansDadeLeftSumProcess M bracket T n t) P := by
    have huncap' : StronglyAdapted 𝓥
        (doleansDadeLeftSumProcess M bracket T n) := by
      unfold doleansDadeLeftSumProcess
      exact stronglyAdapted_uniformAdaptedMartingaleLeftSumProcess hM
        (stronglyAdapted_doleansDadeExponential hM hbracket) T (n + 1)
    exact ((huncap' t).mono (𝓥.le t)).aestronglyMeasurable
  have hdiff :=
    tendstoInMeasure_cappedDoleansDadeLeftSumProcess_sub
      hM hbracket hMcont hbracketCont T t
  have hsum := TendstoInMeasure.add_real
    (fun n ↦ (hcapMeas n).sub (huncapMeas n))
    huncapMeas hdiff huncap
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      simp only [Pi.sub_apply]
      ring
  · exact Filter.Eventually.of_forall fun omega ↦ by simp

/-- A total continuous nondecreasing path bundled as a Stieltjes function.
The fallback value makes the construction total; all useful equations expose
the intended path under explicit continuity and monotonicity hypotheses. -/
noncomputable def continuousMonotoneStieltjesFunction
    (A : ℝ≥0 → ℝ) : StieltjesFunction ℝ≥0 := by
  classical
  exact if h : Continuous A ∧ Monotone A then
      { toFun := A
        mono' := h.2
        right_continuous' := fun _ ↦ h.1.continuousWithinAt }
    else 0

@[simp]
theorem continuousMonotoneStieltjesFunction_apply
    {A : ℝ≥0 → ℝ} (hAcont : Continuous A) (hAmono : Monotone A)
    (t : ℝ≥0) :
    continuousMonotoneStieltjesFunction A t = A t := by
  simp [continuousMonotoneStieltjesFunction, hAcont, hAmono]

/-- Uniform left sums against the increments of a continuous nondecreasing
path converge to integration against its Stieltjes measure. -/
theorem uniformPartition_weighted_stieltjes_tendsto
    (A w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hAcont : Continuous A) (hAmono : Monotone A)
    (hw : Continuous w) :
    Tendsto
      (fun k ↦ ∑ i ∈ Finset.range (k + 1),
        w (uniformPartitionTime t (k + 1) i) *
          (A (uniformPartitionTime t (k + 1) (i + 1)) -
            A (uniformPartitionTime t (k + 1) i)))
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc 0 t, w s ∂
        (continuousMonotoneStieltjesFunction A).measure)) := by
  let F := continuousMonotoneStieltjesFunction A
  let mu : Measure ℝ≥0 := F.measure
  have hF (s : ℝ≥0) : F s = A s := by
    exact continuousMonotoneStieltjesFunction_apply hAcont hAmono s
  have hmu (a b : ℝ≥0) :
      mu (Set.Ioc a b) = ENNReal.ofReal (A b - A a) := by
    simp only [mu, StieltjesFunction.measure_Ioc, hF]
  have hfinite : mu (Set.Ioc 0 t) ≠ ∞ := by
    rw [hmu]
    exact ENNReal.ofReal_ne_top
  have hone : IntegrableOn (fun _ : ℝ≥0 ↦ (1 : ℝ))
      (Set.Ioc 0 t) mu :=
    integrableOn_const hfinite
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    ((isCompact_Icc.image_of_continuousOn hw.continuousOn).isBounded)
  have hwint : IntegrableOn w (Set.Ioc 0 t) mu := by
    refine mu.integrableOn_of_bounded (M := C) hfinite
      hw.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hC (w s) ⟨s, Set.Ioc_subset_Icc_self hs, rfl⟩
  have hraw := uniformPartition_weighted_integral_tendsto
    (μ := mu) (fun _ : ℝ≥0 ↦ (1 : ℝ)) w t hone
      (by simpa only [mul_one] using hwint) (fun _ ↦ zero_le_one)
      hw.continuousOn
  change Tendsto _ Filter.atTop
    (𝓝 (∫ s in Set.Ioc 0 t, w s ∂mu))
  convert hraw using 1
  · funext k
    apply Finset.sum_congr rfl
    intro i _hi
    rw [setIntegral_one_eq_measureReal, setIntegral_one_eq_measureReal]
    simp only [measureReal_def, hmu]
    have hpos1 :
        0 ≤ A (uniformPartitionTime t (k + 1) (i + 1)) - A 0 :=
      sub_nonneg.mpr (hAmono bot_le)
    have hpos0 : 0 ≤ A (uniformPartitionTime t (k + 1) i) - A 0 :=
      sub_nonneg.mpr (hAmono bot_le)
    rw [ENNReal.toReal_ofReal hpos1, ENNReal.toReal_ofReal hpos0]
    ring
  · simp only [mul_one]

/-- Uniform left sums of a process-valued weight against increments of a
candidate bracket process. -/
def bracketWeightedLeftSum
    {W : Type*} (H A : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    H (uniformPartitionTime t n i) omega *
      (A (uniformPartitionTime t n (i + 1)) omega -
        A (uniformPartitionTime t n i) omega)

/-- The pathwise Stieltjes integral of a process-valued weight against a
continuous nondecreasing bracket candidate.  On exceptional paths the total
Stieltjes-function construction uses its zero fallback. -/
def stieltjesBracketIntegral
    {W : Type*} (H A : ℝ≥0 → W → ℝ) (t : ℝ≥0)
    (omega : W) : ℝ :=
  ∫ s in Set.Ioc 0 t, H s omega ∂
    (continuousMonotoneStieltjesFunction (fun r ↦ A r omega)).measure

/-- Fixed-time measurability of the weight and bracket makes each bracket
left sum almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_bracketWeightedLeftSum
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    (H A : ℝ≥0 → W → ℝ)
    (hH : ∀ s, AEStronglyMeasurable (H s) P)
    (hA : ∀ s, AEStronglyMeasurable (A s) P)
    (t : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (bracketWeightedLeftSum H A t n) P := by
  unfold bracketWeightedLeftSum
  have hs : AEStronglyMeasurable
      (∑ i ∈ Finset.range n, fun omega ↦
        H (uniformPartitionTime t n i) omega *
          (A (uniformPartitionTime t n (i + 1)) omega -
            A (uniformPartitionTime t n i) omega)) P := by
    apply Finset.aestronglyMeasurable_sum
    intro i _hi
    exact (hH _).mul ((hA _).sub (hA _))
  apply hs.congr
  filter_upwards with omega
  simp only [Finset.sum_apply]

/-- Random continuous weights integrated against random continuous
nondecreasing brackets converge in measure to their pathwise Stieltjes
integral. -/
theorem bracketWeightedLeftSum_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (H A : ℝ≥0 → W → ℝ)
    (hH : ∀ s, AEStronglyMeasurable (H s) P)
    (hA : ∀ s, AEStronglyMeasurable (A s) P)
    (hHcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ H s omega))
    (hApath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ A s omega) ∧ Monotone (fun s ↦ A s omega))
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ bracketWeightedLeftSum H A t (n + 1))
      Filter.atTop (stieltjesBracketIntegral H A t) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact aestronglyMeasurable_bracketWeightedLeftSum
      H A hH hA t (n + 1)
  · filter_upwards [hHcont, hApath] with omega hHomega hAomega
    exact uniformPartition_weighted_stieltjes_tendsto
      (fun s ↦ A s omega) (fun s ↦ H s omega) t
      hAomega.1 hAomega.2 hHomega

/-- At the terminal horizon, the uncapped process is exactly the classical
Doléans left Riemann sum. -/
theorem doleansDadeLeftSumProcess_terminal
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    doleansDadeLeftSumProcess M bracket T n T omega =
      ∑ i ∈ Finset.range (n + 1),
        doleansDadeExponential M bracket
            (uniformPartitionTime T (n + 1) i) omega *
          (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
            M (uniformPartitionTime T (n + 1) i) omega) := by
  exact uniformAdaptedMartingaleLeftSumProcess_terminal M
    (doleansDadeExponential M bracket) T n omega

/-- Evaluating a coherent left-sum process at `t` is the same as taking the
terminal left sum of the deterministically stopped integrator, bracket, and
exponential on the original horizon. -/
theorem doleansDadeLeftSumProcess_eq_stopped_terminal
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    doleansDadeLeftSumProcess M bracket T n t omega =
      doleansDadeLeftSumProcess
        (fun s omega ↦ M (min s t) omega)
        (fun s omega ↦ bracket (min s t) omega) T n T omega := by
  rw [doleansDadeLeftSumProcess_terminal]
  unfold doleansDadeLeftSumProcess
    uniformAdaptedMartingaleLeftSumProcess elementaryMartingaleIntegralSum
  simp only [Finset.sum_apply, elementaryMartingaleIntegralProcess]
  apply Finset.sum_congr rfl
  intro i _hi
  let s₀ := uniformPartitionTime T (n + 1) i
  let s₁ := uniformPartitionTime T (n + 1) (i + 1)
  have hs : s₀ ≤ s₁ :=
    monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i)
  by_cases h₀ : s₀ ≤ t
  · have hmin₀ : min t s₀ = s₀ := min_eq_right h₀
    have hmin₀' : min s₀ t = s₀ := min_eq_left h₀
    simp only [s₀] at hmin₀ hmin₀' ⊢
    rw [hmin₀, hmin₀']
    simp only [doleansDadeExponential, doleansDadeLog]
    rw [hmin₀']
    rw [min_comm t (uniformPartitionTime T (n + 1) (i + 1))]
  · have ht₀ : t ≤ s₀ := le_of_not_ge h₀
    have ht₁ : t ≤ s₁ := ht₀.trans hs
    simp only [s₀, s₁] at ht₀ ht₁ ⊢
    rw [min_eq_left ht₀, min_eq_left ht₁,
      min_eq_right ht₀, min_eq_right ht₁]
    simp only [sub_self, mul_zero]

/-- Every stopped diagonal capped-Doléans left sum is a martingale when the
correspondingly stopped integrator is a martingale. -/
theorem
    martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    {M bracket : ℝ≥0 → W → ℝ} {tau : W → WithTop ℝ≥0}
    (hM : Martingale (localizingStoppedProcess M tau) 𝓥 P)
    (hMadapt : StronglyAdapted 𝓥 M)
    (hbracket : StronglyAdapted 𝓥 bracket)
    (T : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess
        (cappedDoleansDadeLeftSumProcess M bracket T n) tau) 𝓥 P := by
  unfold cappedDoleansDadeLeftSumProcess
  exact
    martingale_localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess
      hM (stronglyAdapted_cappedDoleansDadeExponential
        hMadapt hbracket (n + 1))
      (n + 1) (norm_cappedDoleansDadeExponential_le M bracket (n + 1))
      T (n + 1)

theorem doleansDadeExponential_pos
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    0 < doleansDadeExponential M bracket t omega :=
  Real.exp_pos _

theorem doleansDadeExponential_zero
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : M 0 omega = 0) (hbracket : bracket 0 omega = 0) :
    doleansDadeExponential M bracket 0 omega = 1 := by
  simp [doleansDadeExponential, doleansDadeLog, hM, hbracket]

/-- Continuous paths of the martingale and bracket give a continuous
stochastic-exponential path. -/
theorem continuous_doleansDadeExponential
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (omega : W)
    (hM : Continuous (fun t => M t omega))
    (hbracket : Continuous (fun t => bracket t omega)) :
    Continuous (fun t => doleansDadeExponential M bracket t omega) := by
  exact Real.continuous_exp.comp
    (hM.sub (continuous_const.mul hbracket))

/-- Capping paired dyadic exits by larger continuous exits gives a
grid-independent `L²` bound for the resulting Doléans-transform error.  The
outer exponential exit turns every diagonal cap into the same bounded
before-exit coefficient. -/
theorem eLpNorm_pairedExit_sub_outerCappedDyadic_cappedDoleans_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝒱 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T H K R K' R' : ℝ≥0) (hKK' : K ≤ K') (hRR' : R ≤ R')
    (m n : ℕ) (t : ℝ≥0) :
    let E := doleansDadeExponential M bracket
    let tau : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K omega)
        (continuousExitTime E H R omega)
    let theta : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K' omega)
        (continuousExitTime E H R' omega)
    let rho : W → WithTop ℝ≥0 := fun omega =>
      min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
    eLpNorm
      (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) tau t -
        localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) rho t) 2 P ≤
      R' * eLpNorm
        ((localizingStoppedProcess M tau - localizingStoppedProcess M rho) T -
          (localizingStoppedProcess M tau - localizingStoppedProcess M rho) 0)
        2 P := by
  dsimp only
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K' omega)
      (continuousExitTime E H R' omega)
  let rho : W → WithTop ℝ≥0 := fun omega =>
    min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
  let Hn := cappedDoleansDadeExponential M bracket (n + 1)
  let Hkill := beforeContinuousExitProcessOf E Hn H R'
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have hMtau : Martingale (localizingStoppedProcess M tau) 𝒱 P :=
    martingale_localizingStoppedProcess_min_continuousExitTime
      hM hMcont hM.stronglyAdapted hEadapt H K R
  have hMrho : Martingale (localizingStoppedProcess M rho) 𝒱 P :=
    martingale_localizingStoppedProcess_pairedDyadic_min_outerContinuousExit
      hM hMcont hM.stronglyAdapted hEadapt H K R K' R' m
  have htauM (omega : W) : tau omega ≤
      continuousExitTime M H K' omega :=
    (min_le_left _ _).trans
      (continuousExitTime_mono_radius M H K K' hKK' omega)
  have hrhoM (omega : W) : rho omega ≤
      continuousExitTime M H K' omega :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htauE (omega : W) : tau omega ≤
      continuousExitTime E H R' omega :=
    (min_le_right _ _).trans
      (continuousExitTime_mono_radius E H R R' hRR' omega)
  have hrhoE (omega : W) : rho omega ≤
      continuousExitTime E H R' omega :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMtauT : MemLp (localizingStoppedProcess M tau T) 2 P := by
    apply MemLp.of_bound
      ((hMtau.stronglyAdapted T).mono (𝒱.le T)).aestronglyMeasurable K'
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_of_le_continuousExitTime
        hMcont H K' htauM T omega
  have hMrhoT : MemLp (localizingStoppedProcess M rho T) 2 P := by
    apply MemLp.of_bound
      ((hMrho.stronglyAdapted T).mono (𝒱.le T)).aestronglyMeasurable K'
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_of_le_continuousExitTime
        hMcont H K' hrhoM T omega
  have hNT : MemLp
      ((localizingStoppedProcess M tau -
        localizingStoppedProcess M rho) T) 2 P :=
    hMtauT.sub hMrhoT
  have hHkill : StronglyAdapted 𝒱 Hkill :=
    stronglyAdapted_beforeContinuousExitProcessOf hEadapt
      (stronglyAdapted_cappedDoleansDadeExponential
        hM.stronglyAdapted hbracket (n + 1)) H R'
  have hcap : ∀ (s : ℝ≥0) omega,
      (s : WithTop ℝ≥0) < continuousExitTime E H R' omega →
        ‖Hn s omega‖ ≤ R' := by
    intro s omega hs
    have hER := norm_le_of_lt_continuousExitTime hEcont H R' s omega hs
    rw [abs_of_pos (doleansDadeExponential_pos M bracket s omega)] at hER
    dsimp only [Hn, cappedDoleansDadeExponential]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (min_le_left _ _).trans hER
    · exact le_min (doleansDadeExponential_pos M bracket s omega).le
        (NNReal.coe_nonneg _)
  have hHkillBound : ∀ s omega, ‖Hkill s omega‖ ≤ R' :=
    norm_beforeContinuousExitProcessOf_le H R' R' hcap
  have hgeneric := eLpNorm_sub_localized_uniformAdapted_apply_le
    hMtau hMrho T hNT hHkill R' hHkillBound n t
  have hreplace := uniformAdapted_sub_localized_replace_beforeContinuousExit
    M E Hn T (n + 1) H R' htauE hrhoE
  have heqProcess :
      localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) rho =
      localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hkill T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hkill T (n + 1)) rho := by
    rw [localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      uniformAdaptedMartingaleLeftSumProcess_sub, hreplace,
      ← uniformAdaptedMartingaleLeftSumProcess_sub,
      ← localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess,
      ← localizingStoppedProcess_uniformAdaptedMartingaleLeftSumProcess]
  unfold cappedDoleansDadeLeftSumProcess
  change eLpNorm
    ((localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) tau -
        localizingStoppedProcess
          (uniformAdaptedMartingaleLeftSumProcess M Hn T (n + 1)) rho) t)
      2 P ≤ _
  rw [congrFun heqProcess t]
  exact hgeneric

/-- The grid-independent outer-capped Doléans error bound tends to zero as
the inner dyadic exits converge to their continuous exits. -/
theorem tendsto_outerCappedDyadic_doleans_error_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (H K R K' R' T : ℝ≥0) (hKK' : K ≤ K') (hRR' : R ≤ R')
    (hpos : ∀ omega, (⊥ : WithTop ℝ≥0) <
      min (continuousExitTime M H K omega)
        (continuousExitTime (doleansDadeExponential M bracket) H R omega)) :
    let E := doleansDadeExponential M bracket
    let tau : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K omega)
        (continuousExitTime E H R omega)
    let theta : W → WithTop ℝ≥0 := fun omega =>
      min (continuousExitTime M H K' omega)
        (continuousExitTime E H R' omega)
    let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
      min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
    Tendsto
      (fun m => R' * eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) 0) 2 P)
      Filter.atTop (nhds 0) := by
  dsimp only
  let E := doleansDadeExponential M bracket
  let tau : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K omega)
      (continuousExitTime E H R omega)
  let theta : W → WithTop ℝ≥0 := fun omega =>
    min (continuousExitTime M H K' omega)
      (continuousExitTime E H R' omega)
  let rho : ℕ → W → WithTop ℝ≥0 := fun m omega =>
    min (pairedDyadicHittingTimeNNReal M E H K R m omega) (theta omega)
  have hEadapt : StronglyAdapted 𝒱 E :=
    stronglyAdapted_doleansDadeExponential hM hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have htau_rho (m : ℕ) (omega : W) : tau omega ≤ rho m omega := by
    have hMdyadic : continuousExitTime M H K omega ≤
        dyadicHittingTimeNNReal M H K m omega := by
      unfold continuousExitTime
      exact iInf_le _ m
    have hEdyadic : continuousExitTime E H R omega ≤
        dyadicHittingTimeNNReal E H R m omega := by
      unfold continuousExitTime
      exact iInf_le _ m
    have hsigma : tau omega ≤
        pairedDyadicHittingTimeNNReal M E H K R m omega := by
      exact min_le_min hMdyadic hEdyadic
    have htheta : tau omega ≤ theta omega :=
      min_le_min (continuousExitTime_mono_radius M H K K' hKK' omega)
        (continuousExitTime_mono_radius E H R R' hRR' omega)
    exact le_min hsigma htheta
  have hrhopos (m : ℕ) (omega : W) :
      (⊥ : WithTop ℝ≥0) < rho m omega :=
    (hpos omega).trans_le (htau_rho m omega)
  have hzero (m : ℕ) :
      (localizingStoppedProcess M tau -
        localizingStoppedProcess M (rho m)) 0 = fun _ => 0 := by
    funext omega
    simp only [Pi.sub_apply]
    rw [localizingStoppedProcess_zero_of_pos M tau omega (hpos omega),
      localizingStoppedProcess_zero_of_pos M (rho m) omega
        (hrhopos m omega), sub_self]
  have hraw :=
    tendsto_eLpNorm_two_localizingStoppedProcess_pairedDyadic_min_outerExit
      (P := P) hM hEadapt hMcont H K R K' R' hKK' hRR' hpos T
  have hterminal : Tendsto
      (fun m => eLpNorm
        ((localizingStoppedProcess M tau -
          localizingStoppedProcess M (rho m)) T) 2 P)
      Filter.atTop (nhds 0) := by
    simpa only [tau, rho, theta, Pi.sub_apply,
      eLpNorm_sub_comm] using hraw
  have hincrement : Tendsto
      (fun m => eLpNorm
        ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T -
          (localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) 0) 2 P)
      Filter.atTop (nhds 0) := by
    apply hterminal.congr'
    exact Filter.Eventually.of_forall fun m => by
      change eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T) 2 P =
        eLpNorm
          ((localizingStoppedProcess M tau -
              localizingStoppedProcess M (rho m)) T -
            (localizingStoppedProcess M tau -
              localizingStoppedProcess M (rho m)) 0) 2 P
      rw [hzero m]
      change eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T) 2 P =
        eLpNorm
          ((localizingStoppedProcess M tau -
            localizingStoppedProcess M (rho m)) T - 0) 2 P
      rw [sub_zero]
  have hmul := ENNReal.Tendsto.const_mul
    (a := (R' : ℝ≥0∞)) hincrement (Or.inr ENNReal.coe_ne_top)
  simpa only [tau, rho, theta, mul_zero] using hmul

/-- After stopping both the integrator and the stochastic exponential at
bounded continuous exits, the diagonal capped Doléans left sums have a
grid-independent terminal `L²` bound.  The exponential exit, rather than
the growing deterministic cap, supplies the uniform coefficient bound. -/
theorem
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R : ℝ≥0) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R) T) 2 P ≤
      R * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) 0)
          2 P := by
  let E := doleansDadeExponential M bracket
  have hEadapt : StronglyAdapted 𝓥 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  have hEcont : ∀ omega, Continuous (fun t => E t omega) := fun omega =>
    continuous_doleansDadeExponential M bracket omega
      (hMcont omega) (hbracketCont omega)
  have hcap : ∀ (t : ℝ≥0) omega,
      (t : WithTop ℝ≥0) < continuousExitTime E ET R omega →
        ‖cappedDoleansDadeExponential M bracket (n + 1) t omega‖ ≤ R := by
    intro t omega ht
    have hER := norm_le_of_lt_continuousExitTime hEcont ET R t omega ht
    rw [abs_of_pos (doleansDadeExponential_pos M bracket t omega)] at hER
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (min_le_left _ _).trans hER
    · exact le_min (doleansDadeExponential_pos M bracket t omega).le
        (NNReal.coe_nonneg _)
  unfold cappedDoleansDadeLeftSumProcess
  exact eLpNorm_doubleExit_localized_uniformAdaptedOf_le
    hM hMcont hEadapt
    (stronglyAdapted_cappedDoleansDadeExponential
      hM.stronglyAdapted hbracket (n + 1))
    T MT K ET R R hcap n

/-- The same two bounded continuous exits turn every diagonal capped
Doléans left-sum process into a genuine martingale. -/
theorem
    martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (T MT K ET R : ℝ≥0) (n : ℕ) :
    Martingale
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R))
      𝓥 P := by
  let tauM := continuousExitTime M MT K
  let E := doleansDadeExponential M bracket
  let X := cappedDoleansDadeLeftSumProcess M bracket T n
  let X1 := localizingStoppedProcess X tauM
  have hN1 : Martingale (localizingStoppedProcess M tauM) 𝓥 P :=
    martingale_localizingStoppedProcess_continuousExitTime hM hMcont MT K
  have hX1 : Martingale X1 𝓥 P := by
    exact martingale_localizingStoppedProcess_cappedDoleansDadeLeftSumProcess
      hN1 hM.stronglyAdapted hbracket T n
  have hXcont : ∀ omega, Continuous (fun t => X t omega) := fun omega =>
    continuous_uniformAdaptedMartingaleLeftSumProcess hMcont
      T (n + 1) omega
  have hX1cont : ∀ omega, Continuous (fun t => X1 t omega) :=
    continuous_localizingStoppedProcess_continuousExitTime hXcont MT K
  have hEadapt : StronglyAdapted 𝓥 E :=
    stronglyAdapted_doleansDadeExponential hM.stronglyAdapted hbracket
  exact martingale_localizingStoppedProcess_continuousExitTime_of_adapted
    hX1 hX1cont hEadapt ET R

/-- The grid-independent `L²` bound for twice-exit-localized diagonal
Doléans sums holds at every observation time, not only at the terminal
horizon.  Before the horizon this is martingale contraction; afterwards it
uses eventual constancy of the coherent left-sum process. -/
theorem
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R t : ℝ≥0) (n : ℕ) :
    eLpNorm
      (localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n)
          (continuousExitTime M MT K))
        (continuousExitTime (doleansDadeExponential M bracket) ET R) t) 2 P ≤
      R * eLpNorm
        (localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) T -
          localizingStoppedProcess
            (localizingStoppedProcess M (continuousExitTime M MT K))
            (continuousExitTime (doleansDadeExponential M bracket) ET R) 0)
          2 P := by
  let tauM := continuousExitTime M MT K
  let tauE := continuousExitTime (doleansDadeExponential M bracket) ET R
  let X := cappedDoleansDadeLeftSumProcess M bracket T n
  let X1 := localizingStoppedProcess X tauM
  let X2 := localizingStoppedProcess X1 tauE
  have hterminal :=
    eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_le
      hM hMcont hbracket hbracketCont T MT K ET R n
  rcases le_total t T with htT | hTt
  · exact (martingale_eLpNorm_le_of_le
      (martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
        hM hMcont hbracket T MT K ET R n) htT one_le_two).trans hterminal
  · have hXconst : ∀ s, T ≤ s → X s = X T := by
      intro s hTs
      exact uniformAdaptedMartingaleLeftSumProcess_eq_terminal_of_le
        M (cappedDoleansDadeExponential M bracket (n + 1)) T n s hTs
    have hX1const : ∀ s, T ≤ s → X1 s = X1 T := by
      intro s hTs
      exact localizingStoppedProcess_eq_terminal_of_le
        X tauM T s hTs hXconst
    have hX2eq : X2 t = X2 T :=
      localizingStoppedProcess_eq_terminal_of_le
        X1 tauE T t hTt hX1const
    rw [show localizingStoppedProcess
        (localizingStoppedProcess
          (cappedDoleansDadeLeftSumProcess M bracket T n) tauM) tauE t =
        localizingStoppedProcess
          (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n) tauM) tauE T
      from hX2eq]
    exact hterminal

/-- The twice-exit-localized diagonal capped Doléans sums are uniformly
integrable at every observation time. -/
theorem
    uniformIntegrable_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝓥]
    [𝓥.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} (hM : Martingale M 𝓥 P)
    (hMcont : ∀ omega, Continuous (fun t => M t omega))
    (hbracket : StronglyAdapted 𝓥 bracket)
    (hbracketCont : ∀ omega, Continuous (fun t => bracket t omega))
    (T MT K ET R t : ℝ≥0) :
    UniformIntegrable
      (fun n =>
        localizingStoppedProcess
          (localizingStoppedProcess
            (cappedDoleansDadeLeftSumProcess M bracket T n)
            (continuousExitTime M MT K))
          (continuousExitTime (doleansDadeExponential M bracket) ET R) t)
      1 P := by
  let E := doleansDadeExponential M bracket
  let N := localizingStoppedProcess
    (localizingStoppedProcess M (continuousExitTime M MT K))
    (continuousExitTime E ET R)
  let C : ℝ≥0 := (R * eLpNorm (N T - N 0) 2 P).toNNReal
  have hNmart : Martingale N 𝓥 P := by
    have hN1 := martingale_localizingStoppedProcess_continuousExitTime
      hM hMcont MT K
    have hN1cont := continuous_localizingStoppedProcess_continuousExitTime
      (Z := M) hMcont MT K
    exact martingale_localizingStoppedProcess_continuousExitTime_of_adapted
      hN1 hN1cont
        (stronglyAdapted_doleansDadeExponential
          hM.stronglyAdapted hbracket) ET R
  have hNT : MemLp (N T) 2 P := by
    apply MemLp.of_bound
      ((hNmart.stronglyAdapted T).mono (𝓥.le T)).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun omega =>
      norm_localizingStoppedProcess_le K
        (norm_localizingStoppedProcess_continuousExitTime_le hMcont MT K)
        T omega
  have hN0 : MemLp (N 0) 2 P :=
    martingale_memLp_of_le hNmart bot_le one_le_two hNT
  have hfinite : R * eLpNorm (N T - N 0) 2 P ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hNT.sub hN0).2.ne
  apply uniformIntegrable_one_of_uniform_eLpNorm_two (C := C)
  · intro n
    exact (((martingale_doubleExit_localized_cappedDoleansDadeLeftSumProcess
      hM hMcont hbracket T MT K ET R n).stronglyAdapted t).mono
        (𝓥.le t)).aestronglyMeasurable
  · intro n
    rw [show (C : ℝ≥0∞) = R * eLpNorm (N T - N 0) 2 P by
      exact ENNReal.coe_toNNReal hfinite]
    exact
      eLpNorm_doubleExit_localized_cappedDoleansDadeLeftSumProcess_apply_le
        hM hMcont hbracket hbracketCont T MT K ET R t n

/-- Under the before-stop quadratic-variation contract, the quadratic sums
weighted by one half of the Doléans--Dade exponential converge in measure to
the corresponding pathwise Stieltjes bracket integral.  This is the
second-order half of the drift cancellation for an arbitrary continuous
bracket. -/
theorem
    generalItoMixedQuadratic_doleansDadeLog_tendstoInMeasure_stieltjes
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝓥 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝓥 M) (hbracket : StronglyAdapted 𝓥 bracket)
    (hMcont : ∀ᵐ omega ∂P, Continuous (fun s ↦ M s omega))
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n ↦ generalItoMixedQuadraticApprox
        (fun _ x ↦ Real.exp x) (doleansDadeLog M bracket) M t (n + 1))
      Filter.atTop
      (stieltjesBracketIntegral
        (fun s omega ↦ (1 / 2 : ℝ) *
          doleansDadeExponential M bracket s omega)
        bracket t) := by
  have hsecond : Continuous (fun p : ℝ × ℝ ↦
      itoSpaceSecondDerivative (fun _ x ↦ Real.exp x) p.1 p.2) := by
    simp only [itoSpaceSecondDerivative, Real.deriv_exp]
    fun_prop
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝓥.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝓥.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hweightMeas : ∀ s, AEStronglyMeasurable
      (fun omega ↦ (1 / 2 : ℝ) *
        doleansDadeExponential M bracket s omega) P := by
    intro s
    exact aestronglyMeasurable_const.mul
      (Real.continuous_exp.comp_aestronglyMeasurable (hlogMeas s))
  have hweightCont : ∀ᵐ omega ∂P, Continuous (fun s ↦
      (1 / 2 : ℝ) * doleansDadeExponential M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact continuous_const.mul
      (continuous_doleansDadeExponential M bracket omega
        hMomega hbracketOmega.1)
  have hG := bracketWeightedLeftSum_tendstoInMeasure
    (fun s omega ↦ (1 / 2 : ℝ) *
      doleansDadeExponential M bracket s omega)
    bracket hweightMeas hbracketMeas hweightCont hbracketPath t
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact aestronglyMeasurable_generalItoMixedQuadraticApprox
        (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket) M
        hlogMeas hMmeas 0 (n + 1)
    · filter_upwards with omega
      simp [generalItoMixedQuadraticApprox, stieltjesBracketIntegral,
        uniformPartitionTime]
  · apply generalItoMixedQuadratic_tendstoInMeasure_of_beforeStop
      (fun _ x ↦ Real.exp x) hsecond (doleansDadeLog M bracket) M
      hlogMeas hMmeas t ht bracket
        (stieltjesBracketIntegral
          (fun s omega ↦ (1 / 2 : ℝ) *
            doleansDadeExponential M bracket s omega) bracket t)
      (Y := doleansDadeLog M bracket)
    · intro a ha
      simpa only [min_eq_right ha] using hbefore t a
    · simp only [itoSpaceSecondDerivative, Real.deriv_exp]
      change TendstoInMeasure P
        (fun k ↦ bracketWeightedLeftSum
          (fun s omega ↦ (1 / 2 : ℝ) *
            Real.exp (doleansDadeLog M bracket s omega))
          bracket t (k + 1)) Filter.atTop
        (stieltjesBracketIntegral
          (fun s omega ↦ (1 / 2 : ℝ) *
            doleansDadeExponential M bracket s omega) bracket t)
      simpa only [doleansDadeExponential] using hG
    · refine ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, ?_⟩
      filter_upwards [hMcont, hbracketPath]
        with omega hMomega hbracketOmega
      exact hMomega.sub (continuous_const.mul hbracketOmega.1)

/-- The compensated logarithm `M - (1/2) bracket` has the same fixed-time
quadratic variation as `M`: the continuous monotone bracket term has zero
quadratic variation and hence may be removed. -/
theorem hasQuadraticVariationInProbabilityAt_doleansDadeLog
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted 𝒱 M) (hbracket : StronglyAdapted 𝒱 bracket)
    (hbracketPath : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ bracket s omega) ∧
        Monotone (fun s ↦ bracket s omega))
    (hbefore : HasQuadraticVariationBeforeStopProcessInProbability
      M bracket P)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (doleansDadeLog M bracket) P t (bracket t) := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketZero : HasQuadraticVariationInProbabilityAt
      bracket P t (fun _ ↦ 0) :=
    quadraticVariation_continuous_monotone_inProbability_zero
      bracket hbracketMeas hbracketPath t
  have hdriftZero : HasQuadraticVariationInProbabilityAt
      (fun s omega ↦ (-1 / 2 : ℝ) * bracket s omega) P t (fun _ ↦ 0) := by
    simpa only [mul_zero] using hbracketZero.const_mul hbracketMeas (-1 / 2 : ℝ)
  have hsum := hdriftZero.add_of_left_zero_of_aestronglyMeasurable
    (hbefore.toProcess t)
    (fun s ↦ aestronglyMeasurable_const.mul (hbracketMeas s)) hMmeas
  apply hsum.congr
  · intro s
    filter_upwards with omega
    simp only [doleansDadeLog]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Taylor's second-order remainder for the exponential of the compensated
logarithm vanishes in probability.  The bracket limit required by Taylor's
theorem is supplied by `hasQuadraticVariationInProbabilityAt_doleansDadeLog`.
-/
theorem doleansDadeLog_exp_stateTaylorRemainder_tendstoInMeasure
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
      (fun n ↦ itoStateTaylorRemainderApprox Real.exp
        (doleansDadeLog M bracket) t (n + 1))
      Filter.atTop (fun _ ↦ 0) := by
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s ↦
    ((hM s).mono (𝒱.le s)).aestronglyMeasurable
  have hbracketMeas : ∀ s, AEStronglyMeasurable (bracket s) P :=
    fun s ↦ ((hbracket s).mono (𝒱.le s)).aestronglyMeasurable
  have hlogMeas : ∀ s,
      AEStronglyMeasurable (doleansDadeLog M bracket s) P := by
    intro s
    exact (hMmeas s).sub
      (aestronglyMeasurable_const.mul (hbracketMeas s))
  have hlogCont : ∀ᵐ omega ∂P,
      Continuous (fun s ↦ doleansDadeLog M bracket s omega) := by
    filter_upwards [hMcont, hbracketPath]
      with omega hMomega hbracketOmega
    exact hMomega.sub (continuous_const.mul hbracketOmega.1)
  have hself : IsContinuousProcessModification
      (doleansDadeLog M bracket) (doleansDadeLog M bracket) P :=
    ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl, hlogCont⟩
  exact hself.stateTaylorRemainder_tendstoInMeasure Real.exp
    Real.contDiff_exp t (bracket t) hlogMeas
    (hasQuadraticVariationInProbabilityAt_doleansDadeLog
      hM hbracket hbracketPath hbefore t)

/-- The exponential test function has zero time derivative. -/
theorem itoTimeDerivative_exp_state (s x : ℝ) :
    itoTimeDerivative (fun _ x => Real.exp x) s x = 0 := by
  simp [itoTimeDerivative]

/-- The first state derivative of the exponential test function is itself. -/
theorem itoSpaceDerivative_exp_state (s x : ℝ) :
    itoSpaceDerivative (fun _ x => Real.exp x) s x = Real.exp x := by
  simp [itoSpaceDerivative, Real.deriv_exp]

end StochasticCalculus
