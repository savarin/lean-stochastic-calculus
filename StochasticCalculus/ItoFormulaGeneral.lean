/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.ItoFormulaPartition

/-!
# Continuous modifications of natural Itô processes

Doob's compact-time `L²` bound for a continuous modification of a natural
Itô process, uniform-step control of differences of continuous
modifications, the limit of a fast-converging sequence of modifications,
continuous representatives of elementary finite combinations, and the
existence of a continuous modification of every natural predictable Itô
integral, with its before-stop quadratic variation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W]
  {P : Measure W} {B X μ σ : ℝ≥0 → W → ℝ}

variable [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian P]

omit [CompleteSpace W] [BorelSpace W] in
/-- A continuous modification of a natural Itô process satisfies Doob's
compact-time `L²` bound.  The proof first controls the increasing union of
dyadic-grid events, transfers those countably many values across the
fixed-time modification relation, and then uses path continuity to detect
every strict excursion on `[0,t]`. -/
theorem IsContinuousProcessModification.naturalIto_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {Y : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) Y P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let R : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB hsm rfl U
  let A : Set W :=
    {omega | ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2}
  let D : Set W :=
    ⋃ n : ℕ, {omega | (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega}
  have hdyadic : ∀ᵐ omega ∂P, ∀ n : ℕ,
      dyadicPartitionSqMax Y t n omega =
        dyadicPartitionSqMax R t n omega := by
    apply ae_all_iff.mpr
    intro n
    exact (dyadicPartitionSqMax_congr_ae hmod.fixedTime_ae_eq t n).symm
  have hAD : A ≤ᵐ[P] D := by
    filter_upwards [hmod.continuous_paths, hdyadic] with omega hcontinuous heq
    intro homega
    change ∃ s : ℝ≥0, s ≤ t ∧ (ε : ℝ) < (Y s omega) ^ 2 at homega
    obtain ⟨s, hst, hs⟩ := homega
    obtain ⟨n, hn⟩ := exists_lt_dyadicPartitionSqMax_of_continuous
      Y t omega hcontinuous hst hs
    simp only [D, Set.mem_iUnion]
    refine ⟨n, ?_⟩
    change (ε : ℝ) ≤ dyadicPartitionSqMax R t n omega
    rw [← heq n]
    exact hn.le
  change (ε : ℝ≥0∞) * P A ≤ ENNReal.ofReal (‖U‖ ^ 2)
  calc
    (ε : ℝ≥0∞) * P A ≤ (ε : ℝ≥0∞) * P D :=
      mul_le_mul_of_nonneg_left (measure_mono_ae hAD) bot_le
    _ ≤ ENNReal.ofReal (‖U‖ ^ 2) := by
      exact naturalItoProcessRepresentative_dyadicPartition_maximal_sq_iUnion
        hB hsm U ε t

omit [CompleteSpace W] [BorelSpace W] in
/-- The difference of continuous modifications of two natural Itô processes
is a continuous modification of the natural Itô process of the integrand
difference.  Representative linearity is used only at fixed times, where it
is valid almost everywhere. -/
theorem naturalItoContinuousModification_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V) YV P) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U - V))
      (fun s omega => YU s omega - YV s omega) P := by
  constructor
  · intro s
    filter_upwards [naturalItoProcessRepresentative_sub_ae hB hsm U V s,
      hU.fixedTime_ae_eq s, hV.fixedTime_ae_eq s]
      with omega hsub hYU hYV
    rw [← hsub, hYU, hYV]
  · filter_upwards [hU.continuous_paths, hV.continuous_paths]
      with omega hYU hYV
    exact hYU.sub hYV

omit [CompleteSpace W] [BorelSpace W] in
/-- Compact-time Doob estimate for the difference of any two continuous
natural-Itô representatives.  This is the uniform-Cauchy estimate consumed
by the predictable-`L²` density construction. -/
theorem naturalItoContinuousModification_sub_compact_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P)
    {YU YV : ℝ≥0 → W → ℝ}
    (hU : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl U) YU P)
    (hV : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V) YV P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P {omega | ∃ s : ℝ≥0, s ≤ t ∧
        (ε : ℝ) < (YU s omega - YV s omega) ^ 2} ≤
      ENNReal.ofReal (‖U - V‖ ^ 2) := by
  have hmod := naturalItoContinuousModification_sub hB hsm U V hU hV
  exact hmod.naturalIto_compact_maximal_sq_ineq hB hsm (U - V) ε t

omit [CompleteSpace W] [BorelSpace W] in
/-- Borel--Cantelli consequence of the compact maximal estimate.  If the
normalized squared `L²` increments of a sequence of integrands are summable,
then the corresponding continuous representatives eventually have uniformly
small successive increments on `[0,t]`, almost surely. -/
theorem naturalItoContinuousModifications_eventually_uniform_step
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U n)) (Y n) P)
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsum : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (t : ℝ≥0) :
    ∀ᵐ omega ∂P, ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ t →
      (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
  let A : ℕ → Set W := fun n =>
    {omega | ∃ s : ℝ≥0, s ≤ t ∧
      (δ n : ℝ) < (Y (n + 1) s omega - Y n s omega) ^ 2}
  have hmeasure : ∀ n,
      P (A n) ≤
        ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) := by
    intro n
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr (ne_of_gt (hδ n))))
      (Or.inl ENNReal.coe_ne_top)).2
    rw [mul_comm]
    exact naturalItoContinuousModification_sub_compact_maximal_sq_ineq
      hB hsm (U (n + 1)) (U n) (hmod (n + 1)) (hmod n) (δ n) t
  have hsumMeasure : (∑' n : ℕ, P (A n)) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hmeasure)
  have hBC := ae_eventually_notMem hsumMeasure
  filter_upwards [hBC] with omega homega
  filter_upwards [homega] with n hn
  intro s hst
  by_contra hle
  exact hn ⟨s, hst, lt_of_not_ge hle⟩

/-- Pointwise canonical limit of a sequence of candidate process
representatives.  The fallback branch is irrelevant on the almost-everywhere
set where the sequence is Cauchy. -/
noncomputable def continuousModificationSequenceLimit
    (Y : ℕ → ℝ≥0 → W → ℝ) : ℝ≥0 → W → ℝ :=
  fun s omega => completeCauchySeqLimit (fun n => Y n s omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- Closure of continuous natural-Itô modifications under a sufficiently
fast predictable-`L²` limit.  The two summability hypotheses are exactly the
probabilistic Borel--Cantelli bound and the deterministic uniform-Cauchy
bound, respectively. -/
theorem continuousModification_naturalItoProcess_of_fast_tendsto
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (V : PredictableProcessL2 (Filtration.natural B hsm) P)
    (U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P)
    (Y : ℕ → ℝ≥0 → W → ℝ)
    (hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl (U n)) (Y n) P)
    (hUV : Filter.Tendsto U Filter.atTop (nhds V))
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞)
    (hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ))) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB hsm rfl V)
      (continuousModificationSequenceLimit Y) P := by
  have hcontinuous : ∀ᵐ omega ∂P, ∀ n : ℕ,
      Continuous (fun s => Y n s omega) := by
    apply ae_all_iff.mpr
    intro n
    exact (hmod n).continuous_paths
  have hsteps : ∀ᵐ omega ∂P, ∀ k : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ s : ℝ≥0, s ≤ (k : ℝ≥0) →
        (Y (n + 1) s omega - Y n s omega) ^ 2 ≤ (δ n : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    exact naturalItoContinuousModifications_eventually_uniform_step
      hB hsm U Y hmod δ hδ hsumProbability k
  have huniform : ∀ᵐ omega ∂P, ∀ k : ℕ,
      UniformCauchySeqOn (fun n s => Y n s omega) Filter.atTop
        (Set.Iic (k : ℝ≥0)) := by
    filter_upwards [hsteps] with omega homega
    intro k
    apply uniformCauchySeqOn_of_eventually_dist_le_of_summable
      (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0))
      (fun n => Real.sqrt (δ n : ℝ))
      (fun n => Real.sqrt_nonneg _) hsumUniform
    filter_upwards [homega k] with n hn
    intro s hs
    have hsqrt := Real.sqrt_le_sqrt (hn s hs)
    simpa only [Real.dist_eq, Real.sqrt_sq_eq_abs, abs_sub_comm] using hsqrt
  constructor
  · intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s ≤ (k : ℝ≥0) := exists_nat_ge s
    have hpointwise : ∀ᵐ omega ∂P,
        Filter.Tendsto (fun n => Y n s omega) Filter.atTop
          (nhds (continuousModificationSequenceLimit Y s omega)) := by
      filter_upwards [huniform] with omega homega
      unfold continuousModificationSequenceLimit
      exact tendsto_completeCauchySeqLimit ((homega k).cauchySeq hsk)
    have hYmeas : ∀ n, AEStronglyMeasurable (Y n s) P := by
      intro n
      have hrepmeas : AEStronglyMeasurable
          (naturalItoProcessRepresentative hB hsm rfl (U n) s) P :=
        AEStronglyMeasurable.mono ((Filtration.natural B hsm).le s)
          (stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm rfl (U n) s).aestronglyMeasurable
      exact hrepmeas.congr ((hmod n).fixedTime_ae_eq s)
    have hrestrict : Filter.Tendsto
        (fun n => predictableTimeRestrict (Filtration.natural B hsm) s (U n))
        Filter.atTop
        (nhds (predictableTimeRestrict (Filtration.natural B hsm) s V)) := by
      change Filter.Tendsto
        ((predictableTimeRestrictCLM (Filtration.natural B hsm) s) ∘ U)
        Filter.atTop
        (nhds (predictableTimeRestrict (Filtration.natural B hsm) s V))
      exact ((predictableTimeRestrictCLM
        (Filtration.natural B hsm) s).continuous.tendsto V).comp hUV
    have hLp : Filter.Tendsto
        (fun n => naturalItoProcess hB hsm rfl (U n) s)
        Filter.atTop (nhds (naturalItoProcess hB hsm rfl V s)) := by
      change Filter.Tendsto
        ((naturalItoIntegral hB hsm rfl) ∘
          fun n => predictableTimeRestrict (Filtration.natural B hsm) s (U n))
        Filter.atTop
        (nhds (naturalItoProcess hB hsm rfl V s))
      exact ((naturalItoIntegral hB hsm rfl).continuous.tendsto
        (predictableTimeRestrict (Filtration.natural B hsm) s V)).comp hrestrict
    have htoTarget : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (naturalItoProcessRepresentative hB hsm rfl V s) := by
      have hraw := tendstoInMeasure_of_tendsto_Lp hLp
      apply TendstoInMeasure.congr_right
        (naturalItoProcess_ae_eq_representative hB hsm rfl V s)
      apply TendstoInMeasure.congr_left _ hraw
      intro n
      exact (naturalItoProcess_ae_eq_representative hB hsm rfl (U n) s).trans
        ((hmod n).fixedTime_ae_eq s)
    have htoLimit : TendstoInMeasure P (fun n => Y n s) Filter.atTop
        (continuousModificationSequenceLimit Y s) :=
      tendstoInMeasure_of_tendsto_ae hYmeas hpointwise
    exact tendstoInMeasure_ae_unique htoTarget htoLimit
  · filter_upwards [hcontinuous, huniform] with omega hcont huc
    rw [continuous_iff_continuousAt]
    intro s
    obtain ⟨k, hsk⟩ : ∃ k : ℕ, s < (k : ℝ≥0) := exists_nat_gt s
    have hlimitContinuous : ContinuousOn
        (continuousModificationSequenceLimit Y · omega)
        (Set.Iic (k : ℝ≥0)) := by
      unfold continuousModificationSequenceLimit
      exact continuousOn_completeCauchySeqLimit
        (fun n s => Y n s omega) (Set.Iic (k : ℝ≥0)) (huc k)
          (fun n => (hcont n).continuousOn)
    exact hlimitContinuous.continuousAt (Iic_mem_nhds hsk)

/-- The explicit continuous Brownian-block representative of the natural Itô
process associated with a finite elementary predictable integrand. -/
noncomputable def elementaryFinsuppItoContinuousRepresentative
    (B : ℝ≥0 → W → ℝ) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    ℝ≥0 → W → ℝ :=
  fun s omega => ∑ x ∈ v.support,
    v x * (x.2.2 : W → ℝ) omega *
      (B (min s x.2.1.1) omega - B (min s x.1) omega)

omit [CompleteSpace W] [BorelSpace W] in
/-- On the finite elementary predictable layer, the selected natural Itô
representative has an explicit continuous modification. -/
theorem elementaryFinsuppItoContinuousModification
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P v))
      (elementaryFinsuppItoContinuousRepresentative B hsm v) P := by
  constructor
  · intro s
    change naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P v) s =ᵐ[P]
      (fun omega => ∑ x ∈ v.support, v x * (x.2.2 : W → ℝ) omega *
        (B (min s x.2.1.1) omega - B (min s x.1) omega))
    exact naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
      hB.toIsPreBrownianReal hsm v s
  · filter_upwards [hB.cont] with omega hBcontinuous
    unfold elementaryFinsuppItoContinuousRepresentative
    apply continuous_finsetSum
    intro x _hx
    exact continuous_const.mul
      ((hBcontinuous.comp (continuous_id.min continuous_const)).sub
        (hBcontinuous.comp (continuous_id.min continuous_const)))

omit [CompleteSpace W] [BorelSpace W] in
/-- Quantitative version of elementary density: the approximation rate may
be prescribed arbitrarily, as long as every requested radius is positive.
This is the form used to choose a Borel--Cantelli-fast sequence. -/
theorem exists_elementaryFinsupp_continuousModifications_dist_lt
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ v : ℕ →
        (ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ),
      (∀ n, dist U
        (elementaryFinsuppToPredictable
          (Filtration.natural B hsm) P (v n)) < r n) ∧
      ∀ n, IsContinuousProcessModification
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
          (elementaryFinsuppToPredictable
            (Filtration.natural B hsm) P (v n)))
        (elementaryFinsuppItoContinuousRepresentative B hsm (v n)) P := by
  have hdense := denseRange_elementaryFinsuppToPredictable (P := P)
    (Filtration.natural B hsm)
  choose v hv using fun n => hdense.exists_dist_lt U (hr n)
  refine ⟨v, hv, ?_⟩
  intro n
  exact elementaryFinsuppItoContinuousModification hB hsm (v n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Every natural Itô process has a continuous modification.  Choose
elementary predictable integrands within `8⁻ⁿ` of the target.  Their
successive squared `L²` distances are dominated by `4 · 64⁻ⁿ`; with
thresholds `4⁻ⁿ`, both series required by the fast-limit closure theorem
are geometric. -/
theorem exists_continuousModification_naturalItoProcess
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (V : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ∃ Y : ℝ≥0 → W → ℝ, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl V) Y P := by
  let r : ℕ → ℝ := fun n => (1 / 8 : ℝ) ^ n
  obtain ⟨v, hv, hvmod⟩ :=
    exists_elementaryFinsupp_continuousModifications_dist_lt
      hB hsm V r (by intro n; simp only [r]; positivity)
  let U : ℕ → PredictableProcessL2 (Filtration.natural B hsm) P :=
    fun n => elementaryFinsuppToPredictable
      (Filtration.natural B hsm) P (v n)
  let Y : ℕ → ℝ≥0 → W → ℝ :=
    fun n => elementaryFinsuppItoContinuousRepresentative B hsm (v n)
  let δ : ℕ → ℝ≥0 := fun n => (1 / 4 : ℝ≥0) ^ n
  have hdist : ∀ n, dist V (U n) < (1 / 8 : ℝ) ^ n := by
    intro n
    simpa only [U, r] using hv n
  have hmod : ∀ n, IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl (U n))
      (Y n) P := by
    intro n
    simpa only [U, Y] using hvmod n
  have hUV : Filter.Tendsto U Filter.atTop (nhds V) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hpow : Filter.Tendsto (fun n : ℕ => (1 / 8 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hpow ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hr : (1 / 8 : ℝ) ^ n < ε := by
      have hrabs := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (pow_nonneg (by norm_num) n)] at hrabs
      exact hrabs
    have hn := hdist n
    rw [dist_comm] at hn
    exact hn.trans hr
  have hδ : ∀ n, 0 < δ n := by
    intro n
    simp only [δ]
    positivity
  have hsq : ∀ n, ‖U (n + 1) - U n‖ ^ 2 ≤
      4 * (1 / 64 : ℝ) ^ n := by
    intro n
    have hstep : ‖U (n + 1) - U n‖ < 2 * (1 / 8 : ℝ) ^ n := by
      calc
        ‖U (n + 1) - U n‖ = dist (U (n + 1)) (U n) :=
          (dist_eq_norm _ _).symm
        _ ≤ dist (U (n + 1)) V + dist V (U n) := dist_triangle _ _ _
        _ < (1 / 8 : ℝ) ^ (n + 1) + (1 / 8 : ℝ) ^ n :=
          add_lt_add (by simpa only [dist_comm] using hdist (n + 1))
            (hdist n)
        _ ≤ 2 * (1 / 8 : ℝ) ^ n := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) n]
    have hsq' : ‖U (n + 1) - U n‖ ^ 2 ≤
        (2 * (1 / 8 : ℝ) ^ n) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hstep.le
    calc
      ‖U (n + 1) - U n‖ ^ 2 ≤ (2 * (1 / 8 : ℝ) ^ n) ^ 2 := hsq'
      _ = 4 * (1 / 64 : ℝ) ^ n := by
        have hp : ((1 / 8 : ℝ) ^ n) ^ 2 = (1 / 64 : ℝ) ^ n := by
          rw [show (1 / 64 : ℝ) = (1 / 8 : ℝ) ^ 2 by norm_num]
          simp only [← pow_mul, Nat.mul_comm]
        rw [mul_pow, hp]
        norm_num
  have hnormalized : ∀ n,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞) ≤
        4 * (1 / 16 : ℝ≥0∞) ^ n := by
    intro n
    change ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
        ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
      4 * (1 / 16 : ℝ≥0∞) ^ n
    calc
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) ≤
          ENNReal.ofReal (4 * (1 / 64 : ℝ) ^ n) /
            ((((1 / 4 : ℝ≥0) ^ n) : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact hsq n
      _ = 4 * (1 / 16 : ℝ≥0∞) ^ n := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity), ENNReal.coe_pow]
        have hofReal : ENNReal.ofReal (1 / 64 : ℝ) =
            (1 / 64 : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64)]
          norm_num
        rw [hofReal]
        norm_num only [ENNReal.ofReal_ofNat, ENNReal.coe_div,
          ENNReal.coe_one, ENNReal.coe_ofNat]
        rw [mul_div_assoc]
        congr 1
        simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, ← mul_pow]
        congr 1
        simp only [mul_one, inv_inv]
        change ((4 : ℝ≥0) : ℝ≥0∞) *
            (((64 : ℝ≥0) : ℝ≥0∞))⁻¹ =
          (((16 : ℝ≥0) : ℝ≥0∞))⁻¹
        rw [← ENNReal.coe_inv (by norm_num : (64 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_inv (by norm_num : (16 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_mul]
        norm_num
  have hsumProbability : (∑' n : ℕ,
      ENNReal.ofReal (‖U (n + 1) - U n‖ ^ 2) / (δ n : ℝ≥0∞)) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (b := ∑' n : ℕ, 4 * (1 / 16 : ℝ≥0∞) ^ n)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.inv_ne_top.mpr
          (ne_of_gt (tsub_pos_iff_lt.mpr
            (by norm_num : (1 / 16 : ℝ≥0∞) < 1)))
    · exact ENNReal.tsum_le_tsum hnormalized
  have hsumUniform : Summable (fun n => Real.sqrt (δ n : ℝ)) := by
    change Summable (fun n : ℕ => Real.sqrt ((1 / 4 : ℝ) ^ n))
    apply (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
      (by positivity) (by norm_num)).congr
    intro n
    have hp : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
      simp only [← pow_mul, Nat.mul_comm]
    rw [hp, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  exact ⟨continuousModificationSequenceLimit Y,
    continuousModification_naturalItoProcess_of_fast_tendsto
      hB.toIsPreBrownianReal hsm V U Y hmod hUV δ hδ
        hsumProbability hsumUniform⟩

/-- Completed fine-grid cells before a deterministic time converge to the
stopped bracket of a natural Itô integral.  Unlike the earlier rational-grid
prefix theorem, the partition size is unrestricted; continuity has removed
the unique boundary-crossing cell. -/
theorem quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t a : ℝ≥0) (ha : a ≤ t) :
    TendstoInMeasure P
      (fun n => quadraticVariationBeforeStopApprox
        (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U)
        t (n + 1) a)
      Filter.atTop (predictableQuadraticVariation hsm U (min t a)) := by
  let M : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  obtain ⟨Y, hmod⟩ :=
    exists_continuousModification_naturalItoProcess hB hsm U
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := by
    intro s
    exact AEStronglyMeasurable.mono
      ((Filtration.natural B hsm).le s)
      (stronglyMeasurable_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm rfl U s).aestronglyMeasurable
  have hstop :=
    quadraticVariation_stopped_naturalItoProcessRepresentative_bracket
      hB hsm U a t
  exact hmod.quadraticVariationBeforeStopApprox_tendstoInMeasure
    hMmeas t a ⟨bot_le, ha⟩
      (predictableQuadraticVariation hsm U (min t a)) hstop

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] in
/-- Along a continuous path, the second-derivative weights at a fine left
endpoint and at the left endpoint of its active coarse block become uniformly
close as both meshes vanish. -/
theorem generalItoSecondDerivative_activeBlockWeight_eventually_small
    (f : ℝ → ℝ → ℝ) (X : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W)
    (hsecond : Continuous (fun p : ℝ × ℝ =>
      itoSpaceSecondDerivative f p.1 p.2))
    (hpath : ContinuousOn (fun s => X s omega) (Set.Icc 0 t)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
        ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (k + 1),
          uniformPartitionTime t (k + 1) j <
              uniformPartitionTime t (n + 1) (i + 1) ∧
            uniformPartitionTime t (n + 1) (i + 1) ≤
              uniformPartitionTime t (k + 1) (j + 1) →
          |itoSpaceSecondDerivative f
              (uniformPartitionTime t (n + 1) i : ℝ)
              (X (uniformPartitionTime t (n + 1) i) omega) -
            itoSpaceSecondDerivative f
              (uniformPartitionTime t (k + 1) j : ℝ)
              (X (uniformPartitionTime t (k + 1) j) omega)| < epsilon := by
  let g : ℝ≥0 → ℝ := fun s =>
    itoSpaceSecondDerivative f (s : ℝ) (X s omega)
  have hpair : ContinuousOn
      (fun s : ℝ≥0 => ((s : ℝ), X s omega)) (Set.Icc 0 t) :=
    NNReal.continuous_coe.continuousOn.prodMk hpath
  have hg : ContinuousOn g (Set.Icc 0 t) := by
    exact hsecond.comp_continuousOn hpair
  have huc : UniformContinuousOn g (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  intro epsilon hepsilon
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Filter.Tendsto
      (fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hdiv : Filter.Tendsto
      (fun m : ℕ => ((t / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
    change Filter.Tendsto
      (NNReal.toReal ∘ fun m : ℕ => t / ((m + 1 : ℕ) : ℝ≥0))
      Filter.atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiv (eta / 2) (half_pos heta)
  refine ⟨N, ?_⟩
  intro k n hkN hnN
  have hkmesh : ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN k hkN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  have hnmesh : ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < eta / 2 := by
    have hnear := hN n hnN
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hnear
  intro i hi j hj hactive
  have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hi0 : i ≤ n + 1 :=
    (Nat.le_add_right i 1).trans (Finset.mem_range.mp hi)
  have hj0 : j ≤ k + 1 :=
    (Nat.le_add_right j 1).trans (Finset.mem_range.mp hj)
  have hifine := uniformPartitionTime_mem_Icc_of_le t hnpos hi0
  have hjcoarse := uniformPartitionTime_mem_Icc_of_le t hkpos hj0
  have hdistLe := dist_uniformPartition_left_to_active_coarse_left_le
    t (n + 1) (k + 1) i j hnpos hkpos hactive
  have hdist : dist (uniformPartitionTime t (n + 1) i)
      (uniformPartitionTime t (k + 1) j) < eta := by
    calc
      _ ≤ ((t / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
          ((t / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := hdistLe
      _ < eta / 2 + eta / 2 := add_lt_add hnmesh hkmesh
      _ = eta := by ring
  have hout := hmod
    (uniformPartitionTime t (n + 1) i) hifine
    (uniformPartitionTime t (k + 1) j) hjcoarse hdist
  simpa only [g, Real.dist_eq] using hout

end StochasticCalculus
