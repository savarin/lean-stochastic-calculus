/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.Novikov
import StochasticCalculus.QuadraticVariation
import StochasticCalculus.QuadraticVariationDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian

/-!
# Girsanov change of measure

This file begins the predictable-integrand Girsanov theorem by constructing
the terminal change of measure from the Doléans--Dade exponential.  The
definition is the unnormalised density `Z_T · P`, rather than an abstract or
existentially chosen probability measure.  Novikov's theorem supplies the
missing normalization `∫ Z_T dP = 1`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- Enlarging a filtration enlarges its predictable sigma-algebra. -/
theorem Filtration.predictable_mono
    {W I : Type*} [MeasurableSpace W] [Preorder I] [OrderBot I]
    {V U : Filtration I ‹MeasurableSpace W›} (hVU : V ≤ U) :
    V.predictable ≤ U.predictable := by
  apply MeasurableSpace.generateFrom_le
  rintro A (⟨S, hS, rfl⟩ | ⟨t, S, hS, rfl⟩)
  · exact MeasurableSpace.measurableSet_generateFrom
      (Or.inl ⟨S, hVU ⊥ S hS, rfl⟩)
  · exact MeasurableSpace.measurableSet_generateFrom
      (Or.inr ⟨t, S, hVU t S hS, rfl⟩)

/-- Strong adaptation is monotone under enlargement of the filtration. -/
theorem StronglyAdapted.mono_filtration
    {W I : Type*} [MeasurableSpace W] [Preorder I]
    {E : I → Type*} [∀ t, TopologicalSpace (E t)]
    {V U : Filtration I ‹MeasurableSpace W›} {X : ∀ t, W → E t}
    (hX : StronglyAdapted V X) (hVU : V ≤ U) : StronglyAdapted U X :=
  fun t ↦ (hX t).mono (hVU t)

/-- Strong predictability is monotone under enlargement of the filtration. -/
theorem IsStronglyPredictable.mono_filtration
    {W I E : Type*} [MeasurableSpace W] [Preorder I] [OrderBot I]
    [TopologicalSpace E]
    {V U : Filtration I ‹MeasurableSpace W›} {X : I → W → E}
    (hX : IsStronglyPredictable V X) (hVU : V ≤ U) :
    IsStronglyPredictable U X :=
  hX.mono (Filtration.predictable_mono hVU)

/-- A strongly predictable real process on nonnegative time is jointly
measurable for the ambient product measurable space. -/
theorem IsStronglyPredictable.measurable_uncurry_nnreal
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {theta : ℝ≥0 → W → ℝ}
    (h : IsStronglyPredictable V theta) :
    Measurable (Function.uncurry theta) := by
  apply (h.mono ?_).measurable
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (V.le 0 A hA)
  · intro i A hA
    exact measurableSet_Ioi.prod (V.le i A hA)

/-- If all future increments restricted to past events have their
mass-scaled Gaussian laws, then each increment is independent of the current
filtration. -/
theorem indep_increment_filtration_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (V s) (MeasurableSpace.comap
      (fun omega ↦ X t omega - X s omega) inferInstance) P := by
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc P :=
    (((hadapt t).mono (V.le t)).aemeasurable).sub
      (((hadapt s).mono (V.le s)).aemeasurable)
  have hmapU : P.map inc = gaussianReal 0 (t - s) := by
    have h := hrestricted hst (A := Set.univ) MeasurableSet.univ
    simpa only [inc, Measure.restrict_univ, measure_univ, one_smul] using h
  apply indep_comap_of_bcf (V.le s) hinc
  intro A hA f
  have hincR : AEMeasurable inc (P.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  have hmapA := hrestricted hst hA
  calc
    (∫ omega in A, f (inc omega) ∂P) =
        ∫ x, f x ∂((P.restrict A).map inc) := by
      rw [integral_map hincR f.continuous.measurable.aestronglyMeasurable]
    _ = ∫ x, f x ∂(P A • gaussianReal 0 (t - s)) := by
      simpa only [inc] using congrArg (fun mu ↦ ∫ x, f x ∂mu) hmapA
    _ = P.real A * ∫ x, f x ∂(gaussianReal 0 (t - s)) := by
      rw [integral_smul_measure, smul_eq_mul, measureReal_def]
    _ = P.real A * ∫ omega, f (inc omega) ∂P := by
      congr 1
      rw [← hmapU, integral_map hinc f.continuous.measurable.aestronglyMeasurable]

/-- Past-event Gaussian increment laws imply independent increments. -/
theorem hasIndepIncrements_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    HasIndepIncrements X P := by
  intro n times htimes
  let Y : Fin n → W → ℝ := fun i omega ↦
    X (times i.succ) omega - X (times i.castSucc) omega
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
      have ha : a ∉ S := by
        intro haS
        exact (lt_irrefl a) (hmax a haS)
      have hprev : MeasurableSet[V (times a.castSucc)]
          (⋂ i ∈ S, Y i ⁻¹' sets i) := by
        apply S.measurableSet_biInter
        intro i hi
        have hiright : i.succ ≤ a.castSucc := by
          apply Fin.mk_le_mk.mpr
          have hia := hmax i hi
          omega
        have hleft : i.castSucc ≤ i.succ := Fin.castSucc_le_succ i
        have hYi : StronglyMeasurable[V (times i.succ)] (Y i) := by
          exact (hadapt (times i.succ)).sub
            ((hadapt (times i.castSucc)).mono (V.mono (htimes hleft)))
        exact (hYi.mono (V.mono (htimes hiright))).measurable
          (hsets i (by simp [hi]))
      have hcurr : MeasurableSet[MeasurableSpace.comap (Y a) inferInstance]
          (Y a ⁻¹' sets a) :=
        (hsets a (by simp)).preimage (comap_measurable (Y a))
      have hindep := indep_increment_filtration_of_map_restrict_increment_eq
        hadapt hrestricted (htimes (Fin.castSucc_le_succ a))
      have hfactor :=
        (hindep.indepSet_of_measurableSet hprev hcurr).measure_inter_eq_mul
      rw [Finset.set_biInter_insert, Finset.prod_insert ha, Set.inter_comm,
        hfactor, ih (fun i hi ↦ hsets i (by simp [hi]))]
      exact mul_comm _ _

/-- A process is pre-Brownian once every future increment, restricted to an
arbitrary event in the current filtration, has the corresponding
mass-scaled centered Gaussian law.  This isolates the probabilistic endpoint
of exponential-martingale proofs of Lévy and Girsanov theorems. -/
theorem isPreBrownianReal_of_map_restrict_increment_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hzero : ∀ omega, X 0 omega = 0)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    IsPreBrownianReal X P := by
  apply HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · intro t
    have hX : AEMeasurable (X t) P :=
      ((hadapt t).mono (V.le t)).aemeasurable
    refine ⟨hX, ?_⟩
    have h := hrestricted (s := 0) (t := t) (by exact bot_le)
      (A := Set.univ) MeasurableSet.univ
    simpa only [Measure.restrict_univ, hzero, sub_zero, measure_univ,
      one_smul, tsub_zero] using h
  · exact hasIndepIncrements_of_map_restrict_increment_eq hadapt hrestricted

/-- Almost-sure normalization variant of the past-event Gaussian increment
criterion.  Subtracting the time-zero random variable leaves every increment
unchanged and produces an everywhere normalized representative. -/
theorem isPreBrownianReal_of_map_restrict_increment_eq_of_ae_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {X : ℝ≥0 → W → ℝ}
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ X t omega - X s omega) =
          P A • gaussianReal 0 (t - s)) :
    IsPreBrownianReal X P := by
  let Y : ℝ≥0 → W → ℝ := fun t omega ↦ -X 0 omega + X t omega
  have hYadapt : StronglyAdapted V Y := by
    intro t
    exact ((hadapt 0).mono (V.mono bot_le)).neg.add (hadapt t)
  have hYrestricted : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W},
      MeasurableSet[V s] A →
        (P.restrict A).map (fun omega ↦ Y t omega - Y s omega) =
          P A • gaussianReal 0 (t - s) := by
    intro s t hst A hA
    have hfun : (fun omega ↦ Y t omega - Y s omega) =
        (fun omega ↦ X t omega - X s omega) := by
      funext omega
      simp only [Y]
      ring
    rw [hfun]
    exact hrestricted hst hA
  have hY := isPreBrownianReal_of_map_restrict_increment_eq hYadapt
    (fun omega ↦ by simp only [Y]; ring) hYrestricted
  apply hY.congr
  intro t
  filter_upwards [hzero] with omega homega
  simp only [Y, homega, neg_zero, zero_add]

/-- Process-valued quadratic covariation along uniform partitions. -/
def HasCrossVariationProcessInProbability
    {W : Type*} [MeasurableSpace W]
    (X Y covariation : ℝ≥0 → W → ℝ) (P : Measure W) : Prop :=
  ∀ t, TendstoInMeasure P
    (fun n ↦ quadraticCovariationApprox X Y t (n + 1))
    Filter.atTop (covariation t)

/-- A quadratic-variation process is its own cross-variation process. -/
theorem HasQuadraticVariationProcessInProbability.toCrossVariationSelf
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Q : ℝ≥0 → W → ℝ}
    (h : HasQuadraticVariationProcessInProbability X Q P) :
    HasCrossVariationProcessInProbability X X Q P := by
  intro t
  apply (h t).congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    unfold quadraticCovariationApprox quadraticVariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    rw [pow_two]

/-- Every pre-Brownian version is stochastically continuous, even though its
sample paths need not be the continuous version.  Chebyshev's inequality and
the exact Gaussian increment variance give the result directly. -/
theorem IsPreBrownianReal.tendstoInMeasure_eval
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n ↦ B (a n)) atTop (B r) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  have haReal : Tendsto (fun n ↦ ((a n : ℝ≥0) : ℝ)) atTop (nhds (r : ℝ)) :=
    (NNReal.continuous_coe.tendsto r).comp ha
  have hnndist : Tendsto
      (fun n ↦ (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ))
      atTop (nhds 0) := by
    have hnn := haReal.nndist (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (r : ℝ)) atTop (nhds (r : ℝ)))
    have hnn' : Tendsto
        (fun n ↦ nndist ((a n : ℝ≥0) : ℝ) (r : ℝ))
        atTop (nhds 0) := by simpa using hnn
    have hcoe := (NNReal.continuous_coe.tendsto 0).comp hnn'
    change Tendsto
      (fun n ↦ (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ))
      atTop (nhds 0) at hcoe
    exact hcoe
  have hbound : Tendsto
      (fun n ↦ ENNReal.ofReal
        ((nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) / epsilon ^ 2))
      atTop (nhds 0) := by
    have hdiv := hnndist.div_const (epsilon ^ 2)
    have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdiv
    change Tendsto
      (fun n ↦ ENNReal.ofReal
        ((nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) / epsilon ^ 2))
      atTop (nhds (ENNReal.ofReal (0 / epsilon ^ 2))) at hofReal
    simpa using hofReal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbound (fun _ ↦ zero_le) ?_
  intro n
  have hmem : MemLp (B (a n) - B r) 2 P :=
    (hB.hasLaw_sub (a n) r).hasGaussianLaw.memLp_two
  have hmean : ∫ omega, B (a n) omega - B r omega ∂P = 0 := by
    rw [integral_sub (hB.integrable_eval (a n)) (hB.integrable_eval r),
      hB.integral_eval (a n), hB.integral_eval r, sub_zero]
  have hvar : variance (B (a n) - B r) P =
      (nndist ((a n : ℝ≥0) : ℝ) (r : ℝ) : ℝ) := by
    rw [(hB.hasLaw_sub (a n) r).variance_eq, variance_id_gaussianReal]
    rfl
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  simpa only [Pi.sub_apply, Real.dist_eq, hmean, sub_zero, hvar] using hcheb

/-- A continuous function of two random variables preserves joint
convergence in measure.  The proof uses the subsequence characterization:
first choose an almost-surely convergent subsequence for the first variable,
then refine it for the second variable. -/
theorem TendstoInMeasure.continuous_comp₂
    {A E F G : Type*} [MeasurableSpace A]
    [MetricSpace E] [MetricSpace F] [MetricSpace G]
    {P : Measure A} [IsFiniteMeasure P]
    {X : ℕ → A → E} {Y : ℕ → A → F}
    {x : A → E} {y : A → F}
    (hXmeas : ∀ n, AEStronglyMeasurable (X n) P)
    (hYmeas : ∀ n, AEStronglyMeasurable (Y n) P)
    (hX : TendstoInMeasure P X atTop x)
    (hY : TendstoInMeasure P Y atTop y)
    {f : E → F → G} (hf : Continuous f.uncurry) :
    TendstoInMeasure P (fun n omega ↦ f (X n omega) (Y n omega)) atTop
      (fun omega ↦ f (x omega) (y omega)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff]
  · intro ns hns
    obtain ⟨ks, hks, hXae⟩ :=
      (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    obtain ⟨ls, hls, hYae⟩ :=
      ((hY.comp hns.tendsto_atTop).comp hks.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ks ∘ ls, hks.comp hls, ?_⟩
    filter_upwards [hXae, hYae] with omega hXomega hYomega
    have hpair : Tendsto (fun i ↦
        (X (ns ((ks ∘ ls) i)) omega, Y (ns ((ks ∘ ls) i)) omega))
        atTop (nhds (x omega, y omega)) := by
      rw [nhds_prod_eq]
      simpa only [Function.comp_apply] using
        (hXomega.comp hls.tendsto_atTop).prodMk hYomega
    change Tendsto (Function.uncurry f ∘ fun i ↦
      (X (ns ((ks ∘ ls) i)) omega, Y (ns ((ks ∘ ls) i)) omega))
      atTop (nhds (Function.uncurry f (x omega, y omega)))
    exact hf.continuousAt.tendsto.comp hpair
  · intro n
    exact hf.comp_aestronglyMeasurable₂ (hXmeas n) (hYmeas n)

/-- A continuous map preserves convergence in measure on a finite measure
space. -/
theorem TendstoInMeasure.continuous_comp
    {A E F : Type*} [MeasurableSpace A] [MetricSpace E] [MetricSpace F]
    {P : Measure A} [IsFiniteMeasure P]
    {X : ℕ → A → E} {x : A → E}
    (hXmeas : ∀ n, AEStronglyMeasurable (X n) P)
    (hX : TendstoInMeasure P X atTop x)
    {f : E → F} (hf : Continuous f) :
    TendstoInMeasure P (fun n omega ↦ f (X n omega)) atTop
      (fun omega ↦ f (x omega)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff]
  · intro ns hns
    obtain ⟨ks, hks, hXae⟩ :=
      (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ks, hks, ?_⟩
    filter_upwards [hXae] with omega hXomega
    exact hf.continuousAt.tendsto.comp hXomega
  · intro n
    exact hf.comp_aestronglyMeasurable (hXmeas n)

/-- Pointwise addition preserves convergence in measure in any seminormed
additive group, without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.add_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y : ι → A → E} {x y : A → E}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega => X i omega + Y i omega) l
      (fun omega => x omega + y omega) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hXhalf := hX (epsilon / 2) hhalf
  have hYhalf := hY (epsilon / 2) hhalf
  have hsum : Tendsto (fun i =>
      P {omega | epsilon / 2 ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)})
      l (nhds 0) := by
    simpa only [add_zero] using hXhalf.add hYhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro i
  calc
    P {omega | epsilon ≤
        dist (X i omega + Y i omega) (x omega + y omega)} ≤
        P ({omega | epsilon / 2 ≤ dist (X i omega) (x omega)} ∪
          {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)}) := by
      apply measure_mono
      intro omega homega
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      change epsilon ≤
        dist (X i omega + Y i omega) (x omega + y omega) at homega
      by_contra hunion
      have hXsmall : dist (X i omega) (x omega) < epsilon / 2 :=
        lt_of_not_ge (fun hbad => hunion (Or.inl hbad))
      have hYsmall : dist (Y i omega) (y omega) < epsilon / 2 :=
        lt_of_not_ge (fun hbad => hunion (Or.inr hbad))
      have hdist :
          dist (X i omega + Y i omega) (x omega + y omega) ≤
            dist (X i omega) (x omega) +
              dist (Y i omega) (y omega) :=
        dist_add_add_le _ _ _ _
      linarith
    _ ≤ P {omega | epsilon / 2 ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon / 2 ≤ dist (Y i omega) (y omega)} :=
      measure_union_le _ _

/-- Pairing two families preserves convergence in measure, without
measurability assumptions on either family. -/
theorem TendstoInMeasure.prodMk_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E} {Y : ι → A → F} {x : A → E} {y : A → F}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega ↦ (X i omega, Y i omega)) l
      (fun omega ↦ (x omega, y omega)) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro epsilon hepsilon
  have hsum : Tendsto (fun i ↦
      P {omega | epsilon ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon ≤ dist (Y i omega) (y omega)}) l (nhds 0) := by
    simpa only [add_zero] using
      (hX epsilon hepsilon).add (hY epsilon hepsilon)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ ↦ zero_le) ?_
  intro i
  calc
    P {omega | epsilon ≤
        dist (X i omega, Y i omega) (x omega, y omega)} ≤
        P ({omega | epsilon ≤ dist (X i omega) (x omega)} ∪
          {omega | epsilon ≤ dist (Y i omega) (y omega)}) := by
      apply measure_mono
      intro omega homega
      simpa only [Set.mem_ofPred_eq, Set.mem_union, Prod.dist_eq,
        le_max_iff] using homega
    _ ≤ P {omega | epsilon ≤ dist (X i omega) (x omega)} +
        P {omega | epsilon ≤ dist (Y i omega) (y omega)} :=
      measure_union_le _ _

/-- The first coordinate of a product-valued convergence-in-measure limit
converges without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.fst_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E × F} {x : A → E × F} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) :
    TendstoInMeasure P (fun i omega ↦ (X i omega).1) l
      (fun omega ↦ (x omega).1) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  have hpair := hX epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hpair (fun _ ↦ zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  change epsilon ≤ dist (X i omega).1 (x omega).1 at homega
  change epsilon ≤ dist (X i omega) (x omega)
  rw [Prod.dist_eq]
  exact homega.trans (le_max_left _ _)

/-- The second coordinate of a product-valued convergence-in-measure limit
converges without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.snd_noMeas
    {A E F ι : Type*} [MeasurableSpace A] [PseudoMetricSpace E]
    [PseudoMetricSpace F] {P : Measure A}
    {X : ι → A → E × F} {x : A → E × F} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) :
    TendstoInMeasure P (fun i omega ↦ (X i omega).2) l
      (fun omega ↦ (x omega).2) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro epsilon hepsilon
  have hpair := hX epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hpair (fun _ ↦ zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  change epsilon ≤ dist (X i omega).2 (x omega).2 at homega
  change epsilon ≤ dist (X i omega) (x omega)
  rw [Prod.dist_eq]
  exact homega.trans (le_max_right _ _)

/-- Pointwise subtraction preserves convergence in measure in any
seminormed additive group, without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.sub_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y : ι → A → E} {x y : A → E}
    {l : Filter ι} (hX : TendstoInMeasure P X l x)
    (hY : TendstoInMeasure P Y l y) :
    TendstoInMeasure P (fun i omega => X i omega - Y i omega) l
      (fun omega => x omega - y omega) := by
  have hneg : TendstoInMeasure P (fun i omega => -Y i omega) l
      (fun omega => -y omega) := by
    rw [tendstoInMeasure_iff_norm] at hY ⊢
    intro epsilon hepsilon
    simpa only [neg_sub_neg, norm_neg, norm_sub_rev] using
      hY epsilon hepsilon
  simpa only [sub_eq_add_neg] using
    TendstoInMeasure.add_normed_noMeas hX hneg

/-- Two vanishing differences with a shared intermediate family concatenate
to a vanishing endpoint difference. -/
theorem TendstoInMeasure.sub_chain_normed_noMeas
    {A E ι : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X Y Z : ι → A → E} {l : Filter ι}
    (hXY : TendstoInMeasure P (fun i omega ↦ X i omega - Y i omega) l
      (fun _ ↦ 0))
    (hYZ : TendstoInMeasure P (fun i omega ↦ Y i omega - Z i omega) l
      (fun _ ↦ 0)) :
    TendstoInMeasure P (fun i omega ↦ X i omega - Z i omega) l
      (fun _ ↦ 0) := by
  have hsum := TendstoInMeasure.add_normed_noMeas hXY hYZ
  have hsum' : TendstoInMeasure P (fun i omega ↦
      (X i omega - Y i omega) + (Y i omega - Z i omega)) l
      (fun _ ↦ 0) := by
    simpa only [zero_add] using hsum
  apply hsum'.congr_left
  intro i
  exact Filter.Eventually.of_forall fun omega ↦ by
    change (X i omega - Y i omega) + (Y i omega - Z i omega) =
      X i omega - Z i omega
    rw [sub_add_sub_cancel]

/-- Multiplication by a deterministic complex scalar preserves convergence
in measure without auxiliary measurability hypotheses. -/
theorem TendstoInMeasure.const_mul_complex_noMeas
    {A ι : Type*} [MeasurableSpace A] {P : Measure A}
    {X : ι → A → ℂ} {x : A → ℂ} {l : Filter ι}
    (hX : TendstoInMeasure P X l x) (c : ℂ) :
    TendstoInMeasure P (fun i omega => c * X i omega) l
      (fun omega => c * x omega) := by
  rw [tendstoInMeasure_iff_norm] at hX ⊢
  intro epsilon hepsilon
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, sub_self, norm_zero, Set.ofPred_false,
      measure_empty, not_le.mpr hepsilon] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0))
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hscaled := hX (epsilon / ‖c‖) (div_pos hepsilon hcpos)
    have hfun :
        (fun i => P {omega | epsilon ≤ ‖c * X i omega - c * x omega‖}) =
        (fun i => P {omega | epsilon / ‖c‖ ≤ ‖X i omega - x omega‖}) := by
      funext i
      apply congrArg P
      ext omega
      simp only [Set.mem_ofPred_eq, ← mul_sub, norm_mul]
      rw [div_le_iff₀ hcpos, mul_comm]
    rw [hfun]
    exact hscaled

/-- Pointwise domination by a nonnegative real family transfers convergence
in measure to zero, without measurability assumptions on either family. -/
theorem TendstoInMeasure.of_norm_le_nonneg_noMeas
    {A ι E : Type*} [MeasurableSpace A] [SeminormedAddCommGroup E]
    {P : Measure A} {X : ι → A → E} {b : ι → A → ℝ}
    {l : Filter ι}
    (hb : TendstoInMeasure P b l (fun _ => 0))
    (hb_nonneg : ∀ i omega, 0 ≤ b i omega)
    (hXb : ∀ i omega, ‖X i omega‖ ≤ b i omega) :
    TendstoInMeasure P X l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hb ⊢
  intro epsilon hepsilon
  have hlimit := hb epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hlimit (fun _ => zero_le) ?_
  intro i
  apply measure_mono
  intro omega homega
  simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (hb_nonneg i omega)] at homega ⊢
  exact homega.trans (hXb i omega)

/-- A real-valued convergence-in-measure limit is almost everywhere
nonpositive if every approximant is pointwise nonpositive. -/
theorem TendstoInMeasure.ae_le_zero_of_forall_le_zero
    {A : Type*} [MeasurableSpace A] {P : Measure A}
    {f : ℕ → A → ℝ} {g : A → ℝ}
    (hfg : TendstoInMeasure P f atTop g)
    (hf : ∀ n omega, f n omega ≤ 0) : g ≤ᵐ[P] fun _ => 0 := by
  obtain ⟨ns, _hns, hae⟩ := hfg.exists_seq_tendsto_ae
  filter_upwards [hae] with omega homega
  exact le_of_tendsto homega
    (Filter.Eventually.of_forall fun n => hf (ns n) omega)

set_option maxHeartbeats 4000000 in
-- Combining three convergence-in-measure limits is elaboration-intensive.
/-- Fixed-time Kunita--Watanabe inequality obtained directly from uniform
partition convergence in measure. -/
theorem HasCrossVariationProcessInProbability.sq_le_mul_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C QX QY : ℝ≥0 → W → ℝ}
    (hcross : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (hQX : HasQuadraticVariationProcessInProbability X QX P)
    (hQY : HasQuadraticVariationProcessInProbability Y QY P)
    (t : ℝ≥0) :
    (fun omega => C t omega ^ 2) ≤ᵐ[P]
      fun omega => QX t omega * QY t omega := by
  let cov : ℕ → W → ℝ := fun n =>
    quadraticCovariationApprox X Y t (n + 1)
  let qX : ℕ → W → ℝ := fun n => quadraticVariationApprox X t (n + 1)
  let qY : ℕ → W → ℝ := fun n => quadraticVariationApprox Y t (n + 1)
  have hcovMeas : ∀ n, AEStronglyMeasurable (cov n) P := fun n =>
    aestronglyMeasurable_quadraticCovariationApprox
      hXmeas hYmeas t (n + 1)
  have hqXMeas : ∀ n, AEStronglyMeasurable (qX n) P := fun n =>
    aestronglyMeasurable_quadraticVariationApprox hXmeas t (n + 1)
  have hqYMeas : ∀ n, AEStronglyMeasurable (qY n) P := fun n =>
    aestronglyMeasurable_quadraticVariationApprox hYmeas t (n + 1)
  have hcovSq : TendstoInMeasure P (fun n omega => cov n omega ^ 2)
      atTop (fun omega => C t omega ^ 2) := by
    exact TendstoInMeasure.continuous_comp hcovMeas
      (by simpa only [cov] using hcross t)
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hqProd : TendstoInMeasure P
      (fun n omega => qX n omega * qY n omega) atTop
      (fun omega => QX t omega * QY t omega) := by
    apply TendstoInMeasure.continuous_comp₂ hqXMeas hqYMeas
      (by simpa only [qX, HasQuadraticVariationInProbabilityAt] using hQX t)
      (by simpa only [qY, HasQuadraticVariationInProbabilityAt] using hQY t)
    fun_prop
  have hdiff := hcovSq.sub_real_noMeas hqProd
  have hnonpos : (fun omega => C t omega ^ 2 -
      QX t omega * QY t omega) ≤ᵐ[P] fun _ => 0 :=
    TendstoInMeasure.ae_le_zero_of_forall_le_zero hdiff fun n omega => by
      dsimp only [cov, qX, qY]
      exact sub_nonpos.mpr
        (quadraticCovariationApprox_sq_le X Y t (n + 1) omega)
  filter_upwards [hnonpos] with omega homega
  simpa only [Pi.zero_apply, sub_nonpos] using homega

/-- Continuous real-linear images of Banach-valued martingales are
martingales. -/
theorem Martingale.comp_continuousLinearMap
    {W E F I : Type*} [MeasurableSpace W] [Preorder I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {P : Measure W} {V : Filtration I ‹MeasurableSpace W›}
    {X : I → W → E} (hX : Martingale X V P) (L : E →L[ℝ] F) :
    Martingale (fun t omega ↦ L (X t omega)) V P := by
  refine ⟨fun t ↦ L.continuous.comp_stronglyMeasurable (hX.stronglyMeasurable t),
    fun i j hij ↦ ?_⟩
  exact (L.comp_condExp_comm (hX.integrable j)).symm.trans
    ((hX.condExp_ae_eq hij).fun_comp L)

/-- The terminal stochastic-exponential density used by Girsanov. -/
def girsanovDensity {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : W → ℝ :=
  doleansDadeExponential M bracket T

/-- The Girsanov measure `Q = Z_T · P`, represented by Mathlib's
`Measure.withDensity`. -/
def girsanovMeasure {W : Type*} [MeasurableSpace W]
    (P : Measure W) (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Measure W :=
  P.withDensity (fun omega => ENNReal.ofReal (girsanovDensity M bracket T omega))

/-- The finite-horizon pathwise drift accumulated from a predictable
integrand. -/
def girsanovIntegratedDrift {W : Type*}
    (theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), theta s omega
    ∂nonnegativeLebesgueMeasure

/-- Integrating a strongly predictable process up to a deterministic stopped
horizon produces an adapted finite-variation process. -/
theorem IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} {theta : ℝ≥0 → W → ℝ}
    (htheta : IsStronglyPredictable V theta) (T : ℝ≥0) :
    StronglyAdapted V (girsanovIntegratedDrift theta T) := by
  intro t
  let u : ℝ≥0 := min t T
  let j : Set.Ioc (0 : ℝ≥0) u → Set.Iic t := fun r ↦
    ⟨r, r.prop.2.trans (min_le_left t T)⟩
  have hj : Measurable j := by
    exact measurable_subtype_coe.subtype_mk
  have hprog : StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (fun p : Set.Iic t × W ↦ theta p.1 p.2) :=
    htheta.isStronglyProgressive t
  let F : Set.Ioc (0 : ℝ≥0) u → W → ℝ :=
    fun r omega ↦ theta r omega
  have hF : StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (Function.uncurry F) := by
    have hpair : @Measurable
        (Set.Ioc (0 : ℝ≥0) u × W) (Set.Iic t × W)
        (Subtype.instMeasurableSpace.prod (V t))
        (Subtype.instMeasurableSpace.prod (V t))
        (fun p ↦ (j p.1, p.2)) := Measurable.prodMk
      (hj.comp measurable_fst) measurable_snd
    change StronglyMeasurable[Subtype.instMeasurableSpace.prod (V t)]
      (fun p : Set.Ioc (0 : ℝ≥0) u × W ↦ theta p.1 p.2)
    exact hprog.comp_measurable hpair
  let restrictedTimeMeasure :=
    nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)
  have hmap := map_nonnegativeLebesgueMeasure_restrict_Ioc u
  let : IsFiniteMeasure restrictedTimeMeasure := by
    have : IsFiniteMeasure
        ((volume : Measure ℝ).restrict (Set.Ioc 0 (u : ℝ))) := inferInstance
    have : IsFiniteMeasure (Measure.map ((↑) : ℝ≥0 → ℝ)
        restrictedTimeMeasure) := by
      rw [show Measure.map ((↑) : ℝ≥0 → ℝ) restrictedTimeMeasure =
          (volume : Measure ℝ).restrict (Set.Ioc 0 (u : ℝ)) by
        simpa only [restrictedTimeMeasure] using hmap]
      infer_instance
    exact Measure.isFiniteMeasure_of_map
      NNReal.continuous_coe.measurable.aemeasurable
  let timeMeasure : Measure (Set.Ioc (0 : ℝ≥0) u) :=
    Measure.comap Subtype.val restrictedTimeMeasure
  have hparam : StronglyMeasurable[V t] (fun omega ↦
      ∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure) := by
    let : MeasurableSpace W := V t
    exact hF.integral_prod_left
  convert hparam using 1
  funext omega
  unfold girsanovIntegratedDrift
  change (∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
      ∂nonnegativeLebesgueMeasure) =
    ∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure
  symm
  calc
    (∫ r : Set.Ioc (0 : ℝ≥0) u, F r omega ∂timeMeasure) =
        ∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
          ∂restrictedTimeMeasure := by
      simpa only [F, timeMeasure] using
        (integral_subtype_comap (μ := restrictedTimeMeasure)
          measurableSet_Ioc (fun r ↦ theta r omega))
    _ = ∫ r in Set.Ioc (0 : ℝ≥0) u, theta r omega
          ∂nonnegativeLebesgueMeasure := by
      change (∫ r, theta r omega ∂
          (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 u)).restrict
            (Set.Ioc 0 u)) = _
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_self]

/-- The nonnegative-time drift used in the Girsanov statement agrees with
the real-time integral primitive used by the quadratic-variation library. -/
theorem girsanovIntegratedDrift_eq_integratedDrift
    {W : Type*} [MeasurableSpace W]
    (theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      integratedDrift theta (min t T) omega := by
  unfold girsanovIntegratedDrift integratedDrift
  exact integral_nonnegative_Ioc_eq_real_Icc theta (min t T) omega

/-- A path-regular representative of the stopped Girsanov drift.  On the
zero-terminal-bracket event it is set to zero; elsewhere the terminal
square integral is genuine and the original integral has continuous paths. -/
def regularizedGirsanovIntegratedDrift {W : Type*}
    (bracket theta : ℝ≥0 → W → ℝ) (T t : ℝ≥0) (omega : W) : ℝ :=
  if bracket T omega = 0 then 0 else girsanovIntegratedDrift theta T t omega

/-- Every deterministic-time section of the regularized drift is strongly
measurable.  The terminal-bracket test is globally measurable, while the
uncut drift section is measurable by predictability. -/
theorem stronglyMeasurable_regularizedGirsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hbracket : StronglyAdapted V bracket)
    (htheta : IsStronglyPredictable V theta) (t : ℝ≥0) :
    StronglyMeasurable
      (regularizedGirsanovIntegratedDrift bracket theta T t) := by
  have hbracketT : StronglyMeasurable (bracket T) :=
    (hbracket T).mono (V.le T)
  have hdrift : StronglyMeasurable (girsanovIntegratedDrift theta T t) :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T t).mono (V.le t)
  have hset : MeasurableSet {omega | bracket T omega = 0} :=
    hbracketT.measurable (measurableSet_singleton 0)
  change StronglyMeasurable
    ({omega | bracket T omega = 0}.piecewise
      (fun _ => 0) (girsanovIntegratedDrift theta T t))
  exact stronglyMeasurable_const.piecewise hset hdrift

/-- The regularized stopped drift has continuous paths.  A nonzero terminal
bracket forces the totalized square integral to be genuinely integrable,
and finite-measure `L²` control then gives the needed `L¹` primitive. -/
theorem continuous_regularizedGirsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) (omega : W) :
    Continuous (fun t =>
      regularizedGirsanovIntegratedDrift bracket theta T t omega) := by
  unfold regularizedGirsanovIntegratedDrift
  by_cases hzero : bracket T omega = 0
  · simp only [hzero, if_pos]
    fun_prop
  · simp only [hzero, if_false]
    have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaInt : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    let g : ℝ → ℝ := fun r => theta r.toNNReal omega
    have hprimitive : ContinuousOn
        (fun u => integratedDrift theta u omega)
        (Set.Icc (0 : ℝ≥0) T) := by
      change ContinuousOn (nnrealIntegralPrimitive g)
        (Set.Icc (0 : ℝ≥0) T)
      exact continuousOn_nnrealIntegralPrimitive hthetaInt
    have hmin : Continuous (fun t : ℝ≥0 => min t T) := by fun_prop
    have hcomp := hprimitive.comp_continuous hmin (fun t =>
      show min t T ∈ Set.Icc (0 : ℝ≥0) T from
        ⟨bot_le, min_le_right _ _⟩)
    apply hcomp.congr
    intro t
    exact (girsanovIntegratedDrift_eq_integratedDrift
      theta T t omega).symm

/-- The process `B_t + ∫₀^{t∧T} theta_s ds` appearing in the
finite-horizon Girsanov theorem.  Brownian motion itself is not stopped after
`T`; only the compensating drift is. -/
def girsanovShiftedBrownian {W : Type*}
    (B theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) : ℝ≥0 → W → ℝ :=
  fun t omega => B t omega + girsanovIntegratedDrift theta T t omega

/-- A predictable drift preserves adaptedness when added to an adapted
driver. -/
theorem stronglyAdapted_girsanovShiftedBrownian
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hB : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta) :
    StronglyAdapted V (girsanovShiftedBrownian B theta T) := by
  intro t
  exact (hB t).add
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T t)

theorem girsanovIntegratedDrift_of_horizon_le {W : Type*}
    (theta : ℝ≥0 → W → ℝ) {T t : ℝ≥0} (ht : T ≤ t) (omega : W) :
    girsanovIntegratedDrift theta T t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, theta s omega
        ∂nonnegativeLebesgueMeasure := by
  simp only [girsanovIntegratedDrift, min_eq_right ht]

@[simp]
theorem girsanovDensity_eq_exp_log {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    girsanovDensity M bracket T omega =
      Real.exp (doleansDadeLog M bracket T omega) :=
  rfl

theorem girsanovDensity_pos {W : Type*}
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) (omega : W) :
    0 < girsanovDensity M bracket T omega :=
  Real.exp_pos _

/-- Once the terminal density has expectation one, the exact density measure
agrees with Mathlib's normalized exponential tilt. -/
theorem girsanovMeasure_eq_tilted
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hone : ∫ omega, girsanovDensity M bracket T omega ∂P = 1) :
    girsanovMeasure P M bracket T =
      P.tilted (doleansDadeLog M bracket T) := by
  have hlog : ∫ omega, Real.exp (doleansDadeLog M bracket T omega) ∂P = 1 := by
    simpa only [girsanovDensity_eq_exp_log] using hone
  unfold girsanovMeasure Measure.tilted
  rw [hlog]
  congr 1
  funext omega
  simp only [div_one, girsanovDensity_eq_exp_log]

/-- The terminal density measure is absolutely continuous with respect to
the original measure, without any integrability assumption. -/
theorem girsanovMeasure_absolutelyContinuous
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) :
    girsanovMeasure P M bracket T ≪ P := by
  unfold girsanovMeasure
  exact withDensity_absolutelyContinuous _ _

/-- Strict positivity of a measurable terminal stochastic exponential makes
the change of measure equivalent to the original measure. -/
theorem girsanovMeasure_mutuallyAbsolutelyContinuous
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) :
    girsanovMeasure P M bracket T ≪ P ∧
      P ≪ girsanovMeasure P M bracket T := by
  refine ⟨girsanovMeasure_absolutelyContinuous P M bracket T, ?_⟩
  unfold girsanovMeasure
  apply withDensity_absolutelyContinuous'
  · exact hint.1.aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun omega => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact girsanovDensity_pos M bracket T omega

/-- Vector-valued set integrals under the Girsanov measure are obtained by
real scalar multiplication with the terminal density. -/
theorem setIntegral_girsanovMeasure_smul
    {W E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (P : Measure W)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P) (f : W → E)
    {s : Set W} (hs : MeasurableSet s) :
    ∫ omega in s, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega in s, girsanovDensity M bracket T omega • f omega ∂P := by
  unfold girsanovMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hint.1.aemeasurable.ennreal_ofReal.restrict]
  · apply setIntegral_congr_ae hs
    exact Filter.Eventually.of_forall fun omega _ ↦ by
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  · exact Filter.Eventually.of_forall fun omega ↦ ENNReal.ofReal_lt_top
  · exact hs

/-- Any positive integrable normalized stochastic exponential defines a
probability measure. -/
theorem isProbabilityMeasure_girsanovMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (hint : Integrable (girsanovDensity M bracket T) P)
    (hone : ∫ omega, girsanovDensity M bracket T omega ∂P = 1) :
    IsProbabilityMeasure (girsanovMeasure P M bracket T) := by
  rw [girsanovMeasure_eq_tilted P M bracket T hone]
  exact isProbabilityMeasure_tilted (by
    apply hint.congr
    exact Filter.Eventually.of_forall fun _ => rfl)

/-- The exact hypotheses needed from a continuous local martingale and its
bracket to construct the finite-horizon Girsanov density under Novikov's
condition. -/
structure GirsanovDensityData
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop where
  novikov : NovikovCondition bracket P T
  localQuadraticVariation :
    HasLocalQuadraticVariationProcessInProbability M bracket 𝒱 P
  continuous_martingale_path : ∀ omega, Continuous (fun t => M t omega)
  adapted_martingale : StronglyAdapted 𝒱 M
  adapted_bracket : StronglyAdapted 𝒱 bracket
  continuous_monotone_bracket : ∀ omega,
    Continuous (fun t => bracket t omega) ∧ Monotone (fun t => bracket t omega)
  martingale_zero : ∀ omega, M 0 omega = 0
  bracket_zero : ∀ omega, bracket 0 omega = 0

/-- Girsanov density data at a terminal horizon remains valid at every
earlier deterministic horizon. Only the Novikov field depends on the
horizon; bracket monotonicity and adaptedness provide its restriction. -/
theorem GirsanovDensityData.mono_time
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T t : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) (ht : t ≤ T) :
    GirsanovDensityData P V M bracket t := by
  refine
    { novikov := h.novikov.mono_time
        (fun s ↦ ((h.adapted_bracket s).mono (V.le s)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun omega ↦
          (h.continuous_monotone_bracket omega).2) ht
      localQuadraticVariation := h.localQuadraticVariation
      continuous_martingale_path := h.continuous_martingale_path
      adapted_martingale := h.adapted_martingale
      adapted_bracket := h.adapted_bracket
      continuous_monotone_bracket := h.continuous_monotone_bracket
      martingale_zero := h.martingale_zero
      bracket_zero := h.bracket_zero }

/-- The cross variation of Novikov Girsanov data with a pre-Brownian driver
is bounded by the product of the martingale bracket and Brownian clock. -/
theorem GirsanovDensityData.crossVariation_sq_le_bracket_mul_time_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (fun omega => C t omega ^ 2) ≤ᵐ[P]
      fun omega => bracket t omega * (t : ℝ) := by
  exact hcross.sq_le_mul_ae
    (fun s => ((hdata.adapted_martingale s).mono
      (V.le s)).aestronglyMeasurable)
    (fun s => (hB.aemeasurable s).aestronglyMeasurable)
    hdata.localQuadraticVariation.toProcess
    (fun s => quadraticVariation_preBrownianReal_inProbability hB s) t

/-- At a deterministic time, the Girsanov cross variation vanishes almost
everywhere on the event where the martingale bracket is zero. -/
theorem GirsanovDensityData.crossVariation_eq_zero_of_bracket_eq_zero_ae
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B C P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∀ᵐ omega ∂P, bracket t omega = 0 → C t omega = 0 := by
  filter_upwards [hdata.crossVariation_sq_le_bracket_mul_time_ae
    hcross hB t] with omega homega
  intro hzero
  rw [hzero, zero_mul] at homega
  nlinarith [sq_nonneg (C t omega)]

/-- At each deterministic time, the regularized drift is an almost-everywhere
version of the original totalized drift whenever the latter is the negative
cross variation of the Girsanov martingale and Brownian driver. -/
theorem GirsanovDensityData.regularizedGirsanovIntegratedDrift_ae_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    regularizedGirsanovIntegratedDrift bracket theta T t =ᵐ[P]
      girsanovIntegratedDrift theta T t := by
  by_cases htT : t ≤ T
  · filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae
      hcross hB t] with omega hcrossZero
    unfold regularizedGirsanovIntegratedDrift
    by_cases hzero : bracket T omega = 0
    · rw [if_pos hzero]
      have hbracketNonneg : 0 ≤ bracket t omega := by
        rw [← hdata.bracket_zero omega]
        exact (hdata.continuous_monotone_bracket omega).2 bot_le
      have hbracketLe : bracket t omega ≤ bracket T omega :=
        (hdata.continuous_monotone_bracket omega).2 htT
      have hbracketZero : bracket t omega = 0 := by linarith
      have hdriftZero := hcrossZero hbracketZero
      linarith
    · rw [if_neg hzero]
  · have hTt : T ≤ t := le_of_not_ge htT
    filter_upwards [hdata.crossVariation_eq_zero_of_bracket_eq_zero_ae
      hcross hB T] with omega hcrossZero
    unfold regularizedGirsanovIntegratedDrift
    by_cases hzero : bracket T omega = 0
    · rw [if_pos hzero]
      have hterminalZero := hcrossZero hzero
      have hstop : girsanovIntegratedDrift theta T t omega =
          girsanovIntegratedDrift theta T T omega := by
        rw [girsanovIntegratedDrift_of_horizon_le theta hTt,
          girsanovIntegratedDrift_of_horizon_le theta le_rfl]
      rw [hstop]
      linarith
    · rw [if_neg hzero]

/-- The cross-variation contract may use the continuous regularized drift
representative.  Convergence in probability is insensitive to the
deterministic-time null-set changes used by the regularization. -/
theorem GirsanovDensityData.hasCrossVariationProcessInProbability_neg_regularizedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P) :
    HasCrossVariationProcessInProbability M B
      (fun t omega =>
        -regularizedGirsanovIntegratedDrift bracket theta T t omega) P := by
  intro t
  apply (hcross t).congr_right
  exact (hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t).neg.symm

/-- Although the totalized Girsanov drift need not have continuous paths
pointwise, its continuous regularization is a version at every deterministic
time.  Consequently the adapted original drift is stochastically continuous. -/
theorem GirsanovDensityData.tendstoInMeasure_girsanovIntegratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (hB : IsPreBrownianReal B P)
    {r : ℝ≥0} {a : ℕ → ℝ≥0} (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P
      (fun n => girsanovIntegratedDrift theta T (a n)) atTop
      (girsanovIntegratedDrift theta T r) := by
  let R : ℝ≥0 → W → ℝ :=
    regularizedGirsanovIntegratedDrift bracket theta T
  have hReq (t : ℝ≥0) :
      R t =ᵐ[P] girsanovIntegratedDrift theta T t := by
    exact hdata.regularizedGirsanovIntegratedDrift_ae_eq hcross hB t
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R (a n)) P := by
    exact (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable.congr
        (hReq (a n)).symm
  have hR : TendstoInMeasure P (fun n => R (a n)) atTop (R r) := by
    apply tendstoInMeasure_of_tendsto_ae hRmeas
    exact Filter.Eventually.of_forall fun omega =>
      (continuous_regularizedGirsanovIntegratedDrift htheta
        hbracketTerminal omega).continuousAt.tendsto.comp ha
  exact hR.congr (fun n => hReq (a n)) (hReq r)

/-- Novikov's terminal exponential moment controls the first moment of the
terminal bracket. -/
theorem GirsanovDensityData.integrable_terminalBracket
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    Integrable (bracket T) P := by
  have hmeas : AEStronglyMeasurable (bracket T) P :=
    ((h.adapted_bracket T).mono (V.le T)).aestronglyMeasurable
  have hnonneg : ∀ᵐ omega ∂P, 0 ≤ bracket T omega :=
    Filter.Eventually.of_forall fun omega => by
      rw [← h.bracket_zero omega]
      exact (h.continuous_monotone_bracket omega).2 bot_le
  exact Integrable.of_exp_half_of_ae_nonneg hmeas hnonneg h.novikov

/-- Novikov promotes the stopped density process carried by
`GirsanovDensityData` to a true martingale. -/
theorem GirsanovDensityData.martingale_densityProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) 𝒱 P :=
  h.novikov.martingale_stopAt_doleansDade
    h.localQuadraticVariation h.continuous_martingale_path
    h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
    h.martingale_zero h.bracket_zero

/-- Novikov makes the terminal Girsanov density integrable. -/
theorem GirsanovDensityData.integrable
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    Integrable (girsanovDensity M bracket T) P := by
  simpa only [girsanovDensity, min_self] using
    h.martingale_densityProcess.integrable T

/-- Novikov normalizes the terminal Girsanov density to expectation one. -/
theorem GirsanovDensityData.integral_eq_one
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    ∫ omega, girsanovDensity M bracket T omega ∂P = 1 := by
  simpa only [girsanovDensity] using
    h.novikov.integral_doleansDade_eq_one_of_le
      h.localQuadraticVariation h.continuous_martingale_path
      h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
      h.martingale_zero h.bracket_zero (le_refl T)

/-- The Novikov terminal density defines a probability measure. -/
theorem GirsanovDensityData.isProbabilityMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    IsProbabilityMeasure (girsanovMeasure P M bracket T) :=
  isProbabilityMeasure_girsanovMeasure M bracket T h.integrable h.integral_eq_one

/-- Under Novikov, the original and changed measures have the same null
sets. -/
theorem GirsanovDensityData.mutuallyAbsolutelyContinuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) :
    girsanovMeasure P M bracket T ≪ P ∧
      P ≪ girsanovMeasure P M bracket T :=
  girsanovMeasure_mutuallyAbsolutelyContinuous P M bracket T h.integrable

/-- The conditional expectation of the terminal density is the stopped
density process.  This is the Bayes bridge from the terminal measure to each
filtration time. -/
theorem GirsanovDensityData.condExp_density
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {𝒱 : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P 𝒱]
    [𝒱.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P 𝒱 M bracket T) (t : ℝ≥0) :
    P[girsanovDensity M bracket T | 𝒱 t] =ᵐ[P]
      doleansDadeExponential M bracket (min t T) := by
  have hmart := h.novikov.martingale_stopAt_doleansDade
    h.localQuadraticVariation h.continuous_martingale_path
    h.adapted_martingale h.adapted_bracket h.continuous_monotone_bracket
    h.martingale_zero h.bracket_zero
  by_cases ht : t ≤ T
  · simpa only [girsanovDensity, min_self, min_eq_left ht] using
      hmart.condExp_ae_eq ht
  · have hTt : T ≤ t := le_of_not_ge ht
    have hmeas : StronglyMeasurable[𝒱 t] (girsanovDensity M bracket T) := by
      simpa only [girsanovDensity, min_self] using
        hmart.stronglyAdapted.stronglyMeasurable_le hTt
    rw [condExp_of_stronglyMeasurable (𝒱.le t) hmeas h.integrable]
    simp only [girsanovDensity, min_eq_right hTt]
    exact Filter.EventuallyEq.rfl

/-- On a time-`t` event, integration under the terminal Girsanov measure can
be performed using the stopped density process at time `t`.  The statement
is vector-valued so it applies in particular to complex characteristic
functions. -/
theorem GirsanovDensityData.setIntegral_girsanovMeasure_eq_densityProcess_smul
    {W E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T t : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    {f : W → E} (hf : StronglyMeasurable[V t] f)
    (hfint : Integrable f (girsanovMeasure P M bracket T))
    {A : Set W} (hA : MeasurableSet[V t] A) :
    ∫ omega in A, f omega ∂(girsanovMeasure P M bracket T) =
      ∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P := by
  let Q := girsanovMeasure P M bracket T
  have hA0 : MeasurableSet A := V.le t A hA
  have hterminalInt : Integrable
      (fun omega ↦ girsanovDensity M bracket T omega • f omega) P := by
    have hraw : Integrable (fun omega ↦
        (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal •
          f omega) P :=
      (integrable_withDensity_iff_integrable_smul₀'
        (E := E) h.integrable.1.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp (by
          simpa only [Q, girsanovMeasure] using hfint)
    apply hraw.congr
    exact Filter.Eventually.of_forall fun omega ↦ by
      change (ENNReal.ofReal (girsanovDensity M bracket T omega)).toReal •
        f omega = girsanovDensity M bracket T omega • f omega
      rw [ENNReal.toReal_ofReal (girsanovDensity_pos M bracket T omega).le]
  have hpull := condExp_smul_of_aestronglyMeasurable_right
    h.integrable hterminalInt hf.aestronglyMeasurable
  calc
    ∫ omega in A, f omega ∂Q =
        ∫ omega in A, girsanovDensity M bracket T omega • f omega ∂P := by
      simpa only [Q] using
        setIntegral_girsanovMeasure_smul P M bracket T h.integrable f hA0
    _ = ∫ omega in A,
        P[fun w ↦ girsanovDensity M bracket T w • f w | V t] omega ∂P := by
      symm
      exact setIntegral_condExp (V.le t) hterminalInt hA
    _ = ∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P := by
      apply setIntegral_congr_ae hA0
      filter_upwards [hpull, h.condExp_density t] with omega hp hcond _
      change P[girsanovDensity M bracket T • f | V t] omega = _
      rw [hp]
      change P[girsanovDensity M bracket T | V t] omega • f omega = _
      rw [hcond]

/-- A pathwise-continuous real martingale remains a martingale after replacing
its filtration by its right continuation.  Uniform integrability of the
conditional expectations just above the earlier time supplies the required
`L¹` passage to the limit. -/
theorem Martingale.rightCont_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → ℝ} (hX : Martingale X V P)
    (hcont : ∀ omega, Continuous (fun t ↦ X t omega)) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t ↦
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((Filtration.rightCont V).le s)
    (hX.integrable t) (fun A _ _ ↦ (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n ↦ min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t) := tendsto_const_nhds
    have hs : Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using
      (Tendsto.min ht hs)
  have hcond (n : ℕ) : P[X t | V (u n)] =ᵐ[P] X (u n) :=
    hX.condExp_ae_eq (hut n)
  have hui : UniformIntegrable (fun n ↦ X (u n)) 1 P :=
    (hX.integrable t).uniformIntegrable_condExp (fun n ↦ V.le (u n)) |>.ae_eq hcond
  have hpoint : ∀ᵐ omega ∂P,
      Tendsto (fun n ↦ X (u n) omega) atTop (nhds (X s omega)) :=
    Filter.Eventually.of_forall fun omega ↦ (hcont omega).continuousAt.tendsto.comp hu
  have hinMeasure : TendstoInMeasure P (fun n ↦ X (u n)) atTop (X s) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hX.integrable (u n)).aestronglyMeasurable) hpoint
  have hL1 : Tendsto (fun n ↦ eLpNorm (X (u n) - X s) 1 P) atTop (nhds 0) :=
    (tendstoInMeasure_iff_tendsto_Lp_finite
      le_rfl ENNReal.one_ne_top
      (fun n ↦ memLp_one_iff_integrable.mpr (hX.integrable (u n)))
      (memLp_one_iff_integrable.mpr (hX.integrable s))).mp
      ⟨hinMeasure, hui.2.1⟩
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n ↦ hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      ∫ omega in A, X (u n) omega ∂P = ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n ↦ ∫ omega in A, X (u n) omega ∂P) =
      fun _ ↦ ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- A continuous common-localizer quadratic-variation contract survives
right-continuation of the filtration.  The stopping times remain stopping
times for the larger filtration, and the preceding theorem transports each
localized martingale. -/
theorem HasLocalQuadraticVariationProcessInProbability.rightCont_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ}
    (h : HasLocalQuadraticVariationProcessInProbability M bracket V P)
    (hcont : ∀ omega, Continuous (fun t ↦ M t omega)) :
    HasLocalQuadraticVariationProcessInProbability M bracket
      (Filtration.rightCont V) P := by
  obtain ⟨tau, htau, hmart, hqv⟩ := h
  refine ⟨tau, ?_, ?_, hqv⟩
  · exact
      { isStoppingTime := fun n t ↦
          V.le_rightCont t _ (htau.isStoppingTime n t)
        tendsto_top := htau.tendsto_top
        mono := htau.mono }
  · intro k
    exact StochasticCalculus.Martingale.rightCont_of_continuous (hmart k)
      (continuous_localizingStoppedProcess hcont (tau k))

/-- All Girsanov density data can be transported from a raw filtration to
its right continuation when the driving local martingale has continuous
paths. -/
theorem GirsanovDensityData.rightCont
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T) :
    GirsanovDensityData P (Filtration.rightCont V) M bracket T where
  novikov := h.novikov
  localQuadraticVariation :=
    h.localQuadraticVariation.rightCont_of_continuous h.continuous_martingale_path
  continuous_martingale_path := h.continuous_martingale_path
  adapted_martingale := StochasticCalculus.StronglyAdapted.mono_filtration
    h.adapted_martingale V.le_rightCont
  adapted_bracket := StochasticCalculus.StronglyAdapted.mono_filtration
    h.adapted_bracket V.le_rightCont
  continuous_monotone_bracket := h.continuous_monotone_bracket
  martingale_zero := h.martingale_zero
  bracket_zero := h.bracket_zero

/-- The elementary stochastic integral of an `E`-valued coefficient against
a real martingale on `(a,b]`.  This is the Banach-valued transform needed for
complex Fourier martingales. -/
def elementaryMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → E)
    (t : ℝ≥0) (omega : W) : E :=
  (M (min t b) omega - M (min t a) omega) • Z omega

/-- An integrable elementary predictable transform is a martingale. The
coefficient may be unbounded. -/
theorem martingale_elementaryMartingaleSmulProcess_of_integrable
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (hInt : ∀ t, Integrable (elementaryMartingaleSmulProcess M a b Z t) P) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  have hadapt : StronglyAdapted V
      (elementaryMartingaleSmulProcess M a b Z) := by
    intro t
    rcases le_total t a with hta | hat
    · have hzero : elementaryMartingaleSmulProcess M a b Z t = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hta,
          min_eq_left (hta.trans hab)]
      rw [hzero]
      exact stronglyMeasurable_zero
    · exact ((hM.stronglyMeasurable (min t b)).mono
          (V.mono (min_le_left _ _)) |>.sub
        ((hM.stronglyMeasurable (min t a)).mono
          (V.mono (min_le_left _ _)))).smul
        (hZ.mono (V.mono hat))
  refine ⟨hadapt, ?_⟩
  intro s t hst
  rcases le_total t a with hta | hat
  · have hIt : elementaryMartingaleSmulProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleSmulProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
      funext omega
      have hsa : s ≤ a := hst.trans hta
      simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
    rw [hIt, hIs, condExp_zero]
  · rcases le_total s a with hsa | has
    · have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
          min_eq_left (hsa.trans hab)]
      rw [hIs]
      let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
      have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
        funext omega
        simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
          Pi.smul_apply']
      have hdInt : Integrable d P :=
        (hM.integrable (min t b)).sub (hM.integrable a)
      have hprod : Integrable (d • Z) P := by
        rw [← hprocess]
        exact hInt t
      have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
        hZ.aestronglyMeasurable
      have hdelta := condExp_sub (hM.integrable (min t b))
        (hM.integrable a) (V a)
      have hamin : a ≤ min t b := le_min hat hab
      have hda : P[d | V a] =ᵐ[P] 0 := by
        filter_upwards [hdelta, hM.condExp_ae_eq hamin,
          Filter.Eventually.of_forall (congrFun
            (condExp_of_stronglyMeasurable (V.le a)
              (hM.stronglyMeasurable a) (hM.integrable a)))]
            with omega hd hfuture hpast
        change P[d | V a] omega = 0
        rw [show P[d | V a] omega =
          (P[M (min t b) | V a] - P[M a | V a]) omega by exact hd]
        simp only [Pi.sub_apply, hfuture, hpast, sub_self]
      have hIa : P[d • Z | V a] =ᵐ[P] 0 := by
        filter_upwards [hpull, hda] with omega hp hd
        simpa only [Pi.smul_apply', Pi.zero_apply, hd, zero_smul] using hp
      have htower := condExp_condExp_of_le (μ := P)
        (V.mono hsa) (V.le a) (f := d • Z)
      have hzeroCond : P[d • Z | V s] =ᵐ[P] 0 := by
        filter_upwards [htower, condExp_congr_ae hIa,
          Filter.Eventually.of_forall (congrFun
            (condExp_zero (μ := P) (m := V s) (E := E)))]
            with omega htow hcongr hzero
        rw [← htow, hcongr, hzero]
      rw [hprocess]
      exact hzeroCond
    · rcases le_total b s with hbs | hsb
      · have hconst : elementaryMartingaleSmulProcess M a b Z t =
            elementaryMartingaleSmulProcess M a b Z s := by
          funext omega
          simp [elementaryMartingaleSmulProcess,
            min_eq_right (hbs.trans hst), min_eq_right hbs,
            min_eq_right (has.trans hst), min_eq_right has]
        rw [hconst]
        exact Filter.Eventually.of_forall (congrFun
          (condExp_of_stronglyMeasurable (V.le s) (hadapt s) (hInt s)))
      · let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
        have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
          funext omega
          simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
            Pi.smul_apply']
        have hdInt : Integrable d P :=
          (hM.integrable (min t b)).sub (hM.integrable a)
        have hprod : Integrable (d • Z) P := by
          rw [← hprocess]
          exact hInt t
        have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
          (hZ.mono (V.mono has)).aestronglyMeasurable
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (V s)
        have hsmin : s ≤ min t b := le_min hst hsb
        have hpast := condExp_of_stronglyMeasurable (V.le s)
          ((hM.stronglyMeasurable a).mono (V.mono has)) (hM.integrable a)
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hsmin,
          Filter.Eventually.of_forall (congrFun hpast)]
            with omega hp hd hfuture hpast'
        have hd' : P[d | V s] omega =
            (P[M (min t b) | V s] - P[M a | V s]) omega := hd
        rw [hprocess, hp]
        change P[d | V s] omega • Z omega = _
        rw [hd', Pi.sub_apply, hfuture, hpast']
        simp only [elementaryMartingaleSmulProcess, min_eq_right has,
          min_eq_left hsb]

/-- A bounded Banach-valued coefficient known at the left endpoint defines a
martingale transform against any real martingale. -/
theorem martingale_elementaryMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  apply martingale_elementaryMartingaleSmulProcess_of_integrable hM hab hZ
  intro t
  let d : W → ℝ := fun omega ↦
    M (min t b) omega - M (min t a) omega
  have hd : Integrable d P :=
    (hM.integrable (min t b)).sub (hM.integrable (min t a))
  have hmeas : AEStronglyMeasurable
      (elementaryMartingaleSmulProcess M a b Z t) P := by
    exact hd.aestronglyMeasurable.smul
      (hZ.mono (V.le a)).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  apply (hd.norm.const_mul |C|).mono' hmeas.norm
  filter_upwards with omega
  simp only [elementaryMartingaleSmulProcess, d, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_abs]
  have h := mul_le_mul_of_nonneg_left
    ((hZbound omega).trans (le_abs_self C))
    (abs_nonneg (M (min t b) omega - M (min t a) omega))
  simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using h

/-- A finite sum of Banach-valued elementary transforms against one real
integrator. -/
def elementaryMartingaleSmulSum
    {W E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → E) : ℝ≥0 → W → E :=
  ∑ i ∈ S, elementaryMartingaleSmulProcess M (a i) (b i) (Z i)

/-- Finite sums of bounded predictable Banach-valued transforms are
martingales. -/
theorem martingale_elementaryMartingaleSmulSum
    {W E I : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → E}
    (hZ : ∀ i ∈ S, StronglyMeasurable[V (a i)] (Z i))
    (C : I → ℝ) (hZbound : ∀ i ∈ S, ∀ omega, ‖Z i omega‖ ≤ C i) :
    Martingale (elementaryMartingaleSmulSum M S a b Z) V P := by
  classical
  unfold elementaryMartingaleSmulSum
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using martingale_zero E V P
  | @insert i S hi ih =>
      have hhead : Martingale
          (elementaryMartingaleSmulProcess M (a i) (b i) (Z i)) V P :=
        martingale_elementaryMartingaleSmulProcess (E := E) hM
          (hab i (Finset.mem_insert_self i S))
          (hZ i (Finset.mem_insert_self i S)) (C i)
          (hZbound i (Finset.mem_insert_self i S))
      have htail : Martingale
          (∑ j ∈ S, elementaryMartingaleSmulProcess M (a j) (b j) (Z j))
          V P :=
        ih (fun j hj ↦ hab j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZbound j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hhead.add htail

/-- The coherent uniform-grid Banach-valued transform of a time-dependent
adapted coefficient against a real martingale. -/
def uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  elementaryMartingaleSmulSum M (Finset.range n)
    (fun i ↦ uniformPartitionTime T n i)
    (fun i ↦ uniformPartitionTime T n (i + 1))
    (fun i ↦ H (uniformPartitionTime T n i))

/-- Uniform-grid transforms of a bounded adapted Banach-valued coefficient
against a real martingale are martingales. -/
theorem martingale_uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hH : StronglyAdapted V H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformAdaptedMartingaleSmulProcess M H T n) V P := by
  apply martingale_elementaryMartingaleSmulSum hM (Finset.range n)
    (fun i hi ↦ monotone_uniformPartitionTime_general T n (Nat.le_succ i))
    (fun i hi ↦ hH (uniformPartitionTime T n i))
    (fun _ ↦ K) (fun i hi omega ↦ hHK _ _)

/-- The sum of two coherent Banach-valued left transforms, allowing two
different real martingale integrators and two adapted coefficients. -/
def uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : ℝ≥0 → W → ℝ) (H K : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  uniformAdaptedMartingaleSmulProcess M H T n +
    uniformAdaptedMartingaleSmulProcess N K T n

/-- Bounded adapted coefficients against two real martingales give a
Banach-valued martingale on every deterministic grid. -/
theorem martingale_uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (T : ℝ≥0) (n : ℕ) :
    Martingale
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T n) V P := by
  exact (martingale_uniformAdaptedMartingaleSmulProcess
    hM hH CH hHbound T n).add
      (martingale_uniformAdaptedMartingaleSmulProcess
        hN hK CK hKbound T n)

/-- At the terminal horizon, the coherent Banach-valued transform is the
usual uniform-partition left sum. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T omega =
      ∑ i ∈ Finset.range (n + 1),
        (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
          M (uniformPartitionTime T (n + 1) i) omega) •
            H (uniformPartitionTime T (n + 1) i) omega := by
  simp only [uniformAdaptedMartingaleSmulProcess,
    elementaryMartingaleSmulSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [elementaryMartingaleSmulProcess,
    min_eq_right hright.2, min_eq_right hleft.2]

/-- For real coefficients, the Banach-valued scalar-action construction is
the existing real left-sum process at the terminal horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T =
      uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T := by
  funext omega
  rw [uniformAdaptedMartingaleSmulProcess_terminal,
    uniformAdaptedMartingaleLeftSumProcess_terminal]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [smul_eq_mul, mul_comm]

/-- Taking real parts commutes with the coherent uniform-grid transform. -/
theorem uniformAdaptedMartingaleSmulProcess_re
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).re) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).re) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.reCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.reCLM_apply]

/-- Taking imaginary parts commutes with the coherent uniform-grid
transform. -/
theorem uniformAdaptedMartingaleSmulProcess_im
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).im) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).im) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.imCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.imCLM_apply]

/-- A bounded complex coefficient has a grid-independent terminal `L²`
transform bound.  Splitting into real and imaginary parts loses only the
harmless factor two and reuses the real martingale-transform isometry. -/
theorem
    eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (T : ℝ≥0) (hMT : MemLp (M T) 2 P)
    (hH : StronglyAdapted V H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (n : ℕ) :
    eLpNorm
      (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P ≤
      2 * K * eLpNorm (M T - M 0) 2 P := by
  let F : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let Fre : W → ℝ := fun omega => (F omega).re
  let Fim : W → ℝ := fun omega => (F omega).im
  have hHre : StronglyAdapted V (fun t omega => (H t omega).re) :=
    fun t => Complex.continuous_re.comp_stronglyMeasurable (hH t)
  have hHim : StronglyAdapted V (fun t omega => (H t omega).im) :=
    fun t => Complex.continuous_im.comp_stronglyMeasurable (hH t)
  have hHreBound (t : ℝ≥0) (omega : W) : ‖(H t omega).re‖ ≤ K :=
    (Complex.abs_re_le_norm (H t omega)).trans (hHK t omega)
  have hHimBound (t : ℝ≥0) (omega : W) : ‖(H t omega).im‖ ≤ K :=
    (Complex.abs_im_le_norm (H t omega)).trans (hHK t omega)
  have hRe :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHre K hHreBound n
  have hIm :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHim K hHimBound n
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hRe
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hIm
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_re M H T (n + 1)) T]
    at hRe
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_im M H T (n + 1)) T]
    at hIm
  have hFmeas : AEStronglyMeasurable F P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hM hH K hHK T (n + 1)).integrable T).1
  have hRemeas : AEStronglyMeasurable Fre P :=
    Complex.continuous_re.comp_aestronglyMeasurable hFmeas
  have hImmeas : AEStronglyMeasurable Fim P :=
    Complex.continuous_im.comp_aestronglyMeasurable hFmeas
  have hcastRe : AEStronglyMeasurable (fun omega => (Fre omega : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hRemeas
  have hcastIm : AEStronglyMeasurable
      (fun omega => (Fim omega : ℂ) * Complex.I) P :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hImmeas).mul_const _
  have hdecomp : F = fun omega =>
      (Fre omega : ℂ) + (Fim omega : ℂ) * Complex.I := by
    funext omega
    apply Complex.ext
    · simp [Fre, Fim]
    · rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im,
        Complex.ofReal_re, zero_add]
  calc
    eLpNorm
        (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P =
        eLpNorm F 2 P := by rfl
    _ = eLpNorm
        ((fun omega => (Fre omega : ℂ)) +
          fun omega => (Fim omega : ℂ) * Complex.I) 2 P := by
      rw [hdecomp]
      rfl
    _ ≤ eLpNorm (fun omega => (Fre omega : ℂ)) 2 P +
          eLpNorm (fun omega => (Fim omega : ℂ) * Complex.I) 2 P :=
      eLpNorm_add_le hcastRe hcastIm (by norm_num)
    _ = eLpNorm Fre 2 P + eLpNorm Fim 2 P := by
      congr 1
      · apply eLpNorm_congr_norm_ae
        filter_upwards with omega
        exact Complex.norm_real (Fre omega)
      · apply eLpNorm_congr_norm_ae
        filter_upwards with omega
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    _ ≤ K * eLpNorm (M T - M 0) 2 P +
          K * eLpNorm (M T - M 0) 2 P := add_le_add hRe hIm
    _ = 2 * K * eLpNorm (M T - M 0) 2 P := by ring

/-- A coherent uniform-grid transform is constant after its deterministic
horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T t : ℝ≥0) (n : ℕ) (ht : T ≤ t) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) t =
      uniformAdaptedMartingaleSmulProcess M H T (n + 1) T := by
  funext omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold elementaryMartingaleSmulProcess
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right (hright.2.trans ht), min_eq_right (hleft.2.trans ht),
    min_eq_right hright.2, min_eq_right hleft.2]

/-- Two complex martingale transforms admit the sum of their terminal
grid-independent `L²` bounds. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK) (n : ℕ) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  let A : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let D : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess N K T (n + 1) T
  have hAmeas : AEStronglyMeasurable A P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hM hH CH hHbound T (n + 1)).integrable T).1
  have hDmeas : AEStronglyMeasurable D P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hN hK CK hKbound T (n + 1)).integrable T).1
  calc
    eLpNorm
        (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T)
          2 P = eLpNorm (A + D) 2 P := by rfl
    _ ≤ eLpNorm A 2 P + eLpNorm D 2 P :=
      eLpNorm_add_le hAmeas hDmeas (by norm_num)
    _ ≤ 2 * CH * eLpNorm (M T - M 0) 2 P +
          2 * CK * eLpNorm (N T - N 0) 2 P := by
      exact add_le_add
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hM T hMT hH CH hHbound n)
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hN T hNT hK CK hKbound n)

/-- The two-transform `L²` bound holds at every observation time because
the transform is a martingale before the grid horizon and constant after it. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  have hterminal :=
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
      hM hN T hMT hNT hH hK CH CK hHbound hKbound n
  rcases le_total t T with ht | ht
  · exact (martingale_eLpNorm_le_of_le
      (martingale_uniformAdaptedTwoMartingaleSmulProcess
        hM hN hH hK CH CK hHbound hKbound T (n + 1))
      ht (by norm_num)).trans hterminal
  · have heq :
        uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t =
          uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T := by
      unfold uniformAdaptedTwoMartingaleSmulProcess
      simp only [Pi.add_apply]
      rw [uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le M H T t n ht,
        uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le N K T t n ht]
    rw [heq]
    exact hterminal

/-- Covariation sum on a fixed uniform grid, with every grid endpoint
stopped at the current time.  Unlike a separately repartitioned sum at each
time, this gives a coherent process for martingale approximation. -/
def uniformStoppedCovariationApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (X (min t (uniformPartitionTime T n (i + 1))) omega -
      X (min t (uniformPartitionTime T n i)) omega) *
    (Y (min t (uniformPartitionTime T n (i + 1))) omega -
      Y (min t (uniformPartitionTime T n i)) omega)

/-- Covariation carried by the first `k` cells of one uniform grid. -/
def quadraticCovariationPrefixApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range k,
    (X (uniformPartitionTime T n (i + 1)) omega -
      X (uniformPartitionTime T n i) omega) *
    (Y (uniformPartitionTime T n (i + 1)) omega -
      Y (uniformPartitionTime T n i) omega)

@[simp]
theorem quadraticCovariationPrefixApprox_zero
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n 0 omega = 0 := by
  simp [quadraticCovariationPrefixApprox]

/-- Fixed-time measurability of both processes makes every covariation
prefix measurable. -/
theorem aestronglyMeasurable_quadraticCovariationPrefixApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y : ℝ≥0 → W → ℝ}
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) (n k : ℕ) :
    AEStronglyMeasurable (quadraticCovariationPrefixApprox X Y T n k) P := by
  unfold quadraticCovariationPrefixApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
    (fun i _hi ↦ ((hXmeas (uniformPartitionTime T n (i + 1))).sub
      (hXmeas (uniformPartitionTime T n i))).mul
      ((hYmeas (uniformPartitionTime T n (i + 1))).sub
        (hYmeas (uniformPartitionTime T n i))))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

@[simp]
theorem quadraticCovariationPrefixApprox_full
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n n omega =
      quadraticCovariationApprox X Y T n omega := by
  rfl

/-- Stopping a coherent covariation sum exactly at its `k`-th grid point
turns it into the corresponding prefix sum. -/
theorem uniformStoppedCovariationApprox_uniformPartitionTime
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (hk : k ≤ n) (omega : W) :
    uniformStoppedCovariationApprox X Y T n
        (uniformPartitionTime T n k) omega =
      quadraticCovariationPrefixApprox X Y T n k omega := by
  let increment : ℕ → ℝ := fun i ↦
    (X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega) *
      (Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega)
  have htime : ∀ {i j : ℕ}, i ≤ j →
      uniformPartitionTime T n i ≤ uniformPartitionTime T n j := by
    intro i j hij
    unfold uniformPartitionTime
    gcongr
  have hhead :
      (∑ i ∈ Finset.range k, increment i) =
        quadraticCovariationPrefixApprox X Y T n k omega := by
    unfold quadraticCovariationPrefixApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ k := Finset.mem_range.mp hi
    simp only [increment, min_eq_right (htime hi1),
      min_eq_right (htime ((Nat.le_add_right i 1).trans hi1))]
  have htail : (∑ i ∈ Finset.Ico k n, increment i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k ≤ i := (Finset.mem_Ico.mp hi).1
    simp only [increment, min_eq_left (htime hki),
      min_eq_left (htime (hki.trans (Nat.le_add_right i 1))),
      sub_self, zero_mul]
  unfold uniformStoppedCovariationApprox
  change (∑ i ∈ Finset.range n, increment i) = _
  rw [← Finset.sum_range_add_sum_Ico increment hk, hhead, htail, add_zero]

/-- A point on a rational coarse grid has the same time coordinates on all
of its common uniform refinements. -/
theorem uniformPartitionTime_common_refinement_covariation
    (T : ℝ≥0) {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (i : ℕ) :
    uniformPartitionTime T (k * N) i =
      uniformPartitionTime
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) i := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hj0 : (j : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- A point in the `j`-th coarse block, sampled on an `N`-fold uniform
subdivision, is exactly the corresponding point of the `k*N` common
refinement. -/
theorem uniformPartitionTime_block_common_refinement
    (T : ℝ≥0) {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (j r : ℕ) :
    uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) N r =
      uniformPartitionTime T (k * N) (j * N + r) := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- On a nondegenerate common refinement, the left endpoint of every fine
cell active in a coarse right-endpoint block is one of that block's sampled
subdivision points. -/
theorem uniformPartitionTime_active_block_common_refinement
    (T : ℝ≥0) {k n i j : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (hactive : uniformPartitionTime T k j <
        uniformPartitionTime T (k * n) (i + 1) ∧
      uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T k (j + 1)) :
    ∃ r ∈ Finset.range (n + 1),
      uniformPartitionTime T (k * n) i =
        uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r := by
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hleftTime : uniformPartitionTime T (k * n) (j * n) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hn j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hrightTime : uniformPartitionTime T (k * n) ((j + 1) * n) =
      uniformPartitionTime T k (j + 1) := by
    have h := uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hlo : j * n ≤ i := by
    have hltTime : uniformPartitionTime T (k * n) (j * n) <
        uniformPartitionTime T (k * n) (i + 1) := by
      rw [hleftTime]
      exact hactive.1
    have hlt : j * n < i + 1 := hstrict.lt_iff_lt.mp hltTime
    omega
  have hhi : i < (j + 1) * n := by
    have hleTime : uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T (k * n) ((j + 1) * n) := by
      rw [hrightTime]
      exact hactive.2
    have hle : i + 1 ≤ (j + 1) * n := hstrict.le_iff_le.mp hleTime
    omega
  let r := i - j * n
  have hr : r < n := by
    dsimp only [r]
    rw [add_mul] at hhi
    simp only [one_mul] at hhi
    omega
  have hir : i = j * n + r := by
    dsimp only [r]
    omega
  refine ⟨r, Finset.mem_range.mpr (hr.trans (Nat.lt_succ_self n)), ?_⟩
  rw [hir]
  exact (uniformPartitionTime_block_common_refinement T hk hn j r).symm

/-- A continuous Banach-valued coefficient is uniformly close to its frozen
coarse left-endpoint value on every common refinement.  The bound is uniform
in the number of fine subdivisions inside each coarse cell. -/
theorem commonRefinement_continuousWeight_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E) (hA : Continuous A) (T : ℝ≥0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ, ∀ k, K ≤ k → 0 < k →
      ∀ n, 0 < n → ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
        uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
        ‖A (uniformPartitionTime T (k * n) i) -
          A (uniformPartitionTime T k j)‖ < epsilon := by
  intro epsilon hepsilon
  have huc : UniformContinuousOn A (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hA.continuousOn
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Tendsto
      (fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp
      (tendsto_add_atTop_nat 1)
  have hdiv : Tendsto
      (fun k : ℕ ↦ ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      atTop (nhds (0 : ℝ)) := by
    change Tendsto
      (NNReal.toReal ∘ fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0))
      atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hdiv eta heta
  refine ⟨K + 1, fun k hk hkpos n hn i hi j hj hactive ↦ ?_⟩
  have hkK : K ≤ k - 1 := by omega
  have hmeshNear := hK (k - 1) hkK
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hmesh : ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) < eta := by
    rw [← hkpred]
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hmeshNear
  obtain ⟨r, hr, htime⟩ :=
    uniformPartitionTime_active_block_common_refinement
      T (by by_contra hT; simp_all [uniformPartitionTime]) hkpos hn hactive
  have hkn : 0 < k * n := Nat.mul_pos hkpos hn
  have hi0 : i ≤ k * n := (Finset.mem_range.mp hi).le
  have hfineMem := uniformPartitionTime_mem_Icc_of_le T hkn hi0
  have hj0 : j ≤ k := (Finset.mem_range.mp hj).le
  have hcoarseMem := uniformPartitionTime_mem_Icc_of_le T hkpos hj0
  rw [← dist_eq_norm]
  apply hmod (uniformPartitionTime T (k * n) i) hfineMem
    (uniformPartitionTime T k j) hcoarseMem
  have hstep :
      uniformPartitionTime (T / (k : ℝ≥0)) n r ≤ T / (k : ℝ≥0) := by
    have hrlt : r < n + 1 := Finset.mem_range.mp hr
    exact (uniformPartitionTime_mem_Icc_of_le (T / (k : ℝ≥0)) hn
      (by omega)).2
  rw [htime]
  simp only [NNReal.dist_eq]
  have hnonneg : 0 ≤
      (((uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ≥0) : ℝ) -
        (uniformPartitionTime T k j : ℝ)) := by
    apply sub_nonneg.mpr
    exact_mod_cast (le_add_right (le_refl (uniformPartitionTime T k j)) :
        uniformPartitionTime T k j ≤
          uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r)
  rw [abs_of_nonneg hnonneg]
  have hstepReal :
      (uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ) ≤
        (T / (k : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hstep
  simpa only [NNReal.coe_add, add_sub_cancel_left] using
    hstepReal.trans_lt hmesh

/-- Freezing a continuous complex coefficient times a Lipschitz Brownian
factor separates into a continuous-coefficient error and a Brownian
oscillation error. -/
theorem norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
    {W : Type*} (A : ℝ≥0 → W → ℂ) (B : ℝ≥0 → W → ℝ)
    (g : ℝ → ℂ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) {k n i j : ℕ} (omega : W)
    (alpha R G delta : ℝ)
    (hAclose : ‖A (uniformPartitionTime T (k * n) i) omega -
        A (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ‖A (uniformPartitionTime T k j) omega‖ ≤ R)
    (hgbound : ‖g (B (uniformPartitionTime T (k * n) i) omega)‖ ≤ G)
    (hBclose : |B (uniformPartitionTime T (k * n) i) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta) :
    ‖A (uniformPartitionTime T (k * n) i) omega *
          g (B (uniformPartitionTime T (k * n) i) omega) -
        A (uniformPartitionTime T k j) omega *
          g (B (uniformPartitionTime T k j) omega)‖ ≤
      alpha * G + R * (L : ℝ) * delta := by
  let Af := A (uniformPartitionTime T (k * n) i) omega
  let Ac := A (uniformPartitionTime T k j) omega
  let gf := g (B (uniformPartitionTime T (k * n) i) omega)
  let gc := g (B (uniformPartitionTime T k j) omega)
  have hgclose : ‖gf - gc‖ ≤ (L : ℝ) * delta := by
    have hraw := hg.dist_le_mul
      (B (uniformPartitionTime T (k * n) i) omega)
      (B (uniformPartitionTime T k j) omega)
    rw [Real.dist_eq, dist_eq_norm] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_left hBclose L.coe_nonneg)
  have halpha : 0 ≤ alpha := (norm_nonneg (Af - Ac)).trans hAclose
  have hR : 0 ≤ R := (norm_nonneg Ac).trans hAbound
  calc
    ‖Af * gf - Ac * gc‖ = ‖(Af - Ac) * gf + Ac * (gf - gc)‖ := by
      congr 1
      ring
    _ ≤ ‖(Af - Ac) * gf‖ + ‖Ac * (gf - gc)‖ := norm_add_le _ _
    _ = ‖Af - Ac‖ * ‖gf‖ + ‖Ac‖ * ‖gf - gc‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ alpha * G + R * ((L : ℝ) * delta) := by
      exact add_le_add
        (mul_le_mul hAclose hgbound (norm_nonneg _) halpha)
        (mul_le_mul hAbound hgclose (norm_nonneg _) hR)
    _ = alpha * G + R * (L : ℝ) * delta := by ring

/-- At a coarse boundary of a common refinement, the completed-cell
covariation is exactly the corresponding index prefix. -/
theorem quadraticCovariationBeforeStopApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k N j : ℕ} (hk : 0 < k) (hN : 0 < N) (hj : j ≤ k)
    (omega : W) :
    quadraticCovariationBeforeStopApprox X Y T (k * N)
        (uniformPartitionTime T k j) omega =
      quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega := by
  by_cases hT0 : T = 0
  · subst T
    simp [quadraticCovariationBeforeStopApprox,
      quadraticCovariationPrefixApprox, uniformPartitionTime]
  have hT : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hT0)
  have hkn : 0 < k * N := Nat.mul_pos hk hN
  have hstrict : StrictMono (uniformPartitionTime T (k * N)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * N : ℕ) := by exact_mod_cast hkn
    gcongr
  have hboundary : uniformPartitionTime T (k * N) (j * N) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hN j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hcond (i : ℕ) :
      uniformPartitionTime T (k * N) (i + 1) ≤
          uniformPartitionTime T k j ↔
        i + 1 ≤ j * N := by
    rw [← hboundary]
    exact hstrict.le_iff_le
  have hjN : j * N ≤ k * N := Nat.mul_le_mul_right N hj
  unfold quadraticCovariationBeforeStopApprox
    quadraticCovariationPrefixApprox
  simp_rw [hcond]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A rational covariation prefix on a common refinement is literally the
ordinary covariation sum at the corresponding shorter horizon. -/
theorem quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (omega : W) :
    quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  unfold quadraticCovariationPrefixApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [uniformPartitionTime_common_refinement_covariation T hk hj hN i,
    uniformPartitionTime_common_refinement_covariation T hk hj hN (i + 1)]

/-- At a rational sub-horizon, a coherent stopped common-refinement sum is
exactly the ordinary covariation sum on the shorter horizon. -/
theorem uniformStoppedCovariationApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (hjk : j ≤ k) (omega : W) :
    uniformStoppedCovariationApprox X Y T (k * N)
        (T * (j : ℝ≥0) / (k : ℝ≥0)) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  have hstop := uniformStoppedCovariationApprox_uniformPartitionTime
    X Y T (k * N) (j * N) (Nat.mul_le_mul_right N hjk) omega
  have hprefix := quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj hN omega
  have htime : uniformPartitionTime T (k * N) (j * N) = a := by
    rw [uniformPartitionTime]
    dsimp only [a]
    have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    push_cast
    field_simp
  change uniformStoppedCovariationApprox X Y T (k * N) a omega =
    quadraticCovariationApprox X Y a (j * N) omega
  calc
    uniformStoppedCovariationApprox X Y T (k * N) a omega =
        uniformStoppedCovariationApprox X Y T (k * N)
          (uniformPartitionTime T (k * N) (j * N)) omega := by rw [htime]
    _ = quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega :=
      hstop
    _ = quadraticCovariationApprox X Y a (j * N) omega := by
      simpa only [a] using hprefix

/-- Cross variation at a rational sub-horizon also controls the corresponding
prefix of every common refinement.  Unlike a stopped-process formulation,
this form can be multiplied by random coarse-grid coefficients. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have hcomp := (h a).comp hns.tendsto_atTop
  apply hcomp.congr_left
  intro n
  filter_upwards with omega
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change quadraticCovariationApprox X Y a (ns n + 1) omega = _
  rw [hcount]
  exact (StochasticCalculus.quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) omega).symm

/-- The common-refinement prefix limit, including its zero prefix. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement_all
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  by_cases hj : j = 0
  · subst j
    have hzero : TendstoInMeasure P
        (fun n ↦ quadraticCovariationPrefixApprox X Y T
          (k * (n + 1)) 0) atTop (C 0) := by
      apply (h 0).congr_left
      intro n
      filter_upwards with omega
      rw [quadraticCovariationPrefixApprox_zero]
      unfold quadraticCovariationApprox uniformPartitionTime
      simp
    simpa only [Nat.cast_zero, mul_zero, zero_div, zero_mul] using hzero
  · exact h.quadraticCovariationPrefixApprox_common_refinement T hk
      (Nat.pos_of_ne_zero hj)

/-- Cross-variation mass carried by the cells between two prefix indices. -/
noncomputable def quadraticCovariationBlockApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n lo hi : ℕ) (omega : W) : ℝ :=
  quadraticCovariationPrefixApprox X Y T n hi omega -
    quadraticCovariationPrefixApprox X Y T n lo omega

/-- Two common-refinement prefix limits give the corresponding
cross-variation block limit, with no positivity restriction on either
endpoint. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationBlockApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (lo hi : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (lo * (n + 1)) (hi * (n + 1))) atTop
      (fun omega ↦
        C (T * (hi : ℝ≥0) / (k : ℝ≥0)) omega -
          C (T * (lo : ℝ≥0) / (k : ℝ≥0)) omega) := by
  have hhi := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk hi
  have hlo := h.quadraticCovariationPrefixApprox_common_refinement_all
    T hk lo
  exact hhi.sub_real_noMeas hlo

/-- A complete random coarse-step weight can be integrated against the
cross-variation blocks on every common refinement. -/
theorem
    HasCrossVariationProcessInProbability.fullStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℝ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega)) := by
  apply tendstoInMeasure_finset_sum_mul_fixed_real (Finset.range k)
    (fun i n ↦ quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)))
    (fun i omega ↦ C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega) c
  · intro i _hi
    simpa only [uniformPartitionTime] using
      h.quadraticCovariationBlockApprox_common_refinement T hk i (i + 1)
  · intro i _hi n
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  · exact hcmeas

/-- Complex random coarse-step weights can likewise be integrated against a
real cross variation on common refinements.  The two real component limits
are synchronized before they are reassembled. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBlockApprox X Y T (k * (n + 1))
          (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  let R : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let I : ℕ → W → ℝ := fun n omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * quadraticCovariationBlockApprox X Y T (k * (n + 1))
      (i * (n + 1)) ((i + 1) * (n + 1)) omega
  let r : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).re * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  let im : W → ℝ := fun omega ↦ ∑ i ∈ Finset.range k,
    (c i omega).im * (C (uniformPartitionTime T k (i + 1)) omega -
      C (uniformPartitionTime T k i) omega)
  have hR : TendstoInMeasure P R atTop r := by
    simpa only [R, r] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).re)
        (fun i hi ↦ Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hI : TendstoInMeasure P I atTop im := by
    simpa only [I, im] using h.fullStepWeight_common_refinement hXmeas hYmeas
      T hk (fun i omega ↦ (c i omega).im)
        (fun i hi ↦ Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi))
  have hblockmeas (i n : ℕ) : AEStronglyMeasurable
      (quadraticCovariationBlockApprox X Y T (k * (n + 1))
        (i * (n + 1)) ((i + 1) * (n + 1))) P := by
    unfold quadraticCovariationBlockApprox
    exact (aestronglyMeasurable_quadraticCovariationPrefixApprox
      hXmeas hYmeas T (k * (n + 1)) ((i + 1) * (n + 1))).sub
      (aestronglyMeasurable_quadraticCovariationPrefixApprox
        hXmeas hYmeas T (k * (n + 1)) (i * (n + 1)))
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) P := by
    dsimp only [R]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_re.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hImeas (n : ℕ) : AEStronglyMeasurable (I n) P := by
    dsimp only [I]
    have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
      (fun i hi ↦
        (Complex.continuous_im.comp_aestronglyMeasurable
          (hcmeas i hi)).mul (hblockmeas i n))
    convert hs using 1
    funext omega
    simp only [Finset.sum_apply, Pi.mul_apply]
  let combine : ℝ → ℝ → ℂ := fun x y ↦ (x : ℂ) + (y : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hparts := TendstoInMeasure.continuous_comp₂ hRmeas hImeas hR hI hcombine
  apply hparts.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, R, I, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, R, I, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (quadraticCovariationBlockApprox X Y T (k * (n + 1))
            (i * (n + 1)) ((i + 1) * (n + 1)) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add]
  · exact Filter.Eventually.of_forall fun omega ↦ by
      apply Complex.ext
      · simp only [combine, r, im, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, add_zero, sub_zero]
        change _ = Complex.reCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.reCLM_apply, Complex.mul_re, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [combine, r, im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          zero_add, add_zero, zero_mul, mul_one]
        change _ = Complex.imCLM (∑ i ∈ Finset.range k, c i omega *
          (C (uniformPartitionTime T k (i + 1)) omega -
            C (uniformPartitionTime T k i) omega : ℂ))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Complex.imCLM_apply, Complex.mul_im, Complex.sub_re,
          Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_zero, mul_zero,
          zero_add]

/-- Fixed-time cross variation also controls complex frozen coarse-step
weights when the common-refinement sums are written with completed cells.
This is the form used by the complex Girsanov bracket residual. -/
theorem
    HasCrossVariationProcessInProbability.fullComplexStepWeight_beforeStop_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (c : ℕ → W → ℂ)
    (hcmeas : ∀ i ∈ Finset.range k, AEStronglyMeasurable (c i) P) :
    TendstoInMeasure P
      (fun n omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k (i + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y T (k * (n + 1))
              (uniformPartitionTime T k i) omega : ℂ)) atTop
      (fun omega ↦ ∑ i ∈ Finset.range k, c i omega *
        (C (uniformPartitionTime T k (i + 1)) omega -
          C (uniformPartitionTime T k i) omega : ℂ)) := by
  have hblock := h.fullComplexStepWeight_common_refinement
    hXmeas hYmeas T hk c hcmeas
  apply hblock.congr_left
  intro n
  exact Filter.Eventually.of_forall fun omega ↦ by
    apply Finset.sum_congr rfl
    intro i hi
    have hilt : i < k := Finset.mem_range.mp hi
    rw [quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) (Nat.succ_le_iff.mpr hilt) omega,
      quadraticCovariationBeforeStopApprox_common_refinement
        X Y T hk (Nat.zero_lt_succ n) hilt.le omega]
    unfold quadraticCovariationBlockApprox
    push_cast
    simp only [Nat.succ_eq_add_one]

/-- Complex-valued frozen weights satisfy the same completed-block identity
against a real covariation. -/
theorem quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k (j + 1)) omega -
          quadraticCovariationBeforeStopApprox X Y t n
            (uniformPartitionTime t k j) omega : ℂ)) =
      ∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0) *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ) := by
  have hgrid : ∀ j : ℕ,
      uniformPartitionTime t k j ≤ uniformPartitionTime t k (j + 1) := by
    intro j
    unfold uniformPartitionTime
    gcongr
    omega
  unfold quadraticCovariationBeforeStopApprox
  push_cast
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  let r := uniformPartitionTime t n (i + 1)
  let a := uniformPartitionTime t k j
  let b := uniformPartitionTime t k (j + 1)
  have hab : a ≤ b := hgrid j
  by_cases hra : r ≤ a
  · have hrb : r ≤ b := hra.trans hab
    have hnot : ¬a < r := not_lt_of_ge hra
    simp only [r, a, b] at hra hrb hnot ⊢
    simp only [hra, hrb, hnot, false_and, ↓reduceIte, sub_self,
      zero_mul, mul_zero]
  · by_cases hrb : r ≤ b
    · have har : a < r := lt_of_not_ge hra
      simp only [r, a, b] at hra hrb har ⊢
      simp only [hra, hrb, har, true_and, ↓reduceIte]
      push_cast
      ring
    · simp only [r, a, b] at hra hrb ⊢
      simp only [hra, hrb, and_false, ↓reduceIte, sub_self,
        zero_mul, mul_zero]

/-- A right endpoint in a positive uniform partition activates exactly one
coarse complex step. -/
theorem uniformPartition_rightEndpoint_complexStep_sum_eq
    (t r : ℝ≥0) (k : ℕ) (ht : 0 < t) (hk : 0 < k)
    (c : ℕ → ℂ) {j : ℕ} (hj : j ∈ Finset.range k)
    (hactive : uniformPartitionTime t k j < r ∧
      r ≤ uniformPartitionTime t k (j + 1)) :
    (∑ l ∈ Finset.range k,
      if uniformPartitionTime t k l < r ∧
          r ≤ uniformPartitionTime t k (l + 1) then c l else 0) = c j := by
  have hstrict : StrictMono (uniformPartitionTime t k) := by
    intro a b hab
    unfold uniformPartitionTime
    have hk' : (0 : ℝ≥0) < (k : ℕ) := by exact_mod_cast hk
    gcongr
  rw [Finset.sum_eq_single j]
  · simp only [hactive, and_self, ↓reduceIte]
  · intro l hl hlj
    have hnot : ¬(uniformPartitionTime t k l < r ∧
        r ≤ uniformPartitionTime t k (l + 1)) := by
      intro hlactive
      rcases lt_trichotomy l j with hlt | heq | hgt
      · have hle : l + 1 ≤ j := by omega
        exact (not_lt_of_ge hlactive.2)
          ((hstrict.monotone hle).trans_lt hactive.1)
      · exact hlj heq
      · have hle : j + 1 ≤ l := by omega
        exact (not_lt_of_ge hactive.2)
          ((hstrict.monotone hle).trans_lt hlactive.1)
    simp only [hnot, ↓reduceIte]
  · exact fun hnot ↦ (hnot hj).elim

/-- A complex scalar close to the unique active coarse block is close to
the corresponding complex right-endpoint step sum. -/
theorem norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    (t r : ℝ≥0) (k : ℕ) (hk : 0 < k) (hr0 : 0 < r) (hrt : r ≤ t)
    (weight : ℂ) (c : ℕ → ℂ) (K : ℝ)
    (hclose : ∀ j ∈ Finset.range k,
      uniformPartitionTime t k j < r ∧
        r ≤ uniformPartitionTime t k (j + 1) →
      ‖weight - c j‖ ≤ K) :
    ‖weight - ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        c j
      else 0‖ ≤ K := by
  have hone := uniformPartition_rightEndpoint_blocks_sum_one
    t r k hk hr0 hrt
  have honeC : (∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        (1 : ℂ)
      else 0) = 1 := by
    exact_mod_cast hone
  have hweightSum : weight = ∑ j ∈ Finset.range k,
      if uniformPartitionTime t k j < r ∧
          r ≤ uniformPartitionTime t k (j + 1) then
        weight
      else 0 := by
    calc
      weight = weight * 1 := by ring
      _ = weight * ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            (1 : ℂ)
          else 0 := by rw [honeC]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  have hdiff :
      (weight - (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            c j
          else 0)) =
        (∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then
            weight - c j
          else 0) := by
    calc
      _ = (∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0 := congrArg (fun z ↦ z - ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j < r ∧
              r ≤ uniformPartitionTime t k (j + 1) then c j else 0)
                hweightSum
      _ = ∑ j ∈ Finset.range k,
          ((if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              weight
            else 0) -
            if uniformPartitionTime t k j < r ∧
                r ≤ uniformPartitionTime t k (j + 1) then
              c j
            else 0) := by rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> ring
  rw [hdiff]
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        ‖if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          weight - c j
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k,
        if uniformPartitionTime t k j < r ∧
            r ≤ uniformPartitionTime t k (j + 1) then
          K
        else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hactive
      · exact hclose j hj hactive
      · norm_num
    _ = K := by
      have hscaled := congrArg (fun x : ℝ ↦ K * x) hone
      simpa only [Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul,
        one_mul] using hscaled

/-- Maximum error made by freezing a complex weight on the coarse cells of
a positive common refinement. -/
noncomputable def commonRefinementMaxComplexStepError
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
  (k n : ℕ) (omega : W) : ℝ :=
  (Finset.range ((k + 1) * (n + 1))).sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖

theorem commonRefinementMaxComplexStepError_nonneg
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0)
    (k n : ℕ) (omega : W) :
    0 ≤ commonRefinementMaxComplexStepError A T k n omega := by
  unfold commonRefinementMaxComplexStepError
  exact (norm_nonneg _).trans
    (Finset.le_sup' (fun i ↦
      ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0‖)
      (Finset.mem_range.mpr (Nat.mul_pos
        (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))))

theorem stronglyMeasurable_commonRefinementMaxComplexStepError
    {W : Type*} [MeasurableSpace W] {A : ℝ≥0 → W → ℂ}
    (hA : ∀ s, StronglyMeasurable (A s)) (T : ℝ≥0) (k n : ℕ) :
    StronglyMeasurable (commonRefinementMaxComplexStepError A T k n) := by
  apply Measurable.stronglyMeasurable
  unfold commonRefinementMaxComplexStepError
  let f : ℕ → W → ℝ := fun i omega ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hf : ∀ i ∈ Finset.range ((k + 1) * (n + 1)), Measurable (f i) := by
    intro i _hi
    let g : ℕ → W → ℂ := fun j omega ↦
      if uniformPartitionTime T (k + 1) j <
            uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
          uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
            uniformPartitionTime T (k + 1) (j + 1) then
        A (uniformPartitionTime T (k + 1) j) omega
      else 0
    have hg : ∀ j ∈ Finset.range (k + 1), StronglyMeasurable (g j) := by
      intro j _hj
      dsimp only [g]
      split_ifs
      · exact hA _
      · exact stronglyMeasurable_const
    have hsumFun : StronglyMeasurable
        (∑ j ∈ Finset.range (k + 1), g j) :=
      Finset.stronglyMeasurable_sum (Finset.range (k + 1)) hg
    have hsum : StronglyMeasurable (fun omega ↦
        ∑ j ∈ Finset.range (k + 1),
          if uniformPartitionTime T (k + 1) j <
                uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ∧
              uniformPartitionTime T ((k + 1) * (n + 1)) (i + 1) ≤
                uniformPartitionTime T (k + 1) (j + 1) then
            A (uniformPartitionTime T (k + 1) j) omega
          else 0) := by
      convert hsumFun using 1
      funext omega
      simp only [Finset.sum_apply, g]
    have hnorm :=
      ((hA (uniformPartitionTime T ((k + 1) * (n + 1)) i)).sub hsum)
        |>.norm.measurable
    simpa only [f, Pi.sub_apply] using hnorm
  have hsup := Finset.measurable_sup'
    (⟨0, Finset.mem_range.mpr (Nat.mul_pos
      (Nat.zero_lt_succ k) (Nat.zero_lt_succ n))⟩) hf
  convert hsup using 1
  ext omega
  symm
  exact Finset.sup'_apply _ f omega

/-- The common-refinement freezing error of a continuous complex path
vanishes, uniformly over an arbitrary number of inner subdivisions. -/
theorem commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
    {W : Type*} (A : ℝ≥0 → W → ℂ) (T : ℝ≥0) (hT : 0 < T)
    (omega : W) (hA : Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    Tendsto (fun k ↦ commonRefinementMaxComplexStepError A T k (n k) omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := commonRefinement_continuousWeight_close
    (fun s ↦ A s omega) hA T (epsilon / 2) (by positivity)
  refine ⟨K, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (commonRefinementMaxComplexStepError_nonneg
      A T k (n k) omega)]
  let s := Finset.range ((k + 1) * (n k + 1))
  let f : ℕ → ℝ := fun i ↦
    ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.mul_pos
    (Nat.zero_lt_succ k) (Nat.zero_lt_succ (n k)))⟩
  change s.sup' hs f < epsilon
  rw [Finset.sup'_lt_iff]
  intro i hi
  change i ∈ Finset.range ((k + 1) * (n k + 1)) at hi
  change ‖A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega -
      ∑ j ∈ Finset.range (k + 1),
        if uniformPartitionTime T (k + 1) j <
              uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ∧
            uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) ≤
              uniformPartitionTime T (k + 1) (j + 1) then
          A (uniformPartitionTime T (k + 1) j) omega
        else 0‖ < epsilon
  have hkpos : 0 < k + 1 := Nat.zero_lt_succ k
  have hnpos : 0 < n k + 1 := Nat.zero_lt_succ (n k)
  have hkn : 0 < (k + 1) * (n k + 1) := Nat.mul_pos hkpos hnpos
  have hi1 : i + 1 ≤ (k + 1) * (n k + 1) := Finset.mem_range.mp hi
  have hrt := (uniformPartitionTime_mem_Icc_of_le T hkn hi1).2
  have hr0 :
      0 < uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1) := by
    have hstrict : StrictMono
        (uniformPartitionTime T ((k + 1) * (n k + 1))) := by
      intro a b hab
      unfold uniformPartitionTime
      have hden : (0 : ℝ≥0) < ((k + 1) * (n k + 1) : ℕ) := by
        exact_mod_cast hkn
      gcongr
    have hpos := hstrict (Nat.zero_lt_succ i)
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]
      using hpos
  refine (norm_sub_uniformPartition_rightEndpoint_complexStep_sum_le
    T (uniformPartitionTime T ((k + 1) * (n k + 1)) (i + 1))
      (k + 1) hkpos hr0 hrt
      (A (uniformPartitionTime T ((k + 1) * (n k + 1)) i) omega)
      (fun j ↦ A (uniformPartitionTime T (k + 1) j) omega)
      (epsilon / 2) ?_).trans_lt (by linarith)
  intro j hj hactive
  exact (hK (k + 1) (by omega) hkpos (n k + 1) hnpos i hi j hj
    hactive).le

/-- Measurable continuous complex paths have vanishing common-refinement
freezing error in probability, uniformly over arbitrary inner counts. -/
theorem commonRefinementMaxComplexStepError_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {A : ℝ≥0 → W → ℂ} (hAmeas : ∀ s, StronglyMeasurable (A s))
    (T : ℝ≥0) (hT : 0 < T)
    (hAcont : ∀ omega, Continuous fun s ↦ A s omega) (n : ℕ → ℕ) :
    TendstoInMeasure P
      (fun k ↦ commonRefinementMaxComplexStepError A T k (n k))
      atTop (fun _ ↦ 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro k
    exact (stronglyMeasurable_commonRefinementMaxComplexStepError
      hAmeas T k (n k)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      commonRefinementMaxComplexStepError_tendsto_zero_of_continuous
        A T hT omega (hAcont omega) n

/-- The completed-block freezing estimate remains sharp for complex left
weights; no loss from splitting into real and imaginary components is
needed. -/
theorem norm_complexWeightedQuadraticCovariation_sub_completedBlocks_le
    {W : Type*} [MeasurableSpace W]
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n k : ℕ)
    (weight c : ℕ → W → ℂ) (K : ℝ) (hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range n,
      ‖weight i omega -
        ∑ j ∈ Finset.range k,
          if uniformPartitionTime t k j <
                uniformPartitionTime t n (i + 1) ∧
              uniformPartitionTime t n (i + 1) ≤
                uniformPartitionTime t k (j + 1) then
            c j omega
          else 0‖ ≤ K) :
    ‖(∑ i ∈ Finset.range n, weight i omega *
        ((X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega) *
        (Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega) : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k (j + 1)) omega -
            quadraticCovariationBeforeStopApprox X Y t n
              (uniformPartitionTime t k j) omega : ℂ)‖ ≤
      K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
  rw [quadraticCovariationBeforeStop_uniform_blocks_eq_complexWeighted_cells]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range n,
        (weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(weight i omega -
          ∑ j ∈ Finset.range k,
            if uniformPartitionTime t k j <
                  uniformPartitionTime t n (i + 1) ∧
                uniformPartitionTime t n (i + 1) ≤
                  uniformPartitionTime t k (j + 1) then
              c j omega
            else 0) *
          ((X (uniformPartitionTime t n (i + 1)) omega -
            X (uniformPartitionTime t n i) omega) *
          (Y (uniformPartitionTime t n (i + 1)) omega -
            Y (uniformPartitionTime t n i) omega) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, K *
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, ← Complex.ofReal_sub,
        ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs]
      simp only [Real.norm_eq_abs]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _))
          (abs_nonneg _)
    _ = K * (∑ i ∈ Finset.range n,
        |X (uniformPartitionTime t n (i + 1)) omega -
          X (uniformPartitionTime t n i) omega| *
        |Y (uniformPartitionTime t n (i + 1)) omega -
          Y (uniformPartitionTime t n i) omega|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ K * √(quadraticVariationApprox X t n omega *
        quadraticVariationApprox Y t n omega) := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_uniformPartition_increment_mul_le_sqrt X Y t n omega) hK

/-- The coherent stopped-grid covariation agrees with the ordinary
covariation approximant at its terminal horizon. -/
theorem uniformStoppedCovariationApprox_terminal
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformStoppedCovariationApprox X Y T (n + 1) T omega =
      quadraticCovariationApprox X Y T (n + 1) omega := by
  unfold uniformStoppedCovariationApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right hright.2, min_eq_right hleft.2]

/-- Process-level discrete integration by parts on one fixed uniform grid. -/
theorem uniformStopped_product_decomposition
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T (n + 1) t omega +
        uniformAdaptedMartingaleSmulProcess X Y T (n + 1) t omega +
          uniformStoppedCovariationApprox X Y T (n + 1) t omega := by
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  unfold uniformStoppedCovariationApprox
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  symm
  calc
    (∑ i ∈ Finset.range (n + 1),
        (((Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega) •
              X (uniformPartitionTime T (n + 1) i) omega +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) •
              Y (uniformPartitionTime T (n + 1) i) omega) +
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega) *
          (Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            Y (min t (uniformPartitionTime T (n + 1) i)) omega))) =
        ∑ i ∈ Finset.range (n + 1),
          (X (min t (uniformPartitionTime T (n + 1) (i + 1))) omega *
              Y (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
            X (min t (uniformPartitionTime T (n + 1) i)) omega *
              Y (min t (uniformPartitionTime T (n + 1) i)) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : uniformPartitionTime T (n + 1) i ≤ t
      · rw [min_eq_right hi]
        simp only [smul_eq_mul]
        ring
      · have hright : t ≤ uniformPartitionTime T (n + 1) i := le_of_not_ge hi
        have hnext : uniformPartitionTime T (n + 1) i ≤
            uniformPartitionTime T (n + 1) (i + 1) :=
          monotone_uniformPartitionTime_general T (n + 1) (Nat.le_succ i)
        rw [min_eq_left hright, min_eq_left (hright.trans hnext)]
        simp only [sub_self, zero_smul, zero_mul, add_zero]
    _ = X (min t (uniformPartitionTime T (n + 1) (n + 1))) omega *
          Y (min t (uniformPartitionTime T (n + 1) (n + 1))) omega -
        X (min t (uniformPartitionTime T (n + 1) 0)) omega *
          Y (min t (uniformPartitionTime T (n + 1) 0)) omega := by
      exact Finset.sum_range_sub
        (fun i ↦ X (min t (uniformPartitionTime T (n + 1) i)) omega *
          Y (min t (uniformPartitionTime T (n + 1) i)) omega) (n + 1)
    _ = X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega := by
      have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      have htop : uniformPartitionTime T (n + 1) (n + 1) = T := by
        rw [uniformPartitionTime]
        exact mul_div_cancel_right₀ T hn
      rw [htop]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        min_zero]

/-- Positive-grid form of the coherent discrete product decomposition. -/
theorem uniformStopped_product_decomposition_pos
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (omega : W) :
    X (min t T) omega * Y (min t T) omega - X 0 omega * Y 0 omega =
      uniformAdaptedMartingaleSmulProcess Y X T n t omega +
        uniformAdaptedMartingaleSmulProcess X Y T n t omega +
          uniformStoppedCovariationApprox X Y T n t omega := by
  have hn' : 1 ≤ n := hn
  simpa only [Nat.sub_add_cancel hn'] using
    uniformStopped_product_decomposition X Y T (n - 1) t omega

/-- A measurable Banach-valued `L¹`-norm limit of integrable functions is
integrable. -/
theorem integrable_of_tendsto_eLpNorm_one_sub_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {f : ℕ → W → E} {g : W → E}
    (hf : ∀ n, Integrable (f n) P)
    (hg : AEStronglyMeasurable g P)
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g - f n) 1 P)
      Filter.atTop (nhds 0)) :
    Integrable g P := by
  have hlt : ∀ᶠ n in Filter.atTop,
      eLpNorm (g - f n) 1 P < 1 :=
    (tendsto_order.1 hconv).2 1 (by simp)
  rcases hlt.exists with ⟨n, hn⟩
  have hdiff : Integrable (g - f n) P :=
    memLp_one_iff_integrable.mp
      ⟨hg.sub (hf n).1, hn.trans (by simp)⟩
  simpa only [sub_add_cancel] using hdiff.add (hf n)

/-- A strongly adapted pointwise-in-time `L¹`-norm limit of Banach-valued
martingales is a martingale. -/
theorem martingale_of_tendsto_eLpNorm_one_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hconv : ∀ t, Filter.Tendsto
      (fun n ↦ eLpNorm (Y t - X n t) 1 P) Filter.atTop (nhds 0)) :
    Martingale Y V P := by
  have hYint : ∀ t, Integrable (Y t) P := fun t ↦
    integrable_of_tendsto_eLpNorm_one_sub_banach
      (fun n ↦ (hX n).integrable t)
      ((hYadapt t).mono (V.le t)).aestronglyMeasurable (hconv t)
  refine ⟨hYadapt, ?_⟩
  intro s t hst
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff
    ((stronglyMeasurable_condExp.mono (V.le s)).sub
      ((hYadapt s).mono (V.le s))).aestronglyMeasurable one_ne_zero]
  apply le_antisymm
  · have hconvS : Filter.Tendsto (fun n ↦ eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      convert hconv s using 1
      ext n
      exact eLpNorm_sub_comm (X n s) (Y s) 1 P
    have hsum : Filter.Tendsto (fun n ↦
        eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P)
        Filter.atTop (nhds 0) := by
      simpa only [add_zero] using (hconv t).add hconvS
    apply ge_of_tendsto hsum
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hdecomp :
        P[Y t | V s] - Y s =ᵐ[P]
          P[Y t - X n t | V s] + (X n s - Y s) := by
      filter_upwards [condExp_sub (hYint t) ((hX n).integrable t) (V s),
        (hX n).condExp_ae_eq hst] with omega hsub hmart
      simp only [Pi.sub_apply, Pi.add_apply] at hsub hmart ⊢
      rw [hsub, hmart]
      abel
    calc
      eLpNorm (P[Y t | V s] - Y s) 1 P =
          eLpNorm (P[Y t - X n t | V s] + (X n s - Y s)) 1 P :=
        eLpNorm_congr_ae hdecomp
      _ ≤ eLpNorm (P[Y t - X n t | V s]) 1 P +
            eLpNorm (X n s - Y s) 1 P :=
        eLpNorm_add_le
          (integrable_condExp (μ := P) (m := V s)
          (f := Y t - X n t)).1
          ((((hX n).stronglyMeasurable s).mono
            (V.le s)).aestronglyMeasurable.sub (hYint s).1) le_rfl
      _ ≤ eLpNorm (Y t - X n t) 1 P + eLpNorm (X n s - Y s) 1 P :=
        add_le_add (eLpNorm_condExp_le_eLpNorm _ le_rfl) le_rfl
  · exact zero_le

/-- Banach-valued Vitali convergence in `L¹`: convergence in measure plus
uniform integrability gives convergence of the `L¹` distance. -/
theorem tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {X : ℕ → W → E} {Y : W → E}
    (hUI : UniformIntegrable X 1 P)
    (hconv : TendstoInMeasure P X atTop Y) :
    Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (nhds 0) := by
  have hYmem : MemLp Y 1 P := hUI.memLp_of_tendstoInMeasure hconv
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ (hUI.memLp n).1) hYmem hUI.unifIntegrable hconv

/-- Banach-valued Vitali closure for martingales: convergence in measure
plus uniform integrability at every time gives the `L¹` convergence required
by `martingale_of_tendsto_eLpNorm_one_banach`. -/
theorem martingale_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X : ℕ → ℝ≥0 → W → E} {Y : ℝ≥0 → W → E}
    (hX : ∀ n, Martingale (X n) V P)
    (hYadapt : StronglyAdapted V Y)
    (hUI : ∀ t, UniformIntegrable (fun n ↦ X n t) 1 P)
    (hconv : ∀ t, TendstoInMeasure P (fun n ↦ X n t) atTop (Y t)) :
    Martingale Y V P := by
  apply martingale_of_tendsto_eLpNorm_one_banach hX hYadapt
  intro t
  have hLp : Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI t) (hconv t)
  convert hLp using 1
  ext n
  exact eLpNorm_sub_comm (Y t) (X n t) 1 P

/-- Uniform integrability passes from one measurable family to any
Banach-valued family whose pointwise norm it dominates.  The source and
target spaces may differ. -/
theorem UniformIntegrable.mono_norm_banach
    {W I E F : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {P : Measure W} {f : I → W → E} {g : I → W → F}
    {p : ℝ≥0∞} (hf : UniformIntegrable f p P)
    (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hgf : ∀ i omega, ‖g i omega‖ ≤ ‖f i omega‖) :
    UniformIntegrable g p P := by
  refine ⟨hg, ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hf.2.1 hepsilon
    refine ⟨delta, hdelta, fun i s hs hPs ↦ ?_⟩
    apply (eLpNorm_mono fun omega ↦ ?_).trans (hbound i s hs hPs)
    by_cases homega : omega ∈ s
    · simp only [Set.indicator_of_mem homega]
      exact hgf i omega
    · simp only [Set.indicator_of_notMem homega, norm_zero]
      exact le_rfl
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun i ↦ (eLpNorm_mono (hgf i)).trans (hC i)⟩

/-- Uniform integrability is preserved when restricting to an arbitrary
reindexed subfamily. -/
theorem UniformIntegrable.comp_index
    {W I J E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (g : J → I) :
    UniformIntegrable (fun j => f (g j)) p P := by
  refine ⟨fun j => hf.1 (g j), ?_, ?_⟩
  · intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ := hf.2.1 hepsilon
    exact ⟨delta, hdelta, fun j => hbound (g j)⟩
  · obtain ⟨C, hC⟩ := hf.2.2
    exact ⟨C, fun j => hC (g j)⟩

/-- The sum of two uniformly integrable Banach-valued families is uniformly
integrable. -/
theorem UniformIntegrable.add_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f g : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hg : UniformIntegrable g p P)
    (hp : 1 ≤ p) :
    UniformIntegrable (fun i omega => f i omega + g i omega) p P := by
  refine ⟨fun i => (hf.1 i).add (hg.1 i), ?_, ?_⟩
  · change UnifIntegrable (f + g) p P
    exact hf.2.1.add hg.2.1 hp hf.1 hg.1
  · obtain ⟨Cf, hCf⟩ := hf.2.2
    obtain ⟨Cg, hCg⟩ := hg.2.2
    refine ⟨Cf + Cg, fun i => ?_⟩
    exact (eLpNorm_add_le (hf.1 i) (hg.1 i) hp).trans
      (add_le_add (hCf i) (hCg i))

/-- A fixed natural multiple of a uniformly integrable Banach-valued family
is uniformly integrable. -/
theorem UniformIntegrable.nsmul_banach
    {W I E : Type*} [MeasurableSpace W] [NormedAddCommGroup E]
    {P : Measure W} {f : I → W → E} {p : ℝ≥0∞}
    (hf : UniformIntegrable f p P) (hp : 1 ≤ p) (n : ℕ) :
    UniformIntegrable (fun i omega => n • f i omega) p P := by
  induction n with
  | zero =>
      simp only [zero_nsmul]
      refine ⟨fun _ => aestronglyMeasurable_const, ?_, ⟨0, fun _ => by simp⟩⟩
      intro epsilon hepsilon
      exact ⟨1, one_pos, fun _ _ _ _ => by simp⟩
  | succ n hn =>
      simpa only [Nat.succ_eq_add_one, add_nsmul, one_nsmul] using
        UniformIntegrable.add_banach hn hf hp

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right continuation of its filtration when its values are
uniformly integrable along every convergent deterministic-time sequence. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_uniformIntegrable_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n => X (a n)) atTop (X r))
    (hUI : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        UniformIntegrable (fun n => X (a n)) 1 P) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t =>
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ => (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n =>
    min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ => t) atTop (nhds t) :=
      tendsto_const_nhds
    have hs : Tendsto
        (fun n : ℕ => s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by
      simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  have hL1 : Tendsto (fun n => eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      (hUI s u hu) (hstoch s u hu)
  have hIntegral : Tendsto
      (fun n => ∫ omega in A, X (u n) omega ∂P) atTop
      (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s)
      (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) =
        ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n => ∫ omega in A, X (u n) omega ∂P) =
      fun _ => ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- A stochastically continuous Banach-valued martingale remains a
martingale in the right-continuation of its filtration when it is bounded on
each deterministic time interval.  The local bound supplies uniform
integrability for the values just to the right of the conditioning time. -/
theorem Martingale.rightCont_of_tendstoInMeasure_of_locally_bounded_banach
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X : ℝ≥0 → W → E} (hX : Martingale X V P)
    (hstoch : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0),
      Tendsto a atTop (nhds r) →
        TendstoInMeasure P (fun n ↦ X (a n)) atTop (X r))
    (hbound : ∀ T : ℝ≥0, ∃ K : ℝ≥0, ∀ t ≤ T, ∀ omega,
      ‖X t omega‖ ≤ K) :
    Martingale X (Filtration.rightCont V) P := by
  have hadapt : StronglyAdapted (Filtration.rightCont V) X := fun t ↦
    (hX.stronglyAdapted t).mono (V.le_rightCont t)
  refine ⟨hadapt, fun s t hst ↦ ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    ((Filtration.rightCont V).le s) (hX.integrable t)
    (fun A _ _ ↦ (hX.integrable s).integrableOn) ?_
    (hadapt s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases heq : s = t
  · subst t
    rfl
  have hlt : s < t := lt_of_le_of_ne hst heq
  let u : ℕ → ℝ≥0 := fun n ↦ min t (s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
  have hsu (n : ℕ) : s < u n := by
    apply lt_min hlt
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have hut (n : ℕ) : u n ≤ t := min_le_left _ _
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto u atTop (nhds s) := by
    have ht : Tendsto (fun _ : ℕ ↦ t) atTop (nhds t) := tendsto_const_nhds
    have hs : Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹)
        atTop (nhds s) := by simpa using tendsto_const_nhds.add hinv
    simpa only [u, add_zero, min_eq_right hst] using Tendsto.min ht hs
  obtain ⟨K, hK⟩ := hbound t
  have hmeas (n : ℕ) : AEStronglyMeasurable (X (u n)) P :=
    (hX.integrable (u n)).aestronglyMeasurable
  have hconst : UniformIntegrable
      (fun _ : ℕ ↦ fun _ : W ↦ (K : ℝ)) 1 P :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr (integrable_const (K : ℝ)))
  have hUI : UniformIntegrable (fun n ↦ X (u n)) 1 P :=
    UniformIntegrable.mono_norm_banach hconst hmeas fun n omega ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] using
        hK (u n) (hut n) omega
  have hL1 : Tendsto (fun n ↦ eLpNorm (X (u n) - X s) 1 P)
      atTop (nhds 0) :=
    tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
      hUI (hstoch s u hu)
  have hIntegral : Tendsto (fun n ↦ ∫ omega in A, X (u n) omega ∂P)
      atTop (nhds (∫ omega in A, X s omega ∂P)) :=
    tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n ↦ hX.integrable (u n)) hL1 A
  have hIntegralEq (n : ℕ) :
      (∫ omega in A, X (u n) omega ∂P) = ∫ omega in A, X t omega ∂P := by
    apply hX.setIntegral_eq (hut n)
    apply (show Filtration.rightCont V s ≤ V (u n) by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le_of_le (u n) (hsu n) le_rfl)
    exact hA
  have hConstant : (fun n ↦ ∫ omega in A, X (u n) omega ∂P) =
      fun _ ↦ ∫ omega in A, X t omega ∂P := funext hIntegralEq
  rw [hConstant] at hIntegral
  exact (tendsto_nhds_unique tendsto_const_nhds hIntegral).symm

/-- Doob's fourth-moment maximal estimate for a pre-Brownian process sampled
on a finite uniform grid.  Applied to a shifted pre-Brownian process, this
uniformly controls all fine-grid oscillations inside one coarse interval. -/
theorem preBrownian_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (uniformPartitionTime t n k) omega) ^ 4)} ≤
      ENNReal.ofReal (3 * (t : ℝ) ^ 2) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒱 := monotoneReindexFiltration (Filtration.natural B hsm)
    (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hmart : Martingale (fun k => B (uniformPartitionTime t n k)) 𝒱 P := by
    exact martingale_comp_monotone (martingale_brownian_natural hB hsm)
      (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)
  have hfourth : ∀ k, Integrable
      (fun omega => (B (uniformPartitionTime t n k) omega) ^ 4) P := fun k =>
    integrable_pow_four_of_hasLaw_gaussianReal _
      (hB.hasLaw_eval (uniformPartitionTime t n k))
  have hmax := martingale_maximal_pow_four_ineq hmart hfourth epsilon n
  have htop : uniformPartitionTime t n n = t := by
    unfold uniformPartitionTime
    have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    exact mul_div_cancel_right₀ t hn0
  rw [htop,
    integral_pow_four_of_hasLaw_gaussianReal t (hB.hasLaw_eval t)] at hmax
  exact hmax

/-- Fourth-moment maximal control for all sampled increments inside a
deterministic interval.  The estimate is independent of the number of fine
grid points. -/
theorem preBrownian_interval_uniformPartition_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (a b : ℝ≥0) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k => (B (a + uniformPartitionTime (b - a) n k) omega -
            B a omega) ^ 4)} ≤
      ENNReal.ofReal (3 * ((b - a : ℝ≥0) : ℝ) ^ 2) := by
  let Bs : ℝ≥0 → W → ℝ := fun t omega => B (a + t) omega - B a omega
  have hBs : IsPreBrownianReal Bs P := by
    simpa only [Bs] using hB.shift a
  have hBsmeas : ∀ t, StronglyMeasurable (Bs t) := fun t =>
    (hsm (a + t)).sub (hsm a)
  simpa only [Bs] using preBrownian_uniformPartition_maximal_pow_four_ineq
    hBs hBsmeas (b - a) hn epsilon

/-- A union bound over a coarse uniform partition controls every sampled
Brownian oscillation inside every coarse block.  Its right-hand side is of
order `k * (T/k)²`, hence vanishes as the coarse mesh tends to zero. -/
theorem preBrownian_uniformBlocks_maximal_pow_four_ineq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    (T : ℝ≥0) (k : ℕ) {n : ℕ} (hn : 0 < n) (epsilon : ℝ≥0) :
    epsilon * P (⋃ j ∈ Finset.range k, {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T k j +
                uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
              B (uniformPartitionTime T k j) omega) ^ 4)}) ≤
      (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
  let E : ℕ → Set W := fun j => {omega |
    (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4)}
  have hblock (j : ℕ) : epsilon * P (E j) ≤
      ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
    have hraw := preBrownian_interval_uniformPartition_maximal_pow_four_ineq
      hB hsm (uniformPartitionTime T k j)
        (uniformPartitionTime T k j + T / (k : ℝ≥0)) hn epsilon
    simpa only [E, add_tsub_cancel_left] using hraw
  change epsilon * P (⋃ j ∈ Finset.range k, E j) ≤ _
  calc
    epsilon * P (⋃ j ∈ Finset.range k, E j) ≤
        epsilon * ∑ j ∈ Finset.range k, P (E j) := by
      gcongr
      exact measure_biUnion_finset_le (Finset.range k) E
    _ = ∑ j ∈ Finset.range k, epsilon * P (E j) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range k, ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun j _hj => hblock j
    _ = (k : ℝ≥0∞) * ENNReal.ofReal
        (3 * ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Outside the coarse-block maximal event, every sampled oscillation is
bounded by the chosen fourth-root threshold. -/
theorem blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
    {W : Type*} (B : ℝ≥0 → W → ℝ) (T : ℝ≥0) {k n : ℕ}
    (delta : ℝ≥0) (_hdelta : 0 < delta) {omega : W}
    (homega : omega ∉ ⋃ j ∈ Finset.range k, {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)}) :
    ∀ j ∈ Finset.range k, ∀ r ∈ Finset.range (n + 1),
      |B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta := by
  intro j hj r hr
  have hjnot : omega ∉ {omega |
      ((delta : ℝ) ^ 4) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun r =>
          (B (uniformPartitionTime T k j +
              uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
            B (uniformPartitionTime T k j) omega) ^ 4)} := by
    intro hmem
    apply homega
    simp only [Set.mem_iUnion]
    exact ⟨j, hj, hmem⟩
  simp only [Set.mem_ofPred_eq] at hjnot
  have hsup : (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
          B (uniformPartitionTime T k j) omega) ^ 4) <
      (delta : ℝ) ^ 4 := lt_of_not_ge hjnot
  have hterm := Finset.le_sup'
    (fun r =>
      (B (uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
        B (uniformPartitionTime T k j) omega) ^ 4) hr
  have hpow : |B (uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) n r) omega -
      B (uniformPartitionTime T k j) omega| ^ 4 < (delta : ℝ) ^ 4 := by
    rw [← abs_pow]
    rw [abs_of_nonneg (by positivity)]
    exact hterm.trans_lt hsup
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _)
    delta.coe_nonneg (by norm_num : (4 : ℕ) ≠ 0)).mp hpow |>.le

/-- A concrete diagonal scale: `(k+1)^5` coarse blocks and oscillation
threshold `1/(k+1)` make the exceptional probability vanish, uniformly in
the positive number of inner subdivisions. -/
theorem tendsto_measureReal_preBrownian_polynomialBlocks_maximal_pow_four
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t)) (T : ℝ≥0)
    (n : ℕ → ℕ) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k =>
      let K := (k + 1) ^ 5
      let delta : ℝ≥0 := ((k + 1 : ℕ) : ℝ≥0)⁻¹
      P.real (⋃ j ∈ Finset.range K, {omega |
        ((delta : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
          Finset.nonempty_range_add_one (fun r =>
            (B (uniformPartitionTime T K j +
                uniformPartitionTime (T / (K : ℝ≥0)) (n k) r) omega -
              B (uniformPartitionTime T K j) omega) ^ 4)}))
      atTop (nhds 0) := by
  let d : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0)⁻¹
  let K : ℕ → ℕ := fun k => (k + 1) ^ 5
  let b : ℕ → ℝ := fun k => 3 * (T : ℝ) ^ 2 / ((k : ℝ) + 1)
  have hb : Tendsto b atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (3 * (T : ℝ) ^ 2)
    have hc := h.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun k : ℕ =>
      3 * (T : ℝ) ^ 2 / ((k + 1 : ℕ) : ℝ)) atTop (nhds 0) at hc
    simpa only [b, Nat.cast_add, Nat.cast_one] using hc
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun k => ?_) hb
  let E : Set W := ⋃ j ∈ Finset.range (K k), {omega |
    ((d k : ℝ) ^ 4) ≤ (Finset.range (n k + 1)).sup'
      Finset.nonempty_range_add_one (fun r =>
        (B (uniformPartitionTime T (K k) j +
            uniformPartitionTime (T / (K k : ℝ≥0)) (n k) r) omega -
          B (uniformPartitionTime T (K k) j) omega) ^ 4)}
  have hK : 0 < K k := by
    dsimp only [K]
    positivity
  have hd : 0 < d k := by
    dsimp only [d]
    positivity
  have hraw := preBrownian_uniformBlocks_maximal_pow_four_ineq
    hB hsm T (K k) (hn k) ((d k) ^ 4)
  change ((d k : ℝ≥0∞) ^ 4) * P E ≤ _ at hraw
  have htop : ((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
  change (d k : ℝ) ^ 4 * P.real E ≤
    (((K k : ℕ) : ℝ≥0∞) * ENNReal.ofReal
      (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)).toReal at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  change P.real E ≤ b k
  have hdivide : P.real E ≤
      ((K k : ℝ) *
        (3 * ((T / (K k : ℝ≥0) : ℝ≥0) : ℝ) ^ 2)) /
        (d k : ℝ) ^ 4 := by
    apply (le_div_iff₀ (pow_pos (show (0 : ℝ) < d k by exact_mod_cast hd) 4)).2
    simpa only [mul_comm] using hreal
  calc
    P.real E ≤ _ := hdivide
    _ = b k := by
      dsimp only [K, d, b]
      simp only [NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_div]
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
      push_cast
      ring

/-- Ordinary fixed-time quadratic-variation convergence supplies the
geometric-mean tightness needed by the polynomial two-scale argument.  The
limit assumption is deliberately phrased for the sum: this is exactly the
coercive quantity controlling the geometric mean. -/
theorem HasQuadraticVariationProcessInProbability.polynomialBlocks_eventually_tight_sqrt_mul
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X B QX QB : ℝ≥0 → W → ℝ}
    (hX : HasQuadraticVariationProcessInProbability X QX P)
    (hB : HasQuadraticVariationProcessInProbability B QB P)
    (T : ℝ≥0)
    (hQint : Integrable (fun omega => QX T omega + QB T omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => QX T omega + QB T omega) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox X T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  intro n hn
  let s : ℕ → ℕ := fun k => ((k + 1) ^ 5) * n k
  let r : ℕ → ℕ := fun k => s k - 1
  have hs_pos : ∀ k, 0 < s k := fun k => by
    dsimp only [s]
    exact Nat.mul_pos (by positivity) (hn k)
  have hr : Tendsto r atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hba => ?_⟩
    have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
    have hmul : (a + 1) ^ 5 ≤ s a := by
      exact Nat.le_mul_of_pos_right _ (hn a)
    have halt : a < s a := by omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hr_add : ∀ k, r k + 1 = s k := fun k => by
    dsimp only [r]
    exact Nat.sub_add_cancel (hs_pos k)
  have hqX : TendstoInMeasure P
      (fun k => quadraticVariationApprox X T (s k)) atTop (QX T) := by
    convert (hX T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox X T) (hr_add k).symm
  have hqB : TendstoInMeasure P
      (fun k => quadraticVariationApprox B T (s k)) atTop (QB T) := by
    convert (hB T).comp hr using 1
    exact funext fun k => congrArg (quadraticVariationApprox B T) (hr_add k).symm
  have htight := hqX.eventually_tight_sqrt_mul hqB
    (fun k omega => quadraticVariationApprox_nonneg X T (s k) omega)
    (fun k omega => quadraticVariationApprox_nonneg B T (s k) omega)
    hQint hQnonneg
  simpa only [s] using htight

/-- Girsanov density data and a pre-Brownian driver automatically satisfy
the polynomial-grid tightness condition for the martingale--Brownian
quadratic sums.  In particular, Novikov supplies the only random first
moment needed here. -/
theorem GirsanovDensityData.polynomialBlocks_eventually_tight_sqrt_martingale_preBrownian
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) :
    ∀ n : ℕ → ℕ, (∀ k, 0 < n k) →
      ∀ eta : ℝ, 0 < eta →
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
          P.real {omega | C ≤
            √(quadraticVariationApprox M T (((k + 1) ^ 5) * n k) omega *
              quadraticVariationApprox B T (((k + 1) ^ 5) * n k) omega)} <
            eta := by
  apply h.localQuadraticVariation.toProcess
    |>.polynomialBlocks_eventually_tight_sqrt_mul
      (fun t => quadraticVariation_preBrownianReal_inProbability hB t) T
  · exact h.integrable_terminalBracket.add (integrable_const (T : ℝ))
  · exact Filter.Eventually.of_forall fun omega => by
      have hbracket : 0 ≤ bracket T omega := by
        rw [← h.bracket_zero omega]
        exact (h.continuous_monotone_bracket omega).2 bot_le
      exact add_nonneg hbracket T.coe_nonneg

/-- The normalized complex character of a Brownian increment. -/
def brownianFourierIncrement
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
def brownianFourierIncrementProcess
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
def complexMartingaleCombination
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ) : ℝ≥0 → W → ℂ :=
  fun t omega ↦ (M t omega : ℂ) + ((c * B t omega : ℝ) : ℂ) * Complex.I

/-- The complex bracket of `M + i c B`: the real Brownian quadratic term
changes sign and the real cross variation becomes the imaginary term. -/
def complexMartingaleCombinationBracket
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
noncomputable def complexDoleansDadeExponential
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
noncomputable def complexFreezingDensityLeftMax
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

/-- Cap only the real Novikov-density factor of the complex Girsanov
exponential.  Its oscillatory factor is left unchanged, so the cap is
bounded without requiring path regularity of the pre-Brownian driver. -/
def cappedComplexDoleansDadeExponentialCombination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R : ℝ≥0) (t : ℝ≥0) (omega : W) : ℂ :=
  (cappedDoleansDadeExponential M bracket R t omega : ℂ) *
    Complex.exp
      (((c * (B t omega - C t omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (t : ℝ) / 2 : ℝ) : ℂ))

/-- The capped complex Girsanov exponential has an exact deterministic
modulus bound on every finite time interval. -/
theorem norm_cappedComplexDoleansDadeExponentialCombination_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T t : ℝ≥0) (ht : t ≤ T) (omega : W) :
    ‖cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R t omega‖ ≤
        (R : ℝ) * Real.exp (c ^ 2 * (T : ℝ) / 2) := by
  unfold cappedComplexDoleansDadeExponentialCombination
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · rw [Complex.norm_exp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
      mul_one, neg_zero, zero_add]
    have hexp : Real.exp (c ^ 2 * (t : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      have ht' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg c]
    exact mul_le_mul (min_le_right _ _) hexp
      (Real.exp_pos _).le R.coe_nonneg
  · exact le_min (doleansDadeExponential_pos M bracket t omega).le
      R.coe_nonneg

/-- Adapted inputs make the density-capped complex exponential adapted. -/
theorem stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R : ℝ≥0) :
    StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) := by
  intro t
  apply (Complex.continuous_ofReal.comp_stronglyMeasurable
    (stronglyAdapted_cappedDoleansDadeExponential
      hM hbracket R t)).mul
  apply Complex.continuous_exp.comp_stronglyMeasurable
  exact (((Complex.continuous_ofReal.comp_stronglyMeasurable
    ((hB t).sub (hC t) |>.const_mul c)).mul_const Complex.I).add
      stronglyMeasurable_const)

/-- Deterministic norm bound for the density-capped complex coefficient on
the Girsanov horizon. -/
def cappedComplexGirsanovCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  R * Real.toNNReal (Real.exp (c ^ 2 * (T : ℝ) / 2))

/-- Deterministic norm bound for the Brownian coefficient `i c H` in the
two-integrator complex Euler process. -/
def cappedComplexGirsanovBrownianCoefficientBound
    (c : ℝ) (R T : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal
    (|c| * (cappedComplexGirsanovCoefficientBound c R T : ℝ))

/-- The Euler martingale candidate for the complex Girsanov exponential.
The density factor in the coefficient is capped, while `N` is the chosen
martingale approximation to the local-martingale integrator `M`. -/
def cappedComplexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The uncapped complex Euler process on a uniform grid.  It is the exact
first-order sum whose stochastic Taylor error remains after the increasing
density caps have become inactive. -/
def complexGirsanovEulerProcess
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  (fun _ => H 0) +
    uniformAdaptedTwoMartingaleSmulProcess N B H K U n

/-- The canonical complex uniform-grid Doléans left sum, written directly
for a complex integrator and its algebraic complex bracket. -/
noncomputable def complexDoleansEulerProcess
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) : ℝ≥0 → W → ℂ :=
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    complexDoleansDadeExponential X Q (min t U) omega
  fun t omega => H 0 omega +
    ∑ i ∈ Finset.range n,
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          H (uniformPartitionTime U n i) omega

/-- The exact one-step residual sum for the canonical complex Doléans Euler
process.  Its first two terms telescope; the third is the Euler increment. -/
noncomputable def complexDoleansEulerResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  let E := complexDoleansDadeExponential X Q
  ∑ i ∈ Finset.range n,
    ((E (min t (uniformPartitionTime U n (i + 1))) omega -
        E (min t (uniformPartitionTime U n i)) omega) -
      (X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega) *
          E (min (uniformPartitionTime U n i) U) omega)

/-- Exact multiplicative form of one complex Doléans Euler residual.  This
isolates the analytic remainder `exp z - 1 - dX` before any probabilistic
estimate is applied. -/
theorem complexDoleansDadeExponential_increment_sub_linear
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (Complex.exp
          ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) -
            1 - (X b omega - X a omega)) := by
  unfold complexDoleansDadeExponential
  have hexp :
      Complex.exp (X b omega - Q b omega / 2) =
        Complex.exp (X a omega - Q a omega / 2) *
          Complex.exp
            ((X b omega - X a omega) - (Q b omega - Q a omega) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- The higher-order remainder left after extracting the quadratic-variation
term from one complex Doléans Euler cell. -/
noncomputable def complexDoleansSecondOrderResidual
    (dX dQ : ℂ) : ℂ :=
  Complex.exp (dX - dQ / 2) - 1 - dX - (dX ^ 2 - dQ) / 2

/-- Quantitative higher-order bound for the extracted complex Doléans
remainder.  The first term is cubic in the compensated-log increment; the
second records the finite-variation correction caused by replacing that
increment's square with `dX²`. -/
theorem norm_complexDoleansSecondOrderResidual_le (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        ‖((dX - dQ / 2) ^ 2 - dX ^ 2) / 2‖ := by
  let z : ℂ := dX - dQ / 2
  have hexp :
      ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤
        ‖z‖ ^ 3 * Real.exp ‖z‖ := by
    convert Complex.norm_exp_sub_sum_le_norm_mul_exp z 3 using 1
    congr 1
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  calc
    ‖complexDoleansSecondOrderResidual dX dQ‖ =
        ‖(Complex.exp z - 1 - z - z ^ 2 / 2) +
          (z ^ 2 - dX ^ 2) / 2‖ := by
      congr 1
      unfold complexDoleansSecondOrderResidual z
      ring
    _ ≤ ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ 3 * Real.exp ‖z‖ +
          ‖(z ^ 2 - dX ^ 2) / 2‖ := add_le_add hexp le_rfl
    _ = _ := by rfl

/-- A cancellation-ready version of the one-cell remainder bound.  The
correction to the cubic term contains an explicit bracket increment, rather
than an opaque difference of squares. -/
theorem norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket
    (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
        (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2 := by
  let z : ℂ := dX - dQ / 2
  have hfactor : z ^ 2 - dX ^ 2 = (-dQ / 2) * (z + dX) := by
    dsimp only [z]
    ring
  apply (norm_complexDoleansSecondOrderResidual_le dX dQ).trans
  gcongr
  rw [hfactor]
  simp only [norm_div, norm_mul, norm_neg]
  have hnormtwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnormtwo]
  calc
    ‖dQ‖ / 2 * ‖z + dX‖ / 2 ≤
        ‖dQ‖ / 2 * (‖z‖ + ‖dX‖) / 2 := by
      gcongr
      exact norm_add_le z dX
    _ = _ := by rfl

/-- The nonnegative scalar majorant for one higher-order Doléans cell. -/
noncomputable def complexDoleansSecondOrderResidualBound
    (dX dQ : ℂ) : ℝ :=
  ‖dX - dQ / 2‖ ^ 3 * Real.exp ‖dX - dQ / 2‖ +
    (‖dQ‖ / 2) * (‖dX - dQ / 2‖ + ‖dX‖) / 2

theorem complexDoleansSecondOrderResidualBound_nonneg (dX dQ : ℂ) :
    0 ≤ complexDoleansSecondOrderResidualBound dX dQ := by
  unfold complexDoleansSecondOrderResidualBound
  positivity

/-- The one-cell higher-order remainder is controlled by its explicit
nonnegative scalar majorant. -/
theorem norm_complexDoleansSecondOrderResidual_le_bound (dX dQ : ℂ) :
    ‖complexDoleansSecondOrderResidual dX dQ‖ ≤
      complexDoleansSecondOrderResidualBound dX dQ := by
  exact norm_complexDoleansSecondOrderResidual_le_cubic_add_bracket dX dQ

/-- One Doléans Euler cell splits exactly into a weighted bracket discrepancy
and the higher-order exponential remainder. -/
theorem complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ) (a b : ℝ≥0) (omega : W) :
    (complexDoleansDadeExponential X Q b omega -
        complexDoleansDadeExponential X Q a omega) -
      (X b omega - X a omega) *
        complexDoleansDadeExponential X Q a omega =
      complexDoleansDadeExponential X Q a omega *
        (((X b omega - X a omega) ^ 2 -
              (Q b omega - Q a omega)) / 2 +
          complexDoleansSecondOrderResidual
            (X b omega - X a omega) (Q b omega - Q a omega)) := by
  rw [complexDoleansDadeExponential_increment_sub_linear]
  unfold complexDoleansSecondOrderResidual
  ring

/-- The stopped-grid weighted discrepancy between algebraic squared
increments and increments of the proposed complex bracket. -/
noncomputable def complexDoleansWeightedBracketResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      ((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) ^ 2 -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega))

/-- A complex-weighted real quadratic-variation discrepancy on a stopped
uniform grid.  The complex weight is kept explicit because the Fourier
Doléans exponential is not real-valued. -/
noncomputable def complexWeightedQuadraticResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      (((X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ) ^ 2 -
        ((A (min t (uniformPartitionTime U n (i + 1))) omega -
          A (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- A complex-weighted real cross-variation discrepancy on a stopped uniform
grid. -/
noncomputable def complexWeightedCrossResidualApprox
    {W : Type*} (H : ℝ≥0 → W → ℂ)
    (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    H (min t (uniformPartitionTime U n i)) omega *
      ((((X (min t (uniformPartitionTime U n (i + 1))) omega -
            X (min t (uniformPartitionTime U n i)) omega) *
          (Y (min t (uniformPartitionTime U n (i + 1))) omega -
            Y (min t (uniformPartitionTime U n i)) omega) : ℝ) : ℂ) -
        ((C (min t (uniformPartitionTime U n (i + 1))) omega -
          C (min t (uniformPartitionTime U n i)) omega : ℝ) : ℂ))

/-- A sum over a uniformly subdivided grid can be indexed by its coarse
block and its position inside that block. -/
theorem sum_range_mul_eq_sum_range_sum_range
    {E : Type*} [AddCommMonoid E] (k n : ℕ) (f : ℕ → E) :
    (∑ i ∈ Finset.range (k * n), f i) =
      ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
  calc
    _ = ∑ i : Fin (k * n), f i :=
      (Fin.sum_univ_eq_sum_range f (k * n)).symm
    _ = ∑ p : Fin k × Fin n, f (finProdFinEquiv p) :=
      (Equiv.sum_comp finProdFinEquiv
        (fun i : Fin (k * n) ↦ f i)).symm
    _ = ∑ j : Fin k, ∑ r : Fin n, f (r + n * j) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ j ∈ Finset.range k, ∑ r : Fin n,
        f (r + n * j) := by
      exact Fin.sum_univ_eq_sum_range
        (fun j ↦ ∑ r : Fin n, f (r + n * j)) k
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        f (r + n * j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Fin.sum_univ_eq_sum_range (fun r ↦ f (r + n * j)) n

/-- Frozen complex coarse weights against exact finite-variation increments
are the active right-endpoint step weights against all fine increments. -/
theorem finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (c : ℕ → W → ℂ) (omega : W) :
    (∑ j ∈ Finset.range k, c j omega *
      (A (uniformPartitionTime U k (j + 1)) omega -
        A (uniformPartitionTime U k j) omega : ℂ)) =
      ∑ i ∈ Finset.range (k * n), c (i / n) omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ) := by
  have hblock (j : ℕ) :
      (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ) =
        ∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
    have hleft : uniformPartitionTime U (k * n) (n * j) =
        uniformPartitionTime U k j := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn j 0).symm
    have hright : uniformPartitionTime U (k * n) (n * (j + 1)) =
        uniformPartitionTime U k (j + 1) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          (uniformPartitionTime_block_common_refinement U hk hn (j + 1) 0).symm
    have htel := Finset.sum_range_sub (fun r ↦
      (A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) n
    have hindex : n + n * j = n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simp only [zero_add] at htel
    rw [hindex, hright, hleft] at htel
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htel.symm
  calc
    _ = ∑ j ∈ Finset.range k, c j omega *
        (∑ r ∈ Finset.range n,
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hblock]
    _ = ∑ j ∈ Finset.range k, ∑ r ∈ Finset.range n,
        c j omega *
          (A (uniformPartitionTime U (k * n) (r + n * j + 1)) omega -
            A (uniformPartitionTime U (k * n) (r + n * j)) omega : ℂ) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [sum_range_mul_eq_sum_range_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt : r < n := Finset.mem_range.mp hr
      rw [Nat.add_mul_div_left r j hn, Nat.div_eq_of_lt hrlt,
        zero_add]

/-- Freezing complex weights on completed coarse blocks costs at most the
weight error times the total variation of the real integrator. -/
theorem norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    {W : Type*} (A : ℝ≥0 → W → ℝ) (U : ℝ≥0)
    {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (weight c : ℕ → W → ℂ)
    (K : ℝ) (_hK : 0 ≤ K) (omega : W)
    (hweight : ∀ i ∈ Finset.range (k * n),
      ‖weight i omega - c (i / n) omega‖ ≤ K) :
    ‖(∑ i ∈ Finset.range (k * n), weight i omega *
        (A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k, c j omega *
        (A (uniformPartitionTime U k (j + 1)) omega -
          A (uniformPartitionTime U k j) omega : ℂ)‖ ≤
      K * totalVariationApprox A U (k * n) omega := by
  rw [finiteVariationBeforeStop_uniform_blocks_eq_complexWeighted_cells
    A U hk hn c omega, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i ∈ Finset.range (k * n),
        (weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i ∈ Finset.range (k * n),
        ‖(weight i omega - c (i / n) omega) *
          (A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k * n), K *
        |A (uniformPartitionTime U (k * n) (i + 1)) omega -
          A (uniformPartitionTime U (k * n) i) omega| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      rw [show
        ((A (uniformPartitionTime U (k * n) (i + 1)) omega : ℂ) -
            (A (uniformPartitionTime U (k * n) i) omega : ℂ)) =
          ((A (uniformPartitionTime U (k * n) (i + 1)) omega -
            A (uniformPartitionTime U (k * n) i) omega : ℝ) : ℂ) by
            push_cast
            rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _)
    _ = K * totalVariationApprox A U (k * n) omega := by
      unfold totalVariationApprox
      rw [Finset.mul_sum]

/-- Outside the Brownian block-oscillation event, freezing the complex
Girsanov weight in a finite-variation sum costs its total variation times
the same coefficient-and-Fourier modulus used for covariations. -/
theorem
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
    {W : Type*} [MeasurableSpace W]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
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
          (A (uniformPartitionTime T (k * n) (i + 1)) omega -
            A (uniformPartitionTime T (k * n) i) omega : ℂ)) -
      ∑ j ∈ Finset.range k,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k j) omega *
          (A (uniformPartitionTime T k (j + 1)) omega -
            A (uniformPartitionTime T k j) omega : ℂ)‖ ≤
      (alpha + R * |c| * (delta : ℝ)) *
        totalVariationApprox A T (k * n) omega := by
  have hosc :=
    blockOscillation_le_of_not_mem_uniformBlocks_maximal_pow_four
      B T delta hdelta homega
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by
      exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hweight : ∀ i ∈ Finset.range (k * n),
      ‖complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (k * n) i) omega -
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T k (i / n)) omega‖ ≤
        alpha + R * |c| * (delta : ℝ) := by
    intro i hi
    let j := i / n
    have hilt : i < k * n := Finset.mem_range.mp hi
    have hjlt : j < k := by
      exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hilt)
    have hj : j ∈ Finset.range k := Finset.mem_range.mpr hjlt
    have hleft : uniformPartitionTime T k j =
        uniformPartitionTime T (k * n) (n * j) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn j 0
    have hright : uniformPartitionTime T k (j + 1) =
        uniformPartitionTime T (k * n) (n * (j + 1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        add_zero, Nat.mul_comm] using
          uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    have hjmul : n * j ≤ i := by
      simpa only [j, Nat.mul_comm] using Nat.div_mul_le_self i n
    have hmod : i % n < n := Nat.mod_lt i hn
    have hdecomp : n * j + i % n = i := by
      exact Nat.div_add_mod i n
    have hiRight : i + 1 ≤ n * (j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hactive : uniformPartitionTime T k j <
          uniformPartitionTime T (k * n) (i + 1) ∧
        uniformPartitionTime T (k * n) (i + 1) ≤
          uniformPartitionTime T k (j + 1) := by
      rw [hleft, hright]
      exact ⟨hstrict (by omega), hstrict.monotone hiRight⟩
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
    simpa only [j, mul_one,
      Real.coe_toNNReal |c| (abs_nonneg c)] using hraw
  exact norm_complexWeightedFiniteVariation_sub_completedBlocks_le
    A T hk hn
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

/-- The pathwise complex finite-variation freezing estimate promotes to
convergence in measure when the variation controls are tight and the
Brownian block-oscillation event becomes rare. -/
theorem
    tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (M bracket B C A : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
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
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          totalVariationApprox A T (K r * N r) omega} < eta)
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
          (A (uniformPartitionTime T (K r * N r) (i + 1)) omega -
            A (uniformPartitionTime T (K r * N r) i) omega : ℂ)) -
      ∑ j ∈ Finset.range (K r),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K r) j) omega *
          (A (uniformPartitionTime T (K r) (j + 1)) omega -
            A (uniformPartitionTime T (K r) j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let q : ℕ → W → ℝ := fun r omega ↦
    totalVariationApprox A T (K r * N r) omega
  let small : ℕ → W → ℝ := fun r _ ↦ |c| * (delta r : ℝ)
  let rq : ℕ → W → ℝ := fun r omega ↦ R r omega * q r omega
  let b₁ : ℕ → W → ℝ := fun r omega ↦ alpha r omega * q r omega
  let b₂ : ℕ → W → ℝ := fun r omega ↦ small r omega * rq r omega
  let b : ℕ → W → ℝ := fun r omega ↦ b₁ r omega + b₂ r omega
  have hq_nonneg : ∀ r omega, 0 ≤ q r omega := fun r omega ↦ by
    dsimp only [q, totalVariationApprox]
    exact Finset.sum_nonneg fun _ _hi ↦ abs_nonneg _
  have hq_tight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ q r omega} < eta := by
    simpa only [q] using htvtight
  have hb₁ : TendstoInMeasure P b₁ atTop (fun _ ↦ 0) := by
    apply halphaZero.of_norm_sub_le_mul_of_eventually_tight
      hq_nonneg hq_tight
    intro r omega
    simp only [b₁, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (halpha r omega), q]
    rw [abs_of_nonneg (mul_nonneg (halpha r omega) (hq_nonneg r omega))]
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
    norm_complexDoleansWeightedFiniteVariation_commonRefinement_sub_blocks_le
      M bracket B C A c T hT (hK r) (hN r)
      (alpha r omega) (R r omega) (halpha r omega) (hR r omega)
      (delta r) (hdeltaPos r) (hAclose r omega) (hAbound r omega) homega
  calc
    _ ≤ (alpha r omega + R r omega * |c| * (delta r : ℝ)) *
        q r omega := by simpa only [q] using hraw
    _ = b r omega := by
      dsimp only [b, b₁, b₂, small, rq]
      ring

/-- Girsanov density data supplies all coefficient and Brownian controls for
finite-variation freezing on the polynomial common-refinement scale. -/
theorem
    GirsanovDensityData.tendstoInMeasure_complexDoleansWeightedFiniteVariation_polynomial
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C A : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hCmeas : ∀ t, StronglyMeasurable (C t))
    (hCcont : ∀ omega, Continuous (fun t ↦ C t omega))
    (c : ℝ) (hT : 0 < T) (n : ℕ → ℕ)
    (htvtight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤ totalVariationApprox A T
          (((r + 1) ^ 5) * (n ((r + 1) ^ 5 - 1) + 1)) omega} < eta) :
    TendstoInMeasure P (fun r omega ↦
      let K := (r + 1) ^ 5
      let N := n (K - 1) + 1
      (∑ i ∈ Finset.range (K * N),
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T (K * N) i) omega *
          (A (uniformPartitionTime T (K * N) (i + 1)) omega -
            A (uniformPartitionTime T (K * N) i) omega : ℂ)) -
      ∑ j ∈ Finset.range K,
        complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c)
            (uniformPartitionTime T K j) omega *
          (A (uniformPartitionTime T K (j + 1)) omega -
            A (uniformPartitionTime T K j) omega : ℂ))
      atTop (fun _ ↦ 0) := by
  let K : ℕ → ℕ := fun r ↦ (r + 1) ^ 5
  let s : ℕ → ℕ := fun r ↦ K r - 1
  let N : ℕ → ℕ := fun r ↦ n (s r) + 1
  let H : ℝ≥0 → W → ℂ :=
    girsanovComplexDoleansContinuousCoefficient M bracket C c
  let alpha : ℕ → W → ℝ := fun r ↦
    commonRefinementMaxComplexStepError H T (s r) (n (s r))
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
    have halt : a < K a := by
      dsimp only [K]
      have hbase : a + 1 ≤ (a + 1) ^ 5 := Nat.le_pow (by norm_num)
      omega
    exact hba.trans (Nat.le_sub_one_of_lt halt)
  have hHmeas : ∀ t, StronglyMeasurable (H t) := by
    intro t
    apply stronglyMeasurable_girsanovComplexDoleansContinuousCoefficient
    · intro u
      exact (hdata.adapted_martingale u).mono (V.le u)
    · intro u
      exact (hdata.adapted_bracket u).mono (V.le u)
    · exact hCmeas
  have hHcont : ∀ omega, Continuous (fun t ↦ H t omega) := by
    exact continuous_girsanovComplexDoleansContinuousCoefficient
      hdata.continuous_martingale_path
      (fun omega ↦ (hdata.continuous_monotone_bracket omega).1)
      hCcont c
  have halphaZero : TendstoInMeasure P alpha atTop (fun _ ↦ 0) := by
    have hbase := commonRefinementMaxComplexStepError_tendstoInMeasure_zero
      (P := P) (A := H) hHmeas T hT hHcont n
    change TendstoInMeasure P
      ((fun k ↦ commonRefinementMaxComplexStepError H T k (n k)) ∘ s)
      atTop (fun _ ↦ 0)
    exact hbase.comp hsTop
  have halpha : ∀ r omega, 0 ≤ alpha r omega := fun r omega ↦
    commonRefinementMaxComplexStepError_nonneg H T (s r) (n (s r)) omega
  have hRnonneg : ∀ r omega, 0 ≤ R r omega := fun r omega ↦ by
    exact mul_nonneg (Real.exp_pos _).le
      (complexFreezingDensityLeftMax_nonneg M bracket T (s r) omega)
  have hdensityTight : ∀ eta : ℝ, 0 < eta →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in atTop,
        P.real {omega | D ≤
          complexFreezingDensityLeftMax M bracket T (s r) omega} < eta := by
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
  have hHclose : ∀ r omega, ∀ i ∈ Finset.range (K r * N r),
      ∀ j ∈ Finset.range (K r),
        uniformPartitionTime T (K r) j <
              uniformPartitionTime T (K r * N r) (i + 1) ∧
            uniformPartitionTime T (K r * N r) (i + 1) ≤
              uniformPartitionTime T (K r) (j + 1) →
        ‖H (uniformPartitionTime T (K r * N r) i) omega -
          H (uniformPartitionTime T (K r) j) omega‖ ≤ alpha r omega := by
    intro r omega i hi j hj hactive
    have hcounts : (s r + 1) * (n (s r) + 1) = K r * N r := by
      rw [hsadd]
    have hi' : i ∈ Finset.range ((s r + 1) * (n (s r) + 1)) := by
      simpa only [hcounts] using hi
    have hle :
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) i) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (i + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖ ≤
          commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega := by
      unfold commonRefinementMaxComplexStepError
      exact (le_refl _).trans (Finset.le_sup' (fun u ↦
        ‖H (uniformPartitionTime T ((s r + 1) * (n (s r) + 1)) u) omega -
          ∑ l ∈ Finset.range (s r + 1),
            if uniformPartitionTime T (s r + 1) l <
                  uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ∧
                uniformPartitionTime T
                    ((s r + 1) * (n (s r) + 1)) (u + 1) ≤
                  uniformPartitionTime T (s r + 1) (l + 1) then
              H (uniformPartitionTime T (s r + 1) l) omega else 0‖) hi')
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
      (fun l ↦ H (uniformPartitionTime T (s r + 1) l) omega)
      hj' hactive'
    rw [hsum] at hle
    change ‖H (uniformPartitionTime T (K r * N r) i) omega -
        H (uniformPartitionTime T (K r) j) omega‖ ≤
      commonRefinementMaxComplexStepError H T (s r) (n (s r)) omega
    simpa only [hcounts, hsadd] using hle
  have hHbound : ∀ r omega, ∀ j ∈ Finset.range (K r),
      ‖H (uniformPartitionTime T (K r) j) omega‖ ≤ R r omega := by
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
  apply tendstoInMeasure_complexDoleansWeightedFiniteVariation_sub_blocks
    M bracket B C A c T K N hT hKpos hNpos alpha R halpha hRnonneg
      halphaZero hRtight delta hdelta hdeltaPos
  · simpa only [K, N, s] using htvtight
  · exact hbad
  · exact hHclose
  · exact hHbound

/-- At the grid horizon a complex-weighted stopped cross residual is the
difference between the ordinary complex-weighted cross and finite-variation
sums. -/
theorem complexWeightedCrossResidualApprox_terminal
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X Y C : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexWeightedCrossResidualApprox H X Y C U n U omega =
      (∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          ((X (uniformPartitionTime U n (i + 1)) omega -
            X (uniformPartitionTime U n i) omega) *
          (Y (uniformPartitionTime U n (i + 1)) omega -
            Y (uniformPartitionTime U n i) omega) : ℂ)) -
      ∑ i ∈ Finset.range n,
        H (uniformPartitionTime U n i) omega *
          (C (uniformPartitionTime U n (i + 1)) omega -
            C (uniformPartitionTime U n i) omega : ℂ) := by
  unfold complexWeightedCrossResidualApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi0).2,
    min_eq_right (uniformPartitionTime_mem_Icc_of_le U
      (Nat.pos_of_ne_zero (by omega)) hi1).2]
  push_cast
  ring

/-- A complex-weighted quadratic residual is the self-cross residual. -/
theorem complexWeightedQuadraticResidualApprox_eq_cross_self
    {W : Type*} (H : ℝ≥0 → W → ℂ) (X A : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexWeightedQuadraticResidualApprox H X A U n t omega =
      complexWeightedCrossResidualApprox H X X A U n t omega := by
  unfold complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  apply Finset.sum_congr rfl
  intro i _hi
  push_cast
  rw [pow_two]

/-- The complex second-order discrepancy for `M + i c B` is exactly the
sum of the two real quadratic-variation discrepancies and the real cross
variation discrepancy.  This isolates the three cancellations required by
the Fourier proof without imposing real-valuedness on the left weight. -/
theorem complexDoleansWeightedBracketResidualApprox_combination
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansWeightedBracketResidualApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        U n t omega =
      complexWeightedQuadraticResidualApprox
          (complexDoleansDadeExponential
            (complexMartingaleCombination M B c)
            (complexMartingaleCombinationBracket bracket C c))
          M bracket U n t omega -
        (c ^ 2 : ℂ) *
          complexWeightedQuadraticResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            B (fun s _ ↦ (s : ℝ)) U n t omega +
        (((2 * c : ℝ) : ℂ) * Complex.I) *
          complexWeightedCrossResidualApprox
            (complexDoleansDadeExponential
              (complexMartingaleCombination M B c)
              (complexMartingaleCombinationBracket bracket C c))
            M B C U n t omega := by
  unfold complexDoleansWeightedBracketResidualApprox
    complexWeightedQuadraticResidualApprox
    complexWeightedCrossResidualApprox
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let s := min t (uniformPartitionTime U n i)
  let u := min t (uniformPartitionTime U n (i + 1))
  let h := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c) s omega
  let dM := M u omega - M s omega
  let dA := bracket u omega - bracket s omega
  let dB := B u omega - B s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have hX :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  have hQ :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  change h *
      ((complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega) ^ 2 -
        (complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega)) = _
  rw [hX, hQ]
  change h *
      (((dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I) ^ 2 -
        ((dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I)) =
    h * ((dM : ℂ) ^ 2 - (dA : ℂ)) -
      (c ^ 2 : ℂ) * (h * ((dB : ℂ) ^ 2 - (dt : ℂ))) +
      (((2 * c : ℝ) : ℂ) * Complex.I) *
        (h * (((dM * dB : ℝ) : ℂ) - (dC : ℂ)))
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The sum of higher-order exponential remainders on a stopped uniform
grid. -/
noncomputable def complexDoleansHigherOrderResidualApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℂ :=
  ∑ i ∈ Finset.range n,
    complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega *
      complexDoleansSecondOrderResidual
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

/-- Explicit scalar majorant for the whole stopped-grid higher-order
remainder.  This is the sum of the left exponential modulus times the
one-cell cubic/bracket bound. -/
noncomputable def complexDoleansHigherOrderResidualBoundApprox
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ *
      complexDoleansSecondOrderResidualBound
        (X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega)
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega)

theorem complexDoleansHigherOrderResidualBoundApprox_nonneg
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualBoundApprox
  exact Finset.sum_nonneg fun i _hi => mul_nonneg (norm_nonneg _)
    (complexDoleansSecondOrderResidualBound_nonneg _ _)

/-- The full higher-order majorant is controlled by scalar aggregate bounds.
This separates the analytic input into uniform cell increments and tight
quadratic/finite-variation sums, which can be estimated independently. -/
theorem complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W)
    (K deltaZ deltaX sumZSq sumQ : ℝ)
    (hK : 0 ≤ K) (hdeltaZ : 0 ≤ deltaZ) (hdeltaX : 0 ≤ deltaX)
    (hweight : ∀ i ∈ Finset.range n,
      ‖complexDoleansDadeExponential X Q
        (min t (uniformPartitionTime U n i)) omega‖ ≤ K)
    (hz : ∀ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ≤ deltaZ)
    (hx : ∀ i ∈ Finset.range n,
      ‖X (min t (uniformPartitionTime U n (i + 1))) omega -
        X (min t (uniformPartitionTime U n i)) omega‖ ≤ deltaX)
    (hzsq : (∑ i ∈ Finset.range n,
      ‖(X (min t (uniformPartitionTime U n (i + 1))) omega -
          X (min t (uniformPartitionTime U n i)) omega) -
        (Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega) / 2‖ ^ 2) ≤ sumZSq)
    (hqsum : (∑ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖) ≤ sumQ) :
    complexDoleansHigherOrderResidualBoundApprox X Q U n t omega ≤
      K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
  let dX : ℕ → ℂ := fun i =>
    X (min t (uniformPartitionTime U n (i + 1))) omega -
      X (min t (uniformPartitionTime U n i)) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (min t (uniformPartitionTime U n (i + 1))) omega -
      Q (min t (uniformPartitionTime U n i)) omega
  let z : ℕ → ℂ := fun i => dX i - dQ i / 2
  let E : ℕ → ℂ := fun i =>
    complexDoleansDadeExponential X Q
      (min t (uniformPartitionTime U n i)) omega
  change (∑ i ∈ Finset.range n, ‖E i‖ *
      (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
        (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤ _
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖E i‖ *
          (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
            (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2) ≤
        K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) := by
    have hzi : ‖z i‖ ≤ deltaZ := by simpa only [z, dX, dQ] using hz i hi
    have hxi : ‖dX i‖ ≤ deltaX := by simpa only [dX] using hx i hi
    apply mul_le_mul (hweight i hi)
    · apply add_le_add
      · calc
          ‖z i‖ ^ 3 * Real.exp ‖z i‖ =
              ‖z i‖ * ‖z i‖ ^ 2 * Real.exp ‖z i‖ := by ring
          _ ≤ deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ := by
            gcongr
      · gcongr
    · positivity
    · exact hK
  calc
    (∑ i ∈ Finset.range n, ‖E i‖ *
        (‖z i‖ ^ 3 * Real.exp ‖z i‖ +
          (‖dQ i‖ / 2) * (‖z i‖ + ‖dX i‖) / 2)) ≤
        ∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) :=
      Finset.sum_le_sum hcell
    _ = K * (deltaZ * Real.exp deltaZ *
          (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) +
        ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
          (deltaZ + deltaX) / 2) := by
      have hfirst :
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) =
            K * deltaZ * Real.exp deltaZ *
              (∑ i ∈ Finset.range n, ‖z i‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      have hsecond :
          (∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
            K * ((∑ i ∈ Finset.range n, ‖dQ i‖) / 2) *
              (deltaZ + deltaX) / 2 := by
        calc
          _ = ∑ i ∈ Finset.range n,
              (K * (deltaZ + deltaX) / 4) * ‖dQ i‖ := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = (K * (deltaZ + deltaX) / 4) *
              (∑ i ∈ Finset.range n, ‖dQ i‖) := by
            rw [Finset.mul_sum]
          _ = _ := by ring
      rw [show (∑ i ∈ Finset.range n, K *
          (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ +
            (‖dQ i‖ / 2) * (deltaZ + deltaX) / 2)) =
          (∑ i ∈ Finset.range n,
            K * (deltaZ * ‖z i‖ ^ 2 * Real.exp deltaZ)) +
          ∑ i ∈ Finset.range n,
            K * ((‖dQ i‖ / 2) * (deltaZ + deltaX) / 2) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      rw [hfirst, hsecond]
      ring
    _ ≤ K * (deltaZ * Real.exp deltaZ * sumZSq +
        (sumQ / 2) * (deltaZ + deltaX) / 2) := by
      gcongr

/-- The fourth-root Brownian mesh control extracted from the fourth
variation.  Two square roots are used to keep the quantity in the real
ordered-field API. -/
noncomputable def fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega))

/-- Every Brownian grid increment is bounded by the fourth-root control of
the whole grid. -/
theorem abs_uniformPartition_increment_le_fourthVariationRootApprox
    {W : Type*} (B : ℝ≥0 → W → ℝ) (U : ℝ≥0) {n : ℕ}
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range n) :
    |B (uniformPartitionTime U n (i + 1)) omega -
        B (uniformPartitionTime U n i) omega| ≤
      fourthVariationRootApprox B U n omega := by
  let d := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have hterm : d ^ 4 ≤ fourthVariationApprox B U n omega := by
    unfold fourthVariationApprox
    simpa only [d] using Finset.single_le_sum
      (s := Finset.range n)
      (f := fun j => (B (uniformPartitionTime U n (j + 1)) omega -
        B (uniformPartitionTime U n j) omega) ^ 4)
      (fun j _hj => by positivity) hi
  have hfourth : 0 ≤ fourthVariationApprox B U n omega :=
    fourthVariationApprox_nonneg B U n omega
  have hsq : (|d| ^ 2) ^ 2 ≤ fourthVariationApprox B U n omega := by
    calc
      (|d| ^ 2) ^ 2 = d ^ 4 := by rw [sq_abs]; ring
      _ ≤ fourthVariationApprox B U n omega := hterm
  have hfirst : |d| ^ 2 ≤
      Real.sqrt (fourthVariationApprox B U n omega) :=
    Real.le_sqrt_of_sq_le hsq
  have hsecond : |d| ≤
      Real.sqrt (Real.sqrt (fourthVariationApprox B U n omega)) :=
    Real.le_sqrt_of_sq_le hfirst
  simpa only [d, fourthVariationRootApprox] using hsecond

/-- For a pre-Brownian process, the fourth-root mesh control vanishes in
probability without assuming continuity of the chosen sample paths. -/
theorem fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P
      (fun n => fourthVariationRootApprox B U (n + 1)) atTop
      (fun _ => 0) := by
  have hbase := fourthVariationApprox_preBrownianReal_tendstoInMeasure_zero
    hB U
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fourthVariationApprox B U (n + 1)) P :=
    aestronglyMeasurable_fourthVariationApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable) U (n + 1)
  have hfirst := TendstoInMeasure.continuous_comp hmeas hbase
    Real.continuous_sqrt
  have hsqrtMeas (n : ℕ) : AEStronglyMeasurable
      (fun omega => Real.sqrt (fourthVariationApprox B U (n + 1) omega)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hmeas n)
  have hsecond := TendstoInMeasure.continuous_comp hsqrtMeas hfirst
    Real.continuous_sqrt
  change TendstoInMeasure P
    (fun n omega => Real.sqrt
      (Real.sqrt (fourthVariationApprox B U (n + 1) omega))) atTop
    (fun _ => 0)
  simpa only [Real.sqrt_zero] using hsecond

/-- Maximum absolute increment on the positive uniform `(n+1)`-partition.
The shifted indexing makes the defining finite set nonempty at every outer
index. -/
noncomputable def uniformPartitionMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun i =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|

theorem uniformPartitionMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ uniformPartitionMaxAbsIncrement X U n omega := by
  exact (abs_nonneg (X (uniformPartitionTime U (n + 1) 1) omega -
    X (uniformPartitionTime U (n + 1) 0) omega)).trans
      (Finset.le_sup' (fun i =>
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Each cell increment is bounded by the uniform-partition maximum. -/
theorem abs_uniformPartition_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
        X (uniformPartitionTime U (n + 1) i) omega| ≤
      uniformPartitionMaxAbsIncrement X U n omega :=
  Finset.le_sup' (fun j =>
    |X (uniformPartitionTime U (n + 1) (j + 1)) omega -
      X (uniformPartitionTime U (n + 1) j) omega|) hi

theorem stronglyMeasurable_uniformPartitionMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {X : ℝ≥0 → W → ℝ}
    (hX : ∀ s, StronglyMeasurable (X s)) (U : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (uniformPartitionMaxAbsIncrement X U n) := by
  apply Measurable.stronglyMeasurable
  unfold uniformPartitionMaxAbsIncrement
  let f : ℕ → W → ℝ := fun i omega =>
    |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
      X (uniformPartitionTime U (n + 1) i) omega|
  have hf : ∀ i ∈ Finset.range (n + 1), Measurable (f i) := by
    intro i _hi
    simpa only [f, Pi.sub_apply, Real.norm_eq_abs] using
      ((hX _).sub (hX _)).norm.measurable
  have hsup := Finset.measurable_sup' Finset.nonempty_range_add_one hf
  convert hsup using 1
  ext omega
  rw [Finset.sup'_apply]

/-- Uniform continuity makes the maximum mesh increment vanish pointwise. -/
theorem uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (omega : W)
    (hX : Continuous fun s => X s omega) :
    Tendsto (fun n => uniformPartitionMaxAbsIncrement X U n omega)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (continuous_uniformPartition_increments_tendsto
      (fun s => X s omega) hX U epsilon hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (uniformPartitionMaxAbsIncrement_nonneg X U n omega)]
  rw [uniformPartitionMaxAbsIncrement, Finset.sup'_lt_iff]
  intro i hi
  exact hN n hn i hi

/-- A process with measurable time sections and continuous paths has
vanishing maximum uniform-grid increments in probability. -/
theorem uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement X U n)
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement
      hXmeas U n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega =>
      uniformPartitionMaxAbsIncrement_tendsto_zero_of_continuous
        X U omega (hXcont omega)

/-- The pre-Brownian maximum mesh increment is dominated by the fourth-root
variation control, so it vanishes in probability for arbitrary versions. -/
theorem uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (U : ℝ≥0) :
    TendstoInMeasure P (fun n => uniformPartitionMaxAbsIncrement B U n)
      atTop (fun _ => 0) := by
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas
    (fourthVariationRootApprox_preBrownianReal_tendstoInMeasure_zero hB U)
  · intro n omega
    exact Real.sqrt_nonneg _
  · intro n omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (uniformPartitionMaxAbsIncrement_nonneg B U n omega)]
    rw [uniformPartitionMaxAbsIncrement, Finset.sup'_le_iff]
    intro i hi
    exact abs_uniformPartition_increment_le_fourthVariationRootApprox
      B U omega hi

/-- A stopped-grid mesh control: the endpoint mesh maximum plus the square
root of the sole possible boundary-cell quadratic contribution. -/
noncomputable def uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionMaxAbsIncrement X U n omega +
    Real.sqrt (quadraticVariationCrossingStopApprox
      X U (n + 1) (min t U) omega)

theorem uniformPartitionStoppedMaxAbsIncrement_nonneg
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) :
    0 ≤ uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact add_nonneg
    (uniformPartitionMaxAbsIncrement_nonneg X U n omega)
    (Real.sqrt_nonneg _)

theorem aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X : ℝ≥0 → W → ℝ} (hX : ∀ s, StronglyMeasurable (X s))
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (uniformPartitionStoppedMaxAbsIncrement X U n t) P := by
  unfold uniformPartitionStoppedMaxAbsIncrement
  exact (stronglyMeasurable_uniformPartitionMaxAbsIncrement hX U n
    |>.aestronglyMeasurable).add
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (aestronglyMeasurable_quadraticVariationCrossingStopApprox
          (fun s => (hX s).aestronglyMeasurable) U (n + 1) (min t U)))

/-- Every increment stopped at an arbitrary deterministic observation time
is controlled by the full-cell mesh and the unique crossing-cell term. -/
theorem abs_uniformPartition_stopped_increment_le_max
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    |X (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        X (min t (uniformPartitionTime U (n + 1) i)) omega| ≤
      uniformPartitionStoppedMaxAbsIncrement X U n t omega := by
  let a := min t U
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hrightU : uniformPartitionTime U (n + 1) (i + 1) ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi1).2
  have hleftU : uniformPartitionTime U (n + 1) i ≤ U :=
    (uniformPartitionTime_mem_Icc_of_le U (Nat.zero_lt_succ n) hi0).2
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  rw [hmin _ hrightU, hmin _ hleftU]
  by_cases hright : uniformPartitionTime U (n + 1) (i + 1) ≤ a
  · have hleft : uniformPartitionTime U (n + 1) i ≤ a :=
      (monotone_uniformPartitionTime_general U (n + 1)
        (Nat.le_succ i)).trans hright
    rw [min_eq_right hright, min_eq_right hleft]
    exact (abs_uniformPartition_increment_le_max X U n omega hi).trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have haright : a ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      le_of_not_ge hright
    by_cases hleft : uniformPartitionTime U (n + 1) i ≤ a
    · rw [min_eq_left haright, min_eq_right hleft]
      have hicross : i ∈ uniformPartitionCrossingCells U (n + 1) a := by
        simp only [uniformPartitionCrossingCells, Finset.mem_filter, hi,
          hleft, hright, not_false_eq_true, and_self]
      have hsquare :
          (X a omega - X (uniformPartitionTime U (n + 1) i) omega) ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        unfold quadraticVariationCrossingStopApprox
        exact Finset.single_le_sum
          (fun j _hj => sq_nonneg
            (X a omega - X (uniformPartitionTime U (n + 1) j) omega))
          hicross
      have habsSquare :
          |X a omega - X (uniformPartitionTime U (n + 1) i) omega| ^ 2 ≤
            quadraticVariationCrossingStopApprox X U (n + 1) a omega := by
        simpa only [sq_abs] using hsquare
      exact (Real.le_sqrt_of_sq_le habsSquare).trans
        (le_add_of_nonneg_left
          (uniformPartitionMaxAbsIncrement_nonneg X U n omega))
    · have haleft : a ≤ uniformPartitionTime U (n + 1) i :=
        le_of_not_ge hleft
      rw [min_eq_left haright, min_eq_left haleft, sub_self, abs_zero]
      exact uniformPartitionStoppedMaxAbsIncrement_nonneg X U n t omega

/-- Continuous measurable paths make the stopped mesh control vanish in
probability at every deterministic observation time. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X : ℝ≥0 → W → ℝ} (hXmeas : ∀ s, StronglyMeasurable (X s))
    (hXcont : ∀ omega, Continuous fun s => X s omega)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement X U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh : TendstoInMeasure P
      (fun n => uniformPartitionMaxAbsIncrement X U n) atTop
      (fun _ => 0) :=
    uniformPartitionMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      hXmeas hXcont U
  have hmod : IsContinuousProcessModification X X P :=
    ⟨fun _ => Filter.Eventually.of_forall fun _ => rfl,
      Filter.Eventually.of_forall hXcont⟩
  have hcross : TendstoInMeasure P
      (fun n => quadraticVariationCrossingStopApprox X U (n + 1) a)
      atTop (fun _ => 0) :=
    hmod.quadraticVariationCrossingStopApprox_tendstoInMeasure
      (fun s => (hXmeas s).aestronglyMeasurable) U a
      ⟨bot_le, min_le_right t U⟩
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox X U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hXmeas s).aestronglyMeasurable) U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement X U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        X U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- The stopped mesh control also vanishes for an arbitrary pre-Brownian
representative; Gaussian boundary-cell control replaces path continuity. -/
theorem
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => uniformPartitionStoppedMaxAbsIncrement B U n t)
      atTop (fun _ => 0) := by
  let a := min t U
  have hmesh :=
    uniformPartitionMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U
  have hcross :=
    quadraticVariationCrossingStopApprox_preBrownianReal_tendstoInMeasure
      hB U a
  have hcrossMeas (n : ℕ) : AEStronglyMeasurable
      (quadraticVariationCrossingStopApprox B U (n + 1) a) P :=
    aestronglyMeasurable_quadraticVariationCrossingStopApprox
      (fun s => (hB.aemeasurable s).aestronglyMeasurable)
      U (n + 1) a
  have hroot := TendstoInMeasure.continuous_comp hcrossMeas hcross
    Real.continuous_sqrt
  have hsum := hmesh.add_real_noMeas hroot
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionMaxAbsIncrement B U n omega +
      Real.sqrt (quadraticVariationCrossingStopApprox
        B U (n + 1) (min t U) omega)) atTop (fun _ => 0)
  simpa only [a, add_zero, Real.sqrt_zero] using hsum

/-- Stopped-grid mesh control for the complex martingale combination. -/
noncomputable def girsanovComplexCombinationStoppedMeshControl
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement M U n t omega +
    |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega

theorem girsanovComplexCombinationStoppedMeshControl_nonneg
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCombinationStoppedMeshControl
      M B c U n t omega := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact add_nonneg
    (uniformPartitionStoppedMaxAbsIncrement_nonneg M U n t omega)
    (mul_nonneg (abs_nonneg c)
      (uniformPartitionStoppedMaxAbsIncrement_nonneg B U n t omega))

/-- Every stopped complex-combination cell is bounded by the stopped mesh
control. -/
theorem
    norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dM := M u omega - M s omega
  let dB := B u omega - B s omega
  have heq :
      complexMartingaleCombination M B c u omega -
          complexMartingaleCombination M B c s omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dM : ℂ)‖ + ‖((c * dB : ℝ) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |dM| + |c| * |dB| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one]
    _ ≤ uniformPartitionStoppedMaxAbsIncrement M U n t omega +
        |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega := by
      apply add_le_add
      · simpa only [dM, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            M U n t omega hi
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        simpa only [dB, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            B U n t omega hi
    _ = girsanovComplexCombinationStoppedMeshControl
        M B c U n t omega := rfl

/-- The stopped complex-combination mesh vanishes in probability under the
Challenge path and pre-Brownian hypotheses. -/
theorem girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M B : ℝ≥0 → W → ℝ} (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCombinationStoppedMeshControl M B c U n t)
      atTop (fun _ => 0) := by
  have hM :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hMmeas hMcont U t
  have hBmesh :=
    uniformPartitionStoppedMaxAbsIncrement_preBrownianReal_tendstoInMeasure_zero
      hB U t
  have hsum := hM.add_real_noMeas
    (hBmesh.const_mul_real_noMeas |c|)
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement M U n t omega +
      |c| * uniformPartitionStoppedMaxAbsIncrement B U n t omega)
    atTop (fun _ => 0)
  simpa only [mul_zero, add_zero] using hsum

/-- Stopping a uniform cell at a deterministic observation time cannot
increase the cell's time width. -/
theorem abs_stopped_uniformPartition_time_increment_le_mesh
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (i : ℕ) :
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
  let u := (uniformPartitionTime U (n + 1) (i + 1) : ℝ)
  let s := (uniformPartitionTime U (n + 1) i : ℝ)
  have hmin := abs_min_sub_min_le_max u (t : ℝ) s (t : ℝ)
  have hdist := dist_uniformPartitionTime_succ_eq U
    (Nat.zero_lt_succ n) i
  calc
    |(min t (uniformPartitionTime U (n + 1) (i + 1)) : ℝ) -
        (min t (uniformPartitionTime U (n + 1) i) : ℝ)| =
        |min u (t : ℝ) - min s (t : ℝ)| := by
      simp only [u, s, min_comm]
    _ ≤ |u - s| := by
      simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - s))]
        using hmin
    _ = ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      simpa only [u, s, NNReal.dist_eq, Nat.succ_eq_add_one] using hdist

/-- Stopped-grid mesh control for the proposed complex bracket. -/
noncomputable def girsanovComplexBracketStoppedMeshControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
    c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
    2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega

theorem girsanovComplexBracketStoppedMeshControl_nonneg
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexBracketStoppedMeshControl
      bracket C c U n t omega := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact add_nonneg
    (add_nonneg
      (uniformPartitionStoppedMaxAbsIncrement_nonneg bracket U n t omega)
      (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (uniformPartitionStoppedMaxAbsIncrement_nonneg C U n t omega))

theorem aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracket : ∀ s, StronglyMeasurable (bracket s))
    (hC : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c U n t) P := by
  unfold girsanovComplexBracketStoppedMeshControl
  exact ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
      (P := P) hbracket U n t).add aestronglyMeasurable_const).add
    (aestronglyMeasurable_const.mul
      (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        (P := P) hC U n t))

/-- Every stopped complex-bracket cell increment is bounded by its stopped
mesh control. -/
theorem
    norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega‖ ≤
      girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := by
  let u := min t (uniformPartitionTime U (n + 1) (i + 1))
  let s := min t (uniformPartitionTime U (n + 1) i)
  let dA := bracket u omega - bracket s omega
  let dC := C u omega - C s omega
  let dt := (u : ℝ) - (s : ℝ)
  have htime : |dt| ≤
      ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    dsimp only [dt, u, s]
    rw [NNReal.coe_min, NNReal.coe_min]
    exact abs_stopped_uniformPartition_time_increment_le_mesh U n t i
  have heq :
      complexMartingaleCombinationBracket bracket C c u omega -
          complexMartingaleCombinationBracket bracket C c s omega =
        (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
          ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombinationBracket
    dsimp only [dA, dC, dt]
    push_cast
    ring
  rw [heq]
  calc
    ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
        ((2 * c * dC : ℝ) : ℂ) * Complex.I‖ ≤
        ‖(dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ)‖ +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ (‖(dA : ℂ)‖ + ‖((c ^ 2 * dt : ℝ) : ℂ)‖) +
          ‖((2 * c * dC : ℝ) : ℂ) * Complex.I‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = |dA| + c ^ 2 * |dt| + 2 * |c| * |dC| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
        Complex.norm_I, mul_one, abs_pow]
      rw [sq_abs]
      ring
    _ ≤ |dA| + c ^ 2 *
          ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * |dC| := by
      gcongr
    _ ≤ uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
          c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
        2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega := by
      gcongr
      · simpa only [dA, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            bracket U n t omega hi
      · simpa only [dC, u, s] using
          abs_uniformPartition_stopped_increment_le_max
            C U n t omega hi
    _ = girsanovComplexBracketStoppedMeshControl
        bracket C c U n t omega := rfl

/-- Continuous bracket and drift paths make the stopped complex-bracket
mesh vanish in probability. -/
theorem girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {bracket C : ℝ≥0 → W → ℝ}
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c U n t) atTop (fun _ => 0) := by
  have hA :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hbracketMeas hbracketCont U t
  have hC :=
    uniformPartitionStoppedMaxAbsIncrement_tendstoInMeasure_zero_of_continuous
      (P := P) hCMeas hCCont U t
  have hmesh : Tendsto (fun n : ℕ =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (nhds 0) := by
    have hdiv : Tendsto (fun n : ℕ =>
        ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
        (nhds 0) := by
      have hNN : Tendsto (fun n : ℕ =>
          U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
        (Filter.tendsto_add_atTop_iff_nat 1).2
          (tendsto_const_div_atTop_nhds_zero_nat U)
      change Tendsto (NNReal.toReal ∘ fun n : ℕ =>
        U / ((n + 1 : ℕ) : ℝ≥0)) atTop (nhds (0 : ℝ))
      simpa only [NNReal.coe_zero] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hNN
    simpa only [mul_zero] using hdiv.const_mul (c ^ 2)
  have hmeshMeasure : TendstoInMeasure P (fun n _omega =>
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)) atTop
      (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro _n
      exact aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _omega => hmesh
  have hsum := (hA.add_real_noMeas hmeshMeasure).add_real_noMeas
    (hC.const_mul_real_noMeas (2 * |c|))
  change TendstoInMeasure P (fun n omega =>
    uniformPartitionStoppedMaxAbsIncrement bracket U n t omega +
      c ^ 2 * ((U / ((n + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) +
      2 * |c| * uniformPartitionStoppedMaxAbsIncrement C U n t omega)
    atTop (fun _ => 0)
  simpa only [add_zero, mul_zero] using hsum

/-- Uniform stopped-grid control for the compensated complex logarithmic
increment `ΔX - ΔQ/2`. -/
noncomputable def girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
    girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2

theorem girsanovComplexCompensatedStoppedMeshControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexCompensatedStoppedMeshControl
      M bracket B C c U n t omega := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  exact add_nonneg
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c U n t omega)
    (div_nonneg
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c U n t omega) (by norm_num))

/-- Every stopped compensated complex cell is bounded by the combined
stopped mesh control. -/
theorem norm_girsanov_compensated_stopped_uniformPartition_increment_le
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖(complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombination M B c
          (min t (uniformPartitionTime U (n + 1) i)) omega) -
      (complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
        complexMartingaleCombinationBracket bracket C c
          (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ ≤
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := by
  calc
    _ ≤ ‖complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
        ‖complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket C c
            (min t (uniformPartitionTime U (n + 1) i)) omega‖ / 2 := by
      calc
        _ ≤ ‖complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombination M B c
                (min t (uniformPartitionTime U (n + 1) i)) omega‖ +
            ‖(complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
              complexMartingaleCombinationBracket bracket C c
                (min t (uniformPartitionTime U (n + 1) i)) omega) / 2‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    _ ≤ girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
        girsanovComplexBracketStoppedMeshControl bracket C c U n t omega /
          2 := by
      gcongr
      · exact
          norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
            M B c U n t omega hi
      · exact
          norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
            bracket C c U n t omega hi
    _ = girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t omega := rfl

/-- The stopped compensated mesh vanishes in probability. -/
theorem girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (hB : IsPreBrownianReal B P) (c : ℝ) (U t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) atTop (fun _ => 0) := by
  have hX :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c U t
  have hQ :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hbracketMeas hbracketCont hCMeas hCCont c U t
  have hsum := hX.add_real_noMeas
    (hQ.const_mul_real_noMeas (1 / 2 : ℝ))
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCombinationStoppedMeshControl M B c U n t omega +
      girsanovComplexBracketStoppedMeshControl bracket C c U n t omega / 2)
    atTop (fun _ => 0)
  apply hsum.congr
  · intro n
    exact Filter.Eventually.of_forall fun omega => by ring
  · exact Filter.Eventually.of_forall fun _omega => by ring

theorem aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M B : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCombinationStoppedMeshControl M B c U n t) P := by
  unfold girsanovComplexCombinationStoppedMeshControl
  exact (aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
    hMmeas U n t).add
      ((aestronglyMeasurable_uniformPartitionStoppedMaxAbsIncrement
        hBmeas U n t).const_mul |c|)

theorem aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    AEStronglyMeasurable
      (girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c U n t) P := by
  unfold girsanovComplexCompensatedStoppedMeshControl
  have hX :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c U n t
  have hQ := aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
    (P := P) hbracketMeas hCMeas c U n t
  exact hX.add (by simpa only [div_eq_mul_inv] using hQ.mul_const (2 : ℝ)⁻¹)

/-- Discrete total variation of a complex-valued process on a uniform grid. -/
noncomputable def complexTotalVariationApprox
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    ‖Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega‖

theorem complexTotalVariationApprox_nonneg
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    0 ≤ complexTotalVariationApprox Q U n omega := by
  unfold complexTotalVariationApprox
  exact Finset.sum_nonneg fun _i _hi => norm_nonneg _

/-- Stopping a uniform grid at an arbitrary deterministic time can add at
most one partial-cell contribution to its total variation.  The parameter
`delta` is any common bound for the stopped cell increments. -/
theorem complexTotalVariationApprox_stop_le_of_cell_bound
    {W : Type*} (Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hinc : ∀ i ∈ Finset.range n,
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
        Q (min t (uniformPartitionTime U n i)) omega‖ ≤ delta) :
    complexTotalVariationApprox (fun s w => Q (min t s) w)
        U n omega ≤
      complexTotalVariationApprox Q U n omega + delta := by
  classical
  let a := min t U
  let S := uniformPartitionCrossingCells U n a
  have hmin (s : ℝ≥0) (hs : s ≤ U) : min t s = min a s := by
    by_cases htU : t ≤ U
    · simp only [a, min_eq_left htU]
    · have hUt : U ≤ t := le_of_not_ge htU
      simp only [a, min_eq_right hUt,
        min_eq_right (hs.trans hUt), min_eq_right hs]
  have hcell (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖ ≤
        ‖Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega‖ +
          if i ∈ S then delta else 0 := by
    have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
    have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
    have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
    have hrightU : uniformPartitionTime U n (i + 1) ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2
    have hleftU : uniformPartitionTime U n i ≤ U :=
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2
    rw [hmin _ hrightU, hmin _ hleftU]
    by_cases hright : uniformPartitionTime U n (i + 1) ≤ a
    · have hleft : uniformPartitionTime U n i ≤ a :=
        (monotone_uniformPartitionTime_general U n
          (Nat.le_succ i)).trans hright
      rw [min_eq_right hright, min_eq_right hleft]
      exact le_add_of_nonneg_right (ite_nonneg hdelta (le_refl 0))
    · have haright : a ≤ uniformPartitionTime U n (i + 1) :=
        le_of_not_ge hright
      by_cases hleft : uniformPartitionTime U n i ≤ a
      · have hicross : i ∈ S := by
          simp only [S, uniformPartitionCrossingCells, Finset.mem_filter,
            hi, hleft, hright, not_false_eq_true, and_self]
        have hpartial := hinc i hi
        rw [hmin _ hrightU, hmin _ hleftU,
          min_eq_left haright, min_eq_right hleft] at hpartial
        rw [min_eq_left haright, min_eq_right hleft, if_pos hicross]
        exact hpartial.trans
          (le_add_of_nonneg_left
            (norm_nonneg (Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega)))
      · have haleft : a ≤ uniformPartitionTime U n i :=
          le_of_not_ge hleft
        rw [min_eq_left haright, min_eq_left haleft, sub_self, norm_zero]
        exact add_nonneg (norm_nonneg _) (ite_nonneg hdelta (le_refl 0))
  unfold complexTotalVariationApprox
  calc
    (∑ i ∈ Finset.range n,
        ‖Q (min t (uniformPartitionTime U n (i + 1))) omega -
          Q (min t (uniformPartitionTime U n i)) omega‖) ≤
        ∑ i ∈ Finset.range n,
          (‖Q (uniformPartitionTime U n (i + 1)) omega -
              Q (uniformPartitionTime U n i) omega‖ +
            if i ∈ S then delta else 0) :=
      Finset.sum_le_sum hcell
    _ = (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) +
        ∑ i ∈ Finset.range n, if i ∈ S then delta else 0 := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ i ∈ Finset.range n,
          ‖Q (uniformPartitionTime U n (i + 1)) omega -
            Q (uniformPartitionTime U n i) omega‖) + delta := by
      gcongr
      have hcard : S.card ≤ 1 := by
        simpa only [S] using card_uniformPartitionCrossingCells_le_one U n a
      calc
        (∑ i ∈ Finset.range n, if i ∈ S then delta else 0) =
            ∑ _i ∈ (Finset.range n).filter (· ∈ S), delta := by
          rw [Finset.sum_filter]
        _ = ∑ _i ∈ S, delta := by
          congr 1
          ext i
          simp only [Finset.mem_filter, S, uniformPartitionCrossingCells]
          tauto
        _ = S.card * delta := by simp
        _ ≤ 1 * delta := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hdelta
        _ = delta := one_mul delta

/-- The total variation of the time coordinate on a positive uniform
partition is exactly the length of the interval. -/
theorem totalVariationApprox_time_uniformPartition_succ
    (U : ℝ≥0) (n : ℕ) :
    totalVariationApprox (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () =
      (U : ℝ) := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
          (uniformPartitionTime U (n + 1) i : ℝ)|) =
        ∑ i ∈ Finset.range (n + 1),
          ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr
        (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = (uniformPartitionTime U (n + 1) (n + 1) : ℝ) -
        (uniformPartitionTime U (n + 1) 0 : ℝ) := by
      exact Finset.sum_range_sub
        (fun i => (uniformPartitionTime U (n + 1) i : ℝ)) (n + 1)
    _ = (U : ℝ) := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        NNReal.coe_zero, sub_zero]

/-- Total variation of a nondecreasing real path telescopes on every
positive uniform partition. -/
theorem totalVariationApprox_monotone_uniformPartition_succ
    {W : Type*} (X : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmono : Monotone fun s => X s omega) :
    totalVariationApprox X U (n + 1) omega = X U omega - X 0 omega := by
  unfold totalVariationApprox
  calc
    (∑ i ∈ Finset.range (n + 1),
        |X (uniformPartitionTime U (n + 1) (i + 1)) omega -
          X (uniformPartitionTime U (n + 1) i) omega|) =
        ∑ i ∈ Finset.range (n + 1),
          (X (uniformPartitionTime U (n + 1) (i + 1)) omega -
            X (uniformPartitionTime U (n + 1) i) omega) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr
        (hmono (monotone_uniformPartitionTime_general U (n + 1)
          (Nat.le_succ i)))
    _ = X (uniformPartitionTime U (n + 1) (n + 1)) omega -
        X (uniformPartitionTime U (n + 1) 0) omega := by
      exact Finset.sum_range_sub
        (fun i => X (uniformPartitionTime U (n + 1) i) omega) (n + 1)
    _ = X U omega - X 0 omega := by
      have hn0 : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
      rw [show uniformPartitionTime U (n + 1) (n + 1) = U by
        unfold uniformPartitionTime
        exact mul_div_cancel_right₀ U hn0]
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div]

/-- Negating a real process does not change any discrete total-variation
sum. -/
theorem totalVariationApprox_neg_process
    {W : Type*} (X : ℝ≥0 → W → ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    totalVariationApprox (fun s omega => -X s omega) U n omega =
      totalVariationApprox X U n omega := by
  unfold totalVariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show -X (uniformPartitionTime U n (i + 1)) omega -
      -X (uniformPartitionTime U n i) omega =
      -(X (uniformPartitionTime U n (i + 1)) omega -
        X (uniformPartitionTime U n i) omega) by ring, abs_neg]

/-- The discrete variation of an absolutely continuous drift path is
bounded by the `L¹` norm of its time integrand. -/
theorem totalVariationApprox_integratedDrift_le
    {W : Type*} (mu : ℝ≥0 → W → ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hmu : IntegrableOn (fun r : ℝ => mu r.toNNReal omega)
      (Set.Icc (0 : ℝ) (U : ℝ))) :
    totalVariationApprox (integratedDrift mu) U n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |mu r.toNNReal omega| := by
  let g : ℝ → ℝ := fun r => mu r.toNNReal omega
  change totalVariationApprox
      (fun s (_u : Unit) => nnrealIntegralPrimitive g s) U n () ≤
    ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |g r|
  exact totalVariationApprox_nnrealIntegralPrimitive_le hmu n

/-- Up to its terminal horizon, the totalized Girsanov drift has the same
variation bound as its absolutely continuous real-time primitive. -/
theorem totalVariationApprox_girsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    (theta : ℝ≥0 → W → ℝ) (T : ℝ≥0) (n : ℕ) (omega : W)
    (htheta : IntegrableOn (fun r : ℝ => theta r.toNNReal omega)
      (Set.Icc (0 : ℝ) (T : ℝ))) :
    totalVariationApprox (girsanovIntegratedDrift theta T) T n omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  cases n with
  | zero =>
      unfold totalVariationApprox
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  | succ n =>
      have hn : 0 < n + 1 := Nat.zero_lt_succ n
      calc
        totalVariationApprox (girsanovIntegratedDrift theta T)
            T (n + 1) omega =
            totalVariationApprox (integratedDrift theta) T (n + 1) omega := by
          unfold totalVariationApprox
          apply Finset.sum_congr rfl
          intro i hi
          have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
          have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
          rw [girsanovIntegratedDrift_eq_integratedDrift,
            girsanovIntegratedDrift_eq_integratedDrift,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi1).2,
            min_eq_left (uniformPartitionTime_mem_Icc_of_le
              T hn hi0).2]
        _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
              |theta r.toNNReal omega| :=
          totalVariationApprox_integratedDrift_le theta T (n + 1) omega htheta

/-- A scalar control for the total variation of the proposed complex
bracket `A - c² t + 2 i c C` on a positive uniform grid. -/
noncomputable def girsanovComplexBracketVariationControl
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) : ℝ :=
  totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
    2 * |c| * totalVariationApprox C U (n + 1) omega

/-- For genuine Girsanov density data, the bracket contribution to the
variation control is exactly its terminal value. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_eq
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket C c T n omega =
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| * totalVariationApprox C T (n + 1) omega := by
  unfold girsanovComplexBracketVariationControl
  rw [totalVariationApprox_monotone_uniformPartition_succ bracket T n omega
    (hdata.continuous_monotone_bracket omega).2,
    hdata.bracket_zero omega, sub_zero]

/-- The regularized predictable drift has uniformly bounded discrete
variation.  The zero-bracket branch is identically zero; the other branch
uses the terminal square integral to recover the required `L²`, hence `L¹`,
time integrability. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        T (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (T : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaInt : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          T (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            T (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          T (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) T (n + 1) omega
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta T (n + 1) omega hthetaInt

/-- The terminally regularized Girsanov drift has the same pathwise
variation bound on every earlier deterministic horizon. This separates the
horizon used in the zero-bracket regularization from the grid horizon. -/
theorem totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (n : ℕ) (omega : W) :
    totalVariationApprox
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        U (n + 1) omega ≤
      ∫ r in Set.Icc (0 : ℝ) (U : ℝ), |theta r.toNNReal omega| := by
  by_cases hzero : bracket T omega = 0
  · unfold totalVariationApprox regularizedGirsanovIntegratedDrift
    simp only [hzero, if_pos, neg_zero, sub_self, abs_zero,
      Finset.sum_const_zero]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  · have hsqne : (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
        (theta r.toNNReal omega) ^ 2) ≠ 0 := by
      rw [← integral_nonnegative_Ioc_sq_eq_real_Icc]
      intro hsquare
      apply hzero
      rw [hbracketTerminal]
      exact hsquare
    have hsqInt : IntegrableOn
        (fun r : ℝ => (theta r.toNNReal omega) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
      Integrable.of_integral_ne_zero hsqne
    have hthetaMeasNN : Measurable (fun s : ℝ≥0 => theta s omega) := by
      exact (IsStronglyPredictable.measurable_uncurry_nnreal htheta).comp
        (measurable_id.prodMk measurable_const)
    have hthetaMeas : AEStronglyMeasurable
        (fun r : ℝ => theta r.toNNReal omega)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))) :=
      (hthetaMeasNN.comp
        continuous_real_toNNReal.measurable).aestronglyMeasurable
    let muT : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    let : IsFiniteMeasure muT :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hmemTwo : MemLp
        (fun r : ℝ => theta r.toNNReal omega) 2 muT := by
      apply (memLp_two_iff_integrable_sq
        (by simpa only [muT] using hthetaMeas)).2
      simpa only [muT, IntegrableOn] using hsqInt
    have hthetaIntT : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
      change Integrable (fun r : ℝ => theta r.toNNReal omega) muT
      exact memLp_one_iff_integrable.mp
        (hmemTwo.mono_exponent (by norm_num))
    have hthetaIntU : IntegrableOn
        (fun r : ℝ => theta r.toNNReal omega)
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
      apply hthetaIntT.mono_set
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hUT)
    have hdriftEq : ∀ s, s ≤ U →
        girsanovIntegratedDrift theta T s omega =
          girsanovIntegratedDrift theta U s omega := by
      intro s hs
      unfold girsanovIntegratedDrift
      rw [min_eq_left (hs.trans hUT), min_eq_left hs]
    calc
      totalVariationApprox
          (fun t omega =>
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (n + 1) omega =
          totalVariationApprox
            (fun t omega => -girsanovIntegratedDrift theta T t omega)
            U (n + 1) omega := by
        unfold totalVariationApprox regularizedGirsanovIntegratedDrift
        simp only [hzero, if_false]
      _ = totalVariationApprox (girsanovIntegratedDrift theta T)
          U (n + 1) omega :=
        totalVariationApprox_neg_process
          (girsanovIntegratedDrift theta T) U (n + 1) omega
      _ = totalVariationApprox (girsanovIntegratedDrift theta U)
          U (n + 1) omega := by
        unfold totalVariationApprox
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
        have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
        rw [hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
          (Nat.zero_lt_succ n) hi1).2,
          hdriftEq _ (uniformPartitionTime_mem_Icc_of_le U
            (Nat.zero_lt_succ n) hi0).2]
      _ ≤ ∫ r in Set.Icc (0 : ℝ) (U : ℝ),
            |theta r.toNNReal omega| :=
        totalVariationApprox_girsanovIntegratedDrift_le
          theta U (n + 1) omega hthetaIntU

/-- The complex bracket variation for the continuous regularized drift is
bounded uniformly in the grid by an explicit terminal random variable. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      bracket T omega + c ^ 2 * (T : ℝ) +
        2 * |c| *
          ∫ r in Set.Icc (0 : ℝ) (T : ℝ),
            |theta r.toNNReal omega| := by
  rw [hdata.girsanovComplexBracketVariationControl_eq]
  gcongr
  exact totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le
    htheta hbracketTerminal n omega

/-- Terminal random bound for the variation of the regularized complex
Girsanov bracket.  Writing the `L¹` time norm as another predictable drift
keeps measurability available through the existing adaptedness theorem. -/
noncomputable def girsanovComplexTerminalVariationBound
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ)
    (c : ℝ) (T : ℝ≥0) (omega : W) : ℝ :=
  bracket T omega + c ^ 2 * (T : ℝ) +
    2 * |c| * girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega

theorem GirsanovDensityData.girsanovComplexTerminalVariationBound_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (omega : W) :
    0 ≤ girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbracket : 0 ≤ bracket T omega := by
    rw [← hdata.bracket_zero omega]
    exact (hdata.continuous_monotone_bracket omega).2 bot_le
  have hdrift : 0 ≤ girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T omega := by
    unfold girsanovIntegratedDrift
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  unfold girsanovComplexTerminalVariationBound
  exact add_nonneg
    (add_nonneg hbracket (mul_nonneg (sq_nonneg c) (NNReal.coe_nonneg T)))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c)) hdrift)

theorem GirsanovDensityData.stronglyMeasurable_girsanovComplexTerminalVariationBound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta) (c : ℝ) :
    StronglyMeasurable
      (girsanovComplexTerminalVariationBound bracket theta c T) := by
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega => |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W => |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  have hdrift : StronglyMeasurable (girsanovIntegratedDrift
      (fun s omega => |theta s omega|) T T) :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs T T).mono (V.le T)
  unfold girsanovComplexTerminalVariationBound
  exact (hbracket.add stronglyMeasurable_const).add
    (stronglyMeasurable_const.mul hdrift)

/-- The grid-dependent bracket-variation control is dominated by its
measurable terminal bound. -/
theorem GirsanovDensityData.girsanovComplexBracketVariationControl_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (omega : W) :
    girsanovComplexBracketVariationControl bracket
        (fun t omega =>
          -regularizedGirsanovIntegratedDrift bracket theta T t omega)
        c T n omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
  have hbound := hdata.girsanovComplexBracketVariationControl_le
    htheta hbracketTerminal c n omega
  rw [show (∫ r in Set.Icc (0 : ℝ) (T : ℝ),
      |theta r.toNNReal omega|) = girsanovIntegratedDrift
        (fun s omega => |theta s omega|) T T omega by
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega => |theta s omega|) T omega).symm] at hbound
  exact hbound

/-- Every finite-valued strongly measurable real random variable has
vanishing upper tails on a finite measure space. -/
theorem StronglyMeasurable.exists_measureReal_ge_lt_finite
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ P.real {omega | R ≤ Q omega} < delta := by
  intro delta hdelta
  let S : ℕ → Set W := fun n => {omega | (n : ℝ) ≤ Q omega}
  have hSnull (n : ℕ) : NullMeasurableSet (S n) P := by
    change NullMeasurableSet (Q ⁻¹' Set.Ici (n : ℝ)) P
    exact hQ.aemeasurable.nullMeasurable measurableSet_Ici
  have hSanti : Antitone S := by
    intro n m hnm omega homega
    exact (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ)).trans homega
  have hSinter : ⋂ n, S n = ∅ := by
    ext omega
    simp only [Set.mem_iInter, S, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    intro hall
    obtain ⟨n, hn⟩ := exists_nat_gt (Q omega)
    exact (not_lt_of_ge (hall n)) hn
  have hmeasure : Tendsto (fun n => P (S n)) atTop (nhds 0) := by
    have hraw := tendsto_measure_iInter_atTop hSnull hSanti
      ⟨0, measure_ne_top P (S 0)⟩
    rw [hSinter, measure_empty] at hraw
    change Tendsto (P ∘ S) atTop (nhds 0)
    exact hraw
  have hmeasureReal : Tendsto (fun n => P.real (S n)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmeasureReal delta hdelta
  refine ⟨(N + 1 : ℕ), by positivity, ?_⟩
  have hclose := hN (N + 1) (Nat.le_add_right N 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hclose
  simpa only [S, Nat.cast_add, Nat.cast_one] using hclose

/-- A family pointwise dominated by one finite-valued strongly measurable
random variable is uniformly tight. -/
theorem StronglyMeasurable.eventually_tight_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {Q : W → ℝ} (hQ : StronglyMeasurable Q) (q : ℕ → W → ℝ)
    (hle : ∀ n omega, q n omega ≤ Q omega) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ q n omega} < delta := by
  intro delta hdelta
  obtain ⟨R, hR, htail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P)
      hQ delta hdelta
  refine ⟨R, hR, Filter.Eventually.of_forall fun n ↦ ?_⟩
  apply (measureReal_mono ?_).trans_lt htail
  intro omega homega
  exact homega.trans (hle n omega)

/-- The variation of a monotone Girsanov bracket is uniformly tight along
every positive grid schedule. -/
theorem GirsanovDensityData.eventually_tight_totalVariationApprox_bracket
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox bracket T (N n) omega} <
          delta := by
  have hbracket : StronglyMeasurable (bracket T) :=
    (hdata.adapted_bracket T).mono (V.le T)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hbracket
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_monotone_uniformPartition_succ
    bracket T (N n - 1) omega (hdata.continuous_monotone_bracket omega).2
  rw [hpred, hdata.bracket_zero omega, sub_zero] at hvariation
  exact hvariation.le

/-- The variation of the deterministic time coordinate is uniformly tight
along every positive grid schedule. -/
theorem eventually_tight_totalVariationApprox_time
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (T : ℝ≥0) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} < delta := by
  intro delta hdelta
  refine ⟨(T : ℝ) + 1, by positivity,
    Filter.Eventually.of_forall fun n ↦ ?_⟩
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation := totalVariationApprox_time_uniformPartition_succ
    T (N n - 1)
  rw [hpred] at hvariation
  have hempty : {omega : W | (T : ℝ) + 1 ≤ totalVariationApprox
      (fun t (_omega : W) ↦ (t : ℝ)) T (N n) omega} = ∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have heq : totalVariationApprox (fun t (_omega : W) ↦ (t : ℝ))
        T (N n) omega = (T : ℝ) := by
      simpa only [totalVariationApprox] using hvariation
    rw [heq]
    linarith
  rw [hempty, measureReal_empty]
  exact hdelta

/-- Uniform tightness of the terminally regularized drift variation persists
when the uniform grids range over an earlier horizon. -/
theorem
    eventually_tight_totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_of_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {bracket theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hUT : U ≤ T) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
        P.real {omega | R ≤ totalVariationApprox
          (fun t omega ↦
            -regularizedGirsanovIntegratedDrift bracket theta T t omega)
          U (N n) omega} < delta := by
  let H : W → ℝ := girsanovIntegratedDrift
    (fun s omega ↦ |theta s omega|) U U
  have hthetaAbs : IsStronglyPredictable V
      (fun s omega ↦ |theta s omega|) := by
    change StronglyMeasurable[V.predictable]
      (fun p : ℝ≥0 × W ↦ |theta p.1 p.2|)
    simpa only [Function.uncurry, Real.norm_eq_abs] using htheta.norm
  have hH : StronglyMeasurable H := by
    exact (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaAbs U U).mono (V.le U)
  apply StronglyMeasurable.eventually_tight_of_le (P := P) hH
  intro n omega
  have hpred : N n - 1 + 1 = N n := Nat.sub_add_cancel (hN n)
  have hvariation :=
    totalVariationApprox_neg_regularizedGirsanovIntegratedDrift_le_of_le
      htheta hbracketTerminal hUT (N n - 1) omega
  rw [hpred] at hvariation
  have hIntegral : (∫ r in Set.Icc (0 : ℝ) (U : ℝ),
      |theta r.toNNReal omega|) = H omega := by
    dsimp only [H]
    unfold girsanovIntegratedDrift
    rw [min_self]
    exact (integral_nonnegative_Ioc_eq_real_Icc
      (fun s omega ↦ |theta s omega|) U omega).symm
  rwa [hIntegral] at hvariation

/-- The largest value of the stopped real Girsanov density at the left
endpoints of a uniform grid.  The last terminal endpoint is deliberately
omitted, matching the left weights in the discrete Doleans expansion. -/
noncomputable def girsanovDensityUniformPartitionLeftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k =>
    doleansDadeExponential M bracket
      (min (uniformPartitionTime T (n + 1) k) T) omega

theorem girsanovDensityUniformPartitionLeftMax_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    0 ≤ girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
  exact (doleansDadeExponential_pos M bracket
    (min (uniformPartitionTime T (n + 1) 0) T) omega).le.trans
      (Finset.le_sup' (fun k => doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) k) T) omega)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Doob's nonnegative-submartingale inequality makes the maxima of the
Girsanov density over all deterministic uniform grids uniformly tight. -/
theorem GirsanovDensityData.girsanovDensityUniformPartitionLeftMax_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ n,
        P.real {omega | K ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega} <
            delta := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : 0 < N := by
    have honeDiv : 0 < 1 / delta := one_div_pos.mpr hdelta
    exact_mod_cast honeDiv.trans hN
  let K : ℝ≥0 := ⟨(N : ℝ), Nat.cast_nonneg N⟩
  have hKpos : (0 : ℝ) < K := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast hNpos
  refine ⟨(K : ℝ), hKpos, fun n => ?_⟩
  let D : ℝ≥0 → W → ℝ := fun t omega =>
    doleansDadeExponential M bracket (min t T) omega
  let E : Set W := {omega | (K : ℝ) ≤
    girsanovDensityUniformPartitionLeftMax M bracket T n omega}
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hsample : Martingale (uniformPartitionSample D T (n + 1))
      (uniformPartitionFiltration V T (n + 1)) P :=
    martingale_uniformPartitionSample hDmart T (n + 1)
  have hnonneg : 0 ≤ uniformPartitionSample D T (n + 1) :=
    fun _k omega => (doleansDadeExponential_pos M bracket _ omega).le
  have hraw := maximal_ineq hsample.submartingale hnonneg (ε := K) n
  have hset : {omega |
      (K : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
          (fun k => uniformPartitionSample D T (n + 1) k omega)} = E := by
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
          (Filter.Eventually.of_forall fun omega =>
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
    have := mul_le_mul_of_nonneg_left hdeltaLe (show 0 ≤ (K : ℝ) by positivity)
    nlinarith
  simpa only [E] using htail

/-- A single random bound for all stopped complex Doleans left weights on a
uniform grid.  The extra fixed-time density covers the unique partial cell. -/
noncomputable def girsanovComplexDoleansStoppedWeightControl
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (c ^ 2 * (T : ℝ) / 2) *
    (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
      doleansDadeExponential M bracket (min t T) omega)

theorem girsanovComplexDoleansStoppedWeightControl_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexDoleansStoppedWeightControl
      M bracket c T n t omega := by
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

theorem doleansDadeExponential_uniformPartition_le_leftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) i) T) omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega :=
  Finset.le_sup' (fun k => doleansDadeExponential M bracket
    (min (uniformPartitionTime T (n + 1) k) T) omega) hi

/-- The stopped complex Doleans weight at every left endpoint is bounded by
the density-grid maximum plus the density at the observation time. -/
theorem norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t (uniformPartitionTime T (n + 1) i)) omega‖ ≤
      girsanovComplexDoleansStoppedWeightControl
        M bracket c T n t omega := by
  let s := min t (uniformPartitionTime T (n + 1) i)
  let u := uniformPartitionTime T (n + 1) i
  have hiLe : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have huT : u ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hiLe).2
  have hsT : s ≤ T := (min_le_right t u).trans huT
  have hexp : Real.exp (c ^ 2 * (s : ℝ) / 2) ≤
      Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    have hcoe : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
    nlinarith [sq_nonneg c]
  have hdensity : doleansDadeExponential M bracket s omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega +
        doleansDadeExponential M bracket (min t T) omega := by
    by_cases hut : u ≤ t
    · have hgrid : doleansDadeExponential M bracket s omega ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
        have hsup := doleansDadeExponential_uniformPartition_le_leftMax
          M bracket T n omega hi
        simpa only [s, min_eq_right hut, u, min_eq_left huT] using hsup
      exact hgrid.trans (le_add_of_nonneg_right
        (doleansDadeExponential_pos M bracket (min t T) omega).le)
    · have htu : t ≤ u := le_of_not_ge hut
      have htT : t ≤ T := htu.trans huT
      have hs : s = t := min_eq_left htu
      rw [hs, min_eq_left htT]
      exact le_add_of_nonneg_left
        (girsanovDensityUniformPartitionLeftMax_nonneg
          M bracket T n omega)
  rw [norm_complexDoleansDadeExponential_combination]
  unfold girsanovComplexDoleansStoppedWeightControl
  rw [mul_comm (Real.exp _) _]
  exact mul_le_mul hdensity hexp (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

/-- The random controls for stopped complex Doleans left weights are
eventually tight, uniformly over the deterministic grids. -/
theorem GirsanovDensityData.girsanovComplexDoleansStoppedWeightControl_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexDoleansStoppedWeightControl
            M bracket c T n t omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨A, hA, hAtail⟩ :=
    hdata.girsanovDensityUniformPartitionLeftMax_tight
      (delta / 2) hhalf
  have hDmeas : StronglyMeasurable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega) := by
    have hDadapt := hdata.martingale_densityProcess.stronglyAdapted
    have hmin : min (min t T) T = min t T :=
      min_eq_left (min_le_right t T)
    simpa only [hmin] using
      (hDadapt (min t T)).mono (V.le (min t T))
  obtain ⟨R, hR, hRtail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P) hDmeas
      (delta / 2) hhalf
  let L := max A R
  let e := Real.exp (c ^ 2 * (T : ℝ) / 2)
  refine ⟨e * (2 * L), mul_pos (Real.exp_pos _) (mul_pos (by norm_num)
    (hA.trans_le (le_max_left A R))), ?_⟩
  filter_upwards with n
  have hsubset : {omega | e * (2 * L) ≤
      girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ⊆
        {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
        {omega | R ≤ doleansDadeExponential M bracket (min t T) omega} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hsum :
        girsanovDensityUniformPartitionLeftMax M bracket T n omega +
            doleansDadeExponential M bracket (min t T) omega < 2 * L := by
      have hx : girsanovDensityUniformPartitionLeftMax M bracket T n omega < L :=
        hnot.1.trans_le (le_max_left A R)
      have hy : doleansDadeExponential M bracket (min t T) omega < L :=
        hnot.2.trans_le (le_max_right A R)
      linarith
    have hmul : e *
        (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
          doleansDadeExponential M bracket (min t T) omega) <
        e * (2 * L) :=
      mul_lt_mul_of_pos_left hsum (by
        dsimp only [e]
        exact Real.exp_pos _)
    exact (not_lt_of_ge homega) (by simpa only
      [girsanovComplexDoleansStoppedWeightControl, e] using hmul)
  calc
    P.real {omega | e * (2 * L) ≤
        girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ≤
        P.real ({omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
          {omega | R ≤ doleansDadeExponential M bracket (min t T) omega}) :=
      measureReal_mono hsubset
    _ ≤ P.real {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} +
        P.real {omega | R ≤
          doleansDadeExponential M bracket (min t T) omega} :=
      measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add (hAtail n) hRtail
    _ = delta := by ring

/-- The total variation of the proposed complex bracket is bounded by the
variations of its real finite-variation components. -/
theorem complexTotalVariationApprox_complexMartingaleCombinationBracket_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexTotalVariationApprox
        (complexMartingaleCombinationBracket bracket C c)
        U (n + 1) omega ≤
      girsanovComplexBracketVariationControl bracket C c U n omega := by
  have hcell (i : ℕ) :
      ‖complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) i) omega‖ ≤
        |bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
          bracket (uniformPartitionTime U (n + 1) i) omega| +
        c ^ 2 *
          |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)| +
        2 * |c| *
          |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
            C (uniformPartitionTime U (n + 1) i) omega| := by
    let u := uniformPartitionTime U (n + 1) (i + 1)
    let s := uniformPartitionTime U (n + 1) i
    let dA := bracket u omega - bracket s omega
    let dC := C u omega - C s omega
    let dt := (u : ℝ) - (s : ℝ)
    have heq :
        complexMartingaleCombinationBracket bracket C c u omega -
            complexMartingaleCombinationBracket bracket C c s omega =
          (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
            ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
      unfold complexMartingaleCombinationBracket
      dsimp only [dA, dC, dt]
      push_cast
      ring
    rw [heq]
    dsimp only [dA, dC, dt, u, s]
    calc
      ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
          ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ) +
          ((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ ≤
          ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
            ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖ +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
      _ ≤
          (‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ)‖ +
            ‖((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖) +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_I, mul_one, abs_pow]
        rw [sq_abs]
        ring
  unfold complexTotalVariationApprox girsanovComplexBracketVariationControl
  calc
    (∑ i ∈ Finset.range (n + 1),
        ‖complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) (i + 1)) omega -
            complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) i) omega‖) ≤
        ∑ i ∈ Finset.range (n + 1),
          (|bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega| +
            c ^ 2 *
              |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime U (n + 1) i : ℝ)| +
            2 * |c| *
              |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
                C (uniformPartitionTime U (n + 1) i) omega|) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = totalVariationApprox bracket U (n + 1) omega +
          c ^ 2 * totalVariationApprox
            (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      unfold totalVariationApprox
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      rw [totalVariationApprox_time_uniformPartition_succ]

/-- Stopping the regularized complex bracket at an arbitrary observation
time costs only its single partial-cell mesh increment beyond the terminal
variation envelope. -/
theorem
    GirsanovDensityData.complexTotalVariationApprox_stopped_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexTotalVariationApprox
        (fun s w => complexMartingaleCombinationBracket bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c (min t s) w)
        T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let Q := complexMartingaleCombinationBracket bracket C c
  let delta := girsanovComplexBracketStoppedMeshControl bracket C c T n t omega
  have hstop : complexTotalVariationApprox (fun s w => Q (min t s) w)
      T (n + 1) omega ≤
        complexTotalVariationApprox Q T (n + 1) omega + delta := by
    apply complexTotalVariationApprox_stop_le_of_cell_bound
    · exact girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega
    · intro i hi
      exact
        norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
          bracket C c T n t omega hi
  have hfull : complexTotalVariationApprox Q T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
    exact
      (complexTotalVariationApprox_complexMartingaleCombinationBracket_le
        bracket C c T n omega).trans
        (hdata.girsanovComplexBracketVariationControl_le_terminal
          htheta hbracketTerminal c n omega)
  exact hstop.trans (add_le_add hfull (le_refl delta))

/-- The squared compensated increments are controlled by the squared
martingale increments and the square of the bracket's total variation. -/
theorem sum_norm_compensated_uniformPartition_increment_sq_le
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖(X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega) -
        (Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega) / 2‖ ^ 2) ≤
      2 * (∑ i ∈ Finset.range n,
        ‖X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega‖ ^ 2) +
        (complexTotalVariationApprox Q U n omega) ^ 2 / 2 := by
  let dX : ℕ → ℂ := fun i =>
    X (uniformPartitionTime U n (i + 1)) omega -
      X (uniformPartitionTime U n i) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega
  have hcell (i : ℕ) : ‖dX i - dQ i / 2‖ ^ 2 ≤
      2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
    have hnorm : ‖dX i - dQ i / 2‖ ≤ ‖dX i‖ + ‖dQ i‖ / 2 := by
      calc
        _ ≤ ‖dX i‖ + ‖dQ i / 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    have hsquare := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (by norm_num)))).2
        hnorm
    calc
      ‖dX i - dQ i / 2‖ ^ 2 ≤ (‖dX i‖ + ‖dQ i‖ / 2) ^ 2 := hsquare
      _ ≤ 2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖dX i‖ - ‖dQ i‖ / 2)]
  have hqSq : (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) ≤
      (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun i _hi => norm_nonneg (dQ i))
  change (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤ _
  calc
    (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤
        ∑ i ∈ Finset.range n,
          (2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) / 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 / 2 := by
      gcongr
    _ = _ := by rfl

/-- The squared norms of the `M + i c B` grid increments split exactly into
the two real quadratic-variation sums. -/
theorem sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega‖ ^ 2) =
      quadraticVariationApprox M U n omega +
        c ^ 2 * quadraticVariationApprox B U n omega := by
  unfold quadraticVariationApprox
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let dM := M (uniformPartitionTime U n (i + 1)) omega -
    M (uniformPartitionTime U n i) omega
  let dB := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have heq :
      complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq, Complex.sq_norm, Complex.normSq_add_mul_I]
  dsimp only [dM, dB]
  ring

/-- A stopped-grid analogue of the compensated-square control.  Its only
extra term is the vanishing mesh bound for the unique partial bracket cell. -/
noncomputable def girsanovComplexStoppedCompensatedSquareControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  2 * (quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1) omega +
      c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1) omega) +
    (girsanovComplexTerminalVariationBound bracket theta c T omega +
      girsanovComplexBracketStoppedMeshControl bracket
        (fun u z =>
          -regularizedGirsanovIntegratedDrift bracket theta T u z)
        c T n t omega) ^ 2 / 2

theorem GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (_hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedCompensatedSquareControl
      M bracket B theta c T n t omega := by
  unfold girsanovComplexStoppedCompensatedSquareControl
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (quadraticVariationApprox_nonneg
        (fun s w => M (min t s) w) T (n + 1) omega)
      (mul_nonneg (sq_nonneg c)
        (quadraticVariationApprox_nonneg
          (fun s w => B (min t s) w) T (n + 1) omega))))
    (div_nonneg (sq_nonneg _) (by norm_num))

/-- All squared stopped compensated logarithmic increments are bounded by
the stopped terminal envelope. -/
theorem
    GirsanovDensityData.sum_norm_girsanov_compensated_stopped_increment_sq_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    (∑ i ∈ Finset.range (n + 1),
      ‖(complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) i)) omega) -
        (complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) i)) omega) / 2‖ ^ 2) ≤
      girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let Xs : ℝ≥0 → W → ℂ := fun s w => X (min t s) w
  let Qs : ℝ≥0 → W → ℂ := fun s w => Q (min t s) w
  have hvariation : complexTotalVariationApprox Qs T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega := by
    simpa only [Qs, Q, C] using
      hdata.complexTotalVariationApprox_stopped_le_terminal
        htheta hbracketTerminal c n t omega
  have hvariationNonneg : 0 ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega :=
    add_nonneg (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega)
  have hsquare : (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 ≤
      (girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 :=
    (sq_le_sq₀ (complexTotalVariationApprox_nonneg Qs T (n + 1) omega)
      hvariationNonneg).2 hvariation
  have hsplit : (∑ i ∈ Finset.range (n + 1),
      ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
        Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) =
      quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega := by
    simpa only [Xs, X, complexMartingaleCombination] using
      sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
        (fun s w => M (min t s) w) (fun s w => B (min t s) w)
        c T (n + 1) omega
  change (∑ i ∈ Finset.range (n + 1),
      ‖(Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Xs (uniformPartitionTime T (n + 1) i) omega) -
        (Qs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Qs (uniformPartitionTime T (n + 1) i) omega) / 2‖ ^ 2) ≤ _
  calc
    _ ≤ 2 * (∑ i ∈ Finset.range (n + 1),
          ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 :=
      sum_norm_compensated_uniformPartition_increment_sq_le
        Xs Qs T (n + 1) omega
    _ = 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 := by
      rw [hsplit]
    _ ≤ 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (girsanovComplexTerminalVariationBound bracket theta c T omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 /
            2 := by
      gcongr
    _ = girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := rfl

/-- The stopped compensated-square control converges in probability to a
finite random variable.  Thus the single partial cell does not disturb the
terminal tightness argument. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop
      (fun omega =>
        2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
          (girsanovComplexTerminalVariationBound
            bracket theta c T omega) ^ 2 / 2) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s =>
    ((hdata.adapted_martingale s).mono (V.le s)).aestronglyMeasurable
  have hqM : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min s t) w)
        T (n + 1)) atTop (bracket (min T t)) :=
    (hdata.localQuadraticVariation.toBeforeStop.toStopped hMmeas
      (Filter.Eventually.of_forall hdata.continuous_martingale_path)) T t
  have hqM' : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1)) atTop (bracket (min T t)) := by
    apply hqM.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hqB : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1)) atTop (fun _ => ((min T t : ℝ≥0) : ℝ)) := by
    have hraw := quadraticVariation_stopped_preBrownianReal_inProbability
      hB t T
    apply hraw.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hquadratic := (hqM'.add_real_noMeas
    (hqB.const_mul_real_noMeas (c ^ 2))).const_mul_real_noMeas 2
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hHconst : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hHmesh : TendstoInMeasure P
      (fun n omega => H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega)
      atTop H := by
    simpa only [add_zero] using hHconst.add_real_noMeas hmesh
  have hmeshMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c T n t) P :=
    aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
      hbracketMeas hCMeas c T n t
  let sqHalf : ℝ → ℝ := fun x => x ^ 2 / 2
  have hsq : TendstoInMeasure P (fun n omega =>
      sqHalf (H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
      atTop (fun omega => sqHalf (H omega)) := by
    exact TendstoInMeasure.continuous_comp
      (fun n => hH.aestronglyMeasurable.add (hmeshMeas n))
      hHmesh (by simpa only [sqHalf] using
        (by fun_prop : Continuous (fun x : ℝ => x ^ 2 / 2)))
  have hsum := hquadratic.add_real_noMeas hsq
  change TendstoInMeasure P (fun n omega =>
      2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        sqHalf (H omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
    atTop (fun omega =>
      2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
        sqHalf (H omega))
  simpa only [sqHalf, H, C] using hsum

/-- The stopped compensated-square controls are eventually tight at every
deterministic observation time. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedCompensatedSquareControl
            M bracket B theta c T n t omega} < delta := by
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  let L : W → ℝ := fun omega =>
    2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
      H omega ^ 2 / 2
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hL : StronglyMeasurable L := by
    have hbracket : StronglyMeasurable (bracket (min T t)) :=
      (hdata.adapted_bracket (min T t)).mono (V.le (min T t))
    have hHsq : StronglyMeasurable (fun omega => H omega ^ 2) := by
      rw [show (fun omega => H omega ^ 2) = H * H by
        funext omega
        simp only [Pi.mul_apply, pow_two]]
      exact hH.mul hH
    unfold L
    exact (stronglyMeasurable_const.mul
      (hbracket.add stronglyMeasurable_const)).add
      (hHsq.mul stronglyMeasurable_const)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop L := by
    simpa only [L, H] using
      hdata.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
        hB htheta hbracketTerminal c t
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hL)

/-- Total-variation control for the stopped regularized complex bracket. -/
noncomputable def girsanovComplexStoppedVariationControl
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexTerminalVariationBound bracket theta c T omega +
    girsanovComplexBracketStoppedMeshControl bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedVariationControl
      bracket theta c T n t omega := by
  exact add_nonneg
    (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
    (girsanovComplexBracketStoppedMeshControl_nonneg bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤ girsanovComplexStoppedVariationControl
          bracket theta c T n t omega} < delta := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hconstant : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedVariationControl
        bracket theta c T n t) atTop H := by
    have hsum := hconstant.add_real_noMeas hmesh
    change TendstoInMeasure P (fun n omega =>
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z => -regularizedGirsanovIntegratedDrift
            bracket theta T u z) c T n t omega) atTop H
    simpa only [H, C, add_zero] using hsum
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hH)

/-- The scalar factor that vanishes in the stopped higher-order Doleans
estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderVanishingControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  dz * Real.exp dz + dz + dx

theorem girsanovComplexStoppedHigherOrderVanishingControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderVanishingControl
      M bracket B C c T n t omega := by
  unfold girsanovComplexStoppedHigherOrderVanishingControl
  exact add_nonneg (add_nonneg
    (mul_nonneg
      (girsanovComplexCompensatedStoppedMeshControl_nonneg
        M bracket B C c T n t omega) (Real.exp_pos _).le)
    (girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega))
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega)

theorem girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hB : IsPreBrownianReal B P)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) := by
  have hdz :=
    girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
      hMmeas hMcont hbracketMeas hbracketCont hCMeas hCCont hB c T t
  have hdx :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c T t
  have hdzMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
      (P := P) hMmeas hBmeas hbracketMeas hCMeas c T n t
  have hdxMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c T n t
  let finish : ℝ → ℝ → ℝ := fun dz dx =>
    dz * Real.exp dz + dz + dx
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  have hconv := TendstoInMeasure.continuous_comp₂
    hdzMeas hdxMeas hdz hdx hfinish
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega *
        Real.exp (girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega) +
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c T n t omega +
      girsanovComplexCombinationStoppedMeshControl M B c T n t omega)
    atTop (fun _ => 0)
  simpa only [finish, Real.exp_zero, mul_one, zero_add] using hconv

/-- The tight random factor in the stopped higher-order Doleans estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderTightControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega *
    (girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega +
      girsanovComplexStoppedVariationControl bracket theta c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderTightControl
      M bracket B theta c T n t omega := by
  exact mul_nonneg
    (girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega)
    (add_nonneg
      (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
      (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))

theorem
    GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedHigherOrderTightControl
            M bracket B theta c T n t omega} < delta := by
  have hweight :=
    hdata.girsanovComplexDoleansStoppedWeightControl_tight c t
  have hsquare :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
      hB htheta hbracketTerminal c t
  have hvariation :=
    hdata.girsanovComplexStoppedVariationControl_eventually_tight
      htheta hbracketTerminal c t
  have hsum := eventually_tight_add_of_nonneg
    (fun n omega =>
      hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
    (fun n omega =>
      hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega)
    hsquare hvariation
  simpa only [girsanovComplexStoppedHigherOrderTightControl] using
    eventually_tight_mul_of_nonneg
      (fun n omega =>
        girsanovComplexDoleansStoppedWeightControl_nonneg
          M bracket c T n t omega)
      (fun n omega => add_nonneg
        (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
          c n t omega)
        (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))
      hweight hsum

/-- The stopped higher-order exponential majorant factors into a vanishing
mesh term and an eventually tight random term. -/
theorem GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_le_controls
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t omega ≤
      girsanovComplexStoppedHigherOrderVanishingControl M bracket B
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let K := girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  let S := girsanovComplexStoppedCompensatedSquareControl
    M bracket B theta c T n t omega
  let R := girsanovComplexStoppedVariationControl bracket theta c T n t omega
  have hK : 0 ≤ K :=
    girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega
  have hdz : 0 ≤ dz :=
    girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega
  have hdx : 0 ≤ dx :=
    girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega
  have hS : 0 ≤ S :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg c n t omega
  have hR : 0 ≤ R :=
    hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega
  have hraw : complexDoleansHigherOrderResidualBoundApprox
      X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := by
    apply complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    · exact hK
    · exact hdz
    · exact hdx
    · intro i hi
      exact
        norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
          M bracket B C c T n t omega hi
    · intro i hi
      exact norm_girsanov_compensated_stopped_uniformPartition_increment_le
        M bracket B C c T n t omega hi
    · intro i hi
      exact
        norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
          M B c T n t omega hi
    · simpa only [X, Q, C, S] using
        hdata.sum_norm_girsanov_compensated_stopped_increment_sq_le
          htheta hbracketTerminal c n t omega
    · change complexTotalVariationApprox
          (fun s w => Q (min t s) w) T (n + 1) omega ≤ R
      simpa only [Q, C, R, girsanovComplexStoppedVariationControl] using
        hdata.complexTotalVariationApprox_stopped_le_terminal
          htheta hbracketTerminal c n t omega
  calc
    complexDoleansHigherOrderResidualBoundApprox X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := hraw
    _ ≤ (dz * Real.exp dz + dz + dx) * (K * (S + R)) := by
      have hexp : 0 ≤ Real.exp dz := (Real.exp_pos _).le
      nlinarith [mul_nonneg hK hS, mul_nonneg hK hR,
        mul_nonneg hdz hexp, mul_nonneg (add_nonneg hdz hdx) hR]
    _ = girsanovComplexStoppedHigherOrderVanishingControl M bracket B C
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
      rfl

/-- Under the Challenge hypotheses, the explicit stopped-grid higher-order
majorant vanishes in probability. -/
theorem
    GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t) atTop (fun _ => 0) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, StronglyMeasurable (M s) := fun s =>
    (hdata.adapted_martingale s).mono (V.le s)
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hr : TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) :=
    girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
      hMmeas hdata.continuous_martingale_path hbracketMeas
      (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hBmeas hB hCMeas hCcont c T t
  have hqTight :=
    hdata.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
      hB htheta hbracketTerminal c t
  apply hr.of_norm_sub_le_mul_of_eventually_tight
    (fun n omega =>
      hdata.girsanovComplexStoppedHigherOrderTightControl_nonneg
        c n t omega) hqTight
  intro n omega
  rw [sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (complexDoleansHigherOrderResidualBoundApprox_nonneg
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t omega),
    Real.norm_eq_abs,
    abs_of_nonneg
      (girsanovComplexStoppedHigherOrderVanishingControl_nonneg
        M bracket B C c T n t omega)]
  simpa only [C] using
    hdata.complexDoleansHigherOrderResidualBoundApprox_le_controls
      htheta hbracketTerminal c n t omega

/-- The norm of the full higher-order residual is bounded pathwise by the
explicit sum of its one-cell majorants. -/
theorem norm_complexDoleansHigherOrderResidualApprox_le_bound
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    ‖complexDoleansHigherOrderResidualApprox X Q U n t omega‖ ≤
      complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualApprox
    complexDoleansHigherOrderResidualBoundApprox
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun i _hi => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_complexDoleansSecondOrderResidual_le_bound _ _) (norm_nonneg _)

/-- On every observation time, including a crossing cell, the exact Euler
residual is half the weighted bracket discrepancy plus the higher-order
remainder. -/
theorem complexDoleansEulerResidualApprox_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansEulerResidualApprox X Q U (n + 1) t omega =
      (1 / 2 : ℂ) *
          complexDoleansWeightedBracketResidualApprox
            X Q U (n + 1) t omega +
        complexDoleansHigherOrderResidualApprox
          X Q U (n + 1) t omega := by
  unfold complexDoleansEulerResidualApprox
    complexDoleansWeightedBracketResidualApprox
    complexDoleansHigherOrderResidualApprox
  simp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hleftU := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi0).2
  by_cases hleftT : uniformPartitionTime U (n + 1) i ≤ t
  · rw [min_eq_right hleftT, min_eq_left hleftU]
    rw [complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder]
    ring
  · have htleft : t ≤ uniformPartitionTime U (n + 1) i :=
      le_of_not_ge hleftT
    have hmono : uniformPartitionTime U (n + 1) i ≤
        uniformPartitionTime U (n + 1) (i + 1) :=
      monotone_uniformPartitionTime_general U (n + 1) (Nat.le_succ i)
    have htright : t ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      htleft.trans hmono
    rw [min_eq_left htleft, min_eq_left htright]
    simp [complexDoleansSecondOrderResidual]

/-- Endpoint minus the canonical complex Euler process is exactly the sum
of its one-step residuals. -/
theorem complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U t : ℝ≥0) (n : ℕ) (omega : W) :
    complexDoleansDadeExponential X Q (min t U) omega -
        complexDoleansEulerProcess X Q U (n + 1) t omega =
      complexDoleansEulerResidualApprox X Q U (n + 1) t omega := by
  let E := complexDoleansDadeExponential X Q
  have htelescope :
      (∑ i ∈ Finset.range (n + 1),
        (E (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) i)) omega)) =
        E (min t U) omega - E 0 omega := by
    calc
      _ = E (min t (uniformPartitionTime U (n + 1) (n + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) 0)) omega := by
        simpa using (Finset.sum_range_sub (fun i =>
          E (min t (uniformPartitionTime U (n + 1) i)) omega) (n + 1))
      _ = E (min t U) omega - E 0 omega := by
        simp [uniformPartitionTime]
  dsimp only [E] at htelescope
  unfold complexDoleansEulerProcess complexDoleansEulerResidualApprox
  simp only
  rw [Finset.sum_sub_distrib, htelescope]
  rw [min_eq_left (show (0 : ℝ≥0) ≤ U from bot_le)]
  ring

/-- For the Girsanov complex combination, the self-integrator two-transform
Euler process is exactly the canonical single complex Doléans left sum. -/
theorem complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) :
    complexGirsanovEulerProcess M M bracket B C c U n =
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) U n := by
  funext t omega
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min s U) omega
  let A : ℕ → ℂ := fun i =>
    (M (min t (uniformPartitionTime U n (i + 1))) omega -
      M (min t (uniformPartitionTime U n i)) omega) •
        H (uniformPartitionTime U n i) omega
  let D : ℕ → ℂ := fun i =>
    (B (min t (uniformPartitionTime U n (i + 1))) omega -
      B (min t (uniformPartitionTime U n i)) omega) •
        (((c : ℂ) * Complex.I) * H (uniformPartitionTime U n i) omega)
  let F : ℕ → ℂ := fun i =>
    (complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n (i + 1))) omega -
      complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n i)) omega) *
        H (uniformPartitionTime U n i) omega
  unfold complexGirsanovEulerProcess complexDoleansEulerProcess
    uniformAdaptedTwoMartingaleSmulProcess
    uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
    elementaryMartingaleSmulProcess
  simp only [Pi.add_apply, Finset.sum_apply]
  change H 0 omega +
      ((∑ i ∈ Finset.range n, A i) + ∑ i ∈ Finset.range n, D i) =
    H 0 omega + ∑ i ∈ Finset.range n, F i
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [A, D, F, complexMartingaleCombination]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Once the density cap agrees with the real stochastic exponential on a
whole horizon, the capped and uncapped complex Euler processes agree there
on every grid and at every observation time. -/
theorem cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) (omega : W)
    (hcap : ∀ s ∈ Set.Icc (0 : ℝ≥0) U,
      cappedDoleansDadeExponential M bracket R s omega =
        doleansDadeExponential M bracket s omega) :
    ∀ t, cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n t omega =
      complexGirsanovEulerProcess N M bracket B C c U n t omega := by
  have hcomplex (s : ℝ≥0) (hs : s ≤ U) :
      cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R s omega =
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c) s omega := by
    unfold cappedComplexDoleansDadeExponentialCombination
    rw [hcap s ⟨bot_le, hs⟩,
      complexDoleansDadeExponential_combination_factor]
  intro t
  unfold cappedComplexGirsanovEulerProcess complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  · simpa only [min_eq_left (show (0 : ℝ≥0) ≤ U by exact bot_le)] using
      hcomplex 0 bot_le
  · unfold uniformAdaptedTwoMartingaleSmulProcess
    simp only [Pi.add_apply]
    congr 1
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact hcomplex (min (uniformPartitionTime U n i) U) (min_le_right _ _)
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact congrArg (fun z : ℂ => ((c : ℂ) * Complex.I) * z)
        (hcomplex (min (uniformPartitionTime U n i) U)
          (min_le_right _ _))

/-- If two first integrators agree throughout the deterministic horizon,
their uncapped complex Euler processes agree on every grid and at every
observation time. -/
theorem complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
    {W : Type*} (N N' M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hNN' : ∀ s ∈ Set.Icc (0 : ℝ≥0) U, N s omega = N' s omega) :
    ∀ t, complexGirsanovEulerProcess N M bracket B C c U n t omega =
      complexGirsanovEulerProcess N' M bracket B C c U n t omega := by
  intro t
  unfold complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedTwoMartingaleSmulProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
  have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
  unfold elementaryMartingaleSmulProcess
  congr 2
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2⟩
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2⟩

/-- Unfolding the capped complex Euler process exposes exactly its initial
value and the two coherent martingale transforms. -/
theorem cappedComplexGirsanovEulerProcess_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T : ℝ≥0) (n : ℕ) :
    cappedComplexGirsanovEulerProcess N M bracket B C c R T n =
      let H : ℝ≥0 → W → ℂ := fun s omega =>
        cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R (min s T) omega
      let J : ℝ≥0 → W → ℂ := fun s omega =>
        ((c : ℂ) * Complex.I) * H s omega
      (fun _ => H 0) +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T n := by
  rfl

/-- For a martingale approximation `N` of `M`, every capped complex Euler
process is a genuine martingale.  This is the discrete probabilistic half of
the remaining Girsanov cancellation argument. -/
theorem martingale_cappedComplexGirsanovEulerProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [IsFiniteMeasure P]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) :
    Martingale
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n) V P := by
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  let CH : ℝ := (R : ℝ) * Real.exp (c ^ 2 * (U : ℝ) / 2)
  let CK : ℝ := |c| * CH
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun t =>
    (hcap (min t U)).mono (V.mono (min_le_left t U))
  have hK : StronglyAdapted V K := fun t => by
    exact stronglyMeasurable_const.mul (hH t)
  have hHbound (t : ℝ≥0) (omega : W) : ‖H t omega‖ ≤ CH := by
    exact norm_cappedComplexDoleansDadeExponentialCombination_le
      M bracket B C c R U (min t U) (min_le_right t U) omega
  have hKbound (t : ℝ≥0) (omega : W) : ‖K t omega‖ ≤ CK := by
    dsimp only [K, CK]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hHbound t omega) (abs_nonneg c)
  have hsum : Martingale
      (uniformAdaptedTwoMartingaleSmulProcess N B H K U n) V P :=
    martingale_uniformAdaptedTwoMartingaleSmulProcess
      hN hBmart hH hK CH CK hHbound hKbound U n
  have hH0meas : StronglyMeasurable (H 0) :=
    (hH 0).mono (V.le 0)
  have hH0int : Integrable (H 0) P := by
    refine Integrable.mono' (integrable_const CH)
      hH0meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun omega => hHbound 0 omega
  have hinitial : Martingale (fun _ => H 0) V P :=
    martingale_const_fun V P (hH 0) hH0int
  simpa only [cappedComplexGirsanovEulerProcess, H, K] using
    hinitial.add hsum

/-- The capped complex Euler process has an explicit grid-independent `L²`
bound whenever both real integrators have square-integrable terminal values.
The estimate holds at every observation time and requires no path continuity
of the Brownian integrator. -/
theorem eLpNorm_cappedComplexGirsanovEulerProcess_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R T : ℝ≥0) (hNT : MemLp (N T) 2 P)
    (hBT : MemLp (B T) 2 P) (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R T (n + 1) t) 2 P ≤
      cappedComplexGirsanovCoefficientBound c R T +
        2 * cappedComplexGirsanovCoefficientBound c R T *
          eLpNorm (N T - N 0) 2 P +
        2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
          eLpNorm (B T - B 0) 2 P := by
  let CH : ℝ≥0 := cappedComplexGirsanovCoefficientBound c R T
  let CK : ℝ≥0 :=
    cappedComplexGirsanovBrownianCoefficientBound c R T
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min s T) omega
  let J : ℝ≥0 → W → ℂ := fun s omega =>
    ((c : ℂ) * Complex.I) * H s omega
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun s =>
    (hcap (min s T)).mono (V.mono (min_le_left s T))
  have hJ : StronglyAdapted V J := fun s =>
    stronglyMeasurable_const.mul (hH s)
  have hHbound (s : ℝ≥0) (omega : W) : ‖H s omega‖ ≤ CH := by
    dsimp only [H, CH, cappedComplexGirsanovCoefficientBound]
    rw [Real.toNNReal_of_nonneg (Real.exp_pos _).le]
    simpa only [NNReal.coe_mul, NNReal.coe_mk] using
      norm_cappedComplexDoleansDadeExponentialCombination_le
        M bracket B C c R T (min s T) (min_le_right s T) omega
  have hJbound (s : ℝ≥0) (omega : W) : ‖J s omega‖ ≤ CK := by
    dsimp only [J]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    dsimp only [CK, cappedComplexGirsanovBrownianCoefficientBound]
    rw [Real.toNNReal_of_nonneg
      (mul_nonneg (abs_nonneg c) CH.coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hHbound s omega) (abs_nonneg c)
  have hinitialMeas : AEStronglyMeasurable (H 0) P :=
    ((hH 0).mono (V.le 0)).aestronglyMeasurable
  have hinitial : eLpNorm (H 0) 2 P ≤ CH := by
    calc
      eLpNorm (H 0) 2 P ≤
          P Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (CH : ℝ) :=
        eLpNorm_le_of_ae_bound
          (Filter.Eventually.of_forall fun omega => hHbound 0 omega)
      _ = CH := by simp
  have htransformMeas : AEStronglyMeasurable
      (uniformAdaptedTwoMartingaleSmulProcess
        N B H J T (n + 1) t) P :=
    ((martingale_uniformAdaptedTwoMartingaleSmulProcess
      hN hBmart hH hJ CH CK hHbound hJbound T (n + 1)).integrable t).1
  rw [congrFun
    (cappedComplexGirsanovEulerProcess_eq
      N M bracket B C c R T (n + 1)) t]
  change eLpNorm (H 0 +
    uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤ _
  calc
    eLpNorm (H 0 +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤
        eLpNorm (H 0) 2 P +
          eLpNorm
            (uniformAdaptedTwoMartingaleSmulProcess
              N B H J T (n + 1) t) 2 P :=
      eLpNorm_add_le hinitialMeas htransformMeas (by norm_num)
    _ ≤ CH +
          (2 * CH * eLpNorm (N T - N 0) 2 P +
            2 * CK * eLpNorm (B T - B 0) 2 P) :=
      add_le_add hinitial
        (eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
          hN hBmart T hNT hBT hH hJ CH CK hHbound hJbound n t)
    _ = CH + 2 * CH * eLpNorm (N T - N 0) 2 P +
          2 * CK * eLpNorm (B T - B 0) 2 P := by ring
    _ = cappedComplexGirsanovCoefficientBound c R T +
          2 * cappedComplexGirsanovCoefficientBound c R T *
            eLpNorm (N T - N 0) 2 P +
          2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
            eLpNorm (B T - B 0) 2 P := by rfl

/-- Adaptedness of the two inputs makes the complex Doléans exponential
adapted. -/
theorem stronglyAdapted_complexDoleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X Q : ℝ≥0 → W → ℂ}
    (hX : StronglyAdapted V X) (hQ : StronglyAdapted V Q) :
    StronglyAdapted V (complexDoleansDadeExponential X Q) := by
  intro t
  change StronglyMeasurable[V t]
    (Complex.exp ∘ (X t - (Q t / fun _ : W ↦ (2 : ℂ))))
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((hX t).sub ((hQ t).div stronglyMeasurable_const))

/-- Under the predictable Girsanov contract, the algebraic complex
Doleans exponential is stochastically continuous.  This formulation keeps
the original adapted totalized drift while borrowing path regularity from
its deterministic-time almost-everywhere continuous representative. -/
theorem GirsanovDensityData.tendstoInMeasure_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (a n)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c) r) := by
  have hMlim : TendstoInMeasure P (fun n => M (a n)) atTop (M r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_martingale_path omega).continuousAt.tendsto.comp ha
  have hBlim : TendstoInMeasure P (fun n => B (a n)) atTop (B r) :=
    StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha
  let combine : ℝ → ℝ → ℂ := fun m b =>
    (m : ℂ) + ((c * b : ℝ) : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hXlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombination M B c (a n)) atTop
      (complexMartingaleCombination M B c r) := by
    change TendstoInMeasure P (fun n omega =>
      combine (M (a n) omega) (B (a n) omega)) atTop
        (fun omega => combine (M r omega) (B r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun n => (hsm (a n)).aestronglyMeasurable)
      hMlim hBlim hcombine
  have hbracketLim : TendstoInMeasure P (fun n => bracket (a n)) atTop
      (bracket r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_monotone_bracket omega).1.continuousAt.tendsto.comp ha
  have htimeLim : TendstoInMeasure P
      (fun n => fun _ : W => (a n : ℝ)) atTop (fun _ => (r : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ => aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ =>
        (NNReal.continuous_coe.tendsto r).comp ha
  have hdriftLim := hdata.tendstoInMeasure_girsanovIntegratedDrift
    htheta hbracketTerminal hcross hB ha
  have hdriftMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovIntegratedDrift theta T (a n)) P :=
    (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable
  have hClim : TendstoInMeasure P
      (fun n omega => -girsanovIntegratedDrift theta T (a n) omega)
      atTop (fun omega => -girsanovIntegratedDrift theta T r omega) :=
    TendstoInMeasure.continuous_comp hdriftMeas hdriftLim continuous_neg
  let realPart : ℝ → ℝ → ℂ := fun q t =>
    (q : ℂ) - (c ^ 2 * t : ℝ)
  have hrealPart : Continuous realPart.uncurry := by
    dsimp only [realPart, Function.uncurry]
    fun_prop
  have hrealLim : TendstoInMeasure P (fun n omega =>
      realPart (bracket (a n) omega) (a n : ℝ)) atTop
      (fun omega => realPart (bracket r omega) (r : ℝ)) :=
    TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun _ => aestronglyMeasurable_const)
      hbracketLim htimeLim hrealPart
  let addCross : ℂ → ℝ → ℂ := fun q d =>
    q + ((2 * c * d : ℝ) : ℂ) * Complex.I
  have haddCross : Continuous addCross.uncurry := by
    dsimp only [addCross, Function.uncurry]
    fun_prop
  have hQlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c (a n))
      atTop
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r) := by
    change TendstoInMeasure P (fun n omega =>
      addCross (realPart (bracket (a n) omega) (a n : ℝ))
        (-girsanovIntegratedDrift theta T (a n) omega)) atTop
      (fun omega => addCross (realPart (bracket r omega) (r : ℝ))
        (-girsanovIntegratedDrift theta T r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => (((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hdata.adapted_bracket (a n)).mono
          (V.le (a n))).aestronglyMeasurable)).sub
            (Complex.continuous_ofReal.comp_aestronglyMeasurable
              aestronglyMeasurable_const))))
      (fun n => hdriftMeas n |>.neg)
      hrealLim hClim haddCross
  let finish : ℂ → ℂ → ℂ := fun x q => Complex.exp (x - q / 2)
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  change TendstoInMeasure P (fun n omega =>
    finish (complexMartingaleCombination M B c (a n) omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c
          (a n) omega)) atTop
    (fun omega => finish (complexMartingaleCombination M B c r omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r omega))
  exact TendstoInMeasure.continuous_comp₂
    (fun n => ((stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hBadapt c (a n)).mono
          (V.le (a n))).aestronglyMeasurable)
    (fun n => ((stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket
        (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
          htheta T).neg c (a n)).mono
            (V.le (a n))).aestronglyMeasurable)
    hXlim hQlim hfinish

/-- The algebraic complex exponential stopped at the Girsanov horizon is
integrable.  Its modulus is a bounded deterministic multiple of the stopped
real density. -/
theorem GirsanovDensityData.integrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (t : ℝ≥0) :
    Integrable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P := by
  have hEadapt := stronglyAdapted_complexDoleansDadeExponential
    (stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hB c)
    (stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket hC c)
  have hmeas : AEStronglyMeasurable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P :=
    ((hEadapt (min t T)).mono (V.le (min t T))).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  let k : ℝ := Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2)
  have hrhs : Integrable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega * k) P :=
    (hdata.martingale_densityProcess.integrable t).mul_const k
  apply hrhs.congr
  exact Filter.Eventually.of_forall fun omega => by
    change doleansDadeExponential M bracket (min t T) omega * k =
      ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega‖
    simpa only [k] using
      (norm_complexDoleansDadeExponential_combination
        M bracket B C c (min t T) omega).symm

/-- The complete stopped complex-exponential family is uniformly
integrable.  This supplies the Vitali input for passing deterministic-grid
martingale identities to their continuous-time limit. -/
theorem
    GirsanovDensityData.uniformIntegrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C) (c : ℝ) :
    UniformIntegrable (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) 1 P := by
  have hdensityUI : UniformIntegrable (fun t omega =>
      doleansDadeExponential M bracket (min t T) omega) 1 P := by
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic
        hdata.martingale_densityProcess T)
      (fun t => ⟨min t T, by
        simpa only [Set.mem_Iic] using min_le_right t T⟩)
    simpa only [min_eq_left (min_le_right _ T)] using hUI
  obtain ⟨N, hN⟩ := exists_nat_ge
    (Real.exp (c ^ 2 * (T : ℝ) / 2))
  have hmultiple : UniformIntegrable (fun t omega =>
      N • doleansDadeExponential M bracket (min t T) omega) 1 P :=
    StochasticCalculus.UniformIntegrable.nsmul_banach hdensityUI (by norm_num) N
  apply StochasticCalculus.UniformIntegrable.mono_norm_banach hmultiple
  · intro t
    have hEadapt := stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hB c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
    exact ((hEadapt (min t T)).mono
      (V.le (min t T))).aestronglyMeasurable
  · intro t omega
    rw [norm_complexDoleansDadeExponential_combination]
    have htime : c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2 ≤
        c ^ 2 * (T : ℝ) / 2 := by
      have htime' : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast min_le_right t T
      nlinarith [sq_nonneg c]
    have hexp : Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := Real.exp_le_exp.mpr htime
    have hdensityPos :=
      doleansDadeExponential_pos M bracket (min t T) omega
    calc
      doleansDadeExponential M bracket (min t T) omega *
          Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
          doleansDadeExponential M bracket (min t T) omega *
            Real.exp (c ^ 2 * (T : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hexp hdensityPos.le
      _ ≤ doleansDadeExponential M bracket (min t T) omega * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hdensityPos.le
      _ = ‖N • doleansDadeExponential M bracket (min t T) omega‖ := by
        rw [nsmul_eq_mul, norm_mul, norm_natCast, Real.norm_eq_abs,
          abs_of_pos hdensityPos]
        ring

/-- Stochastic continuity of the algebraic complex exponential is preserved
when its time parameter is stopped at the deterministic Girsanov horizon. -/
theorem
    GirsanovDensityData.tendstoInMeasure_stopAt_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min (a n) T)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min r T)) := by
  exact hdata.tendstoInMeasure_complexDoleans_neg_integratedDrift
    hB hsm hBadapt htheta hbracketTerminal hcross c
      (ha.min tendsto_const_nhds)

/-- The genuinely higher-order half of the canonical stochastic-Taylor
obligation.  Its one-cell summands satisfy
`norm_complexDoleansSecondOrderResidual_le`. -/
def GirsanovComplexDoleansHigherOrderCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- A scalar-majorant formulation of the higher-order stochastic-Taylor
obligation.  It exposes only the explicit nonnegative cellwise bound. -/
def GirsanovComplexDoleansHigherOrderBoundCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualBoundApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- Convergence in measure of the explicit nonnegative majorant closes the
complex higher-order residual. -/
theorem girsanovComplexDoleansHigherOrderCondition_of_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovComplexDoleansHigherOrderBoundCondition
      P M bracket B C T) :
    GirsanovComplexDoleansHigherOrderCondition P M bracket B C T := by
  intro c t
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas (h c t)
  · exact fun n omega =>
      complexDoleansHigherOrderResidualBoundApprox_nonneg
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega
  · exact fun n omega =>
      norm_complexDoleansHigherOrderResidualApprox_le_bound
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega

/-- The Challenge hypotheses discharge the entire higher-order half of the
complex stochastic-Taylor obligation. -/
theorem GirsanovDensityData.girsanovComplexDoleansHigherOrderBoundCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure) :
    GirsanovComplexDoleansHigherOrderBoundCondition P M bracket B
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z) T := by
  intro c t
  exact
    hdata.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
      hB hBmeas htheta hbracketTerminal c t

/-- Paste a complex martingale before a deterministic time to a bounded
past-measurable multiple of another martingale after that time. -/
def martingalePasteMul
    {W : Type*} (X Y : ℝ≥0 → W → ℂ) (H : W → ℂ) (s : ℝ≥0) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  if t ≤ s then X t omega else H omega * Y t omega

/-- Deterministic-time martingale pasting with an integrable measurable
multiplier.  The two pieces only have to agree at the pasting time. -/
theorem martingale_martingalePasteMul_of_integrable
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H)
    (hHYint : ∀ t, Integrable (fun omega ↦ H omega * Y t omega) P)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  have hpasteLeft {t : ℝ≥0} (hts : t ≤ s) :
      martingalePasteMul X Y H s t = X t := by
    funext omega
    simp only [martingalePasteMul, hts, ↓reduceIte]
  have hpasteRight {t : ℝ≥0} (hst : s ≤ t) :
      martingalePasteMul X Y H s t =
        fun omega ↦ H omega * Y t omega := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · exact (hpasteLeft (le_refl s)).trans hmatch.symm
    · funext omega
      simp only [martingalePasteMul, not_le.mpr hst', ↓reduceIte]
  have hpasteAdapt : StronglyAdapted V
      (martingalePasteMul X Y H s) := by
    intro t
    rcases le_total t s with hts | hst
    · rw [hpasteLeft hts]
      exact hX.stronglyMeasurable t
    · rw [hpasteRight hst]
      exact (hH.mono (V.mono hst)).mul (hY.stronglyMeasurable t)
  refine ⟨hpasteAdapt, fun i j hij ↦ ?_⟩
  rcases le_total j s with hjs | hsj
  · rw [hpasteLeft hjs, hpasteLeft (hij.trans hjs)]
    exact hX.condExp_ae_eq hij
  rcases le_total s i with hsi | his
  · rw [hpasteRight hsi, hpasteRight (hsi.trans hij)]
    have hpull := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      (hH.mono (V.mono hsi)) (hHYint j) (hY.integrable j)
    exact hpull.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
      (hY.condExp_ae_eq hij))
  · have hpullS := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      hH (hHYint j) (hY.integrable j)
    have hjRight := hpasteRight hsj
    have hsRight := hpasteRight (le_refl s)
    have hcondS : P[martingalePasteMul X Y H s j | V s] =ᵐ[P]
        martingalePasteMul X Y H s s := by
      rw [hjRight, hsRight]
      exact hpullS.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
        (hY.condExp_ae_eq hsj))
    rw [hpasteLeft (le_refl s)] at hcondS
    have htower := condExp_condExp_of_le (μ := P)
      (V.mono his) (V.le s) (f := martingalePasteMul X Y H s j)
    rw [hpasteLeft his]
    filter_upwards [htower, condExp_congr_ae hcondS,
      hX.condExp_ae_eq his] with omega htowerOmega hcongr hmart
    rw [← htowerOmega, hcongr, hmart]

/-- Bounded deterministic-time multipliers satisfy the integrability
premise of `martingale_martingalePasteMul_of_integrable`. -/
theorem martingale_martingalePasteMul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H) (K : ℝ)
    (hHbound : ∀ omega, ‖H omega‖ ≤ K)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  apply martingale_martingalePasteMul_of_integrable hX hY hH _ hmatch
  intro t
  exact (hY.integrable t).bdd_mul
    (hH.mono (V.le s)).aestronglyMeasurable
    (Filter.Eventually.of_forall hHbound)

/-- Fourier-increment form of the stochastic-exponential martingale
identity.  It is the exact stochastic-calculus input needed by the
characteristic-function proof of Girsanov: on each past event, the current
density weighted by the increment character evolves by the deterministic
Gaussian factor. -/
def GirsanovFourierIncrementCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W}, MeasurableSet[V s] A → ∀ c : ℝ,
    (∫ omega in A,
      doleansDadeExponential M bracket (min t T) omega •
        Complex.exp (((c * (X t omega - X s omega) : ℝ) : ℂ) *
          Complex.I) ∂P) =
      Complex.exp
          (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P

/-- The normalized complex exponential based at time `s`.  Before `s` this
is just the Girsanov density process; after `s` it tests the characteristic
function of the increment of `X`. -/
def girsanovFourierIncrementProcess
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ) (T s : ℝ≥0) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (doleansDadeExponential M bracket (min t T) omega : ℂ) *
    Complex.exp
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I +
        (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))

/-- Before its base time, the normalized Fourier-increment process is just
the stopped density process. -/
theorem girsanovFourierIncrementProcess_of_le_base
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hts : t ≤ s) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        (doleansDadeExponential M bracket (min t T) omega : ℂ) := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_left hts, tsub_eq_zero_of_le hts]
  simp only [sub_self, mul_zero, Complex.ofReal_zero, zero_mul,
    NNReal.coe_zero, zero_div, add_zero, Complex.exp_zero, mul_one]

/-- After its base time, a Fourier-increment process is a bounded
past-measurable multiple of the base-zero process. -/
theorem girsanovFourierIncrementProcess_of_base_le
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hst : s ≤ t) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        Complex.exp
            (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
              ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ))) *
          girsanovFourierIncrementProcess M bracket X T 0 c t omega := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_right hst]
  have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
  rw [hmin0, tsub_zero]
  rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← Complex.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  push_cast
  ring_nf

/-- Adaptedness of the density, bracket, and tested process makes every
normalized Fourier-increment process adapted. -/
theorem stronglyAdapted_girsanovFourierIncrementProcess
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket X : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X) (T s : ℝ≥0) (c : ℝ) :
    StronglyAdapted V (girsanovFourierIncrementProcess M bracket X T s c) := by
  intro t
  have hdensity : StronglyMeasurable[V t]
      (doleansDadeExponential M bracket (min t T)) :=
    (stronglyAdapted_doleansDadeExponential hM hbracket (min t T)).mono
      (V.mono (min_le_left _ _))
  have hdensityC : StronglyMeasurable[V t] (fun omega ↦
      (doleansDadeExponential M bracket (min t T) omega : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hdensity
  have hinc : StronglyMeasurable[V t]
      (fun omega ↦ X t omega - X (min t s) omega) :=
    (hX t).sub ((hX (min t s)).mono (V.mono (min_le_left _ _)))
  have hchar : StronglyMeasurable[V t] (fun omega ↦
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I
  exact hdensityC.mul (Complex.continuous_exp.comp_stronglyMeasurable
    (hchar.add stronglyMeasurable_const))

/-- Martingale form of the Fourier-increment input. -/
def GirsanovFourierIncrementMartingaleCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ s c, Martingale (girsanovFourierIncrementProcess M bracket X T s c) V P

/-- A stopped complex Doléans martingale supplies the base-zero Girsanov
Fourier martingale up to the horizon; after the horizon it is pasted to the
ordinary Brownian Fourier martingale. -/
theorem
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0} (c : ℝ)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hcomplex : Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : Martingale (brownianFourierIncrementProcess B T c) V P) :
    Martingale (girsanovFourierIncrementProcess M bracket X T 0 c) V P := by
  let E : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let Estop : ℝ≥0 → W → ℂ := fun t omega ↦ E (min t T) omega
  let Y := brownianFourierIncrementProcess B T c
  let H : W → ℂ := E T
  have hEstop : Martingale Estop V P := by
    simpa only [Estop, E] using hcomplex
  have hY : Martingale Y V P := by simpa only [Y] using hBrownian
  have hHmeas : StronglyMeasurable[V T] H := by
    simpa only [H, Estop, min_self] using hEstop.stronglyMeasurable T
  have hHint : Integrable H P := by
    simpa only [H, Estop, min_self] using hEstop.integrable T
  have hHYint (t : ℝ≥0) :
      Integrable (fun omega ↦ H omega * Y t omega) P := by
    apply hHint.mul_bdd
    · exact ((hY.stronglyMeasurable t).mono
        (V.le t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega ↦ by
        rw [show ‖Y t omega‖ =
            Real.exp (((t - min t T : ℝ≥0) : ℝ) * c ^ 2 / 2) by
          exact norm_brownianFourierIncrement B c (min t T) t omega]
  have hmatch : (fun omega ↦ H omega * Y T omega) = Estop T := by
    funext omega
    simp only [H, Y, Estop, min_self, brownianFourierIncrementProcess,
      brownianFourierIncrement_self, mul_one]
  have hpaste : Martingale (martingalePasteMul Estop Y H T) V P :=
    martingale_martingalePasteMul_of_integrable
      hEstop hY hHmeas hHYint hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T 0 c)
  intro t
  filter_upwards [hXzero] with omega hzero
  by_cases htT : t ≤ T
  · have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, Estop,
        min_eq_left htT]
    rw [hpasteEq]
    change complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold girsanovFourierIncrementProcess
    rw [min_eq_left htT]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_left htT]
    congr 2
    push_cast
    ring
  · have hTt : T ≤ t := le_of_not_ge htT
    have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E T omega * brownianFourierIncrement B c T t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, H, Y,
        brownianFourierIncrementProcess, min_eq_right hTt]
    rw [hpasteEq]
    change complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) T omega *
      brownianFourierIncrement B c T t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold brownianFourierIncrement girsanovFourierIncrementProcess
    rw [min_eq_right hTt]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_right hTt]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    rw [NNReal.coe_sub hTt]
    push_cast
    ring_nf

/-- It suffices to construct the complex exponential martingale at base
time zero.  Every other base time is obtained by deterministic-time pasting:
the density martingale is used before the base, and a bounded
past-measurable multiple of the base-zero martingale is used afterward. -/
theorem girsanovFourierIncrementMartingaleCondition_of_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hzero : ∀ c, Martingale
      (girsanovFourierIncrementProcess M bracket X T 0 c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  intro s c
  let Z : ℝ≥0 → W → ℂ := fun t omega ↦
    (doleansDadeExponential M bracket (min t T) omega : ℂ)
  let Y := girsanovFourierIncrementProcess M bracket X T 0 c
  let H : W → ℂ := fun omega ↦
    Complex.exp
      (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ)))
  have hZ : Martingale Z V P := by
    simpa only [Z, Complex.ofRealCLM_apply] using
      Martingale.comp_continuousLinearMap hdensity Complex.ofRealCLM
  have hH : StronglyMeasurable[V s] H := by
    have hinc : StronglyMeasurable[V s] (fun omega ↦
        X s omega - X 0 omega) :=
      (hX s).sub ((hX 0).mono (V.mono bot_le))
    exact Complex.continuous_exp.comp_stronglyMeasurable
      (((Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I).add
          stronglyMeasurable_const).neg
  let K : ℝ := Real.exp (-(c ^ 2 * (s : ℝ) / 2))
  have hHbound (omega : W) : ‖H omega‖ ≤ K := by
    dsimp only [H, K]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_sub, mul_one, neg_zero, zero_add, le_refl]
  have hmatch : (fun omega ↦ H omega * Y s omega) = Z s := by
    have hright := girsanovFourierIncrementProcess_of_base_le
      M bracket X T s s c (le_refl s)
    have hleft := girsanovFourierIncrementProcess_of_le_base
      M bracket X T s s c (le_refl s)
    exact hright.symm.trans hleft
  have hpaste : Martingale (martingalePasteMul Z Y H s) V P :=
    martingale_martingalePasteMul hZ (hzero c) hH K hHbound hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T s c)
  intro t
  exact Filter.Eventually.of_forall fun omega ↦ by
    by_cases hts : t ≤ s
    · rw [show martingalePasteMul Z Y H s t omega = Z t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_le_base
        M bracket X T s t c hts).symm omega
    · have hst : s ≤ t := le_of_not_ge hts
      rw [show martingalePasteMul Z Y H s t omega = H omega * Y t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_base_le
        M bracket X T s t c hst).symm omega

/-- A family of stopped complex Doléans martingales, together with the
ordinary post-horizon Brownian Fourier martingales, yields the full
Girsanov Fourier family. -/
theorem
    girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hcomplex : ∀ c, Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : ∀ c,
      Martingale (brownianFourierIncrementProcess B T c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  apply girsanovFourierIncrementMartingaleCondition_of_zero
    hM hbracket hX hdensity
  intro c
  exact
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
      c hM hbracket hX hXeq hXzero (hcomplex c) (hBrownian c)

/-- The complex exponential martingale family implies the eventwise
Fourier-increment identity used by the Girsanov endpoint. -/
theorem girsanovFourierIncrementCondition_of_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovFourierIncrementMartingaleCondition P V M bracket X T) :
    GirsanovFourierIncrementCondition P V M bracket X T := by
  intro s t hst A hA c
  let v : ℂ := (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))
  let char : W → ℂ := fun omega ↦
    (((c * (X t omega - X s omega) : ℝ) : ℂ) * Complex.I)
  have hmartEq := (h s c).setIntegral_eq hst hA
  have hmartEq' :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
      ∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
          Complex.exp (char omega + v) ∂P := by
    simpa only [girsanovFourierIncrementProcess, min_self, sub_self,
      zero_mul, mul_zero, Complex.ofReal_zero, zero_mul, tsub_self, NNReal.coe_zero,
      zero_div, add_zero, Complex.exp_zero, mul_one, min_eq_right hst,
      char, v] using hmartEq
  change (∫ omega in A,
      (doleansDadeExponential M bracket (min t T) omega : ℝ) •
        Complex.exp (char omega) ∂P) =
    Complex.exp (-v) *
      ∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P
  calc
    (∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) ∂P) =
        ∫ omega in A, Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v)) ∂P := by
      apply setIntegral_congr_fun (V.le s A hA)
      intro omega _
      change (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) =
        Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v))
      rw [Complex.real_smul]
      calc
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega) =
            (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              Complex.exp (-v + (char omega + v)) := by
          congr 2
          ring
        _ = (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              (Complex.exp (-v) * Complex.exp (char omega + v)) := by
          rw [Complex.exp_add]
        _ = Complex.exp (-v) *
              ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
                Complex.exp (char omega + v)) := by
          ring
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v) ∂P := by
      rw [integral_const_mul]
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
      rw [hmartEq']

/-- The Fourier-increment stochastic-exponential identity gives the full
pre-Brownian law under the terminal Girsanov measure.  In particular this
route needs neither a separate integrability assumption for the shifted
process nor an all-path continuity representative. -/
theorem GirsanovDensityData.isPreBrownianReal_of_fourierIncrementCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket X T) :
    IsPreBrownianReal X (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hzeroQ : X 0 =ᵐ[Q] fun _ ↦ 0 :=
    h.mutuallyAbsolutelyContinuous.1.ae_eq hzero
  apply isPreBrownianReal_of_map_restrict_increment_eq_of_ae_zero
    hadapt hzeroQ
  intro s t hst A hA
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc Q := by
    exact ((((hadapt t).mono (V.le t)).aemeasurable).sub
      (((hadapt s).mono (V.le s)).aemeasurable)).mono_ac
        (show Q ≪ P from girsanovMeasure_absolutelyContinuous P M bracket T)
  have hincR : AEMeasurable inc (Q.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  let : IsFiniteMeasure (Q A • gaussianReal 0 (t - s)) :=
    (gaussianReal 0 (t - s)).smul_finite (measure_ne_top Q A)
  apply Measure.ext_of_charFun
  funext c
  rw [charFun_apply_real]
  change (∫ x, Complex.exp ((c : ℂ) * (x : ℂ) * Complex.I)
    ∂((Q.restrict A).map inc)) = _
  rw [integral_map hincR (by fun_prop)]
  let f : W → ℂ := fun omega ↦
    Complex.exp ((c : ℂ) * (inc omega : ℂ) * Complex.I)
  have hf : StronglyMeasurable[V t] f := by
    have hincStrong : StronglyMeasurable[V t] inc :=
      (hadapt t).sub ((hadapt s).mono (V.mono hst))
    apply Complex.continuous_exp.comp_stronglyMeasurable
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hincStrong.const_mul c)).mul_const Complex.I
  have hfint : Integrable f Q :=
    (integrable_const (1 : ℝ)).mono
      ((hf.mono (V.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [f, ← Complex.ofReal_mul,
          Complex.norm_exp_ofReal_mul_I, norm_one] using (le_refl (1 : ℝ)))
  have hAt : MeasurableSet[V t] A := V.mono hst A hA
  have hcurrent :=
    h.setIntegral_girsanovMeasure_eq_densityProcess_smul hf hfint hAt
  have hmass :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
        (Q A).toReal := by
    have honeMeas : StronglyMeasurable[V s] (fun _ : W ↦ (1 : ℂ)) := by
      fun_prop
    have honeInt : Integrable (fun _ : W ↦ (1 : ℂ)) Q :=
      integrable_const 1
    have hone := h.setIntegral_girsanovMeasure_eq_densityProcess_smul
      honeMeas honeInt hA
    calc
      (∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
          ∫ omega in A,
            doleansDadeExponential M bracket (min s T) omega • (1 : ℂ) ∂P := by
        apply setIntegral_congr_fun (V.le s A hA)
        intro omega _
        simp only [Complex.real_smul, mul_one]
      _ = ∫ _omega in A, (1 : ℂ) ∂Q := hone.symm
      _ = (Q A).toReal := by
        rw [setIntegral_const]
        simp only [measureReal_def, Complex.real_smul, mul_one]
  have hfourier' :
      (∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P) =
        Complex.exp
            (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
          ∫ omega in A,
            (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
    simpa only [f, inc, Complex.ofReal_mul] using hfourier hst hA c
  change (∫ omega in A, f omega ∂Q) =
    charFun (Q A • gaussianReal 0 (t - s)) c
  have hcharSmul : charFun (Q A • gaussianReal 0 (t - s)) c =
      (Q A).toReal • charFun (gaussianReal 0 (t - s)) c := by
    simp only [charFun_apply_real]
    rw [integral_smul_measure]
  rw [hcurrent, hfourier', hmass, hcharSmul, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
    Complex.real_smul]
  rw [mul_comm]
  congr 1
  push_cast
  ring

/-- Predictable-drift specialization of the Fourier Girsanov endpoint.
Predictability supplies shifted-process adaptedness, while almost-sure
normalization of the driver suffices at time zero. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  have hshiftAdapt : StronglyAdapted V
      (girsanovShiftedBrownian B theta T) :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt htheta
  have hshiftZero : girsanovShiftedBrownian B theta T 0 =ᵐ[P]
      fun _ ↦ 0 := by
    filter_upwards [hBzero] with omega homega
    simp only [girsanovShiftedBrownian, homega, girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  exact h.isPreBrownianReal_of_fourierIncrementCondition
    hshiftAdapt hshiftZero hfourier

/-- Raw-natural-filtration version of the Fourier endpoint.  The density
data and predictable drift are transported internally to the right
continuation, avoiding a right-continuity assumption on the natural
filtration supplied by the caller. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hfourier : GirsanovFourierIncrementCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  have hdata : GirsanovDensityData P (Filtration.rightCont V) M bracket T :=
    h.rightCont
  apply hdata.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
  · exact StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  · exact hB.eval_zero_ae_eq_zero
  · exact StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  · exact hfourier

/-- Predictable-drift specialization with the Fourier input presented as a
family of complex martingales. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourierMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hmart : GirsanovFourierIncrementMartingaleCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier hBadapt hBzero htheta
    (girsanovFourierIncrementCondition_of_martingale hmart)

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint from true martingality of the stopped
algebraic complex Doléans family.  This is the common final assembly for
both local-martingale and deterministic-grid constructions. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hcomplex : ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u omega => -girsanovIntegratedDrift theta T u omega) c)
        (min t T) omega)
      (Filtration.rightCont (Filtration.natural B hsm)) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  let X := girsanovShiftedBrownian B theta T
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hX : StronglyAdapted (Filtration.rightCont V) X :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt hthetaR
  have hXeq (t : ℝ≥0) (omega : W) :
      X t omega = B t omega - C (min t T) omega := by
    change B t omega + girsanovIntegratedDrift theta T t omega =
      B t omega - -girsanovIntegratedDrift theta T (min t T) omega
    rw [sub_neg_eq_add]
    congr 1
    unfold girsanovIntegratedDrift
    rw [min_eq_left (min_le_right t T)]
  have hXzero : X 0 =ᵐ[P] fun _ => 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simp only [X, girsanovShiftedBrownian, homega,
      girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket X T := by
    apply girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
      hdataR.adapted_martingale hdataR.adapted_bracket hX hXeq hXzero
      hdataR.martingale_densityProcess
    · simpa only [C, V] using hcomplex
    · intro c
      exact martingale_brownianFourierIncrementProcess_rightCont_natural
        hB hsm T c
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
      hsm hB htheta
  exact girsanovFourierIncrementCondition_of_martingale hmart

section PredictableIntegral

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- A continuous modification of the natural Itô integral has the same
completed-cell quadratic variation as the selected representative.  This is
the representative bridge needed before applying the process-level Novikov
theorem. -/
theorem IsContinuousProcessModification.hasQuadraticVariationBeforeStop_naturalIto
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P) :
    HasQuadraticVariationBeforeStopProcessInProbability M
      (predictableQuadraticVariation hsm U) P := by
  let N : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  intro t a
  have hNM (b : ℝ≥0) (n : ℕ) :
      quadraticVariationBeforeStopApprox N t (n + 1) b =ᵐ[P]
        quadraticVariationBeforeStopApprox M t (n + 1) b := by
    have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    filter_upwards [hgrid] with omega homega
    unfold quadraticVariationBeforeStopApprox
    apply Finset.sum_congr rfl
    intro i hi
    simp only [N]
    rw [homega n (i + 1), homega n i]
  by_cases ha : a ≤ t
  · exact (quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t a ha).congr_left (hNM a)
  · have hN := quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t t (le_refl t)
    have hsource (n : ℕ) :
        quadraticVariationBeforeStopApprox N t (n + 1) t =ᵐ[P]
          quadraticVariationBeforeStopApprox M t (n + 1) a := by
      filter_upwards [hNM t n] with omega hEq
      calc
        quadraticVariationBeforeStopApprox N t (n + 1) t omega =
            quadraticVariationBeforeStopApprox M t (n + 1) t omega := hEq
        _ = quadraticVariationBeforeStopApprox M t (n + 1) a omega := by
          have hmin := quadraticVariationBeforeStopApprox_min_horizon
            M t a (n + 1) omega
          rw [min_eq_left (le_of_not_ge ha)] at hmin
          exact hmin.symm
    simpa only [min_self, min_eq_left (le_of_not_ge ha)] using
      hN.congr_left hsource

end PredictableIntegral

end StochasticCalculus
