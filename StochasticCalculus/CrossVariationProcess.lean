/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
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
# Cross-variation contracts and convergence in measure

The cross-variation-in-probability contract for a pair of processes, the
fixed-time convergence of pre-Brownian evaluations, and the closure of
convergence in measure under continuous maps, sums, products and complex
scalars.  The file also records that a pre-Brownian law is determined by its
restricted increment laws, and that adaptedness and strong predictability
are monotone under enlargement of the filtration.
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

end StochasticCalculus
