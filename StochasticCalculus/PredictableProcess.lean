/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.FubiniLift
import StochasticCalculus.WienerIntegral
import Mathlib.Probability.Process.Predictable

/-!
# Predictable processes in L²

The Itô integral is defined on *predictable* integrands: processes whose value at time `t` is
measurable with respect to the filtration just before `t`.  On the product space `ℝ≥0 × Ω` with
measure `λ ⊗ P`, these are `L²` functions measurable for the predictable σ-algebra
`𝓕.predictable`.  The elementary predictable processes `1_{(a, b]} ⊗ Z` (a time indicator times
an `𝓕 a`-measurable random variable) generate this σ-algebra; the Itô isometry and density
arguments in `ElementaryIto` and `PredictableDensity` are built from them.

Deterministic `L²` functions embed as constant-in-ω predictable processes via
`deterministicPredictableEmbedding`.  The predictable projection `predictableProjection` is the
`L²` conditional expectation onto `𝓕.predictable`, and `filtrationCondExpL2` is the pointwise-
in-time version `E[F | 𝓕ₜ]`, identified with Mathlib's `condExp` by
`filtrationCondExpL2_ae_eq_condExp`.

## Main definitions

* `TimeProcessL2`, `PredictableProcessL2`: the `L²` process types on the product space;
* `deterministicTimeEmbedding`, `deterministicPredictableEmbedding`: embed deterministic `L²`
  functions as constant-in-ω time processes;
* `iocIndicator`: the indicator `1_{(a, b]}` as an `L²` function;
* `elementaryPredictable`: adapted elementary step functions `1_{(a, b]} ⊗ Z`;
* `adaptedOne`: the constant process `1_{(0, t]} ⊗ 1`;
* `predictableProjection`: `L²` projection onto the predictable σ-algebra via `condExpL2`;
* `filtrationCondExpL2`: timewise `L²` conditional expectation `E[F | 𝓕ₜ]`;
* `expectationL2`: the constant `L²` representative of `E[F]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

recall MeasureTheory.Lp.toLp_coeFn {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] (f : Lp E p μ) (hf : MemLp (f : α → E) p μ) :
    hf.toLp (f : α → E) = f

recall MeasureTheory.MemLp.condExpL2_ae_eq_condExp
    {α : Type u_1} {E : Type u_3} {𝕜 : Type u_4} [RCLike 𝕜]
    {m m₀ : MeasurableSpace α} {μ : Measure α} {f : α → E}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [InnerProductSpace 𝕜 E] (hm : m ≤ m₀) (hf : MemLp f 2 μ)
    [IsFiniteMeasure μ] :
    (condExpL2 E 𝕜 hm hf.toLp : α → E) =ᵐ[μ] μ[f | m]

recall MeasureTheory.AEStronglyMeasurable.prodMk_left
    {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {X : Type u_4} [TopologicalSpace X]
    [SFinite ν] {f : α × β → X} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => f (x, y)) ν

recall MeasureTheory.MemLp.integrable_sq
    {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ

recall MeasureTheory.Integrable.prod_right_ae
    {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [SFinite ν] [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν

recall MeasureTheory.memLp_two_iff_integrable_sq
    {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ

recall MeasureTheory.integrableOn_Lp_of_measure_ne_top
    {α : Type u_1} {mα : MeasurableSpace α} {μ : Measure α}
    {E : Type u_4} [NormedAddCommGroup E] {p : ENNReal} {s : Set α}
    (f : Lp E p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) :
    IntegrableOn (f : α → E) s μ

recall MeasureTheory.setIntegral_prod
    {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [SFinite ν] [NormedSpace ℝ E] [SFinite μ]
    (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ

recall MeasureTheory.integral_condExpL2_eq
    {α : Type u_1} {E' : Type u_3} {𝕜 : Type u_4} [RCLike 𝕜]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedSpace ℝ E'] {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) :
    ∫ x in s, (condExpL2 E' 𝕜 hm f : α → E') x ∂μ = ∫ x in s, f x ∂μ

recall MeasureTheory.measurableSet_predictable_Ioc_prod
    {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι m} (i j : ι) {s : Set Ω}
    (hs : MeasurableSet[𝓕 i] s) :
    MeasurableSet[𝓕.predictable] (Set.Ioc i j ×ˢ s)

recall MeasureTheory.Measure.prod_prod
    {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] (s : Set α) (t : Set β) :
    (μ.prod ν) (s ×ˢ t) = μ s * ν t

recall ProbabilityTheory.IsPreBrownianReal.indepFun_shift
    {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ}
    {P : Measure Ω} (hB : IsPreBrownianReal B P) (t₀ : NNReal) :
    (fun ω (t : NNReal) => B (t₀ + t) ω - B t₀ ω) ⟂ᵢ[P]
      fun ω (t : Set.Iic t₀) => B (↑t) ω

recall MeasureTheory.Filtration.natural_eq_comap
    {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω}
    {β : ι → Type u_3} [(i : ι) → TopologicalSpace (β i)]
    [∀ i, TopologicalSpace.MetrizableSpace (β i)]
    [mβ : (i : ι) → MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    [Preorder ι] (u : (i : ι) → Ω → β i)
    (hum : ∀ i, StronglyMeasurable (u i)) (i : ι) :
    (Filtration.natural u hum) i =
      MeasurableSpace.comap (fun ω (j : Set.Iic i) => u (↑j) ω) inferInstance

recall ProbabilityTheory.IndepFun_iff_Indep
    {Ω : Type u_1} {β : Type u_3} {γ : Type u_4}
    {_mΩ : MeasurableSpace Ω} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    IndepFun f g μ ↔
      Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ

recall ProbabilityTheory.indep_of_indep_of_le_right
    {Ω : Type u_1} {m₁ m₂ m₃ _mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indep m₁ m₃ μ

recall ProbabilityTheory.IndepFun.comp
    {Ω : Type u_1} {β : Type u_6} {β' : Type u_7}
    {γ : Type u_8} {γ' : Type u_9}
    {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}
    {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'}
    {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) μ

recall ProbabilityTheory.IndepFun.congr
    {Ω : Type u_1} {β : Type u_6} {β' : Type u_7}
    {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'}
    (hfg : IndepFun f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    IndepFun f' g' μ

recall ProbabilityTheory.IndepFun.integrable_mul
    {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : Type u_5} [TopologicalSpace E] [ContinuousENorm E] [Mul E]
    [ContinuousMul E] [ENormSMulClass E E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {X Y : Ω → E}
    (hXY : IndepFun X Y μ) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ

recall ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral
    {Ω : Type u_1} {𝕜 : Type u_5} [RCLike 𝕜]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → 𝕜}
    (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y]

recall MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp
    {α : Type u_2} {β : Type u_3} {δ : Type u_4}
    {m0 : MeasurableSpace α} [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} {g g' : β → δ}
    (hf : Measure.QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') :
    g ∘ f =ᵐ[μ] g' ∘ f

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Square-integrable real processes on nonnegative time × sample space. -/
abbrev TimeProcessL2 (P : Measure W) :=
  Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)

omit [CompleteSpace W] [BorelSpace W] in
/-- A product-`L²` representative has an `L²(P)` time section for almost every time.
The exceptional null set may depend on the representative, so this does not define evaluation
of a product-`L²` class at any prescribed time. -/
theorem memLp_timeSection_ae (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, MemLp (fun ω ↦ U (t, ω)) 2 P := by
  have hmeas := (Lp.memLp U).aestronglyMeasurable.prodMk_left
  have hint := (Lp.memLp U).integrable_sq.prod_right_ae
  filter_upwards [hmeas, hint] with t hmt hit
  exact (memLp_two_iff_integrable_sq hmt).2 hit

/-- The predictable `L²` processes associated to a filtration. -/
abbrev PredictableProcessL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  lpMeas ℝ ℝ 𝓕.predictable 2 (nonnegativeLebesgueMeasure.prod P)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- The predictable sigma-algebra is contained in the ambient product sigma-algebra. -/
theorem predictable_le_prod (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (𝓕.le 0 A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (𝓕.le t A hA)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The time coordinate is measurable from the predictable sigma-algebra. -/
theorem measurable_fst_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Measurable (ℝ≥0 × W) ℝ≥0 𝓕.predictable inferInstance Prod.fst := by
  apply measurable_of_Iic
  intro t
  have hset : Prod.fst ⁻¹' Set.Iic t =
      ({0} ×ˢ (Set.univ : Set W)) ∪ (Set.Ioc 0 t ×ˢ Set.univ) := by
    ext ⟨s, w⟩
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
    constructor
    · intro hst
      rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · exact Or.inl hs.symm
      · exact Or.inr ⟨hs, hst⟩
    · rintro (hs | hs)
      · subst s
        exact (zero_le : (0 : ℝ≥0) ≤ t)
      · exact hs.2
  rw [hset]
  exact (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
    (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ)

/-- Pull a deterministic time integrand back to the time--sample product along `Prod.fst`.
This is an isometry because `P` is a probability measure. -/
noncomputable def deterministicTimeEmbedding :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] TimeProcessL2 P :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic time integrand is measurably predictable. -/
theorem deterministicTimeEmbedding_aestronglyMeasurable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    AEStronglyMeasurable[𝓕.predictable]
      (deterministicTimeEmbedding (P := P) f : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := by
  have hcomp : StronglyMeasurable[𝓕.predictable]
      ((f : ℝ≥0 → ℝ) ∘ Prod.fst) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_fst_predictable 𝓕)
  exact hcomp.aestronglyMeasurable.congr
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst).symm

/-- The linear-isometric inclusion of deterministic square-integrable time functions into
predictable product-space processes. -/
noncomputable def deterministicPredictableEmbedding
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] PredictableProcessL2 𝓕 P where
  toFun f := ⟨deterministicTimeEmbedding (P := P) f,
    deterministicTimeEmbedding_aestronglyMeasurable 𝓕 f⟩
  map_add' f g := Subtype.ext (map_add (deterministicTimeEmbedding (P := P)) f g)
  map_smul' c f := Subtype.ext (map_smul (deterministicTimeEmbedding (P := P)) c f)
  norm_map' f := (deterministicTimeEmbedding (P := P)).norm_map f

omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic predictable integrand represents the function `(t, ω) ↦ f t`. -/
theorem deterministicPredictableEmbedding_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (deterministicPredictableEmbedding (P := P) 𝓕 f : (ℝ≥0 × W) → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P] (f : ℝ≥0 → ℝ) ∘ Prod.fst :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_fst

/-! ### Adapted elementary processes -/

/-- Pointwise representative of the one-step process `1_(a,b] Z`. -/
noncomputable def elementaryRepresentative (_𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (a b : ℝ≥0) (Z : W → ℝ) (p : ℝ≥0 × W) : ℝ :=
  if p.1 ∈ Set.Ioc a b then Z p.2 else 0

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- If `Z` is `𝓕_a`-measurable, then `(t, ω) ↦ 1_(a,b](t) Z(ω)` is predictable. -/
theorem stronglyMeasurable_elementaryRepresentative
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓕 a] Z) :
    StronglyMeasurable[𝓕.predictable] (elementaryRepresentative 𝓕 a b Z) := by
  apply Measurable.stronglyMeasurable
  apply measurable_of_Iic
  intro c
  by_cases hc : 0 ≤ c
  · have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        (Set.Ioc a b ×ˢ (Z ⁻¹' Set.Ioi c))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte,
          Set.mem_Iic, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, true_and, not_lt]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte,
          Set.mem_Iic, hc, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi,
          false_and, not_false_eq_true]
    rw [hset]
    exact (measurableSet_predictable_Ioc_prod a b
      (hZ.measurable measurableSet_Ioi)).compl
  · have hc' : c < 0 := lt_of_not_ge hc
    have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        Set.Ioc a b ×ˢ (Z ⁻¹' Set.Iic c) := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte,
          Set.mem_Iic, Set.mem_prod, true_and]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte,
          Set.mem_Iic, Set.mem_prod, false_and, iff_false, not_le, hc']
    rw [hset]
    exact measurableSet_predictable_Ioc_prod a b (hZ.measurable measurableSet_Iic)

/-- The scalar time indicator `1_(a,b]` as an `L²` function. -/
noncomputable def iocIndicator (a b : ℝ≥0) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  indicatorConstLp 2 measurableSet_Ioc
    (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)

/-- The predictable `L²` class represented by `(t, ω) ↦ 1_(a,b](t) Z(ω)` for an
`𝓕_a`-measurable square-integrable coefficient `Z`. -/
noncomputable def elementaryPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : PredictableProcessL2 𝓕 P := by
  let hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  let Zm : W → ℝ := hZ.mk (Z : W → ℝ)
  let H : ℝ≥0 × W → ℝ := elementaryRepresentative 𝓕 a b Zm
  let V : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
    tensor (iocIndicator a b) (Z : Lp ℝ 2 P)
  have hV : (V : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] H := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
          (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
    have hZm : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (Z : W → ℝ) p.2 = Zm p.2 :=
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hZ.ae_eq_mk
    filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg, hZm]
      with p hp hg' hZm'
    rw [hp, hg', hZm']
    by_cases ht : p.1 ∈ Set.Ioc a b <;>
      simp [H, elementaryRepresentative, ht]
  exact ⟨V,
    (stronglyMeasurable_elementaryRepresentative 𝓕 a b hZ.stronglyMeasurable_mk)
      |>.aestronglyMeasurable.congr hV.symm⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Forgetting predictability, an elementary process is the product-space tensor
`1_(a,b] ⊗ Z`. -/
theorem elementaryPredictable_coeLp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P) =
      tensor (iocIndicator a b) (Z : RandomL2 P) := rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A pointwise representative of an elementary predictable process. -/
theorem elementaryPredictable_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      fun p => if p.1 ∈ Set.Ioc a b then (Z : W → ℝ) p.2 else 0 := by
  change (tensor (iocIndicator a b) (Z : Lp ℝ 2 P) : ℝ≥0 × W → ℝ) =ᵐ[_] _
  have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg]
    with p hp hg'
  rw [hp, hg']
  by_cases ht : p.1 ∈ Set.Ioc a b <;> simp [ht]

/-- The constant coefficient `1`, regarded as an `𝓕_a`-measurable `L²(P)` random variable. -/
noncomputable def adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨Lp.const 2 P (1 : ℝ),
    aestronglyMeasurable_const.congr (Lp.coeFn_const 2 P (1 : ℝ)).symm⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- The one-step process with constant coefficient `1` on `(0,t]` is the deterministic
predictable embedding of `intervalIndicator t`. -/
theorem elementaryPredictable_adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    elementaryPredictable (P := P) 𝓕 0 t (adaptedOne (P := P) 𝓕 0) =
      deterministicPredictableEmbedding 𝓕 (intervalIndicator t) := by
  apply Subtype.ext
  rw [elementaryPredictable_coeLp]
  apply Lp.ext
  have hOne : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedOne (P := P) 𝓕 0 : W → ℝ) p.2 = 1 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_const 2 P (1 : ℝ))
  filter_upwards [coeFn_tensor (iocIndicator 0 t)
      (adaptedOne (P := P) 𝓕 0 : RandomL2 P),
    hOne, deterministicPredictableEmbedding_coeFn 𝓕 (intervalIndicator t)]
      with p hp hOnep hdet
  rw [hp, hOnep, hdet, Function.comp_apply, mul_one]
  rfl

/-- Orthogonal projection onto predictable time-space processes.  This is Mathlib's `L²`
conditional expectation with respect to the predictable sigma-algebra. -/
def predictableProjection (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    TimeProcessL2 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  condExpL2 ℝ ℝ (predictable_le_prod 𝓕)

omit [CompleteSpace W] [BorelSpace W] in
/-- Predictable projection preserves integrals over predictable rectangles
`(a, b] × A` with `A ∈ 𝓕_a`.  This is the product-space conditional-expectation identity
available without choosing pointwise time sections. -/
theorem integral_predictableProjection_Ioc
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (a b : ℝ≥0) {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∫ t in Set.Ioc a b, ∫ ω in A,
        (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure =
      ∫ t in Set.Ioc a b, ∫ ω in A, U (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure := by
  let μ := nonnegativeLebesgueMeasure.prod P
  have hrect : μ (Set.Ioc a b ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hQ := integrableOn_Lp_of_measure_ne_top
    (predictableProjection 𝓕 U : TimeProcessL2 P)
    fact_one_le_two_ennreal.elim hrect
  have hU := integrableOn_Lp_of_measure_ne_top
    U fact_one_le_two_ennreal.elim hrect
  rw [← setIntegral_prod _ hQ, ← setIntegral_prod _ hU]
  exact integral_condExpL2_eq (predictable_le_prod 𝓕) U
    (measurableSet_predictable_Ioc_prod a b hA) hrect

/-- Conditional expectation at time `t`, regarded again as an ambient `L²(P)` random variable. -/
def filtrationCondExpL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    RandomL2 P →L[ℝ] RandomL2 P :=
  (lpMeas ℝ ℝ (𝓕 t) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (𝓕.le t))

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The ambient representative of `filtrationCondExpL2` agrees almost everywhere with
Mathlib's function-valued conditional expectation. -/
theorem filtrationCondExpL2_ae_eq_condExp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P] P[(F : W → ℝ) | 𝓕 t] := by
  simpa only [filtrationCondExpL2, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Lp.toLp_coeFn] using
    (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le t)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Timewise `L²` conditional expectation is contractive. -/
theorem norm_filtrationCondExpL2_le
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    ‖filtrationCondExpL2 𝓕 t F‖ ≤ ‖F‖ :=
  norm_condExpL2_coe_le (𝓕.le t) F

/-- The constant `L²` representative of the expectation of `F`. -/
def expectationL2 (F : RandomL2 P) : RandomL2 P :=
  Lp.const 2 P (∫ ω, F ω ∂P)


end StochasticCalculus
