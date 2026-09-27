/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.ItoConstruction
import Mathlib.Probability.Martingale.Basic

/-!
# The natural Itô integral as an L²-valued process

This file gives the quotient/a.e. layer of the time-indexed integral.  A
predictable process is cut off on `(0,t]` inside predictable product `L²`, and
the existing terminal-value Itô isometry is applied to that cutoff.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- The product-space time frame `(0,t] × Ω`. -/
def predictableTimeFrame (t : ℝ≥0) : Set (ℝ≥0 × W) :=
  Set.Ioc 0 t ×ˢ Set.univ

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The initial time frame is measurable for the predictable sigma-algebra. -/
theorem measurableSet_predictableTimeFrame
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    MeasurableSet[𝓕.predictable] (predictableTimeFrame (W := W) t) := by
  exact measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restrict a predictable product-`L²` process to the initial time frame `(0,t]`. -/
noncomputable def predictableTimeRestrict
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) : PredictableProcessL2 𝓕 P := by
  let S := predictableTimeFrame (W := W) t
  have hSpred : MeasurableSet[𝓕.predictable] S :=
    measurableSet_predictableTimeFrame 𝓕 t
  have hS : MeasurableSet S := predictable_le_prod 𝓕 S hSpred
  have hmem : MemLp (S.indicator (U : ℝ≥0 × W → ℝ)) 2
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).indicator hS
  let V : TimeProcessL2 P := hmem.toLp (S.indicator (U : ℝ≥0 × W → ℝ))
  refine ⟨V, ?_⟩
  have hU : AEStronglyMeasurable[𝓕.predictable]
      (U : ℝ≥0 × W → ℝ) (nonnegativeLebesgueMeasure.prod P) :=
    lpMeas.aestronglyMeasurable U
  have hcut : AEStronglyMeasurable[𝓕.predictable]
      (S.indicator (U : ℝ≥0 × W → ℝ))
      (nonnegativeLebesgueMeasure.prod P) := by
    refine ⟨S.indicator (hU.mk (U : ℝ≥0 × W → ℝ)),
      hU.stronglyMeasurable_mk.indicator hSpred, ?_⟩
    filter_upwards [hU.ae_eq_mk] with p hp
    by_cases hps : p ∈ S <;> simp [hps, hp]
  exact hcut.congr (MemLp.coeFn_toLp hmem).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The cutoff has its expected representative. -/
theorem predictableTimeRestrict_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      (predictableTimeFrame (W := W) t).indicator (U : ℝ≥0 × W → ℝ) := by
  let S := predictableTimeFrame (W := W) t
  have hSpred : MeasurableSet[𝓕.predictable] S :=
    measurableSet_predictableTimeFrame 𝓕 t
  have hS : MeasurableSet S := predictable_le_prod 𝓕 S hSpred
  have hmem : MemLp (S.indicator (U : ℝ≥0 × W → ℝ)) 2
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).indicator hS
  change ((hmem.toLp (S.indicator (U : ℝ≥0 × W → ℝ)) : TimeProcessL2 P) :
      ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        S.indicator (U : ℝ≥0 × W → ℝ)
  exact MemLp.coeFn_toLp hmem

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Cutting off in time cannot increase the product-`L²` norm. -/
theorem norm_predictableTimeRestrict_le
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    ‖predictableTimeRestrict 𝓕 t U‖ ≤ ‖U‖ := by
  change ‖(predictableTimeRestrict 𝓕 t U : TimeProcessL2 P)‖ ≤
    ‖(U : TimeProcessL2 P)‖
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_lt_top (U : TimeProcessL2 P)).ne
  calc
    eLpNorm (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ) 2
        (nonnegativeLebesgueMeasure.prod P) =
        eLpNorm ((predictableTimeFrame (W := W) t).indicator
          (U : ℝ≥0 × W → ℝ)) 2 (nonnegativeLebesgueMeasure.prod P) :=
      eLpNorm_congr_ae (predictableTimeRestrict_coeFn 𝓕 t U)
    _ ≤ eLpNorm (U : ℝ≥0 × W → ℝ) 2
        (nonnegativeLebesgueMeasure.prod P) :=
      eLpNorm_indicator_le _ (measurableSet_Ioc.prod MeasurableSet.univ)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restriction to the empty initial frame is zero. -/
@[simp]
theorem predictableTimeRestrict_zero
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 0 U = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 0 U,
    Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with p hp hzero
  rw [hp]
  simp only [predictableTimeFrame, Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
  exact hzero.symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restricting twice to nested initial frames keeps the smaller frame. -/
theorem predictableTimeRestrict_restrict
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {s t : ℝ≥0} (hst : s ≤ t)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 s (predictableTimeRestrict 𝓕 t U) =
      predictableTimeRestrict 𝓕 s U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 s
      (predictableTimeRestrict 𝓕 t U),
    predictableTimeRestrict_coeFn 𝓕 t U,
    predictableTimeRestrict_coeFn 𝓕 s U] with p hstp htp hsp
  rw [hstp]
  by_cases hps : p ∈ predictableTimeFrame (W := W) s
  · have hpt : p ∈ predictableTimeFrame (W := W) t := by
      exact ⟨⟨hps.1.1, hps.1.2.trans hst⟩, Set.mem_univ _⟩
    rw [Set.indicator_of_mem hps, htp, hsp,
      Set.indicator_of_mem hpt, Set.indicator_of_mem hps]
  · rw [Set.indicator_of_notMem hps, hsp, Set.indicator_of_notMem hps]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restricting a process already supported on a smaller initial frame to a
larger frame leaves it unchanged. -/
theorem predictableTimeRestrict_of_le
    (𝒽 : Filtration ℝ≥0 ‹MeasurableSpace W›) {s t : ℝ≥0} (hts : t ≤ s)
    (U : PredictableProcessL2 𝒽 P) :
    predictableTimeRestrict 𝒽 s (predictableTimeRestrict 𝒽 t U) =
      predictableTimeRestrict 𝒽 t U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝒽 s
      (predictableTimeRestrict 𝒽 t U),
    predictableTimeRestrict_coeFn 𝒽 t U] with p hs ht
  rw [hs]
  by_cases hps : p ∈ predictableTimeFrame (W := W) s
  · rw [Set.indicator_of_mem hps]
  · have hpt : p ∉ predictableTimeFrame (W := W) t := by
      intro hp
      exact hps ⟨⟨hp.1.1, hp.1.2.trans hts⟩, hp.2⟩
    rw [Set.indicator_of_notMem hps, ht, Set.indicator_of_notMem hpt]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Nested predictable time restrictions intersect their initial frames. -/
theorem predictableTimeRestrict_min
    (𝒽 : Filtration ℝ≥0 ‹MeasurableSpace W›) (s t : ℝ≥0)
    (U : PredictableProcessL2 𝒽 P) :
    predictableTimeRestrict 𝒽 s (predictableTimeRestrict 𝒽 t U) =
      predictableTimeRestrict 𝒽 (min s t) U := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact predictableTimeRestrict_restrict 𝒽 hst U
  · rw [min_eq_right hts]
    exact predictableTimeRestrict_of_le 𝒽 hts U

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restriction commutes with subtraction. -/
theorem predictableTimeRestrict_sub
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U V : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 t (U - V) =
      predictableTimeRestrict 𝓕 t U - predictableTimeRestrict 𝓕 t V := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 t (U - V),
    predictableTimeRestrict_coeFn 𝓕 t U,
    predictableTimeRestrict_coeFn 𝓕 t V,
    Lp.coeFn_sub (U : TimeProcessL2 P) (V : TimeProcessL2 P),
    Lp.coeFn_sub (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P)
      (predictableTimeRestrict 𝓕 t V : TimeProcessL2 P)]
    with p hsub hU hV hUV hright
  change ((predictableTimeRestrict 𝓕 t (U - V) : TimeProcessL2 P) :
      ℝ≥0 × W → ℝ) p =
    ((((predictableTimeRestrict 𝓕 t U : TimeProcessL2 P) -
      (predictableTimeRestrict 𝓕 t V : TimeProcessL2 P)) : TimeProcessL2 P) :
        ℝ≥0 × W → ℝ) p
  rw [hsub, hright]
  simp only [Pi.sub_apply]
  by_cases hp : p ∈ predictableTimeFrame (W := W) t
  · rw [Set.indicator_of_mem hp]
    change ((((U : TimeProcessL2 P) - (V : TimeProcessL2 P)) : TimeProcessL2 P) :
        ℝ≥0 × W → ℝ) p =
      (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ) p -
        (predictableTimeRestrict 𝓕 t V : ℝ≥0 × W → ℝ) p
    rw [hUV, hU, hV,
      Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    rfl
  · rw [Set.indicator_of_notMem hp, hU, hV,
      Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, sub_zero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Restricting the zero predictable process gives zero. -/
@[simp]
theorem predictableTimeRestrict_zero_process
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    predictableTimeRestrict (P := P) 𝓕 t 0 = 0 := by
  simpa using predictableTimeRestrict_sub (P := P) 𝓕 t 0 0

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Time restriction commutes with negation. -/
theorem predictableTimeRestrict_neg
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 t (-U) = -predictableTimeRestrict 𝓕 t U := by
  simpa using predictableTimeRestrict_sub 𝓕 t 0 U

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Time restriction commutes with addition. -/
theorem predictableTimeRestrict_add
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U V : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 t (U + V) =
      predictableTimeRestrict 𝓕 t U + predictableTimeRestrict 𝓕 t V := by
  rw [← sub_neg_eq_add, predictableTimeRestrict_sub,
    predictableTimeRestrict_neg, sub_neg_eq_add]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Time restriction commutes with real scalar multiplication. -/
theorem predictableTimeRestrict_smul
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (c : ℝ)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrict 𝓕 t (c • U) =
      c • predictableTimeRestrict 𝓕 t U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 t (c • U),
    predictableTimeRestrict_coeFn 𝓕 t U,
    Lp.coeFn_smul c (U : TimeProcessL2 P),
    Lp.coeFn_smul c (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P)]
    with p hleft hU hcU hright
  change ((predictableTimeRestrict 𝓕 t (c • U) : TimeProcessL2 P) :
      ℝ≥0 × W → ℝ) p =
    ((c • (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P) :
      TimeProcessL2 P) : ℝ≥0 × W → ℝ) p
  rw [hleft, hright]
  change (predictableTimeFrame (W := W) t).indicator
      (((c • (U : TimeProcessL2 P) : TimeProcessL2 P) : ℝ≥0 × W → ℝ)) p =
    (c • (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ)) p
  by_cases hp : p ∈ predictableTimeFrame (W := W) t
  · rw [Set.indicator_of_mem hp, hcU]
    change c * (U : ℝ≥0 × W → ℝ) p =
      c * (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ) p
    rw [hU, Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp]
    change 0 = c * (predictableTimeRestrict 𝓕 t U : ℝ≥0 × W → ℝ) p
    rw [hU, Set.indicator_of_notMem hp, mul_zero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Time restriction as a contraction on predictable product `L²`. -/
noncomputable def predictableTimeRestrictCLM
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    PredictableProcessL2 𝓕 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  LinearMap.mkContinuous
    { toFun := predictableTimeRestrict 𝓕 t
      map_add' := predictableTimeRestrict_add 𝓕 t
      map_smul' := predictableTimeRestrict_smul 𝓕 t }
    1 fun U ↦ by simpa using norm_predictableTimeRestrict_le 𝓕 t U

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
@[simp]
theorem predictableTimeRestrictCLM_apply
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeRestrictCLM 𝓕 t U = predictableTimeRestrict 𝓕 t U :=
  rfl

/-- The natural Itô integral up to time `t`, as an equality class in `L²(P)`. -/
noncomputable def naturalItoProcess
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) : RandomL2 P :=
  naturalItoIntegral hB hsm hnat (predictableTimeRestrict 𝓕 t U)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The Itô process starts from zero in `L²(P)`. -/
@[simp]
theorem naturalItoProcess_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) :
    naturalItoProcess hB hsm hnat U 0 = 0 := by
  simp [naturalItoProcess]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Integrating a deterministically stopped predictable process up to `s`
equals integrating the original process up to `min s a`. -/
theorem naturalItoProcess_predictableTimeRestrict
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝒽 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝒽 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝒽 P) (s a : ℝ≥0) :
    naturalItoProcess hB hsm hnat (predictableTimeRestrict 𝒽 a U) s =
      naturalItoProcess hB hsm hnat U (min s a) := by
  unfold naturalItoProcess
  rw [predictableTimeRestrict_min]

/-- The integrand supported on the time slice `(s,t]`. -/
noncomputable def predictableTimeSlice
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (s t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) : PredictableProcessL2 𝓕 P :=
  predictableTimeRestrict 𝓕 t U - predictableTimeRestrict 𝓕 s U

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Taking the part of a predictable process on `(s,t]` is continuous and linear. -/
noncomputable def predictableTimeSliceCLM
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (s t : ℝ≥0) :
    PredictableProcessL2 𝓕 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  predictableTimeRestrictCLM 𝓕 t - predictableTimeRestrictCLM 𝓕 s

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
@[simp]
theorem predictableTimeSliceCLM_apply
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (s t : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) :
    predictableTimeSliceCLM 𝓕 s t U = predictableTimeSlice 𝓕 s t U :=
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Cutting an elementary process to `(s,t]` intersects its time interval with that slice. -/
theorem predictableTimeSlice_elementaryPredictable [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {s t : ℝ≥0} (hst : s ≤ t)
    (a b : ℝ≥0) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    predictableTimeSlice 𝓕 s t (elementaryPredictable 𝓕 a b Z) =
      elementaryPredictable 𝓕 (a ⊔ s) (b ⊓ t)
        (adaptedMono 𝓕 (le_max_left a s) Z) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
      (predictableTimeRestrict 𝓕 t (elementaryPredictable 𝓕 a b Z) :
        TimeProcessL2 P)
      (predictableTimeRestrict 𝓕 s (elementaryPredictable 𝓕 a b Z) :
        TimeProcessL2 P),
    predictableTimeRestrict_coeFn 𝓕 t (elementaryPredictable 𝓕 a b Z),
    predictableTimeRestrict_coeFn 𝓕 s (elementaryPredictable 𝓕 a b Z),
    elementaryPredictable_coeFn 𝓕 a b Z,
    elementaryPredictable_coeFn 𝓕 (a ⊔ s) (b ⊓ t)
      (adaptedMono 𝓕 (le_max_left a s) Z)]
    with p hsub ht hs hU hright
  change (((predictableTimeRestrict 𝓕 t (elementaryPredictable 𝓕 a b Z) :
      TimeProcessL2 P) -
      (predictableTimeRestrict 𝓕 s (elementaryPredictable 𝓕 a b Z) :
        TimeProcessL2 P) : TimeProcessL2 P) : ℝ≥0 × W → ℝ) p =
    (elementaryPredictable 𝓕 (a ⊔ s) (b ⊓ t)
      (adaptedMono 𝓕 (le_max_left a s) Z) : ℝ≥0 × W → ℝ) p
  rw [hsub, Pi.sub_apply, ht, hs, hright]
  by_cases hpt : p ∈ predictableTimeFrame (W := W) t
  · rw [Set.indicator_of_mem hpt]
    by_cases hps : p ∈ predictableTimeFrame (W := W) s
    · rw [Set.indicator_of_mem hps, sub_self]
      have hi : p.1 ∉ Set.Ioc (a ⊔ s) (b ⊓ t) := by
        intro hi
        exact (not_lt_of_ge hps.1.2)
          (lt_of_le_of_lt (le_max_right a s) hi.1)
      rw [ite_eq_right hi]
    · rw [Set.indicator_of_notMem hps, sub_zero, hU]
      have hsx : s < p.1 := by
        by_contra hx
        exact hps ⟨⟨hpt.1.1, le_of_not_gt hx⟩, Set.mem_univ _⟩
      have hi : p.1 ∈ Set.Ioc a b ↔
          p.1 ∈ Set.Ioc (a ⊔ s) (b ⊓ t) := by
        constructor
        · intro hp
          exact ⟨max_lt hp.1 hsx, le_min hp.2 hpt.1.2⟩
        · intro hp
          exact ⟨lt_of_le_of_lt (le_max_left a s) hp.1,
            hp.2.trans (min_le_left b t)⟩
      by_cases hpab : p.1 ∈ Set.Ioc a b
      · rw [ite_eq_left hpab, ite_eq_left (hi.mp hpab)]
        rfl
      · rw [ite_eq_right hpab, ite_eq_right (mt hi.mpr hpab)]
  · have hps : p ∉ predictableTimeFrame (W := W) s := by
      intro hp
      apply hpt
      exact ⟨⟨hp.1.1, hp.1.2.trans hst⟩, hp.2⟩
    have hi : p.1 ∉ Set.Ioc (a ⊔ s) (b ⊓ t) := by
      intro hi
      apply hpt
      exact ⟨⟨lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s)
          (lt_of_le_of_lt (le_max_right a s) hi.1),
        hi.2.trans (min_le_right b t)⟩, Set.mem_univ _⟩
    rw [Set.indicator_of_notMem hpt, Set.indicator_of_notMem hps, sub_zero]
    rw [ite_eq_right hi]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Stopping an elementary process at `t` shortens its right endpoint to `min b t`. -/
theorem predictableTimeRestrict_elementaryPredictable [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    predictableTimeRestrict 𝓕 t (elementaryPredictable 𝓕 a b Z) =
      elementaryPredictable 𝓕 a (b ⊓ t) Z := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableTimeRestrict_coeFn 𝓕 t
      (elementaryPredictable 𝓕 a b Z),
    elementaryPredictable_coeFn 𝓕 a b Z,
    elementaryPredictable_coeFn 𝓕 a (b ⊓ t) Z]
    with p hleft hU hright
  change (predictableTimeRestrict 𝓕 t
      (elementaryPredictable 𝓕 a b Z) : ℝ≥0 × W → ℝ) p =
    (elementaryPredictable 𝓕 a (b ⊓ t) Z : ℝ≥0 × W → ℝ) p
  rw [hleft, hright]
  by_cases hpt : p ∈ predictableTimeFrame (W := W) t
  · rw [Set.indicator_of_mem hpt, hU]
    have hi : p.1 ∈ Set.Ioc a b ↔ p.1 ∈ Set.Ioc a (b ⊓ t) := by
      constructor
      · intro hp
        exact ⟨hp.1, le_min hp.2 hpt.1.2⟩
      · intro hp
        exact ⟨hp.1, hp.2.trans (min_le_left b t)⟩
    by_cases hpab : p.1 ∈ Set.Ioc a b
    · rw [ite_eq_left hpab, ite_eq_left (hi.mp hpab)]
    · rw [ite_eq_right hpab, ite_eq_right (mt hi.mpr hpab)]
  · rw [Set.indicator_of_notMem hpt]
    have hi : p.1 ∉ Set.Ioc a (b ⊓ t) := by
      intro hi
      apply hpt
      exact ⟨⟨lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ a) hi.1,
        hi.2.trans (min_le_right b t)⟩, Set.mem_univ _⟩
    rw [ite_eq_right hi]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- An elementary predictable process on an empty ordered interval is zero. -/
theorem elementaryPredictable_eq_zero_of_le [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b : ℝ≥0} (hba : b ≤ a)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictable 𝓕 a b Z = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [elementaryPredictable_coeFn 𝓕 a b Z,
    Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with p hp hzero
  rw [hp]
  simpa [Set.Ioc_eq_empty_of_le hba] using hzero.symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A Brownian elementary integral beginning after `s` is orthogonal to every
`𝓕_s`-measurable square-integrable random variable. -/
theorem inner_elementaryBrownianValue_adapted_eq_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b)
    (Y : lpMeas ℝ ℝ (𝓕 a) 2 P) (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Y) (Z : RandomL2 P) = 0 := by
  have hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hsa) (lpMeas.aestronglyMeasurable Z)
  have hYZ : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Y : W → ℝ) w * (Z : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Y).mul hZ
  have hind := indep_increment_of_natural_adapted hB hsm hnat hab hYZ
  have hDelta : AEStronglyMeasurable (fun w ↦ B b w - B a w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hfactor := hind.integral_mul_eq_mul_integral hDelta
    (AEStronglyMeasurable.mono (𝓕.le a) hYZ)
  rw [L2.inner_def]
  calc
    ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Y w, (Z : RandomL2 P) w⟫_ℝ ∂P =
        ∫ w, (B b w - B a w) *
          ((Y : W → ℝ) w * (Z : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Y] with w hw
      rw [hw]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B b w - B a w ∂P) *
        ∫ w, (Y : W → ℝ) w * (Z : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
        hB.integral_eval, hB.integral_eval, sub_zero, zero_mul]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A future time slice is orthogonal in product `L²` to every integrand stopped at its
left endpoint. -/
theorem inner_predictableTimeSlice_timeRestrict
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {s t : ℝ≥0} (hst : s ≤ t)
    (U V : PredictableProcessL2 𝓕 P) :
    inner ℝ (predictableTimeSlice 𝓕 s t U) (predictableTimeRestrict 𝓕 s V) = 0 := by
  change inner ℝ (predictableTimeSlice 𝓕 s t U : TimeProcessL2 P)
    (predictableTimeRestrict 𝓕 s V : TimeProcessL2 P) = 0
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub
      (predictableTimeRestrict 𝓕 t U : TimeProcessL2 P)
      (predictableTimeRestrict 𝓕 s U : TimeProcessL2 P),
    predictableTimeRestrict_coeFn 𝓕 t U,
    predictableTimeRestrict_coeFn 𝓕 s U,
    predictableTimeRestrict_coeFn 𝓕 s V]
    with p hslice ht hs hV
  change ⟪(((((predictableTimeRestrict 𝓕 t U : TimeProcessL2 P) -
      (predictableTimeRestrict 𝓕 s U : TimeProcessL2 P)) : TimeProcessL2 P) :
        ℝ≥0 × W → ℝ) p),
    (predictableTimeRestrict 𝓕 s V : ℝ≥0 × W → ℝ) p⟫_ℝ = 0
  rw [hslice]
  simp only [Pi.sub_apply]
  rw [ht, hs, hV]
  by_cases hps : p ∈ predictableTimeFrame (W := W) s
  · have hpt : p ∈ predictableTimeFrame (W := W) t :=
      ⟨⟨hps.1.1, hps.1.2.trans hst⟩, Set.mem_univ _⟩
    simp [hps, hpt]
  · simp [hps]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Process increments are the fixed-horizon integral of the corresponding time slice. -/
theorem naturalItoProcess_sub
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (s t : ℝ≥0) :
    naturalItoProcess hB hsm hnat U t - naturalItoProcess hB hsm hnat U s =
      naturalItoIntegral hB hsm hnat (predictableTimeSlice 𝓕 s t U) := by
  exact ((naturalItoIntegral hB hsm hnat).map_sub _ _).symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Every increment after `s` is orthogonal to every square-integrable random variable
measurable at time `s`. This is the full `L²` martingale-increment law. -/
theorem inner_naturalItoProcess_sub_adapted
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s t : ℝ≥0} (hst : s ≤ t) (U : PredictableProcessL2 𝓕 P)
    (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    inner ℝ
      (naturalItoProcess hB hsm hnat U t - naturalItoProcess hB hsm hnat U s)
      (Z : RandomL2 P) = 0 := by
  rw [naturalItoProcess_sub]
  let L : PredictableProcessL2 𝓕 P →L[ℝ] ℝ :=
    (innerSL ℝ (Z : RandomL2 P)).comp
      ((naturalItoIntegral hB hsm hnat).comp
        (predictableTimeSliceCLM 𝓕 s t))
  have hL : L = 0 := by
    apply ContinuousLinearMap.ext_on
      (s := {V | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
        ∃ Y : lpMeas ℝ ℝ (𝓕 a) 2 P,
          V = elementaryPredictable 𝓕 a b Y})
    · simpa only [elementaryPredictableSpan] using
        (dense_elementaryPredictableSpan (P := P) 𝓕)
    · rintro V ⟨a, b, hab, Y, rfl⟩
      simp only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        predictableTimeSliceCLM_apply, zero_apply]
      rw [predictableTimeSlice_elementaryPredictable 𝓕 hst]
      by_cases hslice : a ⊔ s ≤ b ⊓ t
      · rw [naturalItoIntegral_elementaryPredictable hB hsm hnat hslice]
        rw [real_inner_comm]
        exact inner_elementaryBrownianValue_adapted_eq_zero
          hB hsm hnat (le_max_right a s) hslice
            (adaptedMono 𝓕 (le_max_left a s) Y) Z
      · rw [elementaryPredictable_eq_zero_of_le 𝓕 (le_of_not_ge hslice),
          map_zero, inner_zero_right]
  calc
    inner ℝ (naturalItoIntegral hB hsm hnat (predictableTimeSlice 𝓕 s t U))
        (Z : RandomL2 P) =
        inner ℝ (Z : RandomL2 P)
          (naturalItoIntegral hB hsm hnat (predictableTimeSlice 𝓕 s t U)) :=
      real_inner_comm _ _
    _ = 0 := by
      have happ := congrArg
        (fun A : PredictableProcessL2 𝓕 P →L[ℝ] ℝ ↦ A U) hL
      simpa only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        predictableTimeSliceCLM_apply, zero_apply] using happ

omit [CompleteSpace W] [BorelSpace W] in
/-- Every fixed-time `L²` value of the Itô process has an almost-everywhere representative
measurable for the natural filtration at that time. -/
theorem aestronglyMeasurable_naturalItoProcess
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓕 t]
      (naturalItoProcess hB hsm hnat U t : W → ℝ) P := by
  let T : PredictableProcessL2 𝓕 P →L[ℝ] RandomL2 P :=
    (naturalItoIntegral hB hsm hnat).comp (predictableTimeRestrictCLM 𝓕 t)
  let K : Submodule ℝ (PredictableProcessL2 𝓕 P) :=
    (lpMeas ℝ ℝ (𝓕 t) 2 P).comap T.toLinearMap
  have hgen : {V | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
      ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P,
        V = elementaryPredictable 𝓕 a b Z} ⊆ K := by
    rintro V ⟨a, b, hab, Z, rfl⟩
    change naturalItoIntegral hB hsm hnat
        (predictableTimeRestrict 𝓕 t (elementaryPredictable 𝓕 a b Z)) ∈
      lpMeas ℝ ℝ (𝓕 t) 2 P
    rw [predictableTimeRestrict_elementaryPredictable]
    by_cases hat : a ≤ t
    · have habt : a ≤ b ⊓ t := le_min hab hat
      rw [naturalItoIntegral_elementaryPredictable hB hsm hnat habt,
        mem_lpMeas_iff_aestronglyMeasurable]
      have hBadapted : StronglyAdapted 𝓕 B := by
        rw [hnat]
        exact Filtration.stronglyAdapted_natural hsm
      have hZ : AEStronglyMeasurable[𝓕 t] (Z : W → ℝ) P :=
        AEStronglyMeasurable.mono (𝓕.mono hat) (lpMeas.aestronglyMeasurable Z)
      have hDelta : AEStronglyMeasurable[𝓕 t]
          (fun w ↦ B (b ⊓ t) w - B a w) P :=
        ((hBadapted.stronglyMeasurable_le (min_le_right b t)).sub
          (hBadapted.stronglyMeasurable_le hat)).aestronglyMeasurable
      exact (hZ.mul hDelta).congr
        (coeFn_elementaryBrownianValue hB hsm hnat habt Z).symm
    · have hta : b ⊓ t ≤ a :=
        (min_le_right b t).trans (le_of_not_ge hat)
      rw [elementaryPredictable_eq_zero_of_le 𝓕 hta, map_zero]
      exact Submodule.zero_mem _
  have hspan : elementaryPredictableSpan (P := P) 𝓕 ≤ K := by
    rw [elementaryPredictableSpan]
    exact Submodule.span_le.mpr hgen
  have hKclosed : IsClosed (K : Set (PredictableProcessL2 𝓕 P)) := by
    change IsClosed (T ⁻¹' {F : RandomL2 P |
      AEStronglyMeasurable[𝓕 t] (F : W → ℝ) P})
    exact (isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (𝓕.le t)).preimage
      T.continuous
  have hUclosure : U ∈ closure
      (elementaryPredictableSpan (P := P) 𝓕 :
        Set (PredictableProcessL2 𝓕 P)) := by
    rw [(dense_elementaryPredictableSpan (P := P) 𝓕).closure_eq]
    exact Set.mem_univ U
  have hUK : U ∈ K := by
    apply closure_minimal (fun V hV ↦ hspan hV) hKclosed hUclosure
  change T U ∈ lpMeas ℝ ℝ (𝓕 t) 2 P at hUK
  exact mem_lpMeas_iff_aestronglyMeasurable.mp hUK

/-- The fixed-time Itô value, bundled in the `L²(𝓕_t)` subspace. -/
noncomputable def naturalItoProcessLpMeas
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 t) 2 P :=
  ⟨naturalItoProcess hB hsm hnat U t,
    aestronglyMeasurable_naturalItoProcess hB hsm hnat U t⟩

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem naturalItoProcessLpMeas_coe
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    (naturalItoProcessLpMeas hB hsm hnat U t : RandomL2 P) =
      naturalItoProcess hB hsm hnat U t :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- Conditional expectation of a later Itô value onto `𝓕_s` is the value stopped at `s`. -/
theorem condExpL2_naturalItoProcess
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s t : ℝ≥0} (hst : s ≤ t) (U : PredictableProcessL2 𝓕 P) :
    condExpL2 ℝ ℝ (𝓕.le s) (naturalItoProcess hB hsm hnat U t) =
      naturalItoProcessLpMeas hB hsm hnat U s := by
  let : Fact ((𝓕 s : MeasurableSpace W) ≤ ‹MeasurableSpace W›) := ⟨𝓕.le s⟩
  apply Subtype.ext
  change (lpMeas ℝ ℝ (𝓕 s) 2 P).starProjection
      (naturalItoProcess hB hsm hnat U t) =
    naturalItoProcess hB hsm hnat U s
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (naturalItoProcessLpMeas hB hsm hnat U s).property
  · intro Z hZ
    exact inner_naturalItoProcess_sub_adapted hB hsm hnat hst U ⟨Z, hZ⟩

/-- A strongly `𝓕_t`-measurable representative of each quotient-valued Itô process value. -/
noncomputable def naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) : W → ℝ :=
  (aestronglyMeasurable_naturalItoProcess hB hsm hnat U t).mk
    (naturalItoProcess hB hsm hnat U t : W → ℝ)

omit [CompleteSpace W] [BorelSpace W] in
/-- The selected representative is strongly measurable at its own filtration time. -/
theorem stronglyMeasurable_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t]
      (naturalItoProcessRepresentative hB hsm hnat U t) :=
  (aestronglyMeasurable_naturalItoProcess hB hsm hnat U t).stronglyMeasurable_mk

omit [CompleteSpace W] [BorelSpace W] in
/-- The selected pointwise process represents the quotient-valued Itô process almost surely
at every fixed time. -/
theorem naturalItoProcess_ae_eq_representative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    (naturalItoProcess hB hsm hnat U t : W → ℝ) =ᵐ[P]
      naturalItoProcessRepresentative hB hsm hnat U t :=
  (aestronglyMeasurable_naturalItoProcess hB hsm hnat U t).ae_eq_mk

omit [CompleteSpace W] [BorelSpace W] in
/-- The selected representatives respect deterministic stopping at every
fixed time, up to the quotient's unavoidable almost-everywhere equality. -/
theorem naturalItoProcessRepresentative_predictableTimeRestrict_ae
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝒽 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝒽 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝒽 P) (s a : ℝ≥0) :
    naturalItoProcessRepresentative hB hsm hnat
        (predictableTimeRestrict 𝒽 a U) s =ᵐ[P]
      naturalItoProcessRepresentative hB hsm hnat U (min s a) := by
  calc
    naturalItoProcessRepresentative hB hsm hnat
          (predictableTimeRestrict 𝒽 a U) s =ᵐ[P]
        (naturalItoProcess hB hsm hnat
          (predictableTimeRestrict 𝒽 a U) s : W → ℝ) :=
      (naturalItoProcess_ae_eq_representative hB hsm hnat
        (predictableTimeRestrict 𝒽 a U) s).symm
    _ =ᵐ[P] (naturalItoProcess hB hsm hnat U (min s a) : W → ℝ) := by
      rw [naturalItoProcess_predictableTimeRestrict]
    _ =ᵐ[P] naturalItoProcessRepresentative hB hsm hnat U (min s a) :=
      naturalItoProcess_ae_eq_representative hB hsm hnat U (min s a)

omit [CompleteSpace W] [BorelSpace W] in
/-- The selected representatives satisfy the defining conditional-expectation identity. -/
theorem condExp_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s t : ℝ≥0} (hst : s ≤ t) (U : PredictableProcessL2 𝓕 P) :
    P[naturalItoProcessRepresentative hB hsm hnat U t | 𝓕 s] =ᵐ[P]
      naturalItoProcessRepresentative hB hsm hnat U s := by
  let It := naturalItoProcess hB hsm hnat U t
  let Is := naturalItoProcess hB hsm hnat U s
  have ht := naturalItoProcess_ae_eq_representative hB hsm hnat U t
  have hs := naturalItoProcess_ae_eq_representative hB hsm hnat U s
  have hmem : MemLp (It : W → ℝ) 2 P := Lp.memLp It
  have hbridge := hmem.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le s)
  rw [Lp.toLp_coeFn] at hbridge
  have hprojection :
      (condExpL2 ℝ ℝ (𝓕.le s) It : W → ℝ) =ᵐ[P] (Is : W → ℝ) := by
    rw [condExpL2_naturalItoProcess hB hsm hnat hst U]
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  calc
    P[naturalItoProcessRepresentative hB hsm hnat U t | 𝓕 s] =ᵐ[P]
        P[(It : W → ℝ) | 𝓕 s] := (condExp_congr_ae ht).symm
    _ =ᵐ[P] (condExpL2 ℝ ℝ (𝓕.le s) It : W → ℝ) := hbridge.symm
    _ =ᵐ[P] (Is : W → ℝ) := hprojection
    _ =ᵐ[P] naturalItoProcessRepresentative hB hsm hnat U s := hs

omit [CompleteSpace W] [BorelSpace W] in
/-- The selected time-indexed Itô integral is a Mathlib martingale. -/
theorem martingale_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) :
    Martingale (naturalItoProcessRepresentative hB hsm hnat U) 𝓕 P := by
  refine ⟨stronglyMeasurable_naturalItoProcessRepresentative hB hsm hnat U, ?_⟩
  intro s t hst
  exact condExp_naturalItoProcessRepresentative hB hsm hnat hst U

omit [CompleteSpace W] [BorelSpace W] in
/-- Every increment after `s` is orthogonal to every other natural Itô process stopped at `s`.
This is the intrinsic `L²` martingale law on the closed stochastic-integral range. -/
theorem inner_naturalItoProcess_sub_naturalItoProcess
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s t : ℝ≥0} (hst : s ≤ t)
    (U V : PredictableProcessL2 𝓕 P) :
    inner ℝ
      (naturalItoProcess hB hsm hnat U t - naturalItoProcess hB hsm hnat U s)
      (naturalItoProcess hB hsm hnat V s) = 0 := by
  rw [naturalItoProcess_sub]
  change inner ℝ
    (naturalItoIntegral hB hsm hnat (predictableTimeSlice 𝓕 s t U))
    (naturalItoIntegral hB hsm hnat (predictableTimeRestrict 𝓕 s V)) = 0
  rw [inner_naturalItoIntegral]
  exact inner_predictableTimeSlice_timeRestrict 𝓕 hst U V

omit [CompleteSpace W] [BorelSpace W] in
/-- Fixed-time Itô isometry in norm form. -/
theorem norm_naturalItoProcess
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ‖naturalItoProcess hB hsm hnat U t‖ = ‖predictableTimeRestrict 𝓕 t U‖ := by
  exact norm_naturalItoIntegral hB hsm hnat _

omit [CompleteSpace W] [BorelSpace W] in
/-- A fixed-time value is bounded by the full predictable-process norm. -/
theorem norm_naturalItoProcess_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    ‖naturalItoProcess hB hsm hnat U t‖ ≤ ‖U‖ := by
  rw [norm_naturalItoProcess]
  exact norm_predictableTimeRestrict_le 𝓕 t U

end StochasticCalculus
