/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.QuadraticVariation

/-!
# Elementary predictable quadratic variation

This file proves the quadratic-variation formula for arbitrary finite sums of
adapted Brownian interval blocks, including overlapping intervals, and
identifies the result with the time integral of the squared predictable
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal InnerProductSpace

noncomputable section

set_option linter.unusedDecidableInType false

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [BorelSpace W] in
theorem naturalItoProcessRepresentative_elementaryPredictable_ae_eq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (Filtration.natural B hsm a) 2 P) (s : ℝ≥0) :
    naturalItoProcessRepresentative hB hsm rfl
        (elementaryPredictable (Filtration.natural B hsm) a b Z) s =ᵐ[P]
      fun ω => (Z : W → ℝ) ω *
        (B (min s b) ω - B (min s a) ω) := by
  let 𝓕 := Filtration.natural B hsm
  let U := elementaryPredictable 𝓕 a b Z
  have hrep := naturalItoProcess_ae_eq_representative hB hsm rfl U s
  apply hrep.symm.trans
  by_cases hsa : s ≤ a
  · have hsb : s ≤ b := hsa.trans hab
    have hU0 : predictableTimeRestrict 𝓕 s U = 0 := by
      rw [predictableTimeRestrict_elementaryPredictable]
      apply elementaryPredictable_eq_zero_of_le
      simpa [min_eq_right hsb] using hsa
    have hproc0 : naturalItoProcess hB hsm rfl U s = 0 := by
      dsimp only [𝓕] at hU0
      rw [naturalItoProcess, hU0, map_zero]
    rw [hproc0]
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hzero
    rw [hzero]
    simp [min_eq_left hsa, min_eq_left hsb]
  · have has : a ≤ s := le_of_not_ge hsa
    have hamin : a ≤ b ⊓ s := le_min hab has
    rw [naturalItoProcess, predictableTimeRestrict_elementaryPredictable,
      naturalItoIntegral_elementaryPredictable hB hsm rfl hamin]
    filter_upwards [coeFn_elementaryBrownianValue hB hsm rfl hamin Z]
      with ω hω
    rw [hω]
    simp only [min_comm s b, min_eq_right has]

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem tendstoInMeasure_stopped_brownian_stopped_brownian_covariation_of_le
    (hB : IsBrownianMotion B P) {b c : ℝ≥0} (hbc : b ≤ c) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s ω => B (min s b) ω) (fun s ω => B (min s c) ω)
        t (n + 1)) Filter.atTop
      (fun _ => ((min t b : ℝ≥0) : ℝ)) := by
  let X : ℝ≥0 → W → ℝ := fun s ω => B (min s b) ω
  let Y : ℝ≥0 → W → ℝ := fun s ω => B (min s c) ω
  have hXmeas : ∀ s, AEStronglyMeasurable (X s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s c)).aestronglyMeasurable
  have hX : HasQuadraticVariationInProbabilityAt X P t
      (fun _ => ((min t b : ℝ≥0) : ℝ)) := by
    simpa only [X] using quadraticVariation_stopped_brownian_inProbability hB b t
  have hY : HasQuadraticVariationInProbabilityAt Y P t
      (fun _ => ((min t c : ℝ≥0) : ℝ)) := by
    simpa only [Y] using quadraticVariation_stopped_brownian_inProbability hB c t
  have hblocks := quadraticVariation_two_disjoint_brownian_blocks
    hB (a := 0) (b := b) (c := b) (d := c) zero_le le_rfl hbc 2 1 t
  have hsum : HasQuadraticVariationInProbabilityAt
      (fun s ω => X s ω + Y s ω) P t
      (fun _ =>
        4 * ((min t b : ℝ≥0) : ℝ) +
          (((min t c - min t b : ℝ≥0) : ℝ))) := by
    have hadd := hblocks.add_timeConstant (fun ω => 2 * B 0 ω)
    apply hadd.congr
    · intro s
      filter_upwards with ω
      dsimp only [X, Y]
      have hs0 : min s (0 : ℝ≥0) = 0 := min_eq_right zero_le
      rw [hs0]
      norm_num only [OfNat.ofNat, one_mul]
      ring
    · filter_upwards with ω
      have ht0 : min t (0 : ℝ≥0) = 0 := min_eq_right zero_le
      rw [ht0, tsub_zero, NNReal.coe_sub (min_le_min le_rfl hbc)]
      norm_num only [OfNat.ofNat, one_pow, one_mul, NNReal.coe_zero]
  have hcov := tendstoInMeasure_quadraticCovariationApprox
    hXmeas hYmeas hX hY hsum
  apply hcov.congr_right
  filter_upwards with ω
  rw [NNReal.coe_sub (min_le_min le_rfl hbc)]
  ring

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem tendstoInMeasure_stopped_brownian_stopped_brownian_covariation
    (hB : IsBrownianMotion B P) (b c t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s ω => B (min s b) ω) (fun s ω => B (min s c) ω)
        t (n + 1)) Filter.atTop
      (fun _ => ((min t (min b c) : ℝ≥0) : ℝ)) := by
  rcases le_total b c with hbc | hcb
  · simpa [min_eq_left hbc, min_assoc] using
      tendstoInMeasure_stopped_brownian_stopped_brownian_covariation_of_le
        hB hbc t
  · have hrev :=
      tendstoInMeasure_stopped_brownian_stopped_brownian_covariation_of_le
        hB hcb t
    apply hrev.congr
    · intro n
      filter_upwards with ω
      exact quadraticCovariationApprox_comm _ _ t (n + 1) ω
    · filter_upwards with ω
      simp [min_eq_right hcb]

noncomputable def clippedIntervalCovariation
    (a b c d t : ℝ≥0) : ℝ :=
  (min t (min b d) : ℝ≥0) - (min t (min b c) : ℝ≥0) -
    (min t (min a d) : ℝ≥0) + (min t (min a c) : ℝ≥0)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem tendstoInMeasure_brownian_interval_interval_covariation
    (hB : IsBrownianMotion B P) {a b c d : ℝ≥0}
    (_hab : a ≤ b) (_hcd : c ≤ d) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s ω => B (min s b) ω - B (min s a) ω)
        (fun s ω => B (min s d) ω - B (min s c) ω)
        t (n + 1)) Filter.atTop
      (fun _ => clippedIntervalCovariation a b c d t) := by
  let A : ℝ≥0 → W → ℝ := fun s ω => B (min s a) ω
  let Bb : ℝ≥0 → W → ℝ := fun s ω => B (min s b) ω
  let C : ℝ≥0 → W → ℝ := fun s ω => B (min s c) ω
  let D : ℝ≥0 → W → ℝ := fun s ω => B (min s d) ω
  let q : ℝ≥0 → ℝ≥0 → W → ℝ := fun u v _ => (min t (min u v) : ℝ≥0)
  have hmeas : ∀ u s, AEStronglyMeasurable (fun ω => B (min s u) ω) P :=
    fun u s => (hB.toIsPreBrownianReal.aemeasurable (min s u)).aestronglyMeasurable
  have hBD := tendstoInMeasure_stopped_brownian_stopped_brownian_covariation
    hB b d t
  have hBC := tendstoInMeasure_stopped_brownian_stopped_brownian_covariation
    hB b c t
  have hAD := tendstoInMeasure_stopped_brownian_stopped_brownian_covariation
    hB a d t
  have hAC := tendstoInMeasure_stopped_brownian_stopped_brownian_covariation
    hB a c t
  have hBinterval :=
    tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
      hBD hBC (hmeas b) (hmeas d) (hmeas c) 1 (-1)
  have hAinterval :=
    tendstoInMeasure_quadraticCovariationApprox_linearCombination_right
      hAD hAC (hmeas a) (hmeas d) (hmeas c) 1 (-1)
  have hDCmeas : ∀ s, AEStronglyMeasurable
      (fun ω => 1 * B (min s d) ω + (-1) * B (min s c) ω) P := by
    intro s
    exact (aestronglyMeasurable_const.mul (hmeas d s)).add
      (aestronglyMeasurable_const.mul (hmeas c s))
  have hinterval :=
    tendstoInMeasure_quadraticCovariationApprox_linearCombination_left
      hBinterval hAinterval (hmeas b) (hmeas a)
        hDCmeas 1 (-1)
  apply hinterval.congr
  · intro n
    filter_upwards with ω
    unfold quadraticCovariationApprox
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · filter_upwards with ω
    dsimp only [q, clippedIntervalCovariation]
    ring

theorem clippedIntervalCovariation_comm
    (a b c d t : ℝ≥0) :
    clippedIntervalCovariation a b c d t =
      clippedIntervalCovariation c d a b t := by
  unfold clippedIntervalCovariation
  simp only [min_comm]
  ring

theorem clippedIntervalCovariation_self
    {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) :
    clippedIntervalCovariation a b a b t =
      ((min t b - min t a : ℝ≥0) : ℝ) := by
  unfold clippedIntervalCovariation
  rw [min_self, min_eq_right hab, min_eq_left hab, min_self,
    NNReal.coe_sub (min_le_min le_rfl hab)]
  ring

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem tendstoInMeasure_random_brownian_interval_interval_covariation
    (hB : IsBrownianMotion B P) {a b c d : ℝ≥0}
    (hab : a ≤ b) (hcd : c ≤ d) (r q : W → ℝ)
    (hrMeas : AEStronglyMeasurable r P)
    (hqMeas : AEStronglyMeasurable q P) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => quadraticCovariationApprox
        (fun s ω => r ω * (B (min s b) ω - B (min s a) ω))
        (fun s ω => q ω * (B (min s d) ω - B (min s c) ω))
        t (n + 1)) Filter.atTop
      (fun ω => r ω * q ω * clippedIntervalCovariation a b c d t) := by
  let X : ℝ≥0 → W → ℝ := fun s ω =>
    B (min s b) ω - B (min s a) ω
  let Y : ℝ≥0 → W → ℝ := fun s ω =>
    B (min s d) ω - B (min s c) ω
  have hXmeas : ∀ s, AEStronglyMeasurable (X s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s b)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s a)).aestronglyMeasurable
  have hYmeas : ∀ s, AEStronglyMeasurable (Y s) P := fun s =>
    (hB.toIsPreBrownianReal.aemeasurable (min s d)).aestronglyMeasurable.sub
      (hB.toIsPreBrownianReal.aemeasurable (min s c)).aestronglyMeasurable
  have hbase := tendstoInMeasure_brownian_interval_interval_covariation
    hB hab hcd t
  simpa only [X, Y] using
    tendstoInMeasure_quadraticCovariationApprox_timeConstant_mul
      hbase hXmeas hYmeas r q hrMeas hqMeas

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem quadraticVariation_finset_random_brownian_blocks
    {ι : Type*} [DecidableEq ι] (hB : IsBrownianMotion B P)
    (S : Finset ι) (a b : ι → ℝ≥0)
    (hinterval : ∀ i ∈ S, a i ≤ b i) (c : ι → W → ℝ)
    (hcMeas : ∀ i ∈ S, AEStronglyMeasurable (c i) P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (fun s ω => ∑ i ∈ S,
        c i ω * (B (min s (b i)) ω - B (min s (a i)) ω)) P t
      (fun ω => ∑ i ∈ S, ∑ j ∈ S,
        c i ω * c j ω *
          clippedIntervalCovariation (a i) (b i) (a j) (b j) t) := by
  let X : ι → ℝ≥0 → W → ℝ := fun i s ω =>
    c i ω * (B (min s (b i)) ω - B (min s (a i)) ω)
  let q : ι → ι → W → ℝ := fun i j ω =>
    c i ω * c j ω *
      clippedIntervalCovariation (a i) (b i) (a j) (b j) t
  have hXmeas : ∀ i ∈ S, ∀ s, AEStronglyMeasurable (X i s) P := by
    intro i hi s
    exact (hcMeas i hi).mul
      ((hB.toIsPreBrownianReal.aemeasurable (min s (b i))).aestronglyMeasurable.sub
        (hB.toIsPreBrownianReal.aemeasurable (min s (a i))).aestronglyMeasurable)
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold HasQuadraticVariationInProbabilityAt
      apply tendstoInMeasure_of_tendsto_ae
      · intro n
        have hz : quadraticVariationApprox (fun _ _ => (0 : ℝ)) t (n + 1) =
            (fun _ : W => (0 : ℝ)) := by
          funext ω
          simp [quadraticVariationApprox]
        rw [hz]
        exact aestronglyMeasurable_const
      · filter_upwards with ω
        simp [quadraticVariationApprox]
  | @insert i S hi ih =>
      have hii : a i ≤ b i := hinterval i (Finset.mem_insert_self i S)
      have hiMeas : AEStronglyMeasurable (c i) P :=
        hcMeas i (Finset.mem_insert_self i S)
      have hXiMeas : ∀ s, AEStronglyMeasurable (X i s) P :=
        hXmeas i (Finset.mem_insert_self i S)
      have hRestMeas : ∀ s, AEStronglyMeasurable
          (fun ω => ∑ j ∈ S, X j s ω) P := by
        intro s
        convert Finset.aestronglyMeasurable_sum S
          (fun j hj => hXmeas j (Finset.mem_insert_of_mem hj) s) using 1
        funext ω
        rw [Finset.sum_apply]
      have hXi : HasQuadraticVariationInProbabilityAt (X i) P t
          (fun ω => c i ω ^ 2 *
            ((min t (b i) - min t (a i) : ℝ≥0) : ℝ)) := by
        simpa only [X] using
          quadraticVariation_timeConstant_mul_brownian_interval_inProbability
            hB (c i) hiMeas hii t
      have hRest : HasQuadraticVariationInProbabilityAt
          (fun s ω => ∑ j ∈ S, X j s ω) P t
          (fun ω => ∑ j ∈ S, ∑ k ∈ S, q j k ω) := by
        simpa only [X, q] using ih
          (fun j hj => hinterval j (Finset.mem_insert_of_mem hj))
          (fun j hj => hcMeas j (Finset.mem_insert_of_mem hj))
          (fun j hj s => hXmeas j (Finset.mem_insert_of_mem hj) s)
      have hPair : ∀ j ∈ S, TendstoInMeasure P
          (fun n => quadraticCovariationApprox (X i) (X j) t (n + 1))
          Filter.atTop (q i j) := by
        intro j hj
        simpa only [X, q] using
          tendstoInMeasure_random_brownian_interval_interval_covariation
            hB hii (hinterval j (Finset.mem_insert_of_mem hj))
              (c i) (c j) hiMeas
              (hcMeas j (Finset.mem_insert_of_mem hj)) t
      have hCov : TendstoInMeasure P
          (fun n => quadraticCovariationApprox (X i)
            (fun s ω => ∑ j ∈ S, X j s ω) t (n + 1))
          Filter.atTop (fun ω => ∑ j ∈ S, q i j ω) := by
        simpa only [one_mul] using
          tendstoInMeasure_quadraticCovariationApprox_finset_sum
            S (X i) X (fun _ => 1) (q i) t hXiMeas
              (fun j hj => hXmeas j (Finset.mem_insert_of_mem hj)) hPair
      have hsum := hXi.linearCombination hRest hCov hXiMeas hRestMeas 1 1
      apply hsum.congr
      · intro s
        filter_upwards with ω
        simp only [Finset.sum_insert hi, X, one_mul]
      · filter_upwards with ω
        simp only [Finset.sum_insert hi, q, one_pow, one_mul]
        rw [clippedIntervalCovariation_self hii]
        have hsym : ∑ j ∈ S,
              c j ω * c i ω * clippedIntervalCovariation
                (a j) (b j) (a i) (b i) t =
            ∑ j ∈ S,
              c i ω * c j ω * clippedIntervalCovariation
                (a i) (b i) (a j) (b j) t := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [clippedIntervalCovariation_comm]
          ring
        rw [Finset.sum_add_distrib]
        rw [hsym]
        ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
theorem naturalItoProcess_elementaryFinsuppToPredictable
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ)
    (s : ℝ≥0) :
    naturalItoProcess hB hsm rfl
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v) s =
      ∑ x ∈ v.support, v x • naturalItoProcess hB hsm rfl
        (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s := by
  unfold naturalItoProcess elementaryFinsuppToPredictable
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  change (naturalItoIntegral hB hsm rfl)
      ((predictableTimeRestrictCLM (Filtration.natural B hsm) s)
        (∑ x ∈ v.support, v x •
          elementaryPredictableGenerator (Filtration.natural B hsm) P x)) = _
  rw [map_sum, map_sum]
  simp only [map_smul, predictableTimeRestrictCLM_apply]

omit [CompleteSpace W] [BorelSpace W] in
theorem naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ)
    (s : ℝ≥0) :
    naturalItoProcessRepresentative hB hsm rfl
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v) s =ᵐ[P]
      fun ω => ∑ x ∈ v.support, v x * (x.2.2 : W → ℝ) ω *
        (B (min s x.2.1.1) ω - B (min s x.1) ω) := by
  let U := elementaryFinsuppToPredictable (Filtration.natural B hsm) P v
  have hrep := naturalItoProcess_ae_eq_representative hB hsm rfl U s
  apply hrep.symm.trans
  rw [naturalItoProcess_elementaryFinsuppToPredictable hB hsm v s]
  have hsum := Lp.coeFn_fun_finsetSum v.support
    (fun x => v x • naturalItoProcess hB hsm rfl
      (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s)
  have hterm : ∀ x ∈ v.support,
      (((v x) • naturalItoProcess hB hsm rfl
        (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s :
          RandomL2 P) : W → ℝ) =ᵐ[P]
        fun ω => v x * (x.2.2 : W → ℝ) ω *
          (B (min s x.2.1.1) ω - B (min s x.1) ω) := by
    intro x _hx
    have hvalue := naturalItoProcess_ae_eq_representative hB hsm rfl
      (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s
    have hblock :=
      naturalItoProcessRepresentative_elementaryPredictable_ae_eq
        hB hsm x.2.1.2 x.2.2 s
    filter_upwards [Lp.coeFn_smul (v x)
        (naturalItoProcess hB hsm rfl
          (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s),
      hvalue, hblock] with ω hsmul hval hblk
    rw [hsmul]
    change v x * (naturalItoProcess hB hsm rfl
      (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s :
        W → ℝ) ω = _
    rw [hval]
    have hblk' := hblk
    change naturalItoProcessRepresentative hB hsm rfl
      (elementaryPredictableGenerator (Filtration.natural B hsm) P x) s ω =
        (x.2.2 : W → ℝ) ω *
          (B (min s x.2.1.1) ω - B (min s x.1) ω) at hblk'
    rw [hblk']
    ring
  filter_upwards [hsum, v.support.eventually_all.mpr hterm] with ω hsumω htermω
  rw [hsumω]
  apply Finset.sum_congr rfl
  intro x hx
  exact htermω x hx

omit [CompleteSpace W] [BorelSpace W] in
theorem quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v)) P t
      (fun ω => ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation
            x.1 x.2.1.1 y.1 y.2.1.1 t) := by
  classical
  let c : ElementaryPredictableIndex (Filtration.natural B hsm) P → W → ℝ :=
    fun x ω => v x * (x.2.2 : W → ℝ) ω
  have hcMeas : ∀ x ∈ v.support, AEStronglyMeasurable (c x) P := by
    intro x _hx
    exact aestronglyMeasurable_const.mul
      (AEStronglyMeasurable.mono
        ((Filtration.natural B hsm).le x.1) (lpMeas.aestronglyMeasurable x.2.2))
  have hraw := quadraticVariation_finset_random_brownian_blocks
    hB v.support (fun x => x.1) (fun x => x.2.1.1)
      (fun x _hx => x.2.1.2) c hcMeas t
  apply hraw.congr
  · intro s
    exact (naturalItoProcessRepresentative_elementaryFinsuppToPredictable_ae_eq
      hB.toIsPreBrownianReal hsm v s).symm
  · exact Filter.EventuallyEq.rfl

noncomputable def nnrealIicIndicator (u s : ℝ≥0) : ℝ :=
  (Set.Iic u).indicator (fun _ => (1 : ℝ)) s

noncomputable def nnrealIocIndicator (a b s : ℝ≥0) : ℝ :=
  (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s

theorem integral_nnrealIicIndicator (u t : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t, nnrealIicIndicator u s
        ∂nonnegativeLebesgueMeasure = (min t u : ℝ≥0) := by
  unfold nnrealIicIndicator
  change ∫ s, (Set.Iic u).indicator (fun _ => (1 : ℝ)) s
      ∂nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t) = _
  rw [integral_indicator measurableSet_Iic]
  have hset : Set.Iic u ∩ Set.Ioc (0 : ℝ≥0) t = Set.Ioc 0 (min t u) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hsu, hs0, hst⟩
      exact ⟨hs0, le_min hst hsu⟩
    · rintro ⟨hs0, hmin⟩
      exact ⟨hmin.trans (min_le_right _ _), hs0,
        hmin.trans (min_le_left _ _)⟩
  rw [Measure.restrict_restrict measurableSet_Iic, hset, setIntegral_const,
    Measure.real_def, nonnegativeLebesgueMeasure_Ioc]
  simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (min t u : ℝ))]

theorem nnrealIocIndicator_eq_sub
    (a b : ℝ≥0) (hab : a ≤ b) (s : ℝ≥0) :
    nnrealIocIndicator a b s =
      nnrealIicIndicator b s - nnrealIicIndicator a s := by
  unfold nnrealIocIndicator nnrealIicIndicator
  simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_Iic]
  by_cases hsa : s ≤ a
  · have hsb : s ≤ b := hsa.trans hab
    simp [hsa, hsb, not_lt_of_ge hsa]
  · have has : a < s := lt_of_not_ge hsa
    by_cases hsb : s ≤ b
    · simp [has, hsa, hsb]
    · have hbs : b < s := lt_of_not_ge hsb
      simp [has, hsa, hsb]

theorem nnrealIicIndicator_mul (u v s : ℝ≥0) :
    nnrealIicIndicator u s * nnrealIicIndicator v s =
      nnrealIicIndicator (min u v) s := by
  unfold nnrealIicIndicator
  simp only [Set.indicator_apply, Set.mem_Iic]
  by_cases hsu : s ≤ u <;> by_cases hsv : s ≤ v <;> simp [hsu, hsv]

theorem integral_nnrealIocIndicator_mul
    {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d) (t : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t,
        nnrealIocIndicator a b s * nnrealIocIndicator c d s
        ∂nonnegativeLebesgueMeasure =
      clippedIntervalCovariation a b c d t := by
  have hpoint (s : ℝ≥0) :
      nnrealIocIndicator a b s * nnrealIocIndicator c d s =
        nnrealIicIndicator (min b d) s -
          nnrealIicIndicator (min b c) s -
          nnrealIicIndicator (min a d) s +
          nnrealIicIndicator (min a c) s := by
    rw [nnrealIocIndicator_eq_sub a b hab,
      nnrealIocIndicator_eq_sub c d hcd]
    rw [mul_sub, sub_mul, sub_mul, nnrealIicIndicator_mul,
      nnrealIicIndicator_mul, nnrealIicIndicator_mul,
      nnrealIicIndicator_mul]
    ring
  let : IsFiniteMeasure
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) :=
    isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)
  have hIicInt (u : ℝ≥0) : Integrable (nnrealIicIndicator u)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) := by
    unfold nnrealIicIndicator
    exact (integrable_const (c := (1 : ℝ))).indicator measurableSet_Iic
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  change (∫ s, ((nnrealIicIndicator (min b d) s -
      nnrealIicIndicator (min b c) s) -
      nnrealIicIndicator (min a d) s) +
      nnrealIicIndicator (min a c) s
      ∂nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) = _
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)
  calc
    (∫ s, ((nnrealIicIndicator (min b d) s -
        nnrealIicIndicator (min b c) s) -
        nnrealIicIndicator (min a d) s) +
        nnrealIicIndicator (min a c) s ∂Q) =
        (∫ s, (nnrealIicIndicator (min b d) s -
          nnrealIicIndicator (min b c) s) -
          nnrealIicIndicator (min a d) s ∂Q) +
        ∫ s, nnrealIicIndicator (min a c) s ∂Q :=
      integral_add
        (((hIicInt (min b d)).sub (hIicInt (min b c))).sub
          (hIicInt (min a d))) (hIicInt (min a c))
    _ = ((∫ s, nnrealIicIndicator (min b d) s ∂Q) -
          (∫ s, nnrealIicIndicator (min b c) s ∂Q) -
          (∫ s, nnrealIicIndicator (min a d) s ∂Q)) +
          ∫ s, nnrealIicIndicator (min a c) s ∂Q := by
      have hbd : Integrable (nnrealIicIndicator (min b d)) Q := by
        simpa only [Q] using hIicInt (min b d)
      have hbc : Integrable (nnrealIicIndicator (min b c)) Q := by
        simpa only [Q] using hIicInt (min b c)
      have had : Integrable (nnrealIicIndicator (min a d)) Q := by
        simpa only [Q] using hIicInt (min a d)
      have hsub1 :
          (∫ s, nnrealIicIndicator (min b d) s -
            nnrealIicIndicator (min b c) s ∂Q) =
          (∫ s, nnrealIicIndicator (min b d) s ∂Q) -
            ∫ s, nnrealIicIndicator (min b c) s ∂Q :=
        integral_sub hbd hbc
      have hsub2 :
          (∫ s, (nnrealIicIndicator (min b d) s -
            nnrealIicIndicator (min b c) s) -
            nnrealIicIndicator (min a d) s ∂Q) =
          (∫ s, nnrealIicIndicator (min b d) s -
            nnrealIicIndicator (min b c) s ∂Q) -
            ∫ s, nnrealIicIndicator (min a d) s ∂Q :=
        integral_sub (hbd.sub hbc) had
      rw [hsub2, hsub1]
    _ = clippedIntervalCovariation a b c d t := by
      dsimp only [Q]
      rw [integral_nnrealIicIndicator, integral_nnrealIicIndicator,
        integral_nnrealIicIndicator, integral_nnrealIicIndicator]
      rfl

theorem integrable_nnrealIocIndicator_mul
    (a b c d t : ℝ≥0) :
    Integrable (fun s =>
      nnrealIocIndicator a b s * nnrealIocIndicator c d s)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) := by
  let : IsFiniteMeasure
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) :=
    isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)
  have hbase : Integrable
      ((Set.Ioc a b ∩ Set.Ioc c d).indicator (fun _ => (1 : ℝ)))
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) :=
    (integrable_const (c := (1 : ℝ))).indicator
      (measurableSet_Ioc.inter measurableSet_Ioc)
  apply hbase.congr
  filter_upwards with s
  unfold nnrealIocIndicator
  by_cases hab : s ∈ Set.Ioc a b <;> by_cases hcd : s ∈ Set.Ioc c d <;>
    simp [hab, hcd]

theorem integral_sq_finset_nnrealIocIndicator
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a b : ι → ℝ≥0) (hinterval : ∀ i ∈ S, a i ≤ b i)
    (c : ι → ℝ) (t : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t,
        (∑ i ∈ S, c i * nnrealIocIndicator (a i) (b i) s) ^ 2
        ∂nonnegativeLebesgueMeasure =
      ∑ i ∈ S, ∑ j ∈ S, c i * c j *
        clippedIntervalCovariation (a i) (b i) (a j) (b j) t := by
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)
  have htermInt : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun s =>
      (c i * nnrealIocIndicator (a i) (b i) s) *
        (c j * nnrealIocIndicator (a j) (b j) s)) Q := by
    intro i _hi j _hj
    have hbase := integrable_nnrealIocIndicator_mul
      (a i) (b i) (a j) (b j) t
    apply (hbase.const_mul (c i * c j)).congr
    filter_upwards with s
    ring
  have hexpand (s : ℝ≥0) :
      (∑ i ∈ S, c i * nnrealIocIndicator (a i) (b i) s) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S,
          (c i * nnrealIocIndicator (a i) (b i) s) *
            (c j * nnrealIocIndicator (a j) (b j) s) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  change (∫ s, ∑ i ∈ S, ∑ j ∈ S,
      (c i * nnrealIocIndicator (a i) (b i) s) *
        (c j * nnrealIocIndicator (a j) (b j) s) ∂Q) = _
  rw [integral_finsetSum S (fun i hi =>
    integrable_finsetSum S (fun j hj => htermInt i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj => htermInt i hi j hj)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∫ s, (c i * nnrealIocIndicator (a i) (b i) s) *
        (c j * nnrealIocIndicator (a j) (b j) s) ∂Q) =
        ∫ s, (c i * c j) *
          (nnrealIocIndicator (a i) (b i) s *
            nnrealIocIndicator (a j) (b j) s) ∂Q := by
      apply integral_congr_ae
      filter_upwards with s
      ring
    _ =
        (c i * c j) * ∫ s,
          nnrealIocIndicator (a i) (b i) s *
            nnrealIocIndicator (a j) (b j) s ∂Q := by
      rw [integral_const_mul]
    _ = c i * c j * clippedIntervalCovariation
        (a i) (b i) (a j) (b j) t := by
      dsimp only [Q]
      rw [integral_nnrealIocIndicator_mul (hinterval i hi)
        (hinterval j hj) t]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
theorem elementaryFinsuppToPredictable_coeFn
    (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ) :
    (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => ∑ x ∈ v.support, v x *
        nnrealIocIndicator x.1 x.2.1.1 p.1 *
          (x.2.2 : W → ℝ) p.2 := by
  rw [show elementaryFinsuppToPredictable (Filtration.natural B hsm) P v =
      ∑ x ∈ v.support, v x •
        elementaryPredictableGenerator (Filtration.natural B hsm) P x by
    unfold elementaryFinsuppToPredictable
    rfl]
  have hsum := Lp.coeFn_fun_finsetSum v.support
    (fun x => v x •
      (elementaryPredictableGenerator (Filtration.natural B hsm) P x :
        TimeProcessL2 P))
  have hterm : ∀ x ∈ v.support,
      (((v x) • (elementaryPredictableGenerator
        (Filtration.natural B hsm) P x : TimeProcessL2 P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p => v x * nnrealIocIndicator x.1 x.2.1.1 p.1 *
          (x.2.2 : W → ℝ) p.2 := by
    intro x _hx
    have helem := elementaryPredictable_coeFn
      (Filtration.natural B hsm) x.1 x.2.1.1 x.2.2
    filter_upwards [Lp.coeFn_smul (v x)
        (elementaryPredictableGenerator
          (Filtration.natural B hsm) P x : TimeProcessL2 P),
      helem] with p hsmul helem'
    rw [hsmul]
    change v x * ((elementaryPredictable (Filtration.natural B hsm)
      x.1 x.2.1.1 x.2.2 : TimeProcessL2 P) : ℝ≥0 × W → ℝ) p = _
    change (elementaryPredictable (Filtration.natural B hsm)
      x.1 x.2.1.1 x.2.2 : ℝ≥0 × W → ℝ) p = _ at helem'
    rw [helem']
    unfold nnrealIocIndicator
    by_cases hp : p.1 ∈ Set.Ioc x.1 x.2.1.1 <;> simp [hp]
  filter_upwards [hsum, v.support.eventually_all.mpr hterm] with p hs hp
  have hcoe : ((∑ x ∈ v.support, v x •
      elementaryPredictableGenerator (Filtration.natural B hsm) P x :
        PredictableProcessL2 (Filtration.natural B hsm) P) : TimeProcessL2 P) =
      ∑ x ∈ v.support, v x •
        (elementaryPredictableGenerator (Filtration.natural B hsm) P x :
          TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ (Filtration.natural B hsm).predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype
        (∑ x ∈ v.support, v x •
          elementaryPredictableGenerator (Filtration.natural B hsm) P x) = _
    rw [map_sum]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro x _hx
    rfl
  rw [hcoe]
  rw [hs]
  apply Finset.sum_congr rfl
  intro x hx
  exact hp x hx

/-- The canonical time integral of the square of a predictable `L²` process,
using its selected product-space representative. -/
noncomputable def predictableQuadraticVariation
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) (ω : W) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) t, ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2
    ∂nonnegativeLebesgueMeasure

omit [CompleteSpace W] [BorelSpace W] in
theorem predictableQuadraticVariation_elementaryFinsuppToPredictable
    (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ)
    (t : ℝ≥0) :
    predictableQuadraticVariation hsm
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v) t =ᵐ[P]
      fun ω => ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation x.1 x.2.1.1 y.1 y.2.1.1 t := by
  classical
  let U := elementaryFinsuppToPredictable (Filtration.natural B hsm) P v
  have hcoe := elementaryFinsuppToPredictable_coeFn hsm v
  have hswap := (Measure.measurePreserving_swap
    (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hcoe
  have hswap' :
      (fun p : W × ℝ≥0 => (U : ℝ≥0 × W → ℝ) p.swap) =ᵐ[
        P.prod nonnegativeLebesgueMeasure]
      fun p => ∑ x ∈ v.support, v x *
        nnrealIocIndicator x.1 x.2.1.1 p.2 * (x.2.2 : W → ℝ) p.1 := by
    simpa [U, Function.comp_def] using hswap
  have hsections := Measure.ae_ae_of_ae_prod hswap'
  filter_upwards [hsections] with ω hω
  unfold predictableQuadraticVariation
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t,
        ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2
        ∂nonnegativeLebesgueMeasure) =
        ∫ s in Set.Ioc (0 : ℝ≥0) t,
          (∑ x ∈ v.support,
            (v x * (x.2.2 : W → ℝ) ω) *
              nnrealIocIndicator x.1 x.2.1.1 s) ^ 2
          ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hω] with s hs
      have hs' : (U : ℝ≥0 × W → ℝ) (s, ω) =
          ∑ x ∈ v.support, v x *
            nnrealIocIndicator x.1 x.2.1.1 s *
              (x.2.2 : W → ℝ) ω := by
        simpa only [Prod.swap_prod_mk] using hs
      rw [hs']
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x ∈ v.support, ∑ y ∈ v.support,
        (v x * (x.2.2 : W → ℝ) ω) * (v y * (y.2.2 : W → ℝ) ω) *
          clippedIntervalCovariation x.1 x.2.1.1 y.1 y.2.1.1 t := by
      exact integral_sq_finset_nnrealIocIndicator v.support
        (fun x => x.1) (fun x => x.2.1.1)
        (fun x hx => x.2.1.2)
        (fun x => v x * (x.2.2 : W → ℝ) ω) t

omit [CompleteSpace W] [BorelSpace W] in
theorem quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp_bracket
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ElementaryPredictableIndex (Filtration.natural B hsm) P →₀ ℝ)
    (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v)) P t
      (predictableQuadraticVariation hsm
        (elementaryFinsuppToPredictable (Filtration.natural B hsm) P v) t) := by
  apply (quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp
    hB hsm v t).congr
  · intro s
    exact Filter.EventuallyEq.rfl
  · exact (predictableQuadraticVariation_elementaryFinsuppToPredictable
      hsm v t).symm

end StochasticCalculus
