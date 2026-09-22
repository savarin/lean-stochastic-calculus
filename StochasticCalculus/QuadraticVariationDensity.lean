/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.QuadraticVariationElementary

/-!
# Quadratic variation by predictable-process density

This file extends the exact elementary-integrand calculation to arbitrary
predictable `L²` integrands.  Uniform `L¹` perturbation estimates for both
the discrete quadratic sums and the canonical bracket allow a
convergence-together argument.  A final change of variables identifies the
canonical nonnegative-time bracket with the displayed diffusion variance of
an `IsItoProcess`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal InnerProductSpace

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem quadraticVariationApprox_sub_eq_covariation_sub_add
    (X Y : ℝ≥0 → W → ℝ) (t : ℝ≥0) (n : ℕ) (ω : W) :
    quadraticVariationApprox X t n ω - quadraticVariationApprox Y t n ω =
      quadraticCovariationApprox
        (fun s ω => X s ω - Y s ω)
        (fun s ω => X s ω + Y s ω) t n ω := by
  unfold quadraticVariationApprox quadraticCovariationApprox
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [CompleteSpace W] [BorelSpace W] in
theorem naturalItoProcessRepresentative_sub_ae
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P) (s : ℝ≥0) :
    (fun ω => naturalItoProcessRepresentative hB hsm rfl U s ω -
        naturalItoProcessRepresentative hB hsm rfl V s ω) =ᵐ[P]
      naturalItoProcessRepresentative hB hsm rfl (U - V) s := by
  have hU := naturalItoProcess_ae_eq_representative hB hsm rfl U s
  have hV := naturalItoProcess_ae_eq_representative hB hsm rfl V s
  have hD := naturalItoProcess_ae_eq_representative hB hsm rfl (U - V) s
  have hlin : naturalItoProcess hB hsm rfl (U - V) s =
      naturalItoProcess hB hsm rfl U s -
        naturalItoProcess hB hsm rfl V s := by
    unfold naturalItoProcess
    rw [predictableTimeRestrict_sub, map_sub]
  have hcoe := Lp.coeFn_sub (naturalItoProcess hB hsm rfl U s)
    (naturalItoProcess hB hsm rfl V s)
  filter_upwards [hU, hV, hD, hcoe] with ω hUω hVω hDω hcoeω
  change (naturalItoProcess hB hsm rfl U s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl U s ω at hUω
  change (naturalItoProcess hB hsm rfl V s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl V s ω at hVω
  change (naturalItoProcess hB hsm rfl (U - V) s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl (U - V) s ω at hDω
  rw [← hUω, ← hVω, ← hDω, hlin, hcoeω]
  rfl

omit [CompleteSpace W] [BorelSpace W] in
theorem naturalItoProcessRepresentative_add_ae
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P) (s : ℝ≥0) :
    (fun ω => naturalItoProcessRepresentative hB hsm rfl U s ω +
        naturalItoProcessRepresentative hB hsm rfl V s ω) =ᵐ[P]
      naturalItoProcessRepresentative hB hsm rfl (U + V) s := by
  have hU := naturalItoProcess_ae_eq_representative hB hsm rfl U s
  have hV := naturalItoProcess_ae_eq_representative hB hsm rfl V s
  have hS := naturalItoProcess_ae_eq_representative hB hsm rfl (U + V) s
  have hlin : naturalItoProcess hB hsm rfl (U + V) s =
      naturalItoProcess hB hsm rfl U s +
        naturalItoProcess hB hsm rfl V s := by
    unfold naturalItoProcess
    rw [predictableTimeRestrict_add, map_add]
  have hcoe := Lp.coeFn_add (naturalItoProcess hB hsm rfl U s)
    (naturalItoProcess hB hsm rfl V s)
  filter_upwards [hU, hV, hS, hcoe] with ω hUω hVω hSω hcoeω
  change (naturalItoProcess hB hsm rfl U s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl U s ω at hUω
  change (naturalItoProcess hB hsm rfl V s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl V s ω at hVω
  change (naturalItoProcess hB hsm rfl (U + V) s : W → ℝ) ω =
    naturalItoProcessRepresentative hB hsm rfl (U + V) s ω at hSω
  rw [← hUω, ← hVω, ← hSω, hlin, hcoeω]
  rfl

omit [CompleteSpace W] [BorelSpace W] in
theorem integrable_quadraticVariationApprox_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) (n : ℕ) :
    Integrable (quadraticVariationApprox
      (naturalItoProcessRepresentative hB hsm rfl U) t n) P := by
  unfold quadraticVariationApprox
  exact integrable_finsetSum (Finset.range n) (fun i _hi =>
    integrable_sq_naturalItoProcessRepresentative_sub hB hsm U _ _)

omit [CompleteSpace W] [BorelSpace W] in
theorem integral_abs_quadraticVariationApprox_sub_le
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, |quadraticVariationApprox
          (naturalItoProcessRepresentative hB hsm rfl U) t n ω -
        quadraticVariationApprox
          (naturalItoProcessRepresentative hB hsm rfl V) t n ω| ∂P ≤
      ‖U - V‖ * ‖U + V‖ := by
  let X := naturalItoProcessRepresentative hB hsm rfl U
  let Y := naturalItoProcessRepresentative hB hsm rfl V
  let D := naturalItoProcessRepresentative hB hsm rfl (U - V)
  let S := naturalItoProcessRepresentative hB hsm rfl (U + V)
  let QX := quadraticVariationApprox X t n
  let QY := quadraticVariationApprox Y t n
  let QD := quadraticVariationApprox D t n
  let QS := quadraticVariationApprox S t n
  have hDprocess : ∀ s, (fun ω => X s ω - Y s ω) =ᵐ[P] D s := by
    intro s
    simpa only [X, Y, D] using
      naturalItoProcessRepresentative_sub_ae hB hsm U V s
  have hSprocess : ∀ s, (fun ω => X s ω + Y s ω) =ᵐ[P] S s := by
    intro s
    simpa only [X, Y, S] using
      naturalItoProcessRepresentative_add_ae hB hsm U V s
  have hQD : quadraticVariationApprox
      (fun s ω => X s ω - Y s ω) t n =ᵐ[P] QD := by
    simpa only [QD] using quadraticVariationApprox_congr_ae hDprocess t n
  have hQS : quadraticVariationApprox
      (fun s ω => X s ω + Y s ω) t n =ᵐ[P] QS := by
    simpa only [QS] using quadraticVariationApprox_congr_ae hSprocess t n
  have hQXint : Integrable QX P := by
    simpa only [QX, X] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm U t n
  have hQYint : Integrable QY P := by
    simpa only [QY, Y] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm V t n
  have hQDint : Integrable QD P := by
    simpa only [QD, D] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm (U - V) t n
  have hQSint : Integrable QS P := by
    simpa only [QS, S] using
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB hsm (U + V) t n
  have hDtime : ∀ s, AEStronglyMeasurable (D s) P := fun s =>
    by
      simpa only [D] using AEStronglyMeasurable.mono
        ((Filtration.natural B hsm).le s)
        (StronglyMeasurable.aestronglyMeasurable
          (stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm rfl (U - V) s))
  have hStime : ∀ s, AEStronglyMeasurable (S s) P := fun s =>
    by
      simpa only [S] using AEStronglyMeasurable.mono
        ((Filtration.natural B hsm).le s)
        (StronglyMeasurable.aestronglyMeasurable
          (stronglyMeasurable_naturalItoProcessRepresentative
            hB hsm rfl (U + V) s))
  have hQDmeas : AEStronglyMeasurable QD P := by
    simpa only [QD] using aestronglyMeasurable_quadraticVariationApprox hDtime t n
  have hQSmeas : AEStronglyMeasurable QS P := by
    simpa only [QS] using aestronglyMeasurable_quadraticVariationApprox hStime t n
  have hsqrtQDmeas : AEStronglyMeasurable (fun ω => Real.sqrt (QD ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQDmeas
  have hsqrtQSmeas : AEStronglyMeasurable (fun ω => Real.sqrt (QS ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQSmeas
  have hsqrtQDmem : MemLp (fun ω => Real.sqrt (QD ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hsqrtQDmeas).2
    apply hQDint.congr
    filter_upwards with ω
    rw [Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg D t n ω
  have hsqrtQSmem : MemLp (fun ω => Real.sqrt (QS ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq hsqrtQSmeas).2
    apply hQSint.congr
    filter_upwards with ω
    rw [Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg S t n ω
  have hpoint : (fun ω => |QX ω - QY ω|) ≤ᵐ[P]
      fun ω => Real.sqrt (QD ω) * Real.sqrt (QS ω) := by
    filter_upwards [hQD, hQS] with ω hQDω hQSω
    calc
      |QX ω - QY ω| =
          |quadraticCovariationApprox
            (fun s ω => X s ω - Y s ω)
            (fun s ω => X s ω + Y s ω) t n ω| := by
        rw [← quadraticVariationApprox_sub_eq_covariation_sub_add]
      _ ≤ Real.sqrt
          (quadraticVariationApprox (fun s ω => X s ω - Y s ω) t n ω *
            quadraticVariationApprox (fun s ω => X s ω + Y s ω) t n ω) :=
        Real.abs_le_sqrt (quadraticCovariationApprox_sq_le _ _ t n ω)
      _ = Real.sqrt (QD ω) * Real.sqrt (QS ω) := by
        rw [hQDω, hQSω, Real.sqrt_mul]
        exact quadraticVariationApprox_nonneg D t n ω
  have hleftint : Integrable (fun ω => |QX ω - QY ω|) P :=
    (hQXint.sub hQYint).abs
  have hrightint : Integrable
      (fun ω => Real.sqrt (QD ω) * Real.sqrt (QS ω)) P := by
    change Integrable
      ((fun ω => Real.sqrt (QD ω)) * (fun ω => Real.sqrt (QS ω))) P
    exact hsqrtQDmem.integrable_mul hsqrtQSmem
  have hsqrtQDmem' : MemLp (fun ω => Real.sqrt (QD ω))
      (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat] using hsqrtQDmem
  have hsqrtQSmem' : MemLp (fun ω => Real.sqrt (QS ω))
      (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat] using hsqrtQSmem
  have hsqrtQDpow :
      (fun ω => (Real.sqrt (QD ω)) ^ (2 : ℝ)) =ᵐ[P] QD := by
    filter_upwards with ω
    rw [Real.rpow_two, Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg D t n ω
  have hsqrtQSpow :
      (fun ω => (Real.sqrt (QS ω)) ^ (2 : ℝ)) =ᵐ[P] QS := by
    filter_upwards with ω
    rw [Real.rpow_two, Real.sq_sqrt]
    exact quadraticVariationApprox_nonneg S t n ω
  calc
    (∫ ω, |QX ω - QY ω| ∂P) ≤
        ∫ ω, Real.sqrt (QD ω) * Real.sqrt (QS ω) ∂P :=
      integral_mono_ae hleftint hrightint hpoint
    _ ≤ (∫ ω, (Real.sqrt (QD ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) *
        (∫ ω, (Real.sqrt (QS ω)) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_le_Lp_mul_Lq_of_nonneg
        Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
        (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
        hsqrtQDmem' hsqrtQSmem'
    _ = Real.sqrt (∫ ω, QD ω ∂P) * Real.sqrt (∫ ω, QS ω ∂P) := by
      rw [integral_congr_ae hsqrtQDpow, integral_congr_ae hsqrtQSpow]
      norm_num [← Real.sqrt_eq_rpow]
    _ = ‖naturalItoProcess hB hsm rfl (U - V) t‖ *
        ‖naturalItoProcess hB hsm rfl (U + V) t‖ := by
      rw [show (∫ ω, QD ω ∂P) =
          ‖naturalItoProcess hB hsm rfl (U - V) t‖ ^ 2 by
        simpa only [QD, D] using
          integral_quadraticVariationApprox_naturalItoProcessRepresentative
            hB hsm (U - V) t hn,
        show (∫ ω, QS ω ∂P) =
          ‖naturalItoProcess hB hsm rfl (U + V) t‖ ^ 2 by
        simpa only [QS, S] using
          integral_quadraticVariationApprox_naturalItoProcessRepresentative
            hB hsm (U + V) t hn]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ ‖U - V‖ * ‖U + V‖ := by
      exact mul_le_mul
        (norm_naturalItoProcess_le hB hsm rfl (U - V) t)
        (norm_naturalItoProcess_le hB hsm rfl (U + V) t)
        (norm_nonneg _) (norm_nonneg _)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] in
theorem integral_sq_predictableProcess_eq_norm_sq
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ∫ p, ((U : ℝ≥0 × W → ℝ) p) ^ 2
        ∂(nonnegativeLebesgueMeasure.prod P) = ‖U‖ ^ 2 := by
  calc
    (∫ p, ((U : ℝ≥0 × W → ℝ) p) ^ 2
        ∂(nonnegativeLebesgueMeasure.prod P)) =
        inner ℝ (U : TimeProcessL2 P) (U : TimeProcessL2 P) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with p
      simp [pow_two]
    _ = ‖(U : TimeProcessL2 P)‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖U‖ ^ 2 := rfl

omit [CompleteSpace W] [BorelSpace W] in
theorem integrable_predictableQuadraticVariation
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P) (t : ℝ≥0) :
    Integrable (predictableQuadraticVariation hsm U t) P := by
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)
  have hsq : Integrable (fun p : ℝ≥0 × W =>
      ((U : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  have hmeasure : Q.prod P ≤ nonnegativeLebesgueMeasure.prod P := by
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hsqQ := hsq.mono_measure hmeasure
  have houter := hsqQ.integral_prod_right
  change Integrable (fun y => ∫ x in Set.Ioc (0 : ℝ≥0) t,
    ((U : ℝ≥0 × W → ℝ) (x, y)) ^ 2 ∂nonnegativeLebesgueMeasure) P
  exact houter

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] in
theorem predictableProcess_coeFn_sub
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ((U - V : PredictableProcessL2 (Filtration.natural B hsm) P) :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => (U : ℝ≥0 × W → ℝ) p - (V : ℝ≥0 × W → ℝ) p := by
  have hsub : ((U - V : PredictableProcessL2
      (Filtration.natural B hsm) P) : TimeProcessL2 P) =
      (U : TimeProcessL2 P) - (V : TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ (Filtration.natural B hsm).predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype (U - V) = _
    rw [map_sub]
    rfl
  rw [show ((U - V : PredictableProcessL2
      (Filtration.natural B hsm) P) : ℝ≥0 × W → ℝ) =
      (((U - V : PredictableProcessL2
        (Filtration.natural B hsm) P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) by rfl, hsub]
  filter_upwards [Lp.coeFn_sub (U : TimeProcessL2 P)
      (V : TimeProcessL2 P)] with p hp
  simpa only [Pi.sub_apply] using hp

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] in
theorem predictableProcess_coeFn_add
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P) :
    ((U + V : PredictableProcessL2 (Filtration.natural B hsm) P) :
        ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p => (U : ℝ≥0 × W → ℝ) p + (V : ℝ≥0 × W → ℝ) p := by
  have hadd : ((U + V : PredictableProcessL2
      (Filtration.natural B hsm) P) : TimeProcessL2 P) =
      (U : TimeProcessL2 P) + (V : TimeProcessL2 P) := by
    change (lpMeas ℝ ℝ (Filtration.natural B hsm).predictable 2
      (nonnegativeLebesgueMeasure.prod P)).subtype (U + V) = _
    rw [map_add]
    rfl
  rw [show ((U + V : PredictableProcessL2
      (Filtration.natural B hsm) P) : ℝ≥0 × W → ℝ) =
      (((U + V : PredictableProcessL2
        (Filtration.natural B hsm) P) : TimeProcessL2 P) :
          ℝ≥0 × W → ℝ) by rfl, hadd]
  filter_upwards [Lp.coeFn_add (U : TimeProcessL2 P)
      (V : TimeProcessL2 P)] with p hp
  simpa only [Pi.add_apply] using hp

omit [CompleteSpace W] [BorelSpace W] in
theorem integral_abs_predictableQuadraticVariation_sub_le
    (hsm : ∀ t, StronglyMeasurable (B t))
    (U V : PredictableProcessL2 (Filtration.natural B hsm) P) (t : ℝ≥0) :
    ∫ ω, |predictableQuadraticVariation hsm U t ω -
        predictableQuadraticVariation hsm V t ω| ∂P ≤
      ‖U - V‖ * ‖U + V‖ := by
  let Q := nonnegativeLebesgueMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)
  let F : ℝ≥0 × W → ℝ := fun p =>
    (U : ℝ≥0 × W → ℝ) p - (V : ℝ≥0 × W → ℝ) p
  let G : ℝ≥0 × W → ℝ := fun p =>
    (U : ℝ≥0 × W → ℝ) p + (V : ℝ≥0 × W → ℝ) p
  let A : ℝ≥0 × W → ℝ := fun p =>
    |((U : ℝ≥0 × W → ℝ) p) ^ 2 - ((V : ℝ≥0 × W → ℝ) p) ^ 2|
  have hFmem : MemLp F 2 (nonnegativeLebesgueMeasure.prod P) := by
    dsimp only [F]
    exact (Lp.memLp (U : TimeProcessL2 P)).sub (Lp.memLp (V : TimeProcessL2 P))
  have hGmem : MemLp G 2 (nonnegativeLebesgueMeasure.prod P) := by
    dsimp only [G]
    exact (Lp.memLp (U : TimeProcessL2 P)).add (Lp.memLp (V : TimeProcessL2 P))
  have hAeq : A = fun p => |F p * G p| := by
    funext p
    dsimp only [A, F, G]
    congr 1
    ring
  have hAint : Integrable A (nonnegativeLebesgueMeasure.prod P) := by
    rw [hAeq]
    exact (hFmem.integrable_mul hGmem).abs
  have hmeasure : Q.prod P ≤ nonnegativeLebesgueMeasure.prod P := by
    exact Measure.prod_mono Measure.restrict_le_self le_rfl
  have hAQint := hAint.mono_measure hmeasure
  have hU2int : Integrable (fun p : ℝ≥0 × W =>
      ((U : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : TimeProcessL2 P)).integrable_sq
  have hV2int : Integrable (fun p : ℝ≥0 × W =>
      ((V : ℝ≥0 × W → ℝ) p) ^ 2)
      (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (V : TimeProcessL2 P)).integrable_sq
  have hU2Qint := hU2int.mono_measure hmeasure
  have hV2Qint := hV2int.mono_measure hmeasure
  have hpoint : (fun ω => |predictableQuadraticVariation hsm U t ω -
      predictableQuadraticVariation hsm V t ω|) ≤ᵐ[P]
      fun ω => ∫ s, A (s, ω) ∂Q := by
    filter_upwards [hU2Qint.prod_left_ae, hV2Qint.prod_left_ae]
      with ω hUω hVω
    unfold predictableQuadraticVariation
    change |(∫ s, ((U : ℝ≥0 × W → ℝ) (s, ω)) ^ 2 ∂Q) -
        ∫ s, ((V : ℝ≥0 × W → ℝ) (s, ω)) ^ 2 ∂Q| ≤ _
    rw [← integral_sub hUω hVω]
    exact abs_integral_le_integral_abs
  have hleftint : Integrable (fun ω =>
      |predictableQuadraticVariation hsm U t ω -
        predictableQuadraticVariation hsm V t ω|) P :=
    ((integrable_predictableQuadraticVariation hsm U t).sub
      (integrable_predictableQuadraticVariation hsm V t)).abs
  have hrightint : Integrable (fun ω => ∫ s, A (s, ω) ∂Q) P :=
    hAQint.integral_prod_right
  have hFmem' : MemLp F (ENNReal.ofReal (2 : ℝ))
      (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [ENNReal.ofReal_ofNat] using hFmem
  have hGmem' : MemLp G (ENNReal.ofReal (2 : ℝ))
      (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [ENNReal.ofReal_ofNat] using hGmem
  have hFintSq :
      (∫ p, ‖F p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
        ‖U - V‖ ^ 2 := by
    calc
      (∫ p, ‖F p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
          ∫ p, F p ^ 2 ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ = ∫ p, (((U - V : PredictableProcessL2
          (Filtration.natural B hsm) P) : ℝ≥0 × W → ℝ) p) ^ 2
          ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards [predictableProcess_coeFn_sub hsm U V]
          with p hp
        rw [hp]
      _ = ‖U - V‖ ^ 2 :=
        integral_sq_predictableProcess_eq_norm_sq hsm (U - V)
  have hGintSq :
      (∫ p, ‖G p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
        ‖U + V‖ ^ 2 := by
    calc
      (∫ p, ‖G p‖ ^ (2 : ℝ) ∂(nonnegativeLebesgueMeasure.prod P)) =
          ∫ p, G p ^ 2 ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
      _ = ∫ p, (((U + V : PredictableProcessL2
          (Filtration.natural B hsm) P) : ℝ≥0 × W → ℝ) p) ^ 2
          ∂(nonnegativeLebesgueMeasure.prod P) := by
        apply integral_congr_ae
        filter_upwards [predictableProcess_coeFn_add hsm U V]
          with p hp
        rw [hp]
      _ = ‖U + V‖ ^ 2 :=
        integral_sq_predictableProcess_eq_norm_sq hsm (U + V)
  calc
    (∫ ω, |predictableQuadraticVariation hsm U t ω -
        predictableQuadraticVariation hsm V t ω| ∂P) ≤
        ∫ ω, ∫ s, A (s, ω) ∂Q ∂P :=
      integral_mono_ae hleftint hrightint hpoint
    _ = ∫ p, A p ∂(Q.prod P) :=
      (integral_prod_symm A hAQint).symm
    _ ≤ ∫ p, A p ∂(nonnegativeLebesgueMeasure.prod P) :=
      integral_mono_measure hmeasure
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hAint
    _ = ∫ p, ‖F p‖ * ‖G p‖
        ∂(nonnegativeLebesgueMeasure.prod P) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hAeq]
      simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ (∫ p, ‖F p‖ ^ (2 : ℝ)
          ∂(nonnegativeLebesgueMeasure.prod P)) ^ (1 / (2 : ℝ)) *
        (∫ p, ‖G p‖ ^ (2 : ℝ)
          ∂(nonnegativeLebesgueMeasure.prod P)) ^ (1 / (2 : ℝ)) := by
      exact integral_mul_norm_le_Lp_mul_Lq
        Real.HolderConjugate.two_two hFmem' hGmem'
    _ = ‖U - V‖ * ‖U + V‖ := by
      rw [hFintSq, hGintSq]
      norm_num [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- A convergence-together lemma in measure, with both approximation errors
controlled uniformly in `L¹`. -/
theorem tendstoInMeasure_of_uniform_integral_approx
    [IsFiniteMeasure P]
    (f : ℕ → W → ℝ) (g : W → ℝ)
    (F : ℕ → ℕ → W → ℝ) (G : ℕ → W → ℝ) (a : ℕ → ℝ)
    (ha : Tendsto a Filter.atTop (nhds 0))
    (ha_nonneg : ∀ k, 0 ≤ a k)
    (hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k))
    (hleftInt : ∀ k n, Integrable (fun ω => ‖f n ω - F k n ω‖) P)
    (hleft : ∀ k n, ∫ ω, ‖f n ω - F k n ω‖ ∂P ≤ a k)
    (hrightInt : ∀ k, Integrable (fun ω => ‖G k ω - g ω‖) P)
    (hright : ∀ k, ∫ ω, ‖G k ω - g ω‖ ∂P ≤ a k) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  have hδ4 : 0 < δ / 4 := div_pos hδ (by norm_num)
  have ha_div : Tendsto (fun k => a k / (ε / 3)) Filter.atTop (nhds 0) := by
    simpa only [zero_div] using ha.div_const (ε / 3)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp ha_div) (δ / 4) hδ4
  have haKlt : a K / (ε / 3) < δ / 4 := by
    have := hK K le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (div_nonneg (ha_nonneg K) hε3.le)] at this
    exact this
  have hmiddle := (tendstoInMeasure_iff_measureReal_norm.mp (hFG K))
    (ε / 3) hε3
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmiddle) (δ / 2)
    (div_pos hδ (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  let E : Set W := {ω | ε ≤ ‖f n ω - g ω‖}
  let A : Set W := {ω | ε / 3 ≤ ‖f n ω - F K n ω‖}
  let C : Set W := {ω | ε / 3 ≤ ‖G K ω - g ω‖}
  let D : Set W := {ω | ε / 3 ≤ ‖F K n ω - G K ω‖}
  have hsubset : E ⊆ (A ∪ D) ∪ C := by
    intro ω hω
    by_contra hmem
    simp only [Set.mem_union, not_or, A, C, D, Set.mem_ofPred_eq,
      not_le] at hmem
    have htri : ‖f n ω - g ω‖ ≤
        ‖f n ω - F K n ω‖ + ‖F K n ω - G K ω‖ +
          ‖G K ω - g ω‖ := by
      calc
        ‖f n ω - g ω‖ = ‖(f n ω - F K n ω) +
            (F K n ω - G K ω) + (G K ω - g ω)‖ := by
          congr 1
          ring
        _ ≤ ‖f n ω - F K n ω‖ + ‖F K n ω - G K ω‖ +
            ‖G K ω - g ω‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)
    have hsumlt : ‖f n ω - F K n ω‖ + ‖F K n ω - G K ω‖ +
        ‖G K ω - g ω‖ < ε := by
      calc
        _ < ε / 3 + ε / 3 + ε / 3 := by
          exact add_lt_add (add_lt_add hmem.1.1 hmem.1.2) hmem.2
        _ = ε := by ring
    exact (not_lt_of_ge hω) (htri.trans_lt hsumlt)
  have hAmarkov : (ε / 3) * P.real A ≤
      ∫ ω, ‖f n ω - F K n ω‖ ∂P := by
    simpa only [A] using mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hleftInt K n) (ε / 3)
  have hAle : P.real A ≤ a K / (ε / 3) := by
    apply (le_div_iff₀ hε3).2
    simpa only [mul_comm] using hAmarkov.trans (hleft K n)
  have hCmarkov : (ε / 3) * P.real C ≤
      ∫ ω, ‖G K ω - g ω‖ ∂P := by
    simpa only [C] using mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hrightInt K) (ε / 3)
  have hCle : P.real C ≤ a K / (ε / 3) := by
    apply (le_div_iff₀ hε3).2
    simpa only [mul_comm] using hCmarkov.trans (hright K)
  have hDlt : P.real D < δ / 2 := by
    have hraw := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hraw
    simpa only [D] using hraw
  have hEle : P.real E ≤ P.real A + P.real D + P.real C := by
    calc
      P.real E ≤ P.real ((A ∪ D) ∪ C) := measureReal_mono hsubset
      _ ≤ P.real (A ∪ D) + P.real C := measureReal_union_le _ _
      _ ≤ P.real A + P.real D + P.real C := by
        gcongr
        exact measureReal_union_le _ _
  have hEδ : P.real E < δ := by
    calc
      P.real E ≤ P.real A + P.real D + P.real C := hEle
      _ < δ / 4 + δ / 2 + δ / 4 := by
        exact add_lt_add (add_lt_add (hAle.trans_lt haKlt) hDlt)
          (hCle.trans_lt haKlt)
      _ = δ := by ring
  change dist (P.real E) 0 < δ
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]

omit [CompleteSpace W] [BorelSpace W] in
/-- The natural Itô integral process of an arbitrary predictable `L²`
integrand has the canonical bracket, by elementary density and the two
uniform `L¹` perturbation estimates. -/
theorem quadraticVariation_naturalItoProcessRepresentative
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P) (t : ℝ≥0) :
    HasQuadraticVariationInProbabilityAt
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) P t
      (predictableQuadraticVariation hsm U t) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let e := elementaryFinsuppToPredictable (Filtration.natural B hsm) P
  have hUdense : U ∈ closure (Set.range e) :=
    (denseRange_elementaryFinsuppToPredictable (P := P)
      (Filtration.natural B hsm)) U
  obtain ⟨Uk, hUkRange, hUk⟩ := mem_closure_iff_seq_limit.mp hUdense
  choose v hv using hUkRange
  let f : ℕ → W → ℝ := fun n => quadraticVariationApprox
    (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) t (n + 1)
  let g : W → ℝ := predictableQuadraticVariation hsm U t
  let F : ℕ → ℕ → W → ℝ := fun k n => quadraticVariationApprox
    (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl (Uk k))
      t (n + 1)
  let G : ℕ → W → ℝ := fun k => predictableQuadraticVariation hsm (Uk k) t
  let a : ℕ → ℝ := fun k => ‖U - Uk k‖ * ‖U + Uk k‖
  have ha : Tendsto a Filter.atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => U) Filter.atTop (nhds U) :=
      tendsto_const_nhds
    have hsub := hconst.sub hUk
    have hadd := hconst.add hUk
    have hmul := hsub.norm.mul hadd.norm
    simpa only [a, sub_self, norm_zero, zero_mul] using hmul
  have hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k) := by
    intro k
    have hk := quadraticVariation_naturalItoProcessRepresentative_elementaryFinsupp_bracket
      hB hsm (v k) t
    rw [hv k] at hk
    simpa only [HasQuadraticVariationInProbabilityAt, F, G] using hk
  change TendstoInMeasure P f Filter.atTop g
  apply tendstoInMeasure_of_uniform_integral_approx f g F G a ha
  · intro k
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact hFG
  · intro k n
    have hU :=
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm U t (n + 1)
    have hUk :=
      integrable_quadraticVariationApprox_naturalItoProcessRepresentative
        hB.toIsPreBrownianReal hsm (Uk k) t (n + 1)
    dsimp only [f, F]
    apply ((hU.sub hUk).norm).congr
    filter_upwards with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  · intro k n
    simpa only [f, F, a, Real.norm_eq_abs] using
      integral_abs_quadraticVariationApprox_sub_le
        hB.toIsPreBrownianReal hsm U (Uk k) t (Nat.zero_lt_succ n)
  · intro k
    have hUkInt := integrable_predictableQuadraticVariation hsm (Uk k) t
    have hUInt := integrable_predictableQuadraticVariation hsm U t
    dsimp only [G, g]
    apply ((hUkInt.sub hUInt).norm).congr
    filter_upwards with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  · intro k
    simpa only [G, g, a, Real.norm_eq_abs, abs_sub_comm] using
      integral_abs_predictableQuadraticVariation_sub_le hsm U (Uk k) t

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem map_nonnegativeLebesgueMeasure_restrict_Ioc (t : ℝ≥0) :
    Measure.map ((↑) : ℝ≥0 → ℝ)
        (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t)) =
      (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)) := by
  let f : ℝ≥0 → ℝ := (↑)
  have hf : MeasurableEmbedding f := measurableEmbedding_nnrealCoe_iterated
  have hpre : f ⁻¹' Set.Ioc (0 : ℝ) (t : ℝ) = Set.Ioc (0 : ℝ≥0) t := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioc, f]
    exact and_congr (by norm_cast) (by norm_cast)
  rw [← hpre, ← hf.restrict_map]
  change (Measure.map f (Measure.comap f (volume : Measure ℝ))).restrict
      (Set.Ioc 0 (t : ℝ)) = _
  rw [hf.map_comap, NNReal.range_coe]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  congr 1
  ext s
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
  constructor
  · rintro ⟨hs, _⟩
    exact hs
  · intro hs
    exact ⟨hs, hs.1.le⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem integral_nonnegative_Ioc_eq_real_Icc
    (f : ℝ≥0 → W → ℝ) (t : ℝ≥0) (omega : W) :
    (∫ s in Set.Ioc (0 : ℝ≥0) t, f s omega
        ∂nonnegativeLebesgueMeasure) =
      ∫ r in Set.Icc (0 : ℝ) (t : ℝ), f r.toNNReal omega := by
  have hpres : MeasurePreserving ((↑) : ℝ≥0 → ℝ)
      (nonnegativeLebesgueMeasure.restrict (Set.Ioc 0 t))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ))) :=
    ⟨NNReal.continuous_coe.measurable,
      map_nonnegativeLebesgueMeasure_restrict_Ioc t⟩
  have hchange := hpres.integral_comp measurableEmbedding_nnrealCoe_iterated
    (fun r : ℝ ↦ f r.toNNReal omega)
  calc
    (∫ s in Set.Ioc (0 : ℝ≥0) t, f s omega
        ∂nonnegativeLebesgueMeasure) =
        ∫ r in Set.Ioc (0 : ℝ) (t : ℝ), f r.toNNReal omega := by
          simpa using hchange
    _ = ∫ r in Set.Icc (0 : ℝ) (t : ℝ), f r.toNNReal omega :=
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem integral_nonnegative_Ioc_sq_eq_real_Icc
    (σ : ℝ≥0 → W → ℝ) (t : ℝ≥0) (ω : W) :
    (∫ s in Set.Ioc (0 : ℝ≥0) t, (σ s ω) ^ 2
        ∂nonnegativeLebesgueMeasure) =
      ∫ r in Set.Icc (0 : ℝ) (t : ℝ), (σ r.toNNReal ω) ^ 2 := by
  exact integral_nonnegative_Ioc_eq_real_Icc (fun s omega ↦ (σ s omega) ^ 2) t ω

end StochasticCalculus
