/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Probability.BrownianMotion.Basic

/-!
# A version of a Brownian motion with every path continuous

`IsBrownianReal` gives continuous paths and a zero start only almost surely.
The Girsanov density contract asks for both at every sample point.
`continuousBrownianVersion` replaces the paths on one measurable null set by
the zero path: every path is then continuous and starts at zero, each time
slice stays strongly measurable, and the result is again a Brownian motion
that agrees with the original almost surely at every fixed time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace StochasticCalculus

variable {W : Type*} [MeasurableSpace W]

/-- The measurable null set of sample points whose path is not continuous or
does not start at zero. -/
def brownianExceptionalSet (B : ℝ≥0 → W → ℝ) (P : Measure W) : Set W :=
  toMeasurable P {omega | ¬ (Continuous (fun t => B t omega) ∧ B 0 omega = 0)}

/-- The version of `B` that is the zero path on the exceptional set. -/
def continuousBrownianVersion (B : ℝ≥0 → W → ℝ) (P : Measure W)
    (t : ℝ≥0) : W → ℝ :=
  (brownianExceptionalSet B P)ᶜ.indicator (B t)

theorem measurableSet_brownianExceptionalSet (B : ℝ≥0 → W → ℝ) (P : Measure W) :
    MeasurableSet (brownianExceptionalSet B P) :=
  measurableSet_toMeasurable _ _

theorem measure_brownianExceptionalSet {B : ℝ≥0 → W → ℝ} {P : Measure W}
    (hB : IsBrownianReal B P) :
    P (brownianExceptionalSet B P) = 0 := by
  rw [brownianExceptionalSet, measure_toMeasurable]
  exact ae_iff.mp (hB.cont.and hB.toIsPreBrownianReal.eval_zero_ae_eq_zero)

theorem continuousBrownianVersion_of_mem {B : ℝ≥0 → W → ℝ} {P : Measure W} {omega : W}
    (h : omega ∈ brownianExceptionalSet B P) (t : ℝ≥0) :
    continuousBrownianVersion B P t omega = 0 := by
  simp [continuousBrownianVersion, h]

theorem continuousBrownianVersion_of_notMem {B : ℝ≥0 → W → ℝ} {P : Measure W} {omega : W}
    (h : omega ∉ brownianExceptionalSet B P) (t : ℝ≥0) :
    continuousBrownianVersion B P t omega = B t omega := by
  simp [continuousBrownianVersion, h]

/-- Off the exceptional set, the original path is continuous and starts at zero. -/
theorem continuous_and_zero_of_notMem_brownianExceptionalSet
    {B : ℝ≥0 → W → ℝ} {P : Measure W} {omega : W}
    (h : omega ∉ brownianExceptionalSet B P) :
    Continuous (fun t => B t omega) ∧ B 0 omega = 0 := by
  by_contra hbad
  exact h (subset_toMeasurable P _ hbad)

/-- Every path of the version is continuous. -/
theorem continuous_continuousBrownianVersion (B : ℝ≥0 → W → ℝ) (P : Measure W) (omega : W) :
    Continuous (fun t => continuousBrownianVersion B P t omega) := by
  by_cases h : omega ∈ brownianExceptionalSet B P
  · simp only [continuousBrownianVersion_of_mem h]
    exact continuous_const
  · simp only [continuousBrownianVersion_of_notMem h]
    exact (continuous_and_zero_of_notMem_brownianExceptionalSet h).1

/-- Every path of the version starts at zero. -/
theorem continuousBrownianVersion_zero (B : ℝ≥0 → W → ℝ) (P : Measure W) (omega : W) :
    continuousBrownianVersion B P 0 omega = 0 := by
  by_cases h : omega ∈ brownianExceptionalSet B P
  · exact continuousBrownianVersion_of_mem h 0
  · rw [continuousBrownianVersion_of_notMem h]
    exact (continuous_and_zero_of_notMem_brownianExceptionalSet h).2

theorem stronglyMeasurable_continuousBrownianVersion {B : ℝ≥0 → W → ℝ} (P : Measure W)
    (hsm : ∀ t, StronglyMeasurable (B t)) (t : ℝ≥0) :
    StronglyMeasurable (continuousBrownianVersion B P t) :=
  (hsm t).indicator (measurableSet_brownianExceptionalSet B P).compl

/-- The version agrees with the original almost surely at every fixed time. -/
theorem continuousBrownianVersion_ae_eq {B : ℝ≥0 → W → ℝ} {P : Measure W}
    (hB : IsBrownianReal B P) (t : ℝ≥0) :
    continuousBrownianVersion B P t =ᵐ[P] B t := by
  have hnull : (brownianExceptionalSet B P)ᶜ ∈ ae P :=
    compl_mem_ae_iff.mpr (measure_brownianExceptionalSet hB)
  filter_upwards [hnull] with omega h
  exact continuousBrownianVersion_of_notMem h t

/-- The version is again a Brownian motion. -/
theorem isBrownianReal_continuousBrownianVersion {B : ℝ≥0 → W → ℝ} {P : Measure W}
    (hB : IsBrownianReal B P) :
    IsBrownianReal (continuousBrownianVersion B P) P :=
  ⟨hB.toIsPreBrownianReal.congr fun t => (continuousBrownianVersion_ae_eq hB t).symm,
    Filter.Eventually.of_forall (continuous_continuousBrownianVersion B P)⟩

end StochasticCalculus
