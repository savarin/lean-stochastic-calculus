/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.GirsanovFiltered
import StochasticCalculus.GirsanovConstantOracle

/-!
# Constant-coefficient Girsanov regression

The independent Gaussian-law oracle is from commit
93c77028edae070a11cff3a77b2c0f19f662d4e6 of lean-pipeline/girsanov.
These identities compare the full drift process and exact measure, for
every real coefficient and every finite horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The literal predictable drift specializes to the stopped linear drift. -/
theorem girsanovIntegratedDrift_const {W : Type*} (c : ℝ) (T t : ℝ≥0) (omega : W) :
    girsanovIntegratedDrift (fun _ _ ↦ c) T t omega = c * ((min t T : ℝ≥0) : ℝ) := by
  have hmass : nonnegativeLebesgueMeasure.real (Set.Ioc (0 : ℝ≥0) (min t T)) =
      ((min t T : ℝ≥0) : ℝ) := by
    rw [measureReal_def, nonnegativeLebesgueMeasure_Ioc, NNReal.coe_zero,
      sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  unfold girsanovIntegratedDrift
  rw [setIntegral_const, hmass, smul_eq_mul, mul_comm]

/-- The entire shifted process agrees with the independent constant-drift oracle. -/
theorem girsanovShiftedBrownian_const {W : Type*}
    (B : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0) :
    girsanovShiftedBrownian B (fun _ _ ↦ c) T =
      Girsanov.horizonDriftShifted B c T := by
  funext t omega
  simp only [girsanovShiftedBrownian, Girsanov.horizonDriftShifted,
    girsanovIntegratedDrift_const]

/-- The terminal density measure specializes exactly to the oracle's normalized
Esscher measure, including its one-half variance correction. -/
theorem girsanovMeasure_const_eq_oracle
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (c : ℝ) (T : ℝ≥0) :
    girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
      (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T =
      Girsanov.constantGirsanovMeasure P B c T := by
  have hden : (∫ omega, Real.exp (-c * B T omega) ∂P) =
      Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    simpa using Girsanov.integral_exp_brownian_linearCombination hB 0 (-c) T T
  unfold girsanovMeasure girsanovDensity doleansDadeExponential doleansDadeLog
    Girsanov.constantGirsanovMeasure Measure.tilted
  simp only [min_self, hden]
  congr 1
  funext omega
  congr 1
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Independent regression of the complete constant-coefficient endpoint,
using the Gaussian-law proof rather than the predictable theorem. -/
theorem isPreBrownianReal_girsanovShiftedBrownian_constant_regression
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P) (c : ℝ) (T : ℝ≥0) :
    IsPreBrownianReal (girsanovShiftedBrownian B (fun _ _ ↦ c) T)
      (girsanovMeasure P (fun t omega ↦ -c * B (min t T) omega)
        (fun t _ ↦ c ^ 2 * ((min t T : ℝ≥0) : ℝ)) T) := by
  rw [girsanovShiftedBrownian_const, girsanovMeasure_const_eq_oracle hB]
  exact Girsanov.isPreBrownianReal_horizonDriftShifted_constantGirsanovMeasure hB c T

end StochasticCalculus
