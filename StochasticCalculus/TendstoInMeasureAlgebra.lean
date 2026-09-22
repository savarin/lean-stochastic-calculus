/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.ItoProcess

/-!
# Convergence in measure for real sequences

Algebra of convergence in measure for real-valued sequences of random
variables: sums, products by fixed or constant factors, and comparison,
without measurability side conditions where none are needed.  The later
quadratic-variation layers use these to pass limits through partition sums.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology InnerProductSpace

noncomputable section
set_option linter.unusedDecidableInType false

section TendstoInMeasureRealAlgebra

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise addition preserves real-valued convergence in measure over an
arbitrary filter, without measurability assumptions on the functions. -/
theorem TendstoInMeasure.add_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u v : ι → Ω → ℝ} {U V : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U)
    (hv : TendstoInMeasure Q v l V) :
    TendstoInMeasure Q (fun i ω => u i ω + v i ω) l
      (fun ω => U ω + V ω) := by
  rw [tendstoInMeasure_iff_dist] at hu hv ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have huHalf := hu (ε / 2) hhalf
  have hvHalf := hv (ε / 2) hhalf
  have hsum : Filter.Tendsto
      (fun i =>
        Q {ω | ε / 2 ≤ dist (u i ω) (U ω)} +
          Q {ω | ε / 2 ≤ dist (v i ω) (V ω)}) l (nhds 0) := by
    simpa only [add_zero] using huHalf.add hvHalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro i
  calc
    Q {ω | ε ≤ dist (u i ω + v i ω) (U ω + V ω)} ≤
        Q ({ω | ε / 2 ≤ dist (u i ω) (U ω)} ∪
          {ω | ε / 2 ≤ dist (v i ω) (V ω)}) := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      change ε ≤ dist (u i ω + v i ω) (U ω + V ω) at hω
      by_contra hUnion
      have huSmall : dist (u i ω) (U ω) < ε / 2 :=
        lt_of_not_ge (fun huBad => hUnion (Or.inl huBad))
      have hvSmall : dist (v i ω) (V ω) < ε / 2 :=
        lt_of_not_ge (fun hvBad => hUnion (Or.inr hvBad))
      have hdist :
          dist (u i ω + v i ω) (U ω + V ω) ≤
            dist (u i ω) (U ω) + dist (v i ω) (V ω) :=
        dist_add_add_le _ _ _ _
      linarith
    _ ≤ Q {ω | ε / 2 ≤ dist (u i ω) (U ω)} +
        Q {ω | ε / 2 ≤ dist (v i ω) (V ω)} := measure_union_le _ _

/-- Deterministic scalar multiplication preserves real-valued convergence in
measure over an arbitrary filter, without measurability assumptions on the
functions. -/
theorem TendstoInMeasure.const_mul_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u : ι → Ω → ℝ} {U : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U) (c : ℝ) :
    TendstoInMeasure Q (fun i ω => c * u i ω) l (fun ω => c * U ω) := by
  rw [tendstoInMeasure_iff_norm] at hu ⊢
  intro ε hε
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, sub_self, norm_zero, Set.ofPred_false, measure_empty,
      not_le.mpr hε] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0))
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    have hscaled := hu (ε / |c|) (div_pos hε hcpos)
    have hfun :
        (fun i => Q {x | ε ≤ ‖c * u i x - c * U x‖}) =
        (fun i => Q {x | ε / |c| ≤ ‖u i x - U x‖}) := by
      funext i
      apply congrArg Q
      ext ω
      simp only [Set.mem_ofPred_eq, ← mul_sub, norm_mul, Real.norm_eq_abs]
      rw [div_le_iff₀ hcpos, mul_comm]
    rw [hfun]
    exact hscaled

/-- Pointwise subtraction preserves real-valued convergence in measure over
an arbitrary filter, without measurability assumptions on the functions. -/
theorem TendstoInMeasure.sub_real_noMeas
    {ι : Type*} {Q : Measure Ω} {u v : ι → Ω → ℝ} {U V : Ω → ℝ}
    {l : Filter ι} (hu : TendstoInMeasure Q u l U)
    (hv : TendstoInMeasure Q v l V) :
    TendstoInMeasure Q (fun i ω => u i ω - v i ω) l
      (fun ω => U ω - V ω) := by
  have hneg := hv.const_mul_real_noMeas (-1)
  have hadd := hu.add_real_noMeas hneg
  apply hadd.congr
  · intro i
    filter_upwards with ω
    ring
  · filter_upwards with ω
    ring

/-- Convergence in measure of real-valued sequences is preserved by
pointwise addition. Mathlib's convergence-in-measure API does not currently
package this algebraic operation. -/
theorem TendstoInMeasure.add_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u v : ℕ → Ω → ℝ} {U V : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (hv : TendstoInMeasure Q v Filter.atTop V)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hvMeas : ∀ n, AEStronglyMeasurable (v n) Q) :
    TendstoInMeasure Q (fun n ω => u n ω + v n ω)
      Filter.atTop (fun ω => U ω + V ω) := by
  have _hsumMeas : ∀ n, AEStronglyMeasurable
      (fun ω => u n ω + v n ω) Q :=
    fun n => (huMeas n).add (hvMeas n)
  exact hu.add_real_noMeas hv

/-- Convergence in measure of real-valued sequences is preserved by
pointwise subtraction. -/
theorem TendstoInMeasure.sub_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u v : ℕ → Ω → ℝ} {U V : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (hv : TendstoInMeasure Q v Filter.atTop V)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hvMeas : ∀ n, AEStronglyMeasurable (v n) Q) :
    TendstoInMeasure Q (fun n ω => u n ω - v n ω)
      Filter.atTop (fun ω => U ω - V ω) := by
  have _hsubMeas : ∀ n, AEStronglyMeasurable
      (fun ω => u n ω - v n ω) Q :=
    fun n => (huMeas n).sub (hvMeas n)
  exact hu.sub_real_noMeas hv

/-- Convergence in measure of real-valued sequences is preserved by
multiplication by a deterministic scalar. -/
theorem TendstoInMeasure.const_mul_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u : ℕ → Ω → ℝ} {U : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q) (c : ℝ) :
    TendstoInMeasure Q (fun n ω => c * u n ω)
      Filter.atTop (fun ω => c * U ω) := by
  have _hmulMeas : ∀ n, AEStronglyMeasurable
      (fun ω => c * u n ω) Q :=
    fun n => aestronglyMeasurable_const.mul (huMeas n)
  exact hu.const_mul_real_noMeas c

/-- Convergence in measure of real-valued sequences is preserved by
pointwise multiplication by a fixed measurable random variable. -/
theorem TendstoInMeasure.mul_fixed_real
    {Q : Measure Ω} [IsFiniteMeasure Q]
    {u : ℕ → Ω → ℝ} {U c : Ω → ℝ}
    (hu : TendstoInMeasure Q u Filter.atTop U)
    (huMeas : ∀ n, AEStronglyMeasurable (u n) Q)
    (hcMeas : AEStronglyMeasurable c Q) :
    TendstoInMeasure Q (fun n ω => c ω * u n ω)
      Filter.atTop (fun ω => c ω * U ω) := by
  have hmulMeas : ∀ n, AEStronglyMeasurable
      (fun ω => c ω * u n ω) Q :=
    fun n => hcMeas.mul (huMeas n)
  rw [exists_seq_tendstoInMeasure_atTop_iff hmulMeas]
  intro ns hns
  obtain ⟨ms, hms, huAE⟩ := (hu.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [huAE] with ω hu'
  exact hu'.const_mul (c ω)

end MeasureTheory

end TendstoInMeasureRealAlgebra
