/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.QuadraticVariationDensity

/-!
# Tightness consequences of convergence in measure

Weighted quadratic-variation arguments need uniform control in probability,
not a global moment bound on the finite-variation part of an Itô process.
This file records the elementary tail-transfer lemma that turns the already
proved terminal quadratic-variation convergence into exactly that control.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

noncomputable section

namespace MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

/-- If `q n` converges in measure to `Q`, then an upper tail of `q n` is,
eventually, bounded by a slightly lower upper tail of `Q` plus an arbitrary
error.  No integrability or measurability assumptions beyond those implicit
in convergence in measure are needed. -/
theorem TendstoInMeasure.eventually_measureReal_ge_add_lt
    [IsFiniteMeasure P]
    {q : ℕ → Omega → ℝ} {Q : Omega → ℝ}
    (hq : TendstoInMeasure P q Filter.atTop Q)
    (R epsilon eta : ℝ) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∀ᶠ n in Filter.atTop,
      P.real {omega | R + epsilon ≤ q n omega} <
        eta + P.real {omega | R ≤ Q omega} := by
  have hclose := (tendstoInMeasure_iff_measureReal_norm.mp hq)
    epsilon hepsilon
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hclose) eta heta
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
  let E : Set Omega := {omega | R + epsilon ≤ q n omega}
  let D : Set Omega := {omega | epsilon ≤ ‖q n omega - Q omega‖}
  let T : Set Omega := {omega | R ≤ Q omega}
  have hDlt : P.real D < eta := by
    have hraw := hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hraw
    simpa only [D] using hraw
  have hsubset : E ⊆ D ∪ T := by
    intro omega homega
    by_cases htail : R ≤ Q omega
    · exact Or.inr htail
    · apply Or.inl
      have hQR : Q omega < R := lt_of_not_ge htail
      have hdiff : epsilon < q n omega - Q omega := by
        change R + epsilon ≤ q n omega at homega
        linarith
      change epsilon ≤ ‖q n omega - Q omega‖
      rw [Real.norm_eq_abs]
      exact hdiff.le.trans (le_abs_self (q n omega - Q omega))
  calc
    P.real E ≤ P.real (D ∪ T) := measureReal_mono hsubset
    _ ≤ P.real D + P.real T := measureReal_union_le D T
    _ < eta + P.real T := by linarith

/-- Convergence in measure transfers any vanishing-tail estimate for the
limit to eventual uniform tightness of the approximating sequence. -/
theorem TendstoInMeasure.eventually_tight_of_limit_tails
    [IsFiniteMeasure P]
    {q : ℕ → Omega → ℝ} {Q : Omega → ℝ}
    (hq : TendstoInMeasure P q Filter.atTop Q)
    (hQtail : ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ P.real {omega | R ≤ Q omega} < delta) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨R, hR, hRtail⟩ := hQtail (delta / 2) hhalf
  refine ⟨R + 1, by linarith, ?_⟩
  filter_upwards [hq.eventually_measureReal_ge_add_lt
    R 1 (delta / 2) (by norm_num) hhalf] with n hn
  have hsum : delta / 2 + P.real {omega | R ≤ Q omega} < delta := by
    linarith
  exact hn.trans hsum

/-- A nonnegative integrable real random variable has arbitrarily small
upper tails, in the concrete `measureReal` form used by convergence in
measure. -/
theorem Integrable.exists_measureReal_ge_lt_of_nonnegative
    {Q : Omega → ℝ} (hQint : Integrable Q P) (hQnonneg : 0 ≤ᵐ[P] Q) :
    ∀ delta : ℝ, 0 < delta →
      ∃ R : ℝ, 0 < R ∧ P.real {omega | R ≤ Q omega} < delta := by
  intro delta hdelta
  let I : ℝ := ∫ omega, Q omega ∂P
  have hI : 0 ≤ I := integral_nonneg_of_ae hQnonneg
  let R : ℝ := (I + 1) / delta
  have hR : 0 < R := div_pos (by linarith) hdelta
  have hmarkov : R * P.real {omega | R ≤ Q omega} ≤ I := by
    simpa only [I, R] using
      (mul_meas_ge_le_integral_of_nonneg hQnonneg hQint R)
  have hmeasure : P.real {omega | R ≤ Q omega} ≤ I / R := by
    apply (le_div_iff₀ hR).2
    simpa only [mul_comm] using hmarkov
  have hratio : I / R < delta := by
    apply (div_lt_iff₀ hR).2
    have hdelta_ne : delta ≠ 0 := ne_of_gt hdelta
    have hrewrite : delta * R = I + 1 := by
      dsimp only [R]
      field_simp
    rw [hrewrite]
    linarith
  exact ⟨R, hR, hmeasure.trans_lt hratio⟩

/-- In particular, convergence in measure to a nonnegative integrable limit
makes the approximating sequence eventually tight in probability. -/
theorem TendstoInMeasure.eventually_tight_of_integrable_nonnegative_limit
    [IsFiniteMeasure P]
    {q : ℕ → Omega → ℝ} {Q : Omega → ℝ}
    (hq : TendstoInMeasure P q Filter.atTop Q)
    (hQint : Integrable Q P) (hQnonneg : 0 ≤ᵐ[P] Q) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta :=
  hq.eventually_tight_of_limit_tails
    (hQint.exists_measureReal_ge_lt_of_nonnegative hQnonneg)

end MeasureTheory

namespace StochasticCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B X mu sigma : ℝ≥0 → W → ℝ}

end StochasticCalculus
