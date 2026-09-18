/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.QuadraticVariationTightness

/-!
# Vanishing random errors under a tight control

This file records the elementary localization principle used for weighted
quadratic-variation errors.  A random error that vanishes in measure remains
negligible after multiplication by an eventually tight nonnegative control.
-/

open Filter Topology

noncomputable section

namespace MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

/-- Suppose `r n` vanishes in measure and the nonnegative random variables
`q n` are eventually tight.  If the error from `f n` to `g` is pointwise
bounded by `‖r n‖ * q n`, then `f n` converges to `g` in measure.

This is a probability-localized replacement for a uniform deterministic or
`L¹` bound on `q n`. -/
theorem TendstoInMeasure.of_norm_sub_le_mul_of_eventually_tight
    [IsFiniteMeasure P]
    {f r q : ℕ → Omega → ℝ} {g : Omega → ℝ}
    (hr : TendstoInMeasure P r Filter.atTop (fun _ => 0))
    (hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (hq_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta)
    (hcontrol : ∀ n omega,
      ‖f n omega - g omega‖ ≤ ‖r n omega‖ * q n omega) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hdelta2 : 0 < delta / 2 := half_pos hdelta
  obtain ⟨C, hC, hq_eventually⟩ := hq_tight (delta / 2) hdelta2
  have hepsilonC : 0 < epsilon / C := div_pos hepsilon hC
  have hr_close :=
    (tendstoInMeasure_iff_measureReal_norm.mp hr) (epsilon / C) hepsilonC
  obtain ⟨Nr, hNr⟩ :=
    (Metric.tendsto_atTop.mp hr_close) (delta / 2) hdelta2
  obtain ⟨Nq, hNq⟩ := Filter.eventually_atTop.mp hq_eventually
  refine ⟨max Nr Nq, fun n hn => ?_⟩
  have hnr : Nr ≤ n := (le_max_left Nr Nq).trans hn
  have hnq : Nq ≤ n := (le_max_right Nr Nq).trans hn
  let E : Set Omega := {omega | epsilon ≤ ‖f n omega - g omega‖}
  let R : Set Omega := {omega | epsilon / C ≤ ‖r n omega‖}
  let Q : Set Omega := {omega | C ≤ q n omega}
  have hsubset : E ⊆ R ∪ Q := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, not_or, R, Q, Set.mem_ofPred_eq, not_le] at hnot
    have hproduct : ‖r n omega‖ * q n omega < epsilon := by
      calc
        ‖r n omega‖ * q n omega < (epsilon / C) * C :=
          mul_lt_mul_of_nonneg hnot.1 hnot.2 (norm_nonneg _)
            (hq_nonneg n omega)
        _ = epsilon := div_mul_cancel₀ epsilon hC.ne'
    exact (not_lt_of_ge homega) ((hcontrol n omega).trans_lt hproduct)
  have hRlt : P.real R < delta / 2 := by
    have hraw := hNr n hnr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hraw
    simpa only [R, sub_zero, norm_zero] using hraw
  have hQlt : P.real Q < delta / 2 := by
    simpa only [Q] using hNq n hnq
  have hElt : P.real E < delta := by
    calc
      P.real E ≤ P.real (R ∪ Q) := measureReal_mono hsubset
      _ ≤ P.real R + P.real Q := measureReal_union_le R Q
      _ < delta / 2 + delta / 2 := add_lt_add hRlt hQlt
      _ = delta := by ring
  change dist (P.real E) 0 < delta
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]

/-- A variant of tight-control convergence allowing the pointwise estimate
to fail on exceptional sets whose probabilities vanish. -/
theorem TendstoInMeasure.of_norm_sub_le_mul_of_eventually_tight_outside
    [IsFiniteMeasure P]
    {f : ℕ → Omega → ℝ} {g : Omega → ℝ}
    {q : ℕ → Omega → ℝ} {a : ℕ → ℝ} {bad : ℕ → Set Omega}
    (ha : Tendsto a Filter.atTop (nhds 0))
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (_hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (hq_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta)
    (hbad : Tendsto (fun n => P.real (bad n)) Filter.atTop (nhds 0))
    (hcontrol : ∀ n omega, omega ∉ bad n →
      ‖f n omega - g omega‖ ≤ a n * q n omega) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hdelta2 : 0 < delta / 2 := half_pos hdelta
  obtain ⟨C, hC, hq_eventually⟩ := hq_tight (delta / 2) hdelta2
  have haC : Tendsto (fun n => a n * C) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using ha.mul_const C
  obtain ⟨Na, hNa⟩ :=
    (Metric.tendsto_atTop.mp haC) epsilon hepsilon
  obtain ⟨Nq, hNq⟩ := Filter.eventually_atTop.mp hq_eventually
  obtain ⟨Nb, hNb⟩ :=
    (Metric.tendsto_atTop.mp hbad) (delta / 2) hdelta2
  refine ⟨max Na (max Nq Nb), fun n hn => ?_⟩
  have hna : Na ≤ n := (le_max_left Na (max Nq Nb)).trans hn
  have hnq : Nq ≤ n :=
    (le_max_left Nq Nb).trans ((le_max_right Na (max Nq Nb)).trans hn)
  have hnb : Nb ≤ n :=
    (le_max_right Nq Nb).trans ((le_max_right Na (max Nq Nb)).trans hn)
  have ha_small : a n * C < epsilon := by
    have h := hNa n hna
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (ha_nonneg n) hC.le)] at h
    exact h
  have hbad_small : P.real (bad n) < delta / 2 := by
    have h := hNb n hnb
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  let E : Set Omega := {omega | epsilon ≤ ‖f n omega - g omega‖}
  let Q : Set Omega := {omega | C ≤ q n omega}
  have hsubset : E ⊆ bad n ∪ Q := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, not_or, Q, Set.mem_ofPred_eq, not_le] at hnot
    have hbound := hcontrol n omega hnot.1
    have hproduct : a n * q n omega < epsilon :=
      (mul_le_mul_of_nonneg_left hnot.2.le (ha_nonneg n)).trans_lt ha_small
    exact (not_lt_of_ge homega) (hbound.trans_lt hproduct)
  have hQsmall : P.real Q < delta / 2 := by
    simpa only [Q] using hNq n hnq
  have hEsmall : P.real E < delta := by
    calc
      P.real E ≤ P.real (bad n ∪ Q) := measureReal_mono hsubset
      _ ≤ P.real (bad n) + P.real Q := measureReal_union_le _ _
      _ < delta / 2 + delta / 2 := add_lt_add hbad_small hQsmall
      _ = delta := by ring
  change dist (P.real E) 0 < delta
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]

/-- Pointwise domination outside exceptional sets transfers convergence in
measure to zero when the exceptional probabilities vanish.  No measurability
of the dominated family is needed. -/
theorem TendstoInMeasure.of_norm_le_nonneg_outside_noMeas
    [IsFiniteMeasure P]
    {E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → Omega → E} {b : ℕ → Omega → ℝ}
    {bad : ℕ → Set Omega}
    (hb : TendstoInMeasure P b Filter.atTop (fun _ => 0))
    (hb_nonneg : ∀ n omega, 0 ≤ b n omega)
    (hbad : Tendsto (fun n => P.real (bad n)) Filter.atTop (nhds 0))
    (hcontrol : ∀ n omega, omega ∉ bad n → ‖f n omega‖ ≤ b n omega) :
    TendstoInMeasure P f Filter.atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  have hb_close :=
    (tendstoInMeasure_iff_measureReal_norm.mp hb) epsilon hepsilon
  have hb_close' : Tendsto (fun n =>
      P.real {omega | epsilon ≤ b n omega}) Filter.atTop (nhds 0) := by
    simpa only [sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (hb_nonneg _ _)] using hb_close
  have hsum : Tendsto (fun n =>
      P.real (bad n) + P.real {omega | epsilon ≤ b n omega})
      Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hbad.add hb_close'
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall fun n => ?_) hsum
  let F : Set Omega := {omega | epsilon ≤ ‖f n omega‖}
  let B : Set Omega := {omega | epsilon ≤ b n omega}
  have hsubset : F ⊆ bad n ∪ B := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, not_or, B, Set.mem_ofPred_eq, not_le] at hnot
    exact (not_lt_of_ge homega) ((hcontrol n omega hnot.1).trans_lt hnot.2)
  have hbound : P.real F ≤ P.real (bad n) + P.real B := by
    calc
      P.real F ≤ P.real (bad n ∪ B) := measureReal_mono hsubset
      _ ≤ P.real (bad n) + P.real B := measureReal_union_le _ _
  simpa only [F, B, sub_zero] using hbound

/-- Multiplying an eventually tight nonnegative family by a fixed
nonnegative scalar preserves eventual tightness. -/
theorem eventually_tight_const_mul_of_nonneg
    [IsFiniteMeasure P]
    {q : ℕ → Omega → ℝ} (a : ℝ) (ha : 0 ≤ a)
    (_hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (hq_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ a * q n omega} < delta := by
  intro delta hdelta
  by_cases ha0 : a = 0
  · refine ⟨1, zero_lt_one, Filter.Eventually.of_forall fun n => ?_⟩
    have hempty : {omega | (1 : ℝ) ≤ a * q n omega} = ∅ := by
      ext omega
      simp [ha0]
    rw [hempty, measureReal_empty]
    exact hdelta
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    obtain ⟨C, hC, htail⟩ := hq_tight delta hdelta
    refine ⟨a * C, mul_pos ha_pos hC, ?_⟩
    filter_upwards [htail] with n hn
    have hset : {omega | a * C ≤ a * q n omega} =
        {omega | C ≤ q n omega} := by
      ext omega
      simp only [Set.mem_ofPred_eq]
      exact mul_le_mul_iff_right₀ ha_pos
    simpa only [hset] using hn

/-- Sums of nonnegative eventually tight random controls remain eventually
tight. -/
theorem eventually_tight_add_of_nonneg
    [IsFiniteMeasure P]
    {q r : ℕ → Omega → ℝ}
    (_hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (_hr_nonneg : ∀ n omega, 0 ≤ r n omega)
    (hq_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta)
    (hr_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ r n omega} < delta) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega + r n omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨A, hA, hAtail⟩ := hq_tight (delta / 2) hhalf
  obtain ⟨B, hB, hBtail⟩ := hr_tight (delta / 2) hhalf
  refine ⟨A + B, add_pos hA hB, ?_⟩
  filter_upwards [hAtail, hBtail] with n hnq hnr
  have hsubset : {omega | A + B ≤ q n omega + r n omega} ⊆
      {omega | A ≤ q n omega} ∪ {omega | B ≤ r n omega} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    change A + B ≤ q n omega + r n omega at homega
    linarith
  calc
    P.real {omega | A + B ≤ q n omega + r n omega} ≤
        P.real ({omega | A ≤ q n omega} ∪
          {omega | B ≤ r n omega}) := measureReal_mono hsubset
    _ ≤ P.real {omega | A ≤ q n omega} +
        P.real {omega | B ≤ r n omega} := measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add hnq hnr
    _ = delta := by ring

/-- Products of nonnegative eventually tight random controls remain
eventually tight. -/
theorem eventually_tight_mul_of_nonneg
    [IsFiniteMeasure P]
    {q r : ℕ → Omega → ℝ}
    (_hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (hr_nonneg : ∀ n omega, 0 ≤ r n omega)
    (hq_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega} < delta)
    (hr_tight : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ r n omega} < delta) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ q n omega * r n omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨A, hA, hAtail⟩ := hq_tight (delta / 2) hhalf
  obtain ⟨B, hB, hBtail⟩ := hr_tight (delta / 2) hhalf
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  filter_upwards [hAtail, hBtail] with n hnq hnr
  have hsubset : {omega | A * B ≤ q n omega * r n omega} ⊆
      {omega | A ≤ q n omega} ∪ {omega | B ≤ r n omega} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hproduct : q n omega * r n omega < A * B := by
      calc
        q n omega * r n omega ≤ A * r n omega :=
          mul_le_mul_of_nonneg_right hnot.1.le (hr_nonneg n omega)
        _ < A * B := mul_lt_mul_of_pos_left hnot.2 hA
    exact (not_lt_of_ge homega) hproduct
  calc
    P.real {omega | A * B ≤ q n omega * r n omega} ≤
        P.real ({omega | A ≤ q n omega} ∪
          {omega | B ≤ r n omega}) := measureReal_mono hsubset
    _ ≤ P.real {omega | A ≤ q n omega} +
        P.real {omega | B ≤ r n omega} := measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add hnq hnr
    _ = delta := by ring

/-- Convergent nonnegative factors have an eventually tight geometric mean
as soon as the sum of their limits is integrable and nonnegative. -/
theorem TendstoInMeasure.eventually_tight_sqrt_mul
    [IsFiniteMeasure P]
    {q₁ q₂ : ℕ → Omega → ℝ} {Q₁ Q₂ : Omega → ℝ}
    (hq₁ : TendstoInMeasure P q₁ Filter.atTop Q₁)
    (hq₂ : TendstoInMeasure P q₂ Filter.atTop Q₂)
    (hq₁_nonneg : ∀ n omega, 0 ≤ q₁ n omega)
    (hq₂_nonneg : ∀ n omega, 0 ≤ q₂ n omega)
    (hQint : Integrable (fun omega => Q₁ omega + Q₂ omega) P)
    (hQnonneg : 0 ≤ᵐ[P] fun omega => Q₁ omega + Q₂ omega) :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
        P.real {omega | C ≤ √(q₁ n omega * q₂ n omega)} < delta := by
  have hsum : TendstoInMeasure P (fun n omega => q₁ n omega + q₂ n omega)
      Filter.atTop (fun omega => Q₁ omega + Q₂ omega) :=
    hq₁.add_real_noMeas hq₂
  intro delta hdelta
  obtain ⟨C, hC, htail⟩ :=
    hsum.eventually_tight_of_integrable_nonnegative_limit
      hQint hQnonneg delta hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  apply (measureReal_mono ?_).trans_lt hn
  intro omega homega
  have ha := hq₁_nonneg n omega
  have hb := hq₂_nonneg n omega
  have hsqrt : √(q₁ n omega * q₂ n omega) ≤
      q₁ n omega + q₂ n omega := by
    have hs0 := Real.sqrt_nonneg (q₁ n omega * q₂ n omega)
    have hs2 := Real.sq_sqrt (mul_nonneg ha hb)
    nlinarith [sq_nonneg (q₁ n omega - q₂ n omega)]
  exact homega.trans hsqrt

/-- A nonnegative random variable is integrable whenever its half-scaled
exponential is integrable.  The elementary estimate used here is intentionally
loose; it is only needed to turn an exponential-moment hypothesis into the
first moment required by tightness. -/
theorem Integrable.of_exp_half_of_ae_nonneg
    {Q : Omega → ℝ}
    (hQmeas : AEStronglyMeasurable Q P)
    (hQnonneg : ∀ᵐ omega ∂P, 0 ≤ Q omega)
    (hexp : Integrable (fun omega => Real.exp (Q omega / 2)) P) :
    Integrable Q P := by
  apply Integrable.mono' (hexp.const_mul 2) hQmeas
  filter_upwards [hQnonneg] with omega hQ
  rw [Real.norm_eq_abs, abs_of_nonneg hQ]
  nlinarith [Real.add_one_le_exp (Q omega / 2)]

/-- A countable family of convergent fine approximations admits a strictly
increasing diagonal which follows a convergent family of coarse targets.

This is the convergence-in-measure diagonal step needed for two-scale
partition arguments.  The selected fine index is at least the individual
cutoff for the `k`-th approximation and is forced to increase strictly. -/
theorem TendstoInMeasure.exists_strictMono_diagonal
    [IsFiniteMeasure P]
    {F : ℕ → ℕ → Omega → ℝ} {G : ℕ → Omega → ℝ} {g : Omega → ℝ}
    (hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k))
    (hG : TendstoInMeasure P G Filter.atTop g) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k => F k (m k)) Filter.atTop g := by
  let e : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  have he_pos : ∀ k, 0 < e k := fun k => by
    dsimp only [e]
    positivity
  have hcutoff : ∀ k, ∃ N : ℕ, ∀ n, N ≤ n →
      P.real {omega | e k ≤ ‖F k n omega - G k omega‖} < e k := by
    intro k
    have hclose :=
      (tendstoInMeasure_iff_measureReal_norm.mp (hFG k)) (e k) (he_pos k)
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp hclose) (e k) (he_pos k)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  choose N hN using hcutoff
  let m : ℕ → ℕ := fun k => Nat.rec (N 0)
    (fun i previous => max (N (i + 1)) (previous + 1)) k
  have hNm : ∀ k, N k ≤ m k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k _ih =>
        simp only [m]
        exact le_max_left _ _
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [m]
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have hdiag : TendstoInMeasure P
      (fun k omega => F k (m k) omega - G k omega)
      Filter.atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro epsilon hepsilon
    apply Metric.tendsto_atTop.mpr
    intro delta hdelta
    have he_zero : Filter.Tendsto e Filter.atTop (nhds 0) := by
      simpa only [e, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmin : 0 < min epsilon delta := lt_min hepsilon hdelta
    obtain ⟨K, hK⟩ :=
      (Metric.tendsto_atTop.mp he_zero) (min epsilon delta) hmin
    refine ⟨K, fun k hk => ?_⟩
    have he_small_raw := hK k hk
    have he_small : e k < min epsilon delta := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (he_pos k).le] using
        he_small_raw
    have he_epsilon : e k < epsilon := he_small.trans_le (min_le_left _ _)
    have he_delta : e k < delta := he_small.trans_le (min_le_right _ _)
    have hsubset :
        {omega | epsilon ≤ ‖F k (m k) omega - G k omega‖} ⊆
          {omega | e k ≤ ‖F k (m k) omega - G k omega‖} := by
      intro omega homega
      exact he_epsilon.le.trans homega
    have hmeasure :
        P.real {omega | epsilon ≤ ‖F k (m k) omega - G k omega‖} < delta :=
      (measureReal_mono hsubset).trans_lt
        ((hN k (m k) (hNm k)).trans he_delta)
    change dist
      (P.real {omega | epsilon ≤
        ‖(fun omega => F k (m k) omega - G k omega) omega -
          (fun _ => 0) omega‖}) 0 < delta
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    simpa only [Pi.zero_apply, sub_zero] using hmeasure
  refine ⟨m, hm, ?_⟩
  have hadd := hdiag.add_real_noMeas hG
  apply hadd.congr
  · intro k
    filter_upwards with omega
    ring
  · filter_upwards with omega
    ring

/-- A varying family of limits admits a strictly increasing diagonal whose
error tends to zero; no convergence of the limits themselves is required. -/
theorem TendstoInMeasure.exists_strictMono_diagonal_sub
    [IsFiniteMeasure P]
    {F : ℕ → ℕ → Omega → ℝ} {G : ℕ → Omega → ℝ}
    (hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega => F k (m k) omega - G k omega)
        Filter.atTop (fun _ => 0) := by
  have hdiff : ∀ k, TendstoInMeasure P
      (fun n omega => F k n omega - G k omega) Filter.atTop (fun _ => 0) := by
    intro k
    have hconst : TendstoInMeasure P (fun _ : ℕ => G k)
        Filter.atTop (G k) := by
      intro epsilon hepsilon
      simpa only [edist_self, not_le.mpr hepsilon, Set.ofPred_false,
        measure_empty] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal))
            Filter.atTop (nhds 0))
    have hs := (hFG k).sub_real_noMeas hconst
    apply hs.congr_right
    exact Filter.Eventually.of_forall fun omega => by simp
  obtain ⟨m, hm, hdiag⟩ := TendstoInMeasure.exists_strictMono_diagonal
    (F := fun k n omega => F k n omega - G k omega)
    (G := fun _ _ => 0) (g := fun _ => 0) hdiff (by
      intro epsilon hepsilon
      simpa only [edist_self, not_le.mpr hepsilon, Set.ofPred_false,
        measure_empty] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal))
            Filter.atTop (nhds 0)))
  exact ⟨m, hm, by simpa only [Pi.zero_apply] using hdiag⟩

/-- A varying family of limits in a normed additive group admits a strictly
increasing diagonal whose error tends to zero.  This is the value-generic
version of `exists_strictMono_diagonal_sub`; in particular it can synchronize
complex-valued two-scale approximations without splitting real and imaginary
parts. -/
theorem TendstoInMeasure.exists_strictMono_diagonal_sub_normed
    [IsFiniteMeasure P] {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℕ → Omega → E} {G : ℕ → Omega → E}
    (hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega => F k (m k) omega - G k omega)
        Filter.atTop (fun _ => 0) := by
  let e : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  have he_pos : ∀ k, 0 < e k := fun k => by
    dsimp only [e]
    positivity
  have hcutoff : ∀ k, ∃ N : ℕ, ∀ n, N ≤ n →
      P.real {omega | e k ≤ ‖F k n omega - G k omega‖} < e k := by
    intro k
    have hclose :=
      (tendstoInMeasure_iff_measureReal_norm.mp (hFG k)) (e k) (he_pos k)
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp hclose) (e k) (he_pos k)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  choose N hN using hcutoff
  let m : ℕ → ℕ := fun k => Nat.rec (N 0)
    (fun i previous => max (N (i + 1)) (previous + 1)) k
  have hNm : ∀ k, N k ≤ m k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k _ih =>
        simp only [m]
        exact le_max_left _ _
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [m]
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  refine ⟨m, hm, ?_⟩
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon hepsilon
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have he_zero : Filter.Tendsto e Filter.atTop (nhds 0) := by
    simpa only [e, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmin : 0 < min epsilon delta := lt_min hepsilon hdelta
  obtain ⟨K, hK⟩ :=
    (Metric.tendsto_atTop.mp he_zero) (min epsilon delta) hmin
  refine ⟨K, fun k hk => ?_⟩
  have he_small_raw := hK k hk
  have he_small : e k < min epsilon delta := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (he_pos k).le] using
      he_small_raw
  have he_epsilon : e k < epsilon := he_small.trans_le (min_le_left _ _)
  have he_delta : e k < delta := he_small.trans_le (min_le_right _ _)
  have hsubset :
      {omega | epsilon ≤ ‖F k (m k) omega - G k omega‖} ⊆
        {omega | e k ≤ ‖F k (m k) omega - G k omega‖} := by
    intro omega homega
    exact he_epsilon.le.trans homega
  have hmeasure :
      P.real {omega | epsilon ≤ ‖F k (m k) omega - G k omega‖} < delta :=
    (measureReal_mono hsubset).trans_lt
      ((hN k (m k) (hNm k)).trans he_delta)
  change dist
    (P.real {omega | epsilon ≤
      ‖(fun omega => F k (m k) omega - G k omega) omega -
        (fun _ => 0) omega‖}) 0 < delta
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  simpa only [Pi.zero_apply, sub_zero] using hmeasure

/-- Two varying families of real-valued limits admit one strictly increasing
diagonal along which both errors tend to zero.  Sharing the fine index is
essential when two Taylor expansions must cancel on the same partition. -/
theorem TendstoInMeasure.exists_strictMono_diagonal_sub_two
    [IsFiniteMeasure P]
    {F₁ F₂ : ℕ → ℕ → Omega → ℝ} {G₁ G₂ : ℕ → Omega → ℝ}
    (hFG₁ : ∀ k, TendstoInMeasure P (F₁ k) Filter.atTop (G₁ k))
    (hFG₂ : ∀ k, TendstoInMeasure P (F₂ k) Filter.atTop (G₂ k)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      TendstoInMeasure P (fun k omega => F₁ k (m k) omega - G₁ k omega)
        Filter.atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun k omega => F₂ k (m k) omega - G₂ k omega)
        Filter.atTop (fun _ => 0) := by
  let e : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ)
  have he_pos : ∀ k, 0 < e k := fun k => by
    dsimp only [e]
    positivity
  have hcutoff₁ : ∀ k, ∃ N : ℕ, ∀ n, N ≤ n →
      P.real {omega | e k ≤ ‖F₁ k n omega - G₁ k omega‖} < e k := by
    intro k
    have hclose :=
      (tendstoInMeasure_iff_measureReal_norm.mp (hFG₁ k)) (e k) (he_pos k)
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp hclose) (e k) (he_pos k)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  have hcutoff₂ : ∀ k, ∃ N : ℕ, ∀ n, N ≤ n →
      P.real {omega | e k ≤ ‖F₂ k n omega - G₂ k omega‖} < e k := by
    intro k
    have hclose :=
      (tendstoInMeasure_iff_measureReal_norm.mp (hFG₂ k)) (e k) (he_pos k)
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp hclose) (e k) (he_pos k)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  choose N₁ hN₁ using hcutoff₁
  choose N₂ hN₂ using hcutoff₂
  let m : ℕ → ℕ := fun k => Nat.rec (max (N₁ 0) (N₂ 0))
    (fun i previous =>
      max (max (N₁ (i + 1)) (N₂ (i + 1))) (previous + 1)) k
  have hN₁m : ∀ k, N₁ k ≤ m k := by
    intro k
    induction k with
    | zero =>
        simp only [m]
        exact le_max_left _ _
    | succ k _ih =>
        simp only [m]
        exact (le_max_left _ _).trans (le_max_left _ _)
  have hN₂m : ∀ k, N₂ k ≤ m k := by
    intro k
    induction k with
    | zero =>
        simp only [m]
        exact le_max_right _ _
    | succ k _ih =>
        simp only [m]
        exact (le_max_right _ _).trans (le_max_left _ _)
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [m]
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  have diagonal_error
      (F : ℕ → ℕ → Omega → ℝ) (G : ℕ → Omega → ℝ)
      (N : ℕ → ℕ)
      (hN : ∀ k, ∀ n, N k ≤ n →
        P.real {omega | e k ≤ ‖F k n omega - G k omega‖} < e k)
      (hNm : ∀ k, N k ≤ m k) :
      TendstoInMeasure P (fun k omega => F k (m k) omega - G k omega)
        Filter.atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_measureReal_norm]
    intro epsilon hepsilon
    apply Metric.tendsto_atTop.mpr
    intro delta hdelta
    have he_zero : Filter.Tendsto e Filter.atTop (nhds 0) := by
      simpa only [e, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmin : 0 < min epsilon delta := lt_min hepsilon hdelta
    obtain ⟨K, hK⟩ :=
      (Metric.tendsto_atTop.mp he_zero) (min epsilon delta) hmin
    refine ⟨K, fun k hk => ?_⟩
    have he_small_raw := hK k hk
    have he_small : e k < min epsilon delta := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (he_pos k).le] using
        he_small_raw
    have he_epsilon : e k < epsilon :=
      he_small.trans_le (min_le_left _ _)
    have he_delta : e k < delta :=
      he_small.trans_le (min_le_right _ _)
    have hsubset :
        {omega | epsilon ≤
          ‖(fun omega => F k (m k) omega - G k omega) omega -
            (fun _ => 0) omega‖} ⊆
          {omega | e k ≤ ‖F k (m k) omega - G k omega‖} := by
      intro omega homega
      simp only [Set.mem_ofPred_eq, sub_zero] at homega ⊢
      exact he_epsilon.le.trans homega
    have hmeasure :
        P.real {omega | epsilon ≤
          ‖(fun omega => F k (m k) omega - G k omega) omega -
            (fun _ => 0) omega‖} < delta :=
      (measureReal_mono hsubset).trans_lt
        ((hN k (m k) (hNm k)).trans he_delta)
    change dist
      (P.real {omega | epsilon ≤
        ‖(fun omega => F k (m k) omega - G k omega) omega -
          (fun _ => 0) omega‖}) 0 < delta
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    exact hmeasure
  exact ⟨m, hm,
    diagonal_error F₁ G₁ N₁ hN₁ hN₁m,
    diagonal_error F₂ G₂ N₂ hN₂ hN₂m⟩

/-- Close a two-scale approximation from an almost-everywhere uniform mesh
estimate.  For each fixed coarse mesh, `F k n` converges in measure to
`G k`; the coarse targets converge to `g`; and the original approximation is
eventually within an arbitrarily small multiple of a tight control whenever
both mesh indices exceed one sample-dependent cutoff.

The proof uses the subsequence characterization of convergence in measure.
On an arbitrary subsequence, `exists_strictMono_diagonal` synchronizes the
fixed-coarse limits.  A further subsequence makes the tight control converge
almost everywhere, hence bounded, and the uniform two-mesh estimate closes
the comparison pathwise. -/
theorem TendstoInMeasure.of_ae_two_scale_uniform_control
    [IsFiniteMeasure P]
    {f q : ℕ → Omega → ℝ} {F : ℕ → ℕ → Omega → ℝ}
    {G : ℕ → Omega → ℝ} {g qlim : Omega → ℝ}
    (hfmeas : ∀ n, AEStronglyMeasurable (f n) P)
    (hFG : ∀ k, TendstoInMeasure P (F k) Filter.atTop (G k))
    (hG : TendstoInMeasure P G Filter.atTop g)
    (hq : TendstoInMeasure P q Filter.atTop qlim)
    (hq_nonneg : ∀ n omega, 0 ≤ q n omega)
    (hcontrol : ∀ᵐ omega ∂P, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ k n, N ≤ k → N ≤ n →
        ‖f n omega - F k n omega‖ ≤ epsilon * q n omega) :
    TendstoInMeasure P f Filter.atTop g := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hfmeas]
  intro ns hns
  have hFGns : ∀ k, TendstoInMeasure P
      (fun n => F k (ns n)) Filter.atTop (G k) := fun k =>
    (hFG k).comp hns.tendsto_atTop
  obtain ⟨m, hm, hdiag⟩ :=
    TendstoInMeasure.exists_strictMono_diagonal hFGns hG
  obtain ⟨r₁, hr₁, hdiagAE⟩ := hdiag.exists_seq_tendsto_ae
  have hfine₁ : StrictMono (ns ∘ m ∘ r₁) :=
    hns.comp (hm.comp hr₁)
  have hq₁ : TendstoInMeasure P
      (fun i => q (ns (m (r₁ i)))) Filter.atTop qlim :=
    hq.comp hfine₁.tendsto_atTop
  obtain ⟨r₂, hr₂, hqAE⟩ := hq₁.exists_seq_tendsto_ae
  let r : ℕ → ℕ := r₁ ∘ r₂
  have hr : StrictMono r := hr₁.comp hr₂
  let ns' : ℕ → ℕ := m ∘ r
  have hns' : StrictMono ns' := hm.comp hr
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hdiagAE, hqAE, hcontrol]
    with omega hdiagOmega hqOmega hcontrolOmega
  have hdiagOmega' : Filter.Tendsto
      (fun i => F (r i) (ns (m (r i))) omega)
      Filter.atTop (nhds (g omega)) := by
    change Filter.Tendsto
      ((fun i => F (r₁ i) (ns (m (r₁ i))) omega) ∘ r₂)
      Filter.atTop (nhds (g omega))
    exact hdiagOmega.comp hr₂.tendsto_atTop
  have hqOmega' : Filter.Tendsto
      (fun i => q (ns (m (r i))) omega)
      Filter.atTop (nhds (qlim omega)) := by
    simpa only [r, Function.comp_apply] using hqOmega
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto
      (fun i => q (ns (m (r i))) omega) hqOmega')
  have hC_nonneg : 0 ≤ C := by
    exact (norm_nonneg (q (ns (m (r 0))) omega)).trans
      (hC _ ⟨0, rfl⟩)
  have herror : Filter.Tendsto
      (fun i => f (ns (m (r i))) omega -
        F (r i) (ns (m (r i))) omega)
      Filter.atTop (nhds 0) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    let a : ℝ := epsilon / (C + 1)
    have hC_one : 0 < C + 1 := by linarith
    have ha : 0 < a := div_pos hepsilon hC_one
    obtain ⟨N, hN⟩ := hcontrolOmega a ha
    obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp
      (hr.tendsto_atTop.eventually (Filter.eventually_ge_atTop N))
    have hfine : StrictMono (ns ∘ m ∘ r) := hns.comp (hm.comp hr)
    obtain ⟨Nfine, hNfine⟩ := Filter.eventually_atTop.mp
      (hfine.tendsto_atTop.eventually (Filter.eventually_ge_atTop N))
    refine ⟨max Nr Nfine, fun i hi => ?_⟩
    have hir : Nr ≤ i := (le_max_left Nr Nfine).trans hi
    have hifine : Nfine ≤ i := (le_max_right Nr Nfine).trans hi
    have hbound := hN (r i) (ns (m (r i))) (hNr i hir) (hNfine i hifine)
    have hqC : q (ns (m (r i))) omega ≤ C := by
      rw [← abs_of_nonneg (hq_nonneg _ _), ← Real.norm_eq_abs]
      exact hC _ ⟨i, rfl⟩
    have hmul : a * q (ns (m (r i))) omega ≤ a * C :=
      mul_le_mul_of_nonneg_left hqC ha.le
    have haC : a * C < epsilon := by
      dsimp only [a]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hC_one).2
      nlinarith
    have hlt : ‖f (ns (m (r i))) omega -
        F (r i) (ns (m (r i))) omega‖ < epsilon :=
      hbound.trans_lt (hmul.trans_lt haC)
    simpa only [Real.dist_eq, sub_zero, Real.norm_eq_abs] using hlt
  have hsum := herror.add hdiagOmega'
  simpa only [ns', Function.comp_apply, sub_add_cancel, zero_add] using hsum

end MeasureTheory
