/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovMeshControl

/-!
# Stopped weight and higher-order controls

The left-endpoint maximum of the stopped density, the stopped weight control
of the complex exponential, the compensated square control, the stopped
variation control, and the vanishing and tight higher-order controls that
bound the higher-order residual.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The largest value of the stopped real Girsanov density at the left
endpoints of a uniform grid.  The last terminal endpoint is deliberately
omitted, matching the left weights in the discrete Doleans expansion. -/
noncomputable def girsanovDensityUniformPartitionLeftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k =>
    doleansDadeExponential M bracket
      (min (uniformPartitionTime T (n + 1) k) T) omega

theorem girsanovDensityUniformPartitionLeftMax_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) :
    0 ≤ girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
  exact (doleansDadeExponential_pos M bracket
    (min (uniformPartitionTime T (n + 1) 0) T) omega).le.trans
      (Finset.le_sup' (fun k => doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) k) T) omega)
        (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- Doob's nonnegative-submartingale inequality makes the maxima of the
Girsanov density over all deterministic uniform grids uniformly tight. -/
theorem GirsanovDensityData.girsanovDensityUniformPartitionLeftMax_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ n,
        P.real {omega | K ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega} <
            delta := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / delta)
  have hNpos : 0 < N := by
    have honeDiv : 0 < 1 / delta := one_div_pos.mpr hdelta
    exact_mod_cast honeDiv.trans hN
  let K : ℝ≥0 := ⟨(N : ℝ), Nat.cast_nonneg N⟩
  have hKpos : (0 : ℝ) < K := by
    change (0 : ℝ) < (N : ℝ)
    exact_mod_cast hNpos
  refine ⟨(K : ℝ), hKpos, fun n => ?_⟩
  let D : ℝ≥0 → W → ℝ := fun t omega =>
    doleansDadeExponential M bracket (min t T) omega
  let E : Set W := {omega | (K : ℝ) ≤
    girsanovDensityUniformPartitionLeftMax M bracket T n omega}
  have hDmart : Martingale D V P := by
    simpa only [D] using hdata.martingale_densityProcess
  have hsample : Martingale (uniformPartitionSample D T (n + 1))
      (uniformPartitionFiltration V T (n + 1)) P :=
    martingale_uniformPartitionSample hDmart T (n + 1)
  have hnonneg : 0 ≤ uniformPartitionSample D T (n + 1) :=
    fun _k omega => (doleansDadeExponential_pos M bracket _ omega).le
  have hraw := maximal_ineq hsample.submartingale hnonneg (ε := K) n
  have hset : {omega |
      (K : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
          (fun k => uniformPartitionSample D T (n + 1) k omega)} = E := by
    rfl
  rw [hset] at hraw
  have hterminal :
      ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P = 1 := by
    have htime : uniformPartitionTime T (n + 1) n ≤ T :=
      (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
        (Nat.le_succ n)).2
    have heq := StochasticCalculus.Martingale.integral_eq hDmart htime
    rw [show D T = girsanovDensity M bracket T by
      funext omega
      simp only [D, girsanovDensity, min_self]] at heq
    simpa only [uniformPartitionSample, D,
      min_eq_left htime, hdata.integral_eq_one] using heq.symm
  have hsetIntegral :
      ∫ omega in E, uniformPartitionSample D T (n + 1) n omega ∂P ≤ 1 := by
    calc
      _ ≤ ∫ omega, uniformPartitionSample D T (n + 1) n omega ∂P :=
        setIntegral_le_integral (hsample.integrable n)
          (Filter.Eventually.of_forall fun omega =>
            (doleansDadeExponential_pos M bracket _ omega).le)
      _ = 1 := hterminal
  have hbound : (K : ℝ≥0∞) * P E ≤ 1 :=
    hraw.trans ((ENNReal.ofReal_le_ofReal hsetIntegral).trans_eq (by norm_num))
  have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_one] at hreal
  change (K : ℝ) * P.real E ≤ 1 at hreal
  have hKdelta : 1 < (K : ℝ) * delta := by
    apply (div_lt_iff₀ hdelta).mp
    change 1 / delta < (N : ℝ)
    exact hN
  have htail : P.real E < delta := by
    by_contra hnot
    have hdeltaLe : delta ≤ P.real E := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hdeltaLe (show 0 ≤ (K : ℝ) by positivity)
    nlinarith
  simpa only [E] using htail

/-- A single random bound for all stopped complex Doleans left weights on a
uniform grid.  The extra fixed-time density covers the unique partial cell. -/
noncomputable def girsanovComplexDoleansStoppedWeightControl
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  Real.exp (c ^ 2 * (T : ℝ) / 2) *
    (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
      doleansDadeExponential M bracket (min t T) omega)

theorem girsanovComplexDoleansStoppedWeightControl_nonneg
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (c : ℝ) (T : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexDoleansStoppedWeightControl
      M bracket c T n t omega := by
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

theorem doleansDadeExponential_uniformPartition_le_leftMax
    {W : Type*} (M bracket : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    (n : ℕ) (omega : W) {i : ℕ} (hi : i ∈ Finset.range (n + 1)) :
    doleansDadeExponential M bracket
        (min (uniformPartitionTime T (n + 1) i) T) omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega :=
  Finset.le_sup' (fun k => doleansDadeExponential M bracket
    (min (uniformPartitionTime T (n + 1) k) T) omega) hi

/-- The stopped complex Doleans weight at every left endpoint is bounded by
the density-grid maximum plus the density at the observation time. -/
theorem norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) {i : ℕ}
    (hi : i ∈ Finset.range (n + 1)) :
    ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t (uniformPartitionTime T (n + 1) i)) omega‖ ≤
      girsanovComplexDoleansStoppedWeightControl
        M bracket c T n t omega := by
  let s := min t (uniformPartitionTime T (n + 1) i)
  let u := uniformPartitionTime T (n + 1) i
  have hiLe : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have huT : u ≤ T :=
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hiLe).2
  have hsT : s ≤ T := (min_le_right t u).trans huT
  have hexp : Real.exp (c ^ 2 * (s : ℝ) / 2) ≤
      Real.exp (c ^ 2 * (T : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    have hcoe : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hsT
    nlinarith [sq_nonneg c]
  have hdensity : doleansDadeExponential M bracket s omega ≤
      girsanovDensityUniformPartitionLeftMax M bracket T n omega +
        doleansDadeExponential M bracket (min t T) omega := by
    by_cases hut : u ≤ t
    · have hgrid : doleansDadeExponential M bracket s omega ≤
          girsanovDensityUniformPartitionLeftMax M bracket T n omega := by
        have hsup := doleansDadeExponential_uniformPartition_le_leftMax
          M bracket T n omega hi
        simpa only [s, min_eq_right hut, u, min_eq_left huT] using hsup
      exact hgrid.trans (le_add_of_nonneg_right
        (doleansDadeExponential_pos M bracket (min t T) omega).le)
    · have htu : t ≤ u := le_of_not_ge hut
      have htT : t ≤ T := htu.trans huT
      have hs : s = t := min_eq_left htu
      rw [hs, min_eq_left htT]
      exact le_add_of_nonneg_left
        (girsanovDensityUniformPartitionLeftMax_nonneg
          M bracket T n omega)
  rw [norm_complexDoleansDadeExponential_combination]
  unfold girsanovComplexDoleansStoppedWeightControl
  rw [mul_comm (Real.exp _) _]
  exact mul_le_mul hdensity hexp (Real.exp_pos _).le
    (add_nonneg
      (girsanovDensityUniformPartitionLeftMax_nonneg M bracket T n omega)
      (doleansDadeExponential_pos M bracket (min t T) omega).le)

/-- The random controls for stopped complex Doleans left weights are
eventually tight, uniformly over the deterministic grids. -/
theorem GirsanovDensityData.girsanovComplexDoleansStoppedWeightControl_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T) (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexDoleansStoppedWeightControl
            M bracket c T n t omega} < delta := by
  intro delta hdelta
  have hhalf : 0 < delta / 2 := half_pos hdelta
  obtain ⟨A, hA, hAtail⟩ :=
    hdata.girsanovDensityUniformPartitionLeftMax_tight
      (delta / 2) hhalf
  have hDmeas : StronglyMeasurable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega) := by
    have hDadapt := hdata.martingale_densityProcess.stronglyAdapted
    have hmin : min (min t T) T = min t T :=
      min_eq_left (min_le_right t T)
    simpa only [hmin] using
      (hDadapt (min t T)).mono (V.le (min t T))
  obtain ⟨R, hR, hRtail⟩ :=
    StronglyMeasurable.exists_measureReal_ge_lt_finite (P := P) hDmeas
      (delta / 2) hhalf
  let L := max A R
  let e := Real.exp (c ^ 2 * (T : ℝ) / 2)
  refine ⟨e * (2 * L), mul_pos (Real.exp_pos _) (mul_pos (by norm_num)
    (hA.trans_le (le_max_left A R))), ?_⟩
  filter_upwards with n
  have hsubset : {omega | e * (2 * L) ≤
      girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ⊆
        {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
        {omega | R ≤ doleansDadeExponential M bracket (min t T) omega} := by
    intro omega homega
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hsum :
        girsanovDensityUniformPartitionLeftMax M bracket T n omega +
            doleansDadeExponential M bracket (min t T) omega < 2 * L := by
      have hx : girsanovDensityUniformPartitionLeftMax M bracket T n omega < L :=
        hnot.1.trans_le (le_max_left A R)
      have hy : doleansDadeExponential M bracket (min t T) omega < L :=
        hnot.2.trans_le (le_max_right A R)
      linarith
    have hmul : e *
        (girsanovDensityUniformPartitionLeftMax M bracket T n omega +
          doleansDadeExponential M bracket (min t T) omega) <
        e * (2 * L) :=
      mul_lt_mul_of_pos_left hsum (by
        dsimp only [e]
        exact Real.exp_pos _)
    exact (not_lt_of_ge homega) (by simpa only
      [girsanovComplexDoleansStoppedWeightControl, e] using hmul)
  calc
    P.real {omega | e * (2 * L) ≤
        girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega} ≤
        P.real ({omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} ∪
          {omega | R ≤ doleansDadeExponential M bracket (min t T) omega}) :=
      measureReal_mono hsubset
    _ ≤ P.real {omega | A ≤ girsanovDensityUniformPartitionLeftMax
          M bracket T n omega} +
        P.real {omega | R ≤
          doleansDadeExponential M bracket (min t T) omega} :=
      measureReal_union_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add (hAtail n) hRtail
    _ = delta := by ring

/-- The total variation of the proposed complex bracket is bounded by the
variations of its real finite-variation components. -/
theorem complexTotalVariationApprox_complexMartingaleCombinationBracket_le
    {W : Type*} (bracket C : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    complexTotalVariationApprox
        (complexMartingaleCombinationBracket bracket C c)
        U (n + 1) omega ≤
      girsanovComplexBracketVariationControl bracket C c U n omega := by
  have hcell (i : ℕ) :
      ‖complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) (i + 1)) omega -
          complexMartingaleCombinationBracket bracket C c
            (uniformPartitionTime U (n + 1) i) omega‖ ≤
        |bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
          bracket (uniformPartitionTime U (n + 1) i) omega| +
        c ^ 2 *
          |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
            (uniformPartitionTime U (n + 1) i : ℝ)| +
        2 * |c| *
          |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
            C (uniformPartitionTime U (n + 1) i) omega| := by
    let u := uniformPartitionTime U (n + 1) (i + 1)
    let s := uniformPartitionTime U (n + 1) i
    let dA := bracket u omega - bracket s omega
    let dC := C u omega - C s omega
    let dt := (u : ℝ) - (s : ℝ)
    have heq :
        complexMartingaleCombinationBracket bracket C c u omega -
            complexMartingaleCombinationBracket bracket C c s omega =
          (dA : ℂ) - ((c ^ 2 * dt : ℝ) : ℂ) +
            ((2 * c * dC : ℝ) : ℂ) * Complex.I := by
      unfold complexMartingaleCombinationBracket
      dsimp only [dA, dC, dt]
      push_cast
      ring
    rw [heq]
    dsimp only [dA, dC, dt, u, s]
    calc
      ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
          ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ) +
          ((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ ≤
          ‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ) -
            ((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖ +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := norm_add_le _ _
      _ ≤
          (‖((bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega : ℝ) : ℂ)‖ +
            ‖((c ^ 2 * ((uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
              (uniformPartitionTime U (n + 1) i : ℝ)) : ℝ) : ℂ)‖) +
          ‖((2 * c * (C (uniformPartitionTime U (n + 1) (i + 1)) omega -
              C (uniformPartitionTime U (n + 1) i) omega) : ℝ) : ℂ) *
            Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_I, mul_one, abs_pow]
        rw [sq_abs]
        ring
  unfold complexTotalVariationApprox girsanovComplexBracketVariationControl
  calc
    (∑ i ∈ Finset.range (n + 1),
        ‖complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) (i + 1)) omega -
            complexMartingaleCombinationBracket bracket C c
              (uniformPartitionTime U (n + 1) i) omega‖) ≤
        ∑ i ∈ Finset.range (n + 1),
          (|bracket (uniformPartitionTime U (n + 1) (i + 1)) omega -
              bracket (uniformPartitionTime U (n + 1) i) omega| +
            c ^ 2 *
              |(uniformPartitionTime U (n + 1) (i + 1) : ℝ) -
                (uniformPartitionTime U (n + 1) i : ℝ)| +
            2 * |c| *
              |C (uniformPartitionTime U (n + 1) (i + 1)) omega -
                C (uniformPartitionTime U (n + 1) i) omega|) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = totalVariationApprox bracket U (n + 1) omega +
          c ^ 2 * totalVariationApprox
            (fun s (_u : Unit) => (s : ℝ)) U (n + 1) () +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      unfold totalVariationApprox
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = totalVariationApprox bracket U (n + 1) omega + c ^ 2 * (U : ℝ) +
          2 * |c| * totalVariationApprox C U (n + 1) omega := by
      rw [totalVariationApprox_time_uniformPartition_succ]

/-- Stopping the regularized complex bracket at an arbitrary observation
time costs only its single partial-cell mesh increment beyond the terminal
variation envelope. -/
theorem
    GirsanovDensityData.complexTotalVariationApprox_stopped_le_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexTotalVariationApprox
        (fun s w => complexMartingaleCombinationBracket bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c (min t s) w)
        T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z =>
            -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let Q := complexMartingaleCombinationBracket bracket C c
  let delta := girsanovComplexBracketStoppedMeshControl bracket C c T n t omega
  have hstop : complexTotalVariationApprox (fun s w => Q (min t s) w)
      T (n + 1) omega ≤
        complexTotalVariationApprox Q T (n + 1) omega + delta := by
    apply complexTotalVariationApprox_stop_le_of_cell_bound
    · exact girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega
    · intro i hi
      exact
        norm_complexMartingaleCombinationBracket_stopped_uniformPartition_increment_le
          bracket C c T n t omega hi
  have hfull : complexTotalVariationApprox Q T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega := by
    exact
      (complexTotalVariationApprox_complexMartingaleCombinationBracket_le
        bracket C c T n omega).trans
        (hdata.girsanovComplexBracketVariationControl_le_terminal
          htheta hbracketTerminal c n omega)
  exact hstop.trans (add_le_add hfull (le_refl delta))

/-- The squared compensated increments are controlled by the squared
martingale increments and the square of the bracket's total variation. -/
theorem sum_norm_compensated_uniformPartition_increment_sq_le
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖(X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega) -
        (Q (uniformPartitionTime U n (i + 1)) omega -
          Q (uniformPartitionTime U n i) omega) / 2‖ ^ 2) ≤
      2 * (∑ i ∈ Finset.range n,
        ‖X (uniformPartitionTime U n (i + 1)) omega -
          X (uniformPartitionTime U n i) omega‖ ^ 2) +
        (complexTotalVariationApprox Q U n omega) ^ 2 / 2 := by
  let dX : ℕ → ℂ := fun i =>
    X (uniformPartitionTime U n (i + 1)) omega -
      X (uniformPartitionTime U n i) omega
  let dQ : ℕ → ℂ := fun i =>
    Q (uniformPartitionTime U n (i + 1)) omega -
      Q (uniformPartitionTime U n i) omega
  have hcell (i : ℕ) : ‖dX i - dQ i / 2‖ ^ 2 ≤
      2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
    have hnorm : ‖dX i - dQ i / 2‖ ≤ ‖dX i‖ + ‖dQ i‖ / 2 := by
      calc
        _ ≤ ‖dX i‖ + ‖dQ i / 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_div]; norm_num
    have hsquare := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (by norm_num)))).2
        hnorm
    calc
      ‖dX i - dQ i / 2‖ ^ 2 ≤ (‖dX i‖ + ‖dQ i‖ / 2) ^ 2 := hsquare
      _ ≤ 2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖dX i‖ - ‖dQ i‖ / 2)]
  have hqSq : (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) ≤
      (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun i _hi => norm_nonneg (dQ i))
  change (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤ _
  calc
    (∑ i ∈ Finset.range n, ‖dX i - dQ i / 2‖ ^ 2) ≤
        ∑ i ∈ Finset.range n,
          (2 * ‖dX i‖ ^ 2 + ‖dQ i‖ ^ 2 / 2) :=
      Finset.sum_le_sum fun i _hi => hcell i
    _ = 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖ ^ 2) / 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ 2 * (∑ i ∈ Finset.range n, ‖dX i‖ ^ 2) +
        (∑ i ∈ Finset.range n, ‖dQ i‖) ^ 2 / 2 := by
      gcongr
    _ = _ := by rfl

/-- The squared norms of the `M + i c B` grid increments split exactly into
the two real quadratic-variation sums. -/
theorem sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
    {W : Type*} (M B : ℝ≥0 → W → ℝ) (c : ℝ)
    (U : ℝ≥0) (n : ℕ) (omega : W) :
    (∑ i ∈ Finset.range n,
      ‖complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega‖ ^ 2) =
      quadraticVariationApprox M U n omega +
        c ^ 2 * quadraticVariationApprox B U n omega := by
  unfold quadraticVariationApprox
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  let dM := M (uniformPartitionTime U n (i + 1)) omega -
    M (uniformPartitionTime U n i) omega
  let dB := B (uniformPartitionTime U n (i + 1)) omega -
    B (uniformPartitionTime U n i) omega
  have heq :
      complexMartingaleCombination M B c
          (uniformPartitionTime U n (i + 1)) omega -
        complexMartingaleCombination M B c
          (uniformPartitionTime U n i) omega =
        (dM : ℂ) + ((c * dB : ℝ) : ℂ) * Complex.I := by
    unfold complexMartingaleCombination
    dsimp only [dM, dB]
    push_cast
    ring
  rw [heq, Complex.sq_norm, Complex.normSq_add_mul_I]
  dsimp only [dM, dB]
  ring

/-- A stopped-grid analogue of the compensated-square control.  Its only
extra term is the vanishing mesh bound for the unique partial bracket cell. -/
noncomputable def girsanovComplexStoppedCompensatedSquareControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  2 * (quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1) omega +
      c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1) omega) +
    (girsanovComplexTerminalVariationBound bracket theta c T omega +
      girsanovComplexBracketStoppedMeshControl bracket
        (fun u z =>
          -regularizedGirsanovIntegratedDrift bracket theta T u z)
        c T n t omega) ^ 2 / 2

theorem GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (_hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedCompensatedSquareControl
      M bracket B theta c T n t omega := by
  unfold girsanovComplexStoppedCompensatedSquareControl
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg
      (quadraticVariationApprox_nonneg
        (fun s w => M (min t s) w) T (n + 1) omega)
      (mul_nonneg (sq_nonneg c)
        (quadraticVariationApprox_nonneg
          (fun s w => B (min t s) w) T (n + 1) omega))))
    (div_nonneg (sq_nonneg _) (by norm_num))

/-- All squared stopped compensated logarithmic increments are bounded by
the stopped terminal envelope. -/
theorem
    GirsanovDensityData.sum_norm_girsanov_compensated_stopped_increment_sq_le
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    (∑ i ∈ Finset.range (n + 1),
      ‖(complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombination M B c
            (min t (uniformPartitionTime T (n + 1) i)) omega) -
        (complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) (i + 1))) omega -
          complexMartingaleCombinationBracket bracket
            (fun u z =>
              -regularizedGirsanovIntegratedDrift bracket theta T u z)
            c (min t (uniformPartitionTime T (n + 1) i)) omega) / 2‖ ^ 2) ≤
      girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let Xs : ℝ≥0 → W → ℂ := fun s w => X (min t s) w
  let Qs : ℝ≥0 → W → ℂ := fun s w => Q (min t s) w
  have hvariation : complexTotalVariationApprox Qs T (n + 1) omega ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega := by
    simpa only [Qs, Q, C] using
      hdata.complexTotalVariationApprox_stopped_le_terminal
        htheta hbracketTerminal c n t omega
  have hvariationNonneg : 0 ≤
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega :=
    add_nonneg (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
      (girsanovComplexBracketStoppedMeshControl_nonneg
        bracket C c T n t omega)
  have hsquare : (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 ≤
      (girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 :=
    (sq_le_sq₀ (complexTotalVariationApprox_nonneg Qs T (n + 1) omega)
      hvariationNonneg).2 hvariation
  have hsplit : (∑ i ∈ Finset.range (n + 1),
      ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
        Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) =
      quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega := by
    simpa only [Xs, X, complexMartingaleCombination] using
      sum_norm_complexMartingaleCombination_uniformPartition_increment_sq
        (fun s w => M (min t s) w) (fun s w => B (min t s) w)
        c T (n + 1) omega
  change (∑ i ∈ Finset.range (n + 1),
      ‖(Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Xs (uniformPartitionTime T (n + 1) i) omega) -
        (Qs (uniformPartitionTime T (n + 1) (i + 1)) omega -
          Qs (uniformPartitionTime T (n + 1) i) omega) / 2‖ ^ 2) ≤ _
  calc
    _ ≤ 2 * (∑ i ∈ Finset.range (n + 1),
          ‖Xs (uniformPartitionTime T (n + 1) (i + 1)) omega -
            Xs (uniformPartitionTime T (n + 1) i) omega‖ ^ 2) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 :=
      sum_norm_compensated_uniformPartition_increment_sq_le
        Xs Qs T (n + 1) omega
    _ = 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (complexTotalVariationApprox Qs T (n + 1) omega) ^ 2 / 2 := by
      rw [hsplit]
    _ ≤ 2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        (girsanovComplexTerminalVariationBound bracket theta c T omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega) ^ 2 /
            2 := by
      gcongr
    _ = girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega := rfl

/-- The stopped compensated-square control converges in probability to a
finite random variable.  Thus the single partial cell does not disturb the
terminal tightness argument. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop
      (fun omega =>
        2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
          (girsanovComplexTerminalVariationBound
            bracket theta c T omega) ^ 2 / 2) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, AEStronglyMeasurable (M s) P := fun s =>
    ((hdata.adapted_martingale s).mono (V.le s)).aestronglyMeasurable
  have hqM : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min s t) w)
        T (n + 1)) atTop (bracket (min T t)) :=
    (hdata.localQuadraticVariation.toBeforeStop.toStopped hMmeas
      (Filter.Eventually.of_forall hdata.continuous_martingale_path)) T t
  have hqM' : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => M (min t s) w)
        T (n + 1)) atTop (bracket (min T t)) := by
    apply hqM.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hqB : TendstoInMeasure P
      (fun n => quadraticVariationApprox (fun s w => B (min t s) w)
        T (n + 1)) atTop (fun _ => ((min T t : ℝ≥0) : ℝ)) := by
    have hraw := quadraticVariation_stopped_preBrownianReal_inProbability
      hB t T
    apply hraw.congr_left
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      congr 1
      funext s w
      rw [min_comm]
  have hquadratic := (hqM'.add_real_noMeas
    (hqB.const_mul_real_noMeas (c ^ 2))).const_mul_real_noMeas 2
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hHconst : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hHmesh : TendstoInMeasure P
      (fun n omega => H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega)
      atTop H := by
    simpa only [add_zero] using hHconst.add_real_noMeas hmesh
  have hmeshMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovComplexBracketStoppedMeshControl bracket C c T n t) P :=
    aestronglyMeasurable_girsanovComplexBracketStoppedMeshControl
      hbracketMeas hCMeas c T n t
  let sqHalf : ℝ → ℝ := fun x => x ^ 2 / 2
  have hsq : TendstoInMeasure P (fun n omega =>
      sqHalf (H omega +
        girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
      atTop (fun omega => sqHalf (H omega)) := by
    exact TendstoInMeasure.continuous_comp
      (fun n => hH.aestronglyMeasurable.add (hmeshMeas n))
      hHmesh (by simpa only [sqHalf] using
        (by fun_prop : Continuous (fun x : ℝ => x ^ 2 / 2)))
  have hsum := hquadratic.add_real_noMeas hsq
  change TendstoInMeasure P (fun n omega =>
      2 * (quadraticVariationApprox (fun s w => M (min t s) w)
          T (n + 1) omega +
        c ^ 2 * quadraticVariationApprox (fun s w => B (min t s) w)
          T (n + 1) omega) +
        sqHalf (H omega +
          girsanovComplexBracketStoppedMeshControl bracket C c T n t omega))
    atTop (fun omega =>
      2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
        sqHalf (H omega))
  simpa only [sqHalf, H, C] using hsum

/-- The stopped compensated-square controls are eventually tight at every
deterministic observation time. -/
theorem
    GirsanovDensityData.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedCompensatedSquareControl
            M bracket B theta c T n t omega} < delta := by
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  let L : W → ℝ := fun omega =>
    2 * (bracket (min T t) omega + c ^ 2 * ((min T t : ℝ≥0) : ℝ)) +
      H omega ^ 2 / 2
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hL : StronglyMeasurable L := by
    have hbracket : StronglyMeasurable (bracket (min T t)) :=
      (hdata.adapted_bracket (min T t)).mono (V.le (min T t))
    have hHsq : StronglyMeasurable (fun omega => H omega ^ 2) := by
      rw [show (fun omega => H omega ^ 2) = H * H by
        funext omega
        simp only [Pi.mul_apply, pow_two]]
      exact hH.mul hH
    unfold L
    exact (stronglyMeasurable_const.mul
      (hbracket.add stronglyMeasurable_const)).add
      (hHsq.mul stronglyMeasurable_const)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t) atTop L := by
    simpa only [L, H] using
      hdata.girsanovComplexStoppedCompensatedSquareControl_tendstoInMeasure
        hB htheta hbracketTerminal c t
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hL)

/-- Total-variation control for the stopped regularized complex bracket. -/
noncomputable def girsanovComplexStoppedVariationControl
    {W : Type*} (bracket theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexTerminalVariationBound bracket theta c T omega +
    girsanovComplexBracketStoppedMeshControl bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedVariationControl
      bracket theta c T n t omega := by
  exact add_nonneg
    (hdata.girsanovComplexTerminalVariationBound_nonneg c omega)
    (girsanovComplexBracketStoppedMeshControl_nonneg bracket
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
      c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedVariationControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤ girsanovComplexStoppedVariationControl
          bracket theta c T n t omega} < delta := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let H : W → ℝ := girsanovComplexTerminalVariationBound
    bracket theta c T
  have hH : StronglyMeasurable H := by
    simpa only [H] using
      hdata.stronglyMeasurable_girsanovComplexTerminalVariationBound
        htheta c
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hmesh : TendstoInMeasure P
      (fun n => girsanovComplexBracketStoppedMeshControl
        bracket C c T n t) atTop (fun _ => 0) :=
    girsanovComplexBracketStoppedMeshControl_tendstoInMeasure_zero
      hbracketMeas (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hCMeas hCcont c T t
  have hconstant : TendstoInMeasure P (fun _n : ℕ => H) atTop H :=
    tendstoInMeasure_of_tendsto_ae
      (fun _n => hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _omega => tendsto_const_nhds)
  have hconv : TendstoInMeasure P
      (fun n => girsanovComplexStoppedVariationControl
        bracket theta c T n t) atTop H := by
    have hsum := hconstant.add_real_noMeas hmesh
    change TendstoInMeasure P (fun n omega =>
      girsanovComplexTerminalVariationBound bracket theta c T omega +
        girsanovComplexBracketStoppedMeshControl bracket
          (fun u z => -regularizedGirsanovIntegratedDrift
            bracket theta T u z) c T n t omega) atTop H
    simpa only [H, C, add_zero] using hsum
  exact hconv.eventually_tight_of_limit_tails
    (StronglyMeasurable.exists_measureReal_ge_lt_finite hH)

/-- The scalar factor that vanishes in the stopped higher-order Doleans
estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderVanishingControl
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  dz * Real.exp dz + dz + dx

theorem girsanovComplexStoppedHigherOrderVanishingControl_nonneg
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderVanishingControl
      M bracket B C c T n t omega := by
  unfold girsanovComplexStoppedHigherOrderVanishingControl
  exact add_nonneg (add_nonneg
    (mul_nonneg
      (girsanovComplexCompensatedStoppedMeshControl_nonneg
        M bracket B C c T n t omega) (Real.exp_pos _).le)
    (girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega))
    (girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega)

theorem girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {M bracket B C : ℝ≥0 → W → ℝ}
    (hMmeas : ∀ s, StronglyMeasurable (M s))
    (hMcont : ∀ omega, Continuous fun s => M s omega)
    (hbracketMeas : ∀ s, StronglyMeasurable (bracket s))
    (hbracketCont : ∀ omega, Continuous fun s => bracket s omega)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (hB : IsPreBrownianReal B P)
    (hCMeas : ∀ s, StronglyMeasurable (C s))
    (hCCont : ∀ omega, Continuous fun s => C s omega)
    (c : ℝ) (T t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) := by
  have hdz :=
    girsanovComplexCompensatedStoppedMeshControl_tendstoInMeasure_zero
      hMmeas hMcont hbracketMeas hbracketCont hCMeas hCCont hB c T t
  have hdx :=
    girsanovComplexCombinationStoppedMeshControl_tendstoInMeasure_zero
      (P := P) hMmeas hMcont hB c T t
  have hdzMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCompensatedStoppedMeshControl
      (P := P) hMmeas hBmeas hbracketMeas hCMeas c T n t
  have hdxMeas (n : ℕ) :=
    aestronglyMeasurable_girsanovComplexCombinationStoppedMeshControl
      (P := P) hMmeas hBmeas c T n t
  let finish : ℝ → ℝ → ℝ := fun dz dx =>
    dz * Real.exp dz + dz + dx
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  have hconv := TendstoInMeasure.continuous_comp₂
    hdzMeas hdxMeas hdz hdx hfinish
  change TendstoInMeasure P (fun n omega =>
    girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega *
        Real.exp (girsanovComplexCompensatedStoppedMeshControl
          M bracket B C c T n t omega) +
      girsanovComplexCompensatedStoppedMeshControl
        M bracket B C c T n t omega +
      girsanovComplexCombinationStoppedMeshControl M B c T n t omega)
    atTop (fun _ => 0)
  simpa only [finish, Real.exp_zero, mul_one, zero_add] using hconv

/-- The tight random factor in the stopped higher-order Doleans estimate. -/
noncomputable def girsanovComplexStoppedHigherOrderTightControl
    {W : Type*} (M bracket B theta : ℝ≥0 → W → ℝ) (c : ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega *
    (girsanovComplexStoppedCompensatedSquareControl
        M bracket B theta c T n t omega +
      girsanovComplexStoppedVariationControl bracket theta c T n t omega)

theorem GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_nonneg
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    0 ≤ girsanovComplexStoppedHigherOrderTightControl
      M bracket B theta c T n t omega := by
  exact mul_nonneg
    (girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega)
    (add_nonneg
      (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
      (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))

theorem
    GirsanovDensityData.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
        P.real {omega | K ≤
          girsanovComplexStoppedHigherOrderTightControl
            M bracket B theta c T n t omega} < delta := by
  have hweight :=
    hdata.girsanovComplexDoleansStoppedWeightControl_tight c t
  have hsquare :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_eventually_tight
      hB htheta hbracketTerminal c t
  have hvariation :=
    hdata.girsanovComplexStoppedVariationControl_eventually_tight
      htheta hbracketTerminal c t
  have hsum := eventually_tight_add_of_nonneg
    (fun n omega =>
      hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
        c n t omega)
    (fun n omega =>
      hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega)
    hsquare hvariation
  simpa only [girsanovComplexStoppedHigherOrderTightControl] using
    eventually_tight_mul_of_nonneg
      (fun n omega =>
        girsanovComplexDoleansStoppedWeightControl_nonneg
          M bracket c T n t omega)
      (fun n omega => add_nonneg
        (hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg
          c n t omega)
        (hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega))
      hweight hsum

/-- The stopped higher-order exponential majorant factors into a vanishing
mesh term and an eventually tight random term. -/
theorem GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_le_controls
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t omega ≤
      girsanovComplexStoppedHigherOrderVanishingControl M bracket B
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  let X := complexMartingaleCombination M B c
  let Q := complexMartingaleCombinationBracket bracket C c
  let K := girsanovComplexDoleansStoppedWeightControl M bracket c T n t omega
  let dz := girsanovComplexCompensatedStoppedMeshControl
    M bracket B C c T n t omega
  let dx := girsanovComplexCombinationStoppedMeshControl M B c T n t omega
  let S := girsanovComplexStoppedCompensatedSquareControl
    M bracket B theta c T n t omega
  let R := girsanovComplexStoppedVariationControl bracket theta c T n t omega
  have hK : 0 ≤ K :=
    girsanovComplexDoleansStoppedWeightControl_nonneg
      M bracket c T n t omega
  have hdz : 0 ≤ dz :=
    girsanovComplexCompensatedStoppedMeshControl_nonneg
      M bracket B C c T n t omega
  have hdx : 0 ≤ dx :=
    girsanovComplexCombinationStoppedMeshControl_nonneg
      M B c T n t omega
  have hS : 0 ≤ S :=
    hdata.girsanovComplexStoppedCompensatedSquareControl_nonneg c n t omega
  have hR : 0 ≤ R :=
    hdata.girsanovComplexStoppedVariationControl_nonneg c n t omega
  have hraw : complexDoleansHigherOrderResidualBoundApprox
      X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := by
    apply complexDoleansHigherOrderResidualBoundApprox_le_of_cell_bounds
    · exact hK
    · exact hdz
    · exact hdx
    · intro i hi
      exact
        norm_complexDoleansDadeExponential_combination_stopped_le_weightControl
          M bracket B C c T n t omega hi
    · intro i hi
      exact norm_girsanov_compensated_stopped_uniformPartition_increment_le
        M bracket B C c T n t omega hi
    · intro i hi
      exact
        norm_complexMartingaleCombination_stopped_uniformPartition_increment_le
          M B c T n t omega hi
    · simpa only [X, Q, C, S] using
        hdata.sum_norm_girsanov_compensated_stopped_increment_sq_le
          htheta hbracketTerminal c n t omega
    · change complexTotalVariationApprox
          (fun s w => Q (min t s) w) T (n + 1) omega ≤ R
      simpa only [Q, C, R, girsanovComplexStoppedVariationControl] using
        hdata.complexTotalVariationApprox_stopped_le_terminal
          htheta hbracketTerminal c n t omega
  calc
    complexDoleansHigherOrderResidualBoundApprox X Q T (n + 1) t omega ≤
        K * (dz * Real.exp dz * S + (R / 2) * (dz + dx) / 2) := hraw
    _ ≤ (dz * Real.exp dz + dz + dx) * (K * (S + R)) := by
      have hexp : 0 ≤ Real.exp dz := (Real.exp_pos _).le
      nlinarith [mul_nonneg hK hS, mul_nonneg hK hR,
        mul_nonneg hdz hexp, mul_nonneg (add_nonneg hdz hdx) hR]
    _ = girsanovComplexStoppedHigherOrderVanishingControl M bracket B C
          c T n t omega *
        girsanovComplexStoppedHigherOrderTightControl
          M bracket B theta c T n t omega := by
      rfl

/-- Under the Challenge hypotheses, the explicit stopped-grid higher-order
majorant vanishes in probability. -/
theorem
    GirsanovDensityData.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P)
    (hBmeas : ∀ s, StronglyMeasurable (B s))
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (c : ℝ) (t : ℝ≥0) :
    TendstoInMeasure P (fun n =>
      complexDoleansHigherOrderResidualBoundApprox
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z)
          c) T (n + 1) t) atTop (fun _ => 0) := by
  let C : ℝ≥0 → W → ℝ := fun u z =>
    -regularizedGirsanovIntegratedDrift bracket theta T u z
  have hMmeas : ∀ s, StronglyMeasurable (M s) := fun s =>
    (hdata.adapted_martingale s).mono (V.le s)
  have hbracketMeas : ∀ s, StronglyMeasurable (bracket s) := fun s =>
    (hdata.adapted_bracket s).mono (V.le s)
  have hCMeas : ∀ s, StronglyMeasurable (C s) := fun s => by
    change StronglyMeasurable
      (-regularizedGirsanovIntegratedDrift bracket theta T s)
    exact (stronglyMeasurable_regularizedGirsanovIntegratedDrift
      hdata.adapted_bracket htheta s).neg
  have hCcont : ∀ omega, Continuous (fun s => C s omega) := fun omega => by
    change Continuous
      (-fun s => regularizedGirsanovIntegratedDrift bracket theta T s omega)
    exact (continuous_regularizedGirsanovIntegratedDrift
      htheta hbracketTerminal omega).neg
  have hr : TendstoInMeasure P (fun n =>
      girsanovComplexStoppedHigherOrderVanishingControl
        M bracket B C c T n t) atTop (fun _ => 0) :=
    girsanovComplexStoppedHigherOrderVanishingControl_tendstoInMeasure_zero
      hMmeas hdata.continuous_martingale_path hbracketMeas
      (fun omega => (hdata.continuous_monotone_bracket omega).1)
      hBmeas hB hCMeas hCcont c T t
  have hqTight :=
    hdata.girsanovComplexStoppedHigherOrderTightControl_eventually_tight
      hB htheta hbracketTerminal c t
  apply hr.of_norm_sub_le_mul_of_eventually_tight
    (fun n omega =>
      hdata.girsanovComplexStoppedHigherOrderTightControl_nonneg
        c n t omega) hqTight
  intro n omega
  rw [sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (complexDoleansHigherOrderResidualBoundApprox_nonneg
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t omega),
    Real.norm_eq_abs,
    abs_of_nonneg
      (girsanovComplexStoppedHigherOrderVanishingControl_nonneg
        M bracket B C c T n t omega)]
  simpa only [C] using
    hdata.complexDoleansHigherOrderResidualBoundApprox_le_controls
      htheta hbracketTerminal c n t omega

/-- The norm of the full higher-order residual is bounded pathwise by the
explicit sum of its one-cell majorants. -/
theorem norm_complexDoleansHigherOrderResidualApprox_le_bound
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    ‖complexDoleansHigherOrderResidualApprox X Q U n t omega‖ ≤
      complexDoleansHigherOrderResidualBoundApprox X Q U n t omega := by
  unfold complexDoleansHigherOrderResidualApprox
    complexDoleansHigherOrderResidualBoundApprox
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun i _hi => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_complexDoleansSecondOrderResidual_le_bound _ _) (norm_nonneg _)

end StochasticCalculus
