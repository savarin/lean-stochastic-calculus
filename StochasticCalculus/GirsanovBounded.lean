/-
Copyright (c) 2026 The lean-stochastic-calculus contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-stochastic-calculus contributors
-/
import StochasticCalculus.GirsanovClosure
import StochasticCalculus.GirsanovMoments

/-!
# Girsanov closure under a bounded density

The paired probability limit becomes an L1 limit when the real stochastic
exponential is bounded through the horizon. The real integrator is a true
square-integrable martingale by the Novikov moment consequences.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace StochasticCalculus

/-- Rational identities on horizons below `T` suffice for every ordered
pair below `T`, provided set integrals are continuous along time sequences.
The approximation approaches the earlier time from above, preserving past
event measurability without completing the filtration. -/
theorem setIntegral_eq_of_uniformRational_below
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W} {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {F : ℝ≥0 → W → E} {T : ℝ≥0}
    (hlimit : ∀ (r : ℝ≥0) (a : ℕ → ℝ≥0), r ≤ T →
      (∀ n, a n ≤ T) → Tendsto a atTop (nhds r) → ∀ A : Set W,
        Tendsto (fun n ↦ ∫ omega in A, F (a n) omega ∂P) atTop
          (nhds (∫ omega in A, F r omega ∂P)))
    (hrational : ∀ (U : ℝ≥0), U ≤ T → ∀ {k j : ℕ},
      0 < k → 0 < j → j ≤ k → ∀ {A : Set W},
        MeasurableSet[V (U * (j : ℝ≥0) / (k : ℝ≥0))] A →
          (∫ omega in A, F (U * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
            ∫ omega in A, F U omega ∂P)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set W} (hA : MeasurableSet[V s] A) :
    (∫ omega in A, F s omega ∂P) = ∫ omega in A, F t omega ∂P := by
  by_cases hstEq : s = t
  · subst t
    rfl
  by_cases hs0 : s = 0
  · subst s
    let a : ℕ → ℝ≥0 := fun n ↦ t / (n + 1 : ℕ)
    have ha : Tendsto a atTop (nhds 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
    have haT (n : ℕ) : a n ≤ T := by
      have h := (uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
        (Nat.succ_le_succ (Nat.zero_le n))).2
      have hat : a n ≤ t := by
        simpa only [a, uniformPartitionTime, Nat.cast_one, mul_one] using h
      exact hat.trans htT
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hraw := hrational t htT (Nat.zero_lt_succ n) Nat.one_pos
        (Nat.succ_le_succ (Nat.zero_le n)) (V.mono bot_le A hA)
      simpa only [a, Nat.cast_one, mul_one] using hraw
    have hconv := hlimit 0 a bot_le haT ha A
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv tendsto_const_nhds
  · let tau : Unit → WithTop ℝ≥0 := fun _ ↦ (s : WithTop ℝ≥0)
    have hbound : ∀ omega, tau omega ≤ (t : WithTop ℝ≥0) :=
      fun _ ↦ WithTop.coe_le_coe.mpr hst
    let j : ℕ → ℕ := fun n ↦ uniformPartitionCeilIndex tau t (n + 1)
      (Nat.zero_lt_succ n) hbound ()
    let a : ℕ → ℝ≥0 := fun n ↦ uniformPartitionTime t (n + 1) (j n)
    have hjpos (n : ℕ) : 0 < j n := by
      by_contra hn
      have hj0 : j n = 0 := Nat.eq_zero_of_not_pos hn
      have hspec := uniformPartitionCeilIndex_spec tau t (n + 1)
        (Nat.zero_lt_succ n) hbound ()
      change (s : WithTop ℝ≥0) ≤
        (uniformPartitionTime t (n + 1) (j n) : WithTop ℝ≥0) at hspec
      rw [hj0] at hspec
      simp only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        WithTop.coe_zero] at hspec
      exact hs0 (nonpos_iff_eq_zero.mp (WithTop.coe_le_coe.mp hspec))
    have hjle (n : ℕ) : j n ≤ n + 1 :=
      uniformPartitionCeilIndex_le tau t (n + 1) (Nat.zero_lt_succ n) hbound ()
    have hsa (n : ℕ) : s ≤ a n := by
      exact WithTop.coe_le_coe.mp
        (uniformPartitionCeilIndex_spec tau t (n + 1) (Nat.zero_lt_succ n) hbound ())
    have haT (n : ℕ) : a n ≤ T :=
      ((uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n) (hjle n)).2).trans htT
    have ha : Tendsto a atTop (nhds s) := by
      have hwith := tendsto_uniformPartitionCeilStoppingTime tau t hbound ()
      have huntop := (WithTop.tendsto_untopA WithTop.coe_ne_top).comp hwith
      have hcoe (x : ℝ≥0) : WithTop.untopA (x : WithTop ℝ≥0) = x := rfl
      change Tendsto (fun n ↦ WithTop.untopA (a n : WithTop ℝ≥0))
        atTop (nhds (WithTop.untopA (s : WithTop ℝ≥0))) at huntop
      simpa only [hcoe] using huntop
    have heq (n : ℕ) :
        (∫ omega in A, F (a n) omega ∂P) = ∫ omega in A, F t omega ∂P := by
      have hraw := hrational t htT (Nat.zero_lt_succ n) (hjpos n) (hjle n)
        (V.mono (hsa n) A hA)
      simpa only [a, uniformPartitionTime] using hraw
    have hconv := hlimit s a (hst.trans htT) haT ha A
    rw [show (fun n ↦ ∫ omega in A, F (a n) omega ∂P) =
        (fun _ : ℕ ↦ ∫ omega in A, F t omega ∂P) from funext heq] at hconv
    exact tendsto_nhds_unique hconv tendsto_const_nhds

/-- Under a deterministic density bound, the genuine self-integrator Euler
sums are martingales and have uniformly integrable time sections on every
grid below the Novikov horizon. -/
theorem GirsanovDensityData.martingale_uniformIntegrable_complexEulerSelf_of_density_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hBmart : Martingale B V P)
    (hC : StronglyAdapted V C) (hUT : U ≤ T)
    (R : ℝ≥0) (hR : ∀ s, s ≤ U → ∀ omega,
      doleansDadeExponential M bracket s omega ≤ R) (c : ℝ) :
    (∀ n, Martingale (complexGirsanovEulerProcess
      M M bracket B C c U (n + 1)) V P) ∧
      ∀ t, UniformIntegrable (fun n ↦ complexGirsanovEulerProcess
        M M bracket B C c U (n + 1) t) 1 P := by
  let N : ℝ≥0 → W → ℝ := fun t ↦ M (min t T)
  have hN : Martingale N V P := hdata.martingale_stopAt_martingale
  have hNT : MemLp (N T) 2 P := by
    have hMT := hdata.memLp_two_stoppedValue_martingale (isStoppingTime_const V T)
      (fun _ ↦ le_rfl)
    change MemLp (M T) 2 P at hMT
    simpa only [N, min_self] using hMT
  have hNU : MemLp (N U) 2 P :=
    martingale_memLp_of_le hN hUT (by norm_num) hNT
  have hN0 : MemLp (N 0) 2 P :=
    martingale_memLp_of_le hN bot_le (by norm_num) hNT
  have hBU : MemLp (B U) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval U).memLp ENNReal.ofNat_ne_top
  have hB0 : MemLp (B 0) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval 0).memLp ENNReal.ofNat_ne_top
  let F : ℕ → ℝ≥0 → W → ℂ := fun n ↦
    cappedComplexGirsanovEulerProcess N M bracket B C c R U (n + 1)
  have hF (n : ℕ) : Martingale (F n) V P :=
    martingale_cappedComplexGirsanovEulerProcess hN hBmart
      hdata.adapted_martingale hdata.adapted_bracket hBmart.stronglyAdapted hC
        c R U (n + 1)
  have hFeq (n : ℕ) : F n =
      complexGirsanovEulerProcess M M bracket B C c U (n + 1) := by
    funext t omega
    rw [show F n t omega = complexGirsanovEulerProcess
        N M bracket B C c U (n + 1) t omega from
      cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
        N M bracket B C c R U (n + 1) omega (fun s hs ↦ by
          exact min_eq_left (hR s hs.2 omega)) t]
    exact complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
      N M M bracket B C c U (n + 1) omega
        (fun s hs ↦ by simp only [N, min_eq_left (hs.2.trans hUT)]) t
  refine ⟨fun n ↦ by rw [← hFeq n]; exact hF n, ?_⟩
  intro t
  let L : ℝ≥0∞ := cappedComplexGirsanovCoefficientBound c R U +
    2 * cappedComplexGirsanovCoefficientBound c R U * eLpNorm (N U - N 0) 2 P +
    2 * cappedComplexGirsanovBrownianCoefficientBound c R U *
      eLpNorm (B U - B 0) 2 P
  have hL : L ≠ ∞ := by
    have hNd := (hNU.sub hN0).eLpNorm_ne_top
    have hBd := (hBU.sub hB0).eLpNorm_ne_top
    dsimp only [L]
    finiteness
  apply uniformIntegrable_one_of_uniform_eLpNorm_two
    (fun n ↦ by rw [← hFeq n]; exact ((hF n).integrable t).aestronglyMeasurable)
      L.toNNReal
  intro n
  rw [← hFeq n, ENNReal.coe_toNNReal hL]
  exact eLpNorm_cappedComplexGirsanovEulerProcess_le_of_memLp_terminal
    hN hBmart hdata.adapted_martingale hdata.adapted_bracket
    hBmart.stronglyAdapted hC c R U hNU hBU n t

/-- The exact complex exponential has the eventwise martingale identity at
each rational pair below the horizon whenever its real density is bounded. -/
theorem GirsanovDensityData.setIntegral_complexDoleans_rational_of_density_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T U : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBmart : Martingale B V P) (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (R : ℝ≥0) (hR : ∀ s, s ≤ T → ∀ omega,
      doleansDadeExponential M bracket s omega ≤ R)
    (c : ℝ) (hUT : U ≤ T) {k j : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k)
    {A : Set W} (hA : MeasurableSet[V (U * (j : ℝ≥0) / (k : ℝ≥0))] A) :
    let C : ℝ≥0 → W → ℝ := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
    let E := complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
    (∫ omega in A, E (U * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
      ∫ omega in A, E U omega ∂P := by
  dsimp only
  by_cases hU : U = 0
  · simp only [hU, zero_mul, zero_div]
  have hUpos : 0 < U := bot_lt_iff_ne_bot.mpr hU
  let C : ℝ≥0 → W → ℝ := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
  let E := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let a := U * (j : ℝ≥0) / (k : ℝ≥0)
  have haU : a ≤ U := (uniformPartitionTime_mem_Icc_of_le U hk hjk).2
  have hC : StronglyAdapted V C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift htheta T).neg
  obtain ⟨q, _hq, hpa, hpU⟩ := hdata.exists_rational_pair_girsanovComplexEulerSelf
    hB hsm htheta hbracketTheta hcross c hUT hUpos hk hj hjk
  obtain ⟨hmart, hUI⟩ :=
    hdata.martingale_uniformIntegrable_complexEulerSelf_of_density_le hB hBmart hC hUT
      R (fun s hs ↦ hR s (hs.trans hUT)) c
  let F : ℕ → ℝ≥0 → W → ℂ := fun n ↦
    complexGirsanovEulerProcess M M bracket B C c U (q n + 1)
  have hEa : Integrable (E a) P :=
    by simpa only [E, min_eq_left (haU.trans hUT)] using
      hdata.integrable_stopAt_complexDoleans_combination hBmart.stronglyAdapted hC c a
  have hEU : Integrable (E U) P :=
    by simpa only [E, min_eq_left hUT] using
      hdata.integrable_stopAt_complexDoleans_combination hBmart.stronglyAdapted hC c U
  have hLa := tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    (StochasticCalculus.UniformIntegrable.comp_index (hUI a) q) hpa
  have hLU := tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach
    (StochasticCalculus.UniformIntegrable.comp_index (hUI U) q) hpU
  have hIa := tendsto_setIntegral_of_L1' (E a) hEa.aestronglyMeasurable
    (Filter.Eventually.of_forall fun n ↦ (hmart (q n)).integrable a) hLa A
  have hIU := tendsto_setIntegral_of_L1' (E U) hEU.aestronglyMeasurable
    (Filter.Eventually.of_forall fun n ↦ (hmart (q n)).integrable U) hLU A
  have heq (n : ℕ) : (∫ omega in A, F n a omega ∂P) =
      ∫ omega in A, F n U omega ∂P :=
    (hmart (q n)).setIntegral_eq haU hA
  change Tendsto (fun n ↦ ∫ omega in A, F n a omega ∂P) _ _ at hIa
  simp_rw [heq] at hIa
  exact tendsto_nhds_unique hIa hIU

/-- A bounded real density closes the full complex exponential martingale
identity through the Novikov horizon, including arbitrary observation times. -/
theorem GirsanovDensityData.martingale_stopAt_complexDoleans_of_density_le
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBmart : Martingale B V P) (htheta : IsStronglyPredictable V theta)
    (hbracketTheta : ∀ t omega, bracket t omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) (min t T), (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega ↦ -girsanovIntegratedDrift theta T t omega) P)
    (R : ℝ≥0) (hR : ∀ s, s ≤ T → ∀ omega,
      doleansDadeExponential M bracket s omega ≤ R) (c : ℝ) :
    Martingale (fun t ↦ complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket
        (fun u omega ↦ -girsanovIntegratedDrift theta T u omega) c)
      (min t T)) V P := by
  let C : ℝ≥0 → W → ℝ := fun t omega ↦ -girsanovIntegratedDrift theta T t omega
  let E := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let F : ℝ≥0 → W → ℂ := fun t ↦ E (min t T)
  have hC : StronglyAdapted V C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift htheta T).neg
  have hE : StronglyAdapted V E :=
    stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hBmart.stronglyAdapted c)
      (stronglyAdapted_complexMartingaleCombinationBracket hdata.adapted_bracket hC c)
  have hF : StronglyAdapted V F := fun t ↦
    (hE (min t T)).mono (V.mono (min_le_left t T))
  have hFint (t : ℝ≥0) : Integrable (F t) P :=
    hdata.integrable_stopAt_complexDoleans_combination hBmart.stronglyAdapted hC c t
  have hbrT : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure := by
    simpa only [min_self] using hbracketTheta T
  have hlimit (r : ℝ≥0) (a : ℕ → ℝ≥0) (_hr : r ≤ T) (_haT : ∀ n, a n ≤ T)
      (ha : Tendsto a atTop (nhds r)) (A : Set W) :
      Tendsto (fun n ↦ ∫ omega in A, F (a n) omega ∂P) atTop
        (nhds (∫ omega in A, F r omega ∂P)) := by
    have hp := hdata.tendstoInMeasure_stopAt_complexDoleans_neg_integratedDrift
      hB hsm hBmart.stronglyAdapted htheta hbrT hcross c ha
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (hdata.uniformIntegrable_stopAt_complexDoleans_combination
        hBmart.stronglyAdapted hC c) a
    have hLp := tendsto_eLpNorm_one_of_tendstoInMeasure_of_uniformIntegrable_banach hUI hp
    exact tendsto_setIntegral_of_L1' (F r) (hFint r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n ↦ hFint (a n)) hLp A
  have hrat (U : ℝ≥0) (hUT : U ≤ T) {k j : ℕ}
      (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) {A : Set W}
      (hA : MeasurableSet[V (U * (j : ℝ≥0) / (k : ℝ≥0))] A) :
      (∫ omega in A, F (U * (j : ℝ≥0) / (k : ℝ≥0)) omega ∂P) =
        ∫ omega in A, F U omega ∂P := by
    have haT : U * (j : ℝ≥0) / (k : ℝ≥0) ≤ T :=
      ((uniformPartitionTime_mem_Icc_of_le U hk hjk).2).trans hUT
    simpa only [F, E, C, min_eq_left haT, min_eq_left hUT] using
      hdata.setIntegral_complexDoleans_rational_of_density_le
        hB hsm hBmart htheta hbracketTheta hcross R hR c hUT hk hj hjk hA
  refine ⟨hF, ?_⟩
  intro s t hst
  refine (ae_eq_condExp_of_forall_setIntegral_eq (V.le s)
    (hFint t) (fun A _ _ ↦ (hFint s).integrableOn) ?_
      (hF s).aestronglyMeasurable).symm
  intro A hA _hPA
  by_cases hTs : T ≤ s
  · simp only [F, min_eq_right hTs, min_eq_right (hTs.trans hst)]
  have hsT : s ≤ T := le_of_not_ge hTs
  have heq := setIntegral_eq_of_uniformRational_below hlimit hrat
    (le_min hst hsT) (min_le_right t T) hA
  simpa only [F, min_assoc, min_self] using heq

end StochasticCalculus
