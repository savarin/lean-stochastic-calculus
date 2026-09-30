/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import StochasticCalculus.GirsanovStoppedControl

/-!
# Girsanov change of measure

The endpoint of the predictable-integrand Girsanov theorem.  The
second-order identity for the Euler residual, martingality and
integrability of the capped complex Euler process and of the stopped complex
Doléans--Dade combination, the higher-order and Fourier-increment martingale
conditions, and the conclusion: under the density contract the shifted
driver is pre-Brownian for the exact terminal density measure `Z_T · P`.
The final section records that a strongly adapted continuous modification of
a natural predictable Itô integral carries the local quadratic-variation
contract.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- On every observation time, including a crossing cell, the exact Euler
residual is half the weighted bracket discrepancy plus the higher-order
remainder. -/
theorem complexDoleansEulerResidualApprox_eq_secondOrder
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) :
    complexDoleansEulerResidualApprox X Q U (n + 1) t omega =
      (1 / 2 : ℂ) *
          complexDoleansWeightedBracketResidualApprox
            X Q U (n + 1) t omega +
        complexDoleansHigherOrderResidualApprox
          X Q U (n + 1) t omega := by
  unfold complexDoleansEulerResidualApprox
    complexDoleansWeightedBracketResidualApprox
    complexDoleansHigherOrderResidualApprox
  simp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≤ n + 1 := (Finset.mem_range.mp hi).le
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hleftU := (uniformPartitionTime_mem_Icc_of_le U
    (Nat.zero_lt_succ n) hi0).2
  by_cases hleftT : uniformPartitionTime U (n + 1) i ≤ t
  · rw [min_eq_right hleftT, min_eq_left hleftU]
    rw [complexDoleansDadeExponential_increment_sub_linear_eq_secondOrder]
    ring
  · have htleft : t ≤ uniformPartitionTime U (n + 1) i :=
      le_of_not_ge hleftT
    have hmono : uniformPartitionTime U (n + 1) i ≤
        uniformPartitionTime U (n + 1) (i + 1) :=
      monotone_uniformPartitionTime_general U (n + 1) (Nat.le_succ i)
    have htright : t ≤ uniformPartitionTime U (n + 1) (i + 1) :=
      htleft.trans hmono
    rw [min_eq_left htleft, min_eq_left htright]
    simp [complexDoleansSecondOrderResidual]

/-- Endpoint minus the canonical complex Euler process is exactly the sum
of its one-step residuals. -/
theorem complexDoleansDadeExponential_sub_complexDoleansEulerProcess_eq_residual
    {W : Type*} (X Q : ℝ≥0 → W → ℂ)
    (U t : ℝ≥0) (n : ℕ) (omega : W) :
    complexDoleansDadeExponential X Q (min t U) omega -
        complexDoleansEulerProcess X Q U (n + 1) t omega =
      complexDoleansEulerResidualApprox X Q U (n + 1) t omega := by
  let E := complexDoleansDadeExponential X Q
  have htelescope :
      (∑ i ∈ Finset.range (n + 1),
        (E (min t (uniformPartitionTime U (n + 1) (i + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) i)) omega)) =
        E (min t U) omega - E 0 omega := by
    calc
      _ = E (min t (uniformPartitionTime U (n + 1) (n + 1))) omega -
          E (min t (uniformPartitionTime U (n + 1) 0)) omega := by
        simpa using (Finset.sum_range_sub (fun i =>
          E (min t (uniformPartitionTime U (n + 1) i)) omega) (n + 1))
      _ = E (min t U) omega - E 0 omega := by
        simp [uniformPartitionTime]
  dsimp only [E] at htelescope
  unfold complexDoleansEulerProcess complexDoleansEulerResidualApprox
  simp only
  rw [Finset.sum_sub_distrib, htelescope]
  rw [min_eq_left (show (0 : ℝ≥0) ≤ U from bot_le)]
  ring

/-- For the Girsanov complex combination, the self-integrator two-transform
Euler process is exactly the canonical single complex Doléans left sum. -/
theorem complexGirsanovEulerProcess_self_eq_complexDoleansEulerProcess
    {W : Type*} (M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) :
    complexGirsanovEulerProcess M M bracket B C c U n =
      complexDoleansEulerProcess
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) U n := by
  funext t omega
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      (min s U) omega
  let A : ℕ → ℂ := fun i =>
    (M (min t (uniformPartitionTime U n (i + 1))) omega -
      M (min t (uniformPartitionTime U n i)) omega) •
        H (uniformPartitionTime U n i) omega
  let D : ℕ → ℂ := fun i =>
    (B (min t (uniformPartitionTime U n (i + 1))) omega -
      B (min t (uniformPartitionTime U n i)) omega) •
        (((c : ℂ) * Complex.I) * H (uniformPartitionTime U n i) omega)
  let F : ℕ → ℂ := fun i =>
    (complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n (i + 1))) omega -
      complexMartingaleCombination M B c
        (min t (uniformPartitionTime U n i)) omega) *
        H (uniformPartitionTime U n i) omega
  unfold complexGirsanovEulerProcess complexDoleansEulerProcess
    uniformAdaptedTwoMartingaleSmulProcess
    uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
    elementaryMartingaleSmulProcess
  simp only [Pi.add_apply, Finset.sum_apply]
  change H 0 omega +
      ((∑ i ∈ Finset.range n, A i) + ∑ i ∈ Finset.range n, D i) =
    H 0 omega + ∑ i ∈ Finset.range n, F i
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [A, D, F, complexMartingaleCombination]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Once the density cap agrees with the real stochastic exponential on a
whole horizon, the capped and uncapped complex Euler processes agree there
on every grid and at every observation time. -/
theorem cappedComplexGirsanovEulerProcess_eq_complex_of_cap_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) (omega : W)
    (hcap : ∀ s ∈ Set.Icc (0 : ℝ≥0) U,
      cappedDoleansDadeExponential M bracket R s omega =
        doleansDadeExponential M bracket s omega) :
    ∀ t, cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n t omega =
      complexGirsanovEulerProcess N M bracket B C c U n t omega := by
  have hcomplex (s : ℝ≥0) (hs : s ≤ U) :
      cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R s omega =
        complexDoleansDadeExponential
          (complexMartingaleCombination M B c)
          (complexMartingaleCombinationBracket bracket C c) s omega := by
    unfold cappedComplexDoleansDadeExponentialCombination
    rw [hcap s ⟨bot_le, hs⟩,
      complexDoleansDadeExponential_combination_factor]
  intro t
  unfold cappedComplexGirsanovEulerProcess complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  · simpa only [min_eq_left (show (0 : ℝ≥0) ≤ U by exact bot_le)] using
      hcomplex 0 bot_le
  · unfold uniformAdaptedTwoMartingaleSmulProcess
    simp only [Pi.add_apply]
    congr 1
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact hcomplex (min (uniformPartitionTime U n i) U) (min_le_right _ _)
    · unfold uniformAdaptedMartingaleSmulProcess
        elementaryMartingaleSmulSum
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      unfold elementaryMartingaleSmulProcess
      congr 1
      exact congrArg (fun z : ℂ => ((c : ℂ) * Complex.I) * z)
        (hcomplex (min (uniformPartitionTime U n i) U)
          (min_le_right _ _))

/-- If two first integrators agree throughout the deterministic horizon,
their uncapped complex Euler processes agree on every grid and at every
observation time. -/
theorem complexGirsanovEulerProcess_eq_of_integrator_eq_on_Icc
    {W : Type*} (N N' M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (U : ℝ≥0) (n : ℕ) (omega : W)
    (hNN' : ∀ s ∈ Set.Icc (0 : ℝ≥0) U, N s omega = N' s omega) :
    ∀ t, complexGirsanovEulerProcess N M bracket B C c U n t omega =
      complexGirsanovEulerProcess N' M bracket B C c U n t omega := by
  intro t
  unfold complexGirsanovEulerProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedTwoMartingaleSmulProcess
  simp only [Pi.add_apply]
  congr 1
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n := Finset.mem_range.mp hi
  have hi0 : i ≤ n := (Nat.le_succ i).trans hi1
  have hn : 0 < n := (Nat.zero_le i).trans_lt (Finset.mem_range.mp hi)
  unfold elementaryMartingaleSmulProcess
  congr 2
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi1).2⟩
  · apply hNN'
    exact ⟨bot_le, (min_le_right _ _).trans
      (uniformPartitionTime_mem_Icc_of_le U hn hi0).2⟩

/-- Unfolding the capped complex Euler process exposes exactly its initial
value and the two coherent martingale transforms. -/
theorem cappedComplexGirsanovEulerProcess_eq
    {W : Type*} (N M bracket B C : ℝ≥0 → W → ℝ)
    (c : ℝ) (R T : ℝ≥0) (n : ℕ) :
    cappedComplexGirsanovEulerProcess N M bracket B C c R T n =
      let H : ℝ≥0 → W → ℂ := fun s omega =>
        cappedComplexDoleansDadeExponentialCombination
          M bracket B C c R (min s T) omega
      let J : ℝ≥0 → W → ℂ := fun s omega =>
        ((c : ℂ) * Complex.I) * H s omega
      (fun _ => H 0) +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T n := by
  rfl

/-- For a martingale approximation `N` of `M`, every capped complex Euler
process is a genuine martingale.  This is the discrete probabilistic half of
the remaining Girsanov cancellation argument. -/
theorem martingale_cappedComplexGirsanovEulerProcess
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [IsFiniteMeasure P]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R U : ℝ≥0) (n : ℕ) :
    Martingale
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R U n) V P := by
  let H : ℝ≥0 → W → ℂ := fun t omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min t U) omega
  let K : ℝ≥0 → W → ℂ := fun t omega =>
    ((c : ℂ) * Complex.I) * H t omega
  let CH : ℝ := (R : ℝ) * Real.exp (c ^ 2 * (U : ℝ) / 2)
  let CK : ℝ := |c| * CH
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun t =>
    (hcap (min t U)).mono (V.mono (min_le_left t U))
  have hK : StronglyAdapted V K := fun t => by
    exact stronglyMeasurable_const.mul (hH t)
  have hHbound (t : ℝ≥0) (omega : W) : ‖H t omega‖ ≤ CH := by
    exact norm_cappedComplexDoleansDadeExponentialCombination_le
      M bracket B C c R U (min t U) (min_le_right t U) omega
  have hKbound (t : ℝ≥0) (omega : W) : ‖K t omega‖ ≤ CK := by
    dsimp only [K, CK]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (hHbound t omega) (abs_nonneg c)
  have hsum : Martingale
      (uniformAdaptedTwoMartingaleSmulProcess N B H K U n) V P :=
    martingale_uniformAdaptedTwoMartingaleSmulProcess
      hN hBmart hH hK CH CK hHbound hKbound U n
  have hH0meas : StronglyMeasurable (H 0) :=
    (hH 0).mono (V.le 0)
  have hH0int : Integrable (H 0) P := by
    refine Integrable.mono' (integrable_const CH)
      hH0meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun omega => hHbound 0 omega
  have hinitial : Martingale (fun _ => H 0) V P :=
    martingale_const_fun V P (hH 0) hH0int
  simpa only [cappedComplexGirsanovEulerProcess, H, K] using
    hinitial.add hsum

/-- The capped complex Euler process has an explicit grid-independent `L²`
bound whenever both real integrators have square-integrable terminal values.
The estimate holds at every observation time and requires no path continuity
of the Brownian integrator. -/
theorem eLpNorm_cappedComplexGirsanovEulerProcess_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {N M bracket B C : ℝ≥0 → W → ℝ}
    (hN : Martingale N V P) (hBmart : Martingale B V P)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (R T : ℝ≥0) (hNT : MemLp (N T) 2 P)
    (hBT : MemLp (B T) 2 P) (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (cappedComplexGirsanovEulerProcess
        N M bracket B C c R T (n + 1) t) 2 P ≤
      cappedComplexGirsanovCoefficientBound c R T +
        2 * cappedComplexGirsanovCoefficientBound c R T *
          eLpNorm (N T - N 0) 2 P +
        2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
          eLpNorm (B T - B 0) 2 P := by
  let CH : ℝ≥0 := cappedComplexGirsanovCoefficientBound c R T
  let CK : ℝ≥0 :=
    cappedComplexGirsanovBrownianCoefficientBound c R T
  let H : ℝ≥0 → W → ℂ := fun s omega =>
    cappedComplexDoleansDadeExponentialCombination
      M bracket B C c R (min s T) omega
  let J : ℝ≥0 → W → ℂ := fun s omega =>
    ((c : ℂ) * Complex.I) * H s omega
  have hcap : StronglyAdapted V
      (cappedComplexDoleansDadeExponentialCombination
        M bracket B C c R) :=
    stronglyAdapted_cappedComplexDoleansDadeExponentialCombination
      hM hbracket hB hC c R
  have hH : StronglyAdapted V H := fun s =>
    (hcap (min s T)).mono (V.mono (min_le_left s T))
  have hJ : StronglyAdapted V J := fun s =>
    stronglyMeasurable_const.mul (hH s)
  have hHbound (s : ℝ≥0) (omega : W) : ‖H s omega‖ ≤ CH := by
    dsimp only [H, CH, cappedComplexGirsanovCoefficientBound]
    rw [Real.toNNReal_of_nonneg (Real.exp_pos _).le]
    simpa only [NNReal.coe_mul, NNReal.coe_mk] using
      norm_cappedComplexDoleansDadeExponentialCombination_le
        M bracket B C c R T (min s T) (min_le_right s T) omega
  have hJbound (s : ℝ≥0) (omega : W) : ‖J s omega‖ ≤ CK := by
    dsimp only [J]
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    dsimp only [CK, cappedComplexGirsanovBrownianCoefficientBound]
    rw [Real.toNNReal_of_nonneg
      (mul_nonneg (abs_nonneg c) CH.coe_nonneg)]
    exact mul_le_mul_of_nonneg_left (hHbound s omega) (abs_nonneg c)
  have hinitial : eLpNorm (H 0) 2 P ≤ CH := by
    calc
      eLpNorm (H 0) 2 P ≤
          P Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (CH : ℝ) :=
        eLpNorm_le_of_ae_bound ((hH 0).mono (V.le 0)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun omega => hHbound 0 omega)
      _ = CH := by simp
  rw [congrFun
    (cappedComplexGirsanovEulerProcess_eq
      N M bracket B C c R T (n + 1)) t]
  change eLpNorm (H 0 +
    uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤ _
  calc
    eLpNorm (H 0 +
        uniformAdaptedTwoMartingaleSmulProcess N B H J T (n + 1) t) 2 P ≤
        eLpNorm (H 0) 2 P +
          eLpNorm
            (uniformAdaptedTwoMartingaleSmulProcess
              N B H J T (n + 1) t) 2 P :=
      eLpNorm_add_le (by norm_num)
    _ ≤ CH +
          (2 * CH * eLpNorm (N T - N 0) 2 P +
            2 * CK * eLpNorm (B T - B 0) 2 P) :=
      add_le_add hinitial
        (eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
          hN hBmart T hNT hBT hH hJ CH CK hHbound hJbound n t)
    _ = CH + 2 * CH * eLpNorm (N T - N 0) 2 P +
          2 * CK * eLpNorm (B T - B 0) 2 P := by ring
    _ = cappedComplexGirsanovCoefficientBound c R T +
          2 * cappedComplexGirsanovCoefficientBound c R T *
            eLpNorm (N T - N 0) 2 P +
          2 * cappedComplexGirsanovBrownianCoefficientBound c R T *
            eLpNorm (B T - B 0) 2 P := by rfl

/-- Adaptedness of the two inputs makes the complex Doléans exponential
adapted. -/
theorem stronglyAdapted_complexDoleansDadeExponential
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {X Q : ℝ≥0 → W → ℂ}
    (hX : StronglyAdapted V X) (hQ : StronglyAdapted V Q) :
    StronglyAdapted V (complexDoleansDadeExponential X Q) := by
  intro t
  change StronglyMeasurable[V t]
    (Complex.exp ∘ (X t - (Q t / fun _ : W ↦ (2 : ℂ))))
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((hX t).sub ((hQ t).div stronglyMeasurable_const))

/-- Under the predictable Girsanov contract, the algebraic complex
Doleans exponential is stochastically continuous.  This formulation keeps
the original adapted totalized drift while borrowing path regularity from
its deterministic-time almost-everywhere continuous representative. -/
theorem GirsanovDensityData.tendstoInMeasure_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (a n)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c) r) := by
  have hMlim : TendstoInMeasure P (fun n => M (a n)) atTop (M r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_martingale_path omega).continuousAt.tendsto.comp ha
  have hBlim : TendstoInMeasure P (fun n => B (a n)) atTop (B r) :=
    StochasticCalculus.IsPreBrownianReal.tendstoInMeasure_eval hB ha
  let combine : ℝ → ℝ → ℂ := fun m b =>
    (m : ℂ) + ((c * b : ℝ) : ℂ) * Complex.I
  have hcombine : Continuous combine.uncurry := by
    dsimp only [combine, Function.uncurry]
    fun_prop
  have hXlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombination M B c (a n)) atTop
      (complexMartingaleCombination M B c r) := by
    change TendstoInMeasure P (fun n omega =>
      combine (M (a n) omega) (B (a n) omega)) atTop
        (fun omega => combine (M r omega) (B r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_martingale (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun n => (hsm (a n)).aestronglyMeasurable)
      hMlim hBlim hcombine
  have hbracketLim : TendstoInMeasure P (fun n => bracket (a n)) atTop
      (bracket r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega =>
        (hdata.continuous_monotone_bracket omega).1.continuousAt.tendsto.comp ha
  have htimeLim : TendstoInMeasure P
      (fun n => fun _ : W => (a n : ℝ)) atTop (fun _ => (r : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun _ => aestronglyMeasurable_const
    · exact Filter.Eventually.of_forall fun _ =>
        (NNReal.continuous_coe.tendsto r).comp ha
  have hdriftLim := hdata.tendstoInMeasure_girsanovIntegratedDrift
    htheta hbracketTerminal hcross hB ha
  have hdriftMeas (n : ℕ) : AEStronglyMeasurable
      (girsanovIntegratedDrift theta T (a n)) P :=
    (((IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      htheta T) (a n)).mono (V.le (a n))).aestronglyMeasurable
  have hClim : TendstoInMeasure P
      (fun n omega => -girsanovIntegratedDrift theta T (a n) omega)
      atTop (fun omega => -girsanovIntegratedDrift theta T r omega) :=
    TendstoInMeasure.continuous_comp hdriftMeas hdriftLim continuous_neg
  let realPart : ℝ → ℝ → ℂ := fun q t =>
    (q : ℂ) - (c ^ 2 * t : ℝ)
  have hrealPart : Continuous realPart.uncurry := by
    dsimp only [realPart, Function.uncurry]
    fun_prop
  have hrealLim : TendstoInMeasure P (fun n omega =>
      realPart (bracket (a n) omega) (a n : ℝ)) atTop
      (fun omega => realPart (bracket r omega) (r : ℝ)) :=
    TendstoInMeasure.continuous_comp₂
      (fun n => ((hdata.adapted_bracket (a n)).mono
        (V.le (a n))).aestronglyMeasurable)
      (fun _ => aestronglyMeasurable_const)
      hbracketLim htimeLim hrealPart
  let addCross : ℂ → ℝ → ℂ := fun q d =>
    q + ((2 * c * d : ℝ) : ℂ) * Complex.I
  have haddCross : Continuous addCross.uncurry := by
    dsimp only [addCross, Function.uncurry]
    fun_prop
  have hQlim : TendstoInMeasure P (fun n =>
      complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c (a n))
      atTop
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r) := by
    change TendstoInMeasure P (fun n omega =>
      addCross (realPart (bracket (a n) omega) (a n : ℝ))
        (-girsanovIntegratedDrift theta T (a n) omega)) atTop
      (fun omega => addCross (realPart (bracket r omega) (r : ℝ))
        (-girsanovIntegratedDrift theta T r omega))
    exact TendstoInMeasure.continuous_comp₂
      (fun n => (((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hdata.adapted_bracket (a n)).mono
          (V.le (a n))).aestronglyMeasurable)).sub
            (Complex.continuous_ofReal.comp_aestronglyMeasurable
              aestronglyMeasurable_const))))
      (fun n => hdriftMeas n |>.neg)
      hrealLim hClim haddCross
  let finish : ℂ → ℂ → ℂ := fun x q => Complex.exp (x - q / 2)
  have hfinish : Continuous finish.uncurry := by
    dsimp only [finish, Function.uncurry]
    fun_prop
  change TendstoInMeasure P (fun n omega =>
    finish (complexMartingaleCombination M B c (a n) omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c
          (a n) omega)) atTop
    (fun omega => finish (complexMartingaleCombination M B c r omega)
      (complexMartingaleCombinationBracket bracket
        (fun t omega => -girsanovIntegratedDrift theta T t omega) c r omega))
  exact TendstoInMeasure.continuous_comp₂
    (fun n => ((stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hBadapt c (a n)).mono
          (V.le (a n))).aestronglyMeasurable)
    (fun n => ((stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket
        (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
          htheta T).neg c (a n)).mono
            (V.le (a n))).aestronglyMeasurable)
    hXlim hQlim hfinish

/-- The algebraic complex exponential stopped at the Girsanov horizon is
integrable.  Its modulus is a bounded deterministic multiple of the stopped
real density. -/
theorem GirsanovDensityData.integrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C)
    (c : ℝ) (t : ℝ≥0) :
    Integrable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P := by
  have hEadapt := stronglyAdapted_complexDoleansDadeExponential
    (stronglyAdapted_complexMartingaleCombination
      hdata.adapted_martingale hB c)
    (stronglyAdapted_complexMartingaleCombinationBracket
      hdata.adapted_bracket hC c)
  have hmeas : AEStronglyMeasurable (fun omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) P :=
    ((hEadapt (min t T)).mono (V.le (min t T))).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  let k : ℝ := Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2)
  have hrhs : Integrable (fun omega =>
      doleansDadeExponential M bracket (min t T) omega * k) P :=
    (hdata.martingale_densityProcess.integrable t).mul_const k
  apply hrhs.congr
  exact Filter.Eventually.of_forall fun omega => by
    change doleansDadeExponential M bracket (min t T) omega * k =
      ‖complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega‖
    simpa only [k] using
      (norm_complexDoleansDadeExponential_combination
        M bracket B C c (min t T) omega).symm

/-- The complete stopped complex-exponential family is uniformly
integrable.  This supplies the Vitali input for passing deterministic-grid
martingale identities to their continuous-time limit. -/
theorem
    GirsanovDensityData.uniformIntegrable_stopAt_complexDoleans_combination
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : StronglyAdapted V B) (hC : StronglyAdapted V C) (c : ℝ) :
    UniformIntegrable (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) 1 P := by
  have hdensityUI : UniformIntegrable (fun t omega =>
      doleansDadeExponential M bracket (min t T) omega) 1 P := by
    have hUI := StochasticCalculus.UniformIntegrable.comp_index
      (StochasticCalculus.Martingale.uniformIntegrable_Iic
        hdata.martingale_densityProcess T)
      (fun t => ⟨min t T, by
        simpa only [Set.mem_Iic] using min_le_right t T⟩)
    simpa only [min_eq_left (min_le_right _ T)] using hUI
  obtain ⟨N, hN⟩ := exists_nat_ge
    (Real.exp (c ^ 2 * (T : ℝ) / 2))
  have hmultiple : UniformIntegrable (fun t omega =>
      N • doleansDadeExponential M bracket (min t T) omega) 1 P :=
    StochasticCalculus.UniformIntegrable.nsmul_banach hdensityUI (by norm_num) N
  apply StochasticCalculus.UniformIntegrable.mono_norm_banach hmultiple
  · intro t
    have hEadapt := stronglyAdapted_complexDoleansDadeExponential
      (stronglyAdapted_complexMartingaleCombination
        hdata.adapted_martingale hB c)
      (stronglyAdapted_complexMartingaleCombinationBracket
        hdata.adapted_bracket hC c)
    exact ((hEadapt (min t T)).mono
      (V.le (min t T))).aestronglyMeasurable
  · intro t omega
    rw [norm_complexDoleansDadeExponential_combination]
    have htime : c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2 ≤
        c ^ 2 * (T : ℝ) / 2 := by
      have htime' : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast min_le_right t T
      nlinarith [sq_nonneg c]
    have hexp : Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
        Real.exp (c ^ 2 * (T : ℝ) / 2) := Real.exp_le_exp.mpr htime
    have hdensityPos :=
      doleansDadeExponential_pos M bracket (min t T) omega
    calc
      doleansDadeExponential M bracket (min t T) omega *
          Real.exp (c ^ 2 * ((min t T : ℝ≥0) : ℝ) / 2) ≤
          doleansDadeExponential M bracket (min t T) omega *
            Real.exp (c ^ 2 * (T : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hexp hdensityPos.le
      _ ≤ doleansDadeExponential M bracket (min t T) omega * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hN hdensityPos.le
      _ = ‖N • doleansDadeExponential M bracket (min t T) omega‖ := by
        rw [nsmul_eq_mul, norm_mul, norm_natCast, Real.norm_eq_abs,
          abs_of_pos hdensityPos]
        ring

/-- Stochastic continuity of the algebraic complex exponential is preserved
when its time parameter is stopped at the deterministic Girsanov horizon. -/
theorem
    GirsanovDensityData.tendstoInMeasure_stopAt_complexDoleans_neg_integratedDrift
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hdata : GirsanovDensityData P V M bracket T)
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hBadapt : StronglyAdapted V B)
    (htheta : IsStronglyPredictable V theta)
    (hbracketTerminal : ∀ omega, bracket T omega =
      ∫ s in Set.Ioc (0 : ℝ≥0) T, (theta s omega) ^ 2
        ∂nonnegativeLebesgueMeasure)
    (hcross : HasCrossVariationProcessInProbability M B
      (fun t omega => -girsanovIntegratedDrift theta T t omega) P)
    (c : ℝ) {r : ℝ≥0} {a : ℕ → ℝ≥0}
    (ha : Tendsto a atTop (nhds r)) :
    TendstoInMeasure P (fun n =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min (a n) T)) atTop
      (complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun t omega => -girsanovIntegratedDrift theta T t omega) c)
        (min r T)) := by
  exact hdata.tendstoInMeasure_complexDoleans_neg_integratedDrift
    hB hsm hBadapt htheta hbracketTerminal hcross c
      (ha.min tendsto_const_nhds)

/-- The genuinely higher-order half of the canonical stochastic-Taylor
obligation.  Its one-cell summands satisfy
`norm_complexDoleansSecondOrderResidual_le`. -/
@[expose] def GirsanovComplexDoleansHigherOrderCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- A scalar-majorant formulation of the higher-order stochastic-Taylor
obligation.  It exposes only the explicit nonnegative cellwise bound. -/
def GirsanovComplexDoleansHigherOrderBoundCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (M bracket B C : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ (c : ℝ) (t : ℝ≥0), TendstoInMeasure P (fun n =>
    complexDoleansHigherOrderResidualBoundApprox
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c)
      T (n + 1) t) atTop (fun _ => 0)

/-- Convergence in measure of the explicit nonnegative majorant closes the
complex higher-order residual. -/
theorem girsanovComplexDoleansHigherOrderCondition_of_bound
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {M bracket B C : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovComplexDoleansHigherOrderBoundCondition
      P M bracket B C T) :
    GirsanovComplexDoleansHigherOrderCondition P M bracket B C T := by
  intro c t
  apply TendstoInMeasure.of_norm_le_nonneg_noMeas (h c t)
  · exact fun n omega =>
      complexDoleansHigherOrderResidualBoundApprox_nonneg
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega
  · exact fun n omega =>
      norm_complexDoleansHigherOrderResidualApprox_le_bound
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        T (n + 1) t omega

/-- The Challenge hypotheses discharge the entire higher-order half of the
complex stochastic-Taylor obligation. -/
theorem GirsanovDensityData.girsanovComplexDoleansHigherOrderBoundCondition
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
        ∂nonnegativeLebesgueMeasure) :
    GirsanovComplexDoleansHigherOrderBoundCondition P M bracket B
      (fun u z => -regularizedGirsanovIntegratedDrift bracket theta T u z) T := by
  intro c t
  exact
    hdata.complexDoleansHigherOrderResidualBoundApprox_tendstoInMeasure_zero
      hB hBmeas htheta hbracketTerminal c t

/-- Paste a complex martingale before a deterministic time to a bounded
past-measurable multiple of another martingale after that time. -/
def martingalePasteMul
    {W : Type*} (X Y : ℝ≥0 → W → ℂ) (H : W → ℂ) (s : ℝ≥0) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  if t ≤ s then X t omega else H omega * Y t omega

/-- Deterministic-time martingale pasting with an integrable measurable
multiplier.  The two pieces only have to agree at the pasting time. -/
theorem martingale_martingalePasteMul_of_integrable
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H)
    (hHYint : ∀ t, Integrable (fun omega ↦ H omega * Y t omega) P)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  have hpasteLeft {t : ℝ≥0} (hts : t ≤ s) :
      martingalePasteMul X Y H s t = X t := by
    funext omega
    simp only [martingalePasteMul, hts, ↓reduceIte]
  have hpasteRight {t : ℝ≥0} (hst : s ≤ t) :
      martingalePasteMul X Y H s t =
        fun omega ↦ H omega * Y t omega := by
    rcases eq_or_lt_of_le hst with rfl | hst'
    · exact (hpasteLeft (le_refl s)).trans hmatch.symm
    · funext omega
      simp only [martingalePasteMul, not_le.mpr hst', ↓reduceIte]
  have hpasteAdapt : StronglyAdapted V
      (martingalePasteMul X Y H s) := by
    intro t
    rcases le_total t s with hts | hst
    · rw [hpasteLeft hts]
      exact hX.stronglyMeasurable t
    · rw [hpasteRight hst]
      exact (hH.mono (V.mono hst)).mul (hY.stronglyMeasurable t)
  refine ⟨hpasteAdapt, fun i j hij ↦ ?_⟩
  rcases le_total j s with hjs | hsj
  · rw [hpasteLeft hjs, hpasteLeft (hij.trans hjs)]
    exact hX.condExp_ae_eq hij
  rcases le_total s i with hsi | his
  · rw [hpasteRight hsi, hpasteRight (hsi.trans hij)]
    have hpull := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      (hH.mono (V.mono hsi)) (hHYint j) (hY.integrable j)
    exact hpull.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
      (hY.condExp_ae_eq hij))
  · have hpullS := condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ)
      hH (hHYint j) (hY.integrable j)
    have hjRight := hpasteRight hsj
    have hsRight := hpasteRight (le_refl s)
    have hcondS : P[martingalePasteMul X Y H s j | V s] =ᵐ[P]
        martingalePasteMul X Y H s s := by
      rw [hjRight, hsRight]
      exact hpullS.trans (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl
        (hY.condExp_ae_eq hsj))
    rw [hpasteLeft (le_refl s)] at hcondS
    have htower := condExp_condExp_of_le (μ := P)
      (V.mono his) (V.le s) (f := martingalePasteMul X Y H s j)
    rw [hpasteLeft his]
    filter_upwards [htower, condExp_congr_ae hcondS,
      hX.condExp_ae_eq his] with omega htowerOmega hcongr hmart
    rw [← htowerOmega, hcongr, hmart]

/-- Bounded deterministic-time multipliers satisfy the integrability
premise of `martingale_martingalePasteMul_of_integrable`. -/
theorem martingale_martingalePasteMul
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {X Y : ℝ≥0 → W → ℂ} {H : W → ℂ} {s : ℝ≥0}
    (hX : Martingale X V P) (hY : Martingale Y V P)
    (hH : StronglyMeasurable[V s] H) (K : ℝ)
    (hHbound : ∀ omega, ‖H omega‖ ≤ K)
    (hmatch : (fun omega ↦ H omega * Y s omega) = X s) :
    Martingale (martingalePasteMul X Y H s) V P := by
  apply martingale_martingalePasteMul_of_integrable hX hY hH _ hmatch
  intro t
  exact (hY.integrable t).bdd_mul
    (hH.mono (V.le s)).aestronglyMeasurable
    (Filter.Eventually.of_forall hHbound)

/-- Fourier-increment form of the stochastic-exponential martingale
identity.  It is the exact stochastic-calculus input needed by the
characteristic-function proof of Girsanov: on each past event, the current
density weighted by the increment character evolves by the deterministic
Gaussian factor. -/
def GirsanovFourierIncrementCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set W}, MeasurableSet[V s] A → ∀ c : ℝ,
    (∫ omega in A,
      doleansDadeExponential M bracket (min t T) omega •
        Complex.exp (((c * (X t omega - X s omega) : ℝ) : ℂ) *
          Complex.I) ∂P) =
      Complex.exp
          (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P

/-- The normalized complex exponential based at time `s`.  Before `s` this
is just the Girsanov density process; after `s` it tests the characteristic
function of the increment of `X`. -/
def girsanovFourierIncrementProcess
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ) (T s : ℝ≥0) (c : ℝ) :
    ℝ≥0 → W → ℂ := fun t omega ↦
  (doleansDadeExponential M bracket (min t T) omega : ℂ) *
    Complex.exp
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I +
        (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ)))

/-- Before its base time, the normalized Fourier-increment process is just
the stopped density process. -/
theorem girsanovFourierIncrementProcess_of_le_base
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hts : t ≤ s) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        (doleansDadeExponential M bracket (min t T) omega : ℂ) := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_left hts, tsub_eq_zero_of_le hts]
  simp only [sub_self, mul_zero, Complex.ofReal_zero, zero_mul,
    NNReal.coe_zero, zero_div, add_zero, Complex.exp_zero, mul_one]

/-- After its base time, a Fourier-increment process is a bounded
past-measurable multiple of the base-zero process. -/
theorem girsanovFourierIncrementProcess_of_base_le
    {W : Type*} (M bracket X : ℝ≥0 → W → ℝ)
    (T s t : ℝ≥0) (c : ℝ) (hst : s ≤ t) :
    girsanovFourierIncrementProcess M bracket X T s c t =
      fun omega ↦
        Complex.exp
            (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
              ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ))) *
          girsanovFourierIncrementProcess M bracket X T 0 c t omega := by
  funext omega
  unfold girsanovFourierIncrementProcess
  rw [min_eq_right hst]
  have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
  rw [hmin0, tsub_zero]
  rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← Complex.exp_add]
  congr 1
  rw [NNReal.coe_sub hst]
  push_cast
  ring_nf

/-- Adaptedness of the density, bracket, and tested process makes every
normalized Fourier-increment process adapted. -/
theorem stronglyAdapted_girsanovFourierIncrementProcess
    {W : Type*} [MeasurableSpace W]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {M bracket X : ℝ≥0 → W → ℝ}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X) (T s : ℝ≥0) (c : ℝ) :
    StronglyAdapted V (girsanovFourierIncrementProcess M bracket X T s c) := by
  intro t
  have hdensity : StronglyMeasurable[V t]
      (doleansDadeExponential M bracket (min t T)) :=
    (stronglyAdapted_doleansDadeExponential hM hbracket (min t T)).mono
      (V.mono (min_le_left _ _))
  have hdensityC : StronglyMeasurable[V t] (fun omega ↦
      (doleansDadeExponential M bracket (min t T) omega : ℂ)) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hdensity
  have hinc : StronglyMeasurable[V t]
      (fun omega ↦ X t omega - X (min t s) omega) :=
    (hX t).sub ((hX (min t s)).mono (V.mono (min_le_left _ _)))
  have hchar : StronglyMeasurable[V t] (fun omega ↦
      (((c * (X t omega - X (min t s) omega) : ℝ) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I
  exact hdensityC.mul (Complex.continuous_exp.comp_stronglyMeasurable
    (hchar.add stronglyMeasurable_const))

/-- Martingale form of the Fourier-increment input. -/
def GirsanovFourierIncrementMartingaleCondition
    {W : Type*} [MeasurableSpace W] (P : Measure W)
    (V : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (M bracket X : ℝ≥0 → W → ℝ) (T : ℝ≥0) : Prop :=
  ∀ s c, Martingale (girsanovFourierIncrementProcess M bracket X T s c) V P

/-- A stopped complex Doléans martingale supplies the base-zero Girsanov
Fourier martingale up to the horizon; after the horizon it is pasted to the
ordinary Brownian Fourier martingale. -/
theorem
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0} (c : ℝ)
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hcomplex : Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : Martingale (brownianFourierIncrementProcess B T c) V P) :
    Martingale (girsanovFourierIncrementProcess M bracket X T 0 c) V P := by
  let E : ℝ≥0 → W → ℂ := complexDoleansDadeExponential
    (complexMartingaleCombination M B c)
    (complexMartingaleCombinationBracket bracket C c)
  let Estop : ℝ≥0 → W → ℂ := fun t omega ↦ E (min t T) omega
  let Y := brownianFourierIncrementProcess B T c
  let H : W → ℂ := E T
  have hEstop : Martingale Estop V P := by
    simpa only [Estop, E] using hcomplex
  have hY : Martingale Y V P := by simpa only [Y] using hBrownian
  have hHmeas : StronglyMeasurable[V T] H := by
    simpa only [H, Estop, min_self] using hEstop.stronglyMeasurable T
  have hHint : Integrable H P := by
    simpa only [H, Estop, min_self] using hEstop.integrable T
  have hHYint (t : ℝ≥0) :
      Integrable (fun omega ↦ H omega * Y t omega) P := by
    apply hHint.mul_bdd
    · exact ((hY.stronglyMeasurable t).mono
        (V.le t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega ↦ by
        rw [show ‖Y t omega‖ =
            Real.exp (((t - min t T : ℝ≥0) : ℝ) * c ^ 2 / 2) by
          exact norm_brownianFourierIncrement B c (min t T) t omega]
  have hmatch : (fun omega ↦ H omega * Y T omega) = Estop T := by
    funext omega
    simp only [H, Y, Estop, min_self, brownianFourierIncrementProcess,
      brownianFourierIncrement_self, mul_one]
  have hpaste : Martingale (martingalePasteMul Estop Y H T) V P :=
    martingale_martingalePasteMul_of_integrable
      hEstop hY hHmeas hHYint hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T 0 c)
  intro t
  filter_upwards [hXzero] with omega hzero
  by_cases htT : t ≤ T
  · have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, Estop,
        min_eq_left htT]
    rw [hpasteEq]
    change complexDoleansDadeExponential
      (complexMartingaleCombination M B c)
      (complexMartingaleCombinationBracket bracket C c) t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold girsanovFourierIncrementProcess
    rw [min_eq_left htT]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_left htT]
    congr 2
    push_cast
    ring
  · have hTt : T ≤ t := le_of_not_ge htT
    have hpasteEq : martingalePasteMul Estop Y H T t omega =
        E T omega * brownianFourierIncrement B c T t omega := by
      simp only [martingalePasteMul, htT, ↓reduceIte, H, Y,
        brownianFourierIncrementProcess, min_eq_right hTt]
    rw [hpasteEq]
    change complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c) T omega *
      brownianFourierIncrement B c T t omega = _
    rw [complexDoleansDadeExponential_combination_factor]
    unfold brownianFourierIncrement girsanovFourierIncrementProcess
    rw [min_eq_right hTt]
    have hmin0 : min t (0 : ℝ≥0) = 0 := min_eq_right bot_le
    rw [hmin0, tsub_zero, hzero, sub_zero, hXeq t omega,
      min_eq_right hTt]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    rw [NNReal.coe_sub hTt]
    push_cast
    ring_nf

/-- It suffices to construct the complex exponential martingale at base
time zero.  Every other base time is obtained by deterministic-time pasting:
the density martingale is used before the base, and a bounded
past-measurable multiple of the base-zero martingale is used afterward. -/
theorem girsanovFourierIncrementMartingaleCondition_of_zero
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hzero : ∀ c, Martingale
      (girsanovFourierIncrementProcess M bracket X T 0 c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  intro s c
  let Z : ℝ≥0 → W → ℂ := fun t omega ↦
    (doleansDadeExponential M bracket (min t T) omega : ℂ)
  let Y := girsanovFourierIncrementProcess M bracket X T 0 c
  let H : W → ℂ := fun omega ↦
    Complex.exp
      (-(((c * (X s omega - X 0 omega) : ℝ) : ℂ) * Complex.I +
        ((c ^ 2 * (s : ℝ) / 2 : ℝ) : ℂ)))
  have hZ : Martingale Z V P := by
    simpa only [Z, Complex.ofRealCLM_apply] using
      Martingale.comp_continuousLinearMap hdensity Complex.ofRealCLM
  have hH : StronglyMeasurable[V s] H := by
    have hinc : StronglyMeasurable[V s] (fun omega ↦
        X s omega - X 0 omega) :=
      (hX s).sub ((hX 0).mono (V.mono bot_le))
    exact Complex.continuous_exp.comp_stronglyMeasurable
      (((Complex.continuous_ofReal.comp_stronglyMeasurable
        (hinc.const_mul c)).mul_const Complex.I).add
          stronglyMeasurable_const).neg
  let K : ℝ := Real.exp (-(c ^ 2 * (s : ℝ) / 2))
  have hHbound (omega : W) : ‖H omega‖ ≤ K := by
    dsimp only [H, K]
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_sub, mul_one, neg_zero, zero_add, le_refl]
  have hmatch : (fun omega ↦ H omega * Y s omega) = Z s := by
    have hright := girsanovFourierIncrementProcess_of_base_le
      M bracket X T s s c (le_refl s)
    have hleft := girsanovFourierIncrementProcess_of_le_base
      M bracket X T s s c (le_refl s)
    exact hright.symm.trans hleft
  have hpaste : Martingale (martingalePasteMul Z Y H s) V P :=
    martingale_martingalePasteMul hZ (hzero c) hH K hHbound hmatch
  apply hpaste.congr
    (stronglyAdapted_girsanovFourierIncrementProcess
      hM hbracket hX T s c)
  intro t
  exact Filter.Eventually.of_forall fun omega ↦ by
    by_cases hts : t ≤ s
    · rw [show martingalePasteMul Z Y H s t omega = Z t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_le_base
        M bracket X T s t c hts).symm omega
    · have hst : s ≤ t := le_of_not_ge hts
      rw [show martingalePasteMul Z Y H s t omega = H omega * Y t omega by
          simp only [martingalePasteMul, hts, ↓reduceIte]]
      exact congrFun (girsanovFourierIncrementProcess_of_base_le
        M bracket X T s t c hst).symm omega

/-- A family of stopped complex Doléans martingales, together with the
ordinary post-horizon Brownian Fourier martingales, yields the full
Girsanov Fourier family. -/
theorem
    girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket B C X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hM : StronglyAdapted V M) (hbracket : StronglyAdapted V bracket)
    (hX : StronglyAdapted V X)
    (hXeq : ∀ t omega, X t omega = B t omega - C (min t T) omega)
    (hXzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hdensity : Martingale (fun t omega ↦
      doleansDadeExponential M bracket (min t T) omega) V P)
    (hcomplex : ∀ c, Martingale (fun t omega ↦
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket C c)
        (min t T) omega) V P)
    (hBrownian : ∀ c,
      Martingale (brownianFourierIncrementProcess B T c) V P) :
    GirsanovFourierIncrementMartingaleCondition P V M bracket X T := by
  apply girsanovFourierIncrementMartingaleCondition_of_zero
    hM hbracket hX hdensity
  intro c
  exact
    martingale_girsanovFourierIncrementProcess_zero_of_complexDoleans_stop
      c hM hbracket hX hXeq hXzero (hcomplex c) (hBrownian c)

/-- The complex exponential martingale family implies the eventwise
Fourier-increment identity used by the Girsanov endpoint. -/
theorem girsanovFourierIncrementCondition_of_martingale
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovFourierIncrementMartingaleCondition P V M bracket X T) :
    GirsanovFourierIncrementCondition P V M bracket X T := by
  intro s t hst A hA c
  let v : ℂ := (((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))
  let char : W → ℂ := fun omega ↦
    (((c * (X t omega - X s omega) : ℝ) : ℂ) * Complex.I)
  have hmartEq := (h s c).setIntegral_eq hst hA
  have hmartEq' :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
      ∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
          Complex.exp (char omega + v) ∂P := by
    simpa only [girsanovFourierIncrementProcess, min_self, sub_self,
      zero_mul, mul_zero, Complex.ofReal_zero, zero_mul, tsub_self, NNReal.coe_zero,
      zero_div, add_zero, Complex.exp_zero, mul_one, min_eq_right hst,
      char, v] using hmartEq
  change (∫ omega in A,
      (doleansDadeExponential M bracket (min t T) omega : ℝ) •
        Complex.exp (char omega) ∂P) =
    Complex.exp (-v) *
      ∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P
  calc
    (∫ omega in A,
        (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) ∂P) =
        ∫ omega in A, Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v)) ∂P := by
      apply setIntegral_congr_fun (V.le s A hA)
      intro omega _
      change (doleansDadeExponential M bracket (min t T) omega : ℝ) •
          Complex.exp (char omega) =
        Complex.exp (-v) *
          ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v))
      rw [Complex.real_smul]
      calc
        (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega) =
            (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              Complex.exp (-v + (char omega + v)) := by
          congr 2
          ring
        _ = (doleansDadeExponential M bracket (min t T) omega : ℂ) *
              (Complex.exp (-v) * Complex.exp (char omega + v)) := by
          rw [Complex.exp_add]
        _ = Complex.exp (-v) *
              ((doleansDadeExponential M bracket (min t T) omega : ℂ) *
                Complex.exp (char omega + v)) := by
          ring
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min t T) omega : ℂ) *
            Complex.exp (char omega + v) ∂P := by
      rw [integral_const_mul]
    _ = Complex.exp (-v) *
        ∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
      rw [hmartEq']

/-- The Fourier-increment stochastic-exponential identity gives the full
pre-Brownian law under the terminal Girsanov measure.  In particular this
route needs neither a separate integrability assumption for the shifted
process nor an all-path continuity representative. -/
theorem GirsanovDensityData.isPreBrownianReal_of_fourierIncrementCondition
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket X : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hadapt : StronglyAdapted V X)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket X T) :
    IsPreBrownianReal X (girsanovMeasure P M bracket T) := by
  let Q := girsanovMeasure P M bracket T
  let : IsProbabilityMeasure Q := h.isProbabilityMeasure
  have hzeroQ : X 0 =ᵐ[Q] fun _ ↦ 0 :=
    h.mutuallyAbsolutelyContinuous.1.ae_eq hzero
  apply isPreBrownianReal_of_map_restrict_increment_eq_of_ae_zero
    hadapt hzeroQ
  intro s t hst A hA
  let inc : W → ℝ := fun omega ↦ X t omega - X s omega
  have hinc : AEMeasurable inc Q := by
    exact ((((hadapt t).mono (V.le t)).aemeasurable).sub
      (((hadapt s).mono (V.le s)).aemeasurable)).mono_ac
        (show Q ≪ P from girsanovMeasure_absolutelyContinuous P M bracket T)
  have hincR : AEMeasurable inc (Q.restrict A) :=
    hinc.mono_measure Measure.restrict_le_self
  let : IsFiniteMeasure (Q A • gaussianReal 0 (t - s)) :=
    (gaussianReal 0 (t - s)).smul_finite (measure_ne_top Q A)
  apply Measure.ext_of_charFun
  funext c
  rw [charFun_apply_real]
  change (∫ x, Complex.exp ((c : ℂ) * (x : ℂ) * Complex.I)
    ∂((Q.restrict A).map inc)) = _
  rw [integral_map hincR (by fun_prop)]
  let f : W → ℂ := fun omega ↦
    Complex.exp ((c : ℂ) * (inc omega : ℂ) * Complex.I)
  have hf : StronglyMeasurable[V t] f := by
    have hincStrong : StronglyMeasurable[V t] inc :=
      (hadapt t).sub ((hadapt s).mono (V.mono hst))
    apply Complex.continuous_exp.comp_stronglyMeasurable
    simpa only [Complex.ofReal_mul] using
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        (hincStrong.const_mul c)).mul_const Complex.I
  have hfint : Integrable f Q :=
    (integrable_const (1 : ℝ)).mono
      ((hf.mono (V.le t)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [f, ← Complex.ofReal_mul,
          Complex.norm_exp_ofReal_mul_I, norm_one] using (le_refl (1 : ℝ)))
  have hAt : MeasurableSet[V t] A := V.mono hst A hA
  have hcurrent :=
    h.setIntegral_girsanovMeasure_eq_densityProcess_smul hf hfint hAt
  have hmass :
      (∫ omega in A,
        (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
        (Q A).toReal := by
    have honeMeas : StronglyMeasurable[V s] (fun _ : W ↦ (1 : ℂ)) := by
      fun_prop
    have honeInt : Integrable (fun _ : W ↦ (1 : ℂ)) Q :=
      integrable_const 1
    have hone := h.setIntegral_girsanovMeasure_eq_densityProcess_smul
      honeMeas honeInt hA
    calc
      (∫ omega in A,
          (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P) =
          ∫ omega in A,
            doleansDadeExponential M bracket (min s T) omega • (1 : ℂ) ∂P := by
        apply setIntegral_congr_fun (V.le s A hA)
        intro omega _
        simp only [Complex.real_smul, mul_one]
      _ = ∫ _omega in A, (1 : ℂ) ∂Q := hone.symm
      _ = (Q A).toReal := by
        rw [setIntegral_const]
        simp only [measureReal_def, Complex.real_smul, mul_one]
  have hfourier' :
      (∫ omega in A,
        doleansDadeExponential M bracket (min t T) omega • f omega ∂P) =
        Complex.exp
            (-(((((t - s : ℝ≥0) : ℝ) * c ^ 2 / 2 : ℝ) : ℂ))) *
          ∫ omega in A,
            (doleansDadeExponential M bracket (min s T) omega : ℂ) ∂P := by
    simpa only [f, inc, Complex.ofReal_mul] using hfourier hst hA c
  change (∫ omega in A, f omega ∂Q) =
    charFun (Q A • gaussianReal 0 (t - s)) c
  have hcharSmul : charFun (Q A • gaussianReal 0 (t - s)) c =
      (Q A).toReal • charFun (gaussianReal 0 (t - s)) c := by
    simp only [charFun_apply_real]
    rw [integral_smul_measure]
  rw [hcurrent, hfourier', hmass, hcharSmul, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
    Complex.real_smul]
  rw [mul_comm]
  congr 1
  push_cast
  ring

/-- Predictable-drift specialization of the Fourier Girsanov endpoint.
Predictability supplies shifted-process adaptedness, while almost-sure
normalization of the driver suffices at time zero. -/
theorem GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hfourier : GirsanovFourierIncrementCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  have hshiftAdapt : StronglyAdapted V
      (girsanovShiftedBrownian B theta T) :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt htheta
  have hshiftZero : girsanovShiftedBrownian B theta T 0 =ᵐ[P]
      fun _ ↦ 0 := by
    filter_upwards [hBzero] with omega homega
    simp only [girsanovShiftedBrownian, homega, girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  exact h.isPreBrownianReal_of_fourierIncrementCondition
    hshiftAdapt hshiftZero hfourier

/-- Raw-natural-filtration version of the Fourier endpoint.  The density
data and predictable drift are transported internally to the right
continuation, avoiding a right-continuity assumption on the natural
filtration supplied by the caller. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hfourier : GirsanovFourierIncrementCondition P
      (Filtration.rightCont (Filtration.natural B hsm)) M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  have hdata : GirsanovDensityData P (Filtration.rightCont V) M bracket T :=
    h.rightCont
  apply hdata.isPreBrownianReal_girsanovShiftedBrownian_of_fourier
  · exact StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  · exact hB.eval_zero_ae_eq_zero
  · exact StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  · exact hfourier

/-- Predictable-drift specialization with the Fourier input presented as a
family of complex martingales. -/
theorem
    GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_fourierMartingale
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    [V.IsRightContinuous]
    {M bracket B theta : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (h : GirsanovDensityData P V M bracket T)
    (hBadapt : StronglyAdapted V B)
    (hBzero : B 0 =ᵐ[P] fun _ ↦ 0)
    (htheta : IsStronglyPredictable V theta)
    (hmart : GirsanovFourierIncrementMartingaleCondition P V M bracket
      (girsanovShiftedBrownian B theta T) T) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) :=
  h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier hBadapt hBzero htheta
    (girsanovFourierIncrementCondition_of_martingale hmart)

set_option linter.style.longLine false in
/-- Raw-natural-filtration endpoint from true martingality of the stopped
algebraic complex Doléans family.  This is the common final assembly for
both local-martingale and deterministic-grid constructions. -/
theorem
GirsanovDensityData.isPreBrownianReal_girsanovShiftedBrownian_of_complexDoleans_stop_rightCont_natural
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    [IsProbabilityMeasure P] [IsFiniteMeasure P]
    {B theta M bracket : ℝ≥0 → W → ℝ} {T : ℝ≥0}
    (hsm : ∀ t, StronglyMeasurable (B t))
    (h : GirsanovDensityData P (Filtration.natural B hsm) M bracket T)
    (hB : IsPreBrownianReal B P)
    (htheta : IsStronglyPredictable (Filtration.natural B hsm) theta)
    (hcomplex : ∀ c, Martingale (fun t omega =>
      complexDoleansDadeExponential
        (complexMartingaleCombination M B c)
        (complexMartingaleCombinationBracket bracket
          (fun u omega => -girsanovIntegratedDrift theta T u omega) c)
        (min t T) omega)
      (Filtration.rightCont (Filtration.natural B hsm)) P) :
    IsPreBrownianReal (girsanovShiftedBrownian B theta T)
      (girsanovMeasure P M bracket T) := by
  let V := Filtration.natural B hsm
  let C : ℝ≥0 → W → ℝ := fun t omega =>
    -girsanovIntegratedDrift theta T t omega
  let X := girsanovShiftedBrownian B theta T
  have hdataR : GirsanovDensityData P (Filtration.rightCont V)
      M bracket T := h.rightCont
  have hBadapt : StronglyAdapted (Filtration.rightCont V) B :=
    StochasticCalculus.StronglyAdapted.mono_filtration
      (Filtration.stronglyAdapted_natural hsm) V.le_rightCont
  have hthetaR : IsStronglyPredictable (Filtration.rightCont V) theta :=
    StochasticCalculus.IsStronglyPredictable.mono_filtration htheta V.le_rightCont
  have hC : StronglyAdapted (Filtration.rightCont V) C :=
    (IsStronglyPredictable.stronglyAdapted_girsanovIntegratedDrift
      hthetaR T).neg
  have hX : StronglyAdapted (Filtration.rightCont V) X :=
    stronglyAdapted_girsanovShiftedBrownian hBadapt hthetaR
  have hXeq (t : ℝ≥0) (omega : W) :
      X t omega = B t omega - C (min t T) omega := by
    change B t omega + girsanovIntegratedDrift theta T t omega =
      B t omega - -girsanovIntegratedDrift theta T (min t T) omega
    rw [sub_neg_eq_add]
    congr 1
    unfold girsanovIntegratedDrift
    rw [min_eq_left (min_le_right t T)]
  have hXzero : X 0 =ᵐ[P] fun _ => 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with omega homega
    simp only [X, girsanovShiftedBrownian, homega,
      girsanovIntegratedDrift]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ T by exact bot_le)]
    simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
      add_zero]
  have hmart : GirsanovFourierIncrementMartingaleCondition P
      (Filtration.rightCont V) M bracket X T := by
    apply girsanovFourierIncrementMartingaleCondition_of_complexDoleans_stop
      hdataR.adapted_martingale hdataR.adapted_bracket hX hXeq hXzero
      hdataR.martingale_densityProcess
    · simpa only [C, V] using hcomplex
    · intro c
      exact martingale_brownianFourierIncrementProcess_rightCont_natural
        hB hsm T c
  apply
    h.isPreBrownianReal_girsanovShiftedBrownian_of_fourier_rightCont_natural
      hsm hB htheta
  exact girsanovFourierIncrementCondition_of_martingale hmart

section PredictableIntegral

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- A continuous modification of the natural Itô integral has the same
completed-cell quadratic variation as the selected representative.  This is
the representative bridge needed before applying the process-level Novikov
theorem. -/
theorem IsContinuousProcessModification.hasQuadraticVariationBeforeStop_naturalIto
    (hB : IsBrownianMotion B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    {M : ℝ≥0 → W → ℝ}
    (hmod : IsContinuousProcessModification
      (naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U) M P) :
    HasQuadraticVariationBeforeStopProcessInProbability M
      (predictableQuadraticVariation hsm U) P := by
  let N : ℝ≥0 → W → ℝ :=
    naturalItoProcessRepresentative hB.toIsPreBrownianReal hsm rfl U
  intro t a
  have hNM (b : ℝ≥0) (n : ℕ) :
      quadraticVariationBeforeStopApprox N t (n + 1) b =ᵐ[P]
        quadraticVariationBeforeStopApprox M t (n + 1) b := by
    have hgrid := fixedTime_ae_eq_uniformPartitions hmod.fixedTime_ae_eq t
    filter_upwards [hgrid] with omega homega
    unfold quadraticVariationBeforeStopApprox
    apply Finset.sum_congr rfl
    intro i hi
    simp only [N]
    rw [homega n (i + 1), homega n i]
  by_cases ha : a ≤ t
  · exact (quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t a ha).congr_left (hNM a)
  · have hN := quadraticVariationBeforeStop_naturalItoProcess_tendstoInMeasure
      hB hsm U t t (le_refl t)
    have hsource (n : ℕ) :
        quadraticVariationBeforeStopApprox N t (n + 1) t =ᵐ[P]
          quadraticVariationBeforeStopApprox M t (n + 1) a := by
      filter_upwards [hNM t n] with omega hEq
      calc
        quadraticVariationBeforeStopApprox N t (n + 1) t omega =
            quadraticVariationBeforeStopApprox M t (n + 1) t omega := hEq
        _ = quadraticVariationBeforeStopApprox M t (n + 1) a omega := by
          have hmin := quadraticVariationBeforeStopApprox_min_horizon
            M t a (n + 1) omega
          rw [min_eq_left (le_of_not_ge ha)] at hmin
          exact hmin.symm
    simpa only [min_self, min_eq_left (le_of_not_ge ha)] using
      hN.congr_left hsource

end PredictableIntegral

end StochasticCalculus
