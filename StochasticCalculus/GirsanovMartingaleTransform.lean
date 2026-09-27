/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.GirsanovMeasure

/-!
# Elementary martingale transforms

Banach-valued stochastic integrals of elementary and uniformly adapted
coefficients against a real martingale, their martingale property, and the
prefix and stopped forms of the cross-variation sums along common
refinements of uniform partitions.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace StochasticCalculus

/-- The elementary stochastic integral of an `E`-valued coefficient against
a real martingale on `(a,b]`.  This is the Banach-valued transform needed for
complex Fourier martingales. -/
def elementaryMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (a b : ℝ≥0) (Z : W → E)
    (t : ℝ≥0) (omega : W) : E :=
  (M (min t b) omega - M (min t a) omega) • Z omega

/-- An integrable elementary predictable transform is a martingale. The
coefficient may be unbounded. -/
theorem martingale_elementaryMartingaleSmulProcess_of_integrable
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (hInt : ∀ t, Integrable (elementaryMartingaleSmulProcess M a b Z t) P) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  have hadapt : StronglyAdapted V
      (elementaryMartingaleSmulProcess M a b Z) := by
    intro t
    rcases le_total t a with hta | hat
    · have hzero : elementaryMartingaleSmulProcess M a b Z t = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hta,
          min_eq_left (hta.trans hab)]
      rw [hzero]
      exact stronglyMeasurable_zero
    · exact ((hM.stronglyMeasurable (min t b)).mono
          (V.mono (min_le_left _ _)) |>.sub
        ((hM.stronglyMeasurable (min t a)).mono
          (V.mono (min_le_left _ _)))).smul
        (hZ.mono (V.mono hat))
  refine ⟨hadapt, ?_⟩
  intro s t hst
  rcases le_total t a with hta | hat
  · have hIt : elementaryMartingaleSmulProcess M a b Z t = 0 := by
      funext omega
      simp [elementaryMartingaleSmulProcess, min_eq_left hta,
        min_eq_left (hta.trans hab)]
    have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
      funext omega
      have hsa : s ≤ a := hst.trans hta
      simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
        min_eq_left (hsa.trans hab)]
    rw [hIt, hIs, condExp_zero]
  · rcases le_total s a with hsa | has
    · have hIs : elementaryMartingaleSmulProcess M a b Z s = 0 := by
        funext omega
        simp [elementaryMartingaleSmulProcess, min_eq_left hsa,
          min_eq_left (hsa.trans hab)]
      rw [hIs]
      let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
      have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
        funext omega
        simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
          Pi.smul_apply']
      have hdInt : Integrable d P :=
        (hM.integrable (min t b)).sub (hM.integrable a)
      have hprod : Integrable (d • Z) P := by
        rw [← hprocess]
        exact hInt t
      have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
        hZ.aestronglyMeasurable
      have hdelta := condExp_sub (hM.integrable (min t b))
        (hM.integrable a) (V a)
      have hamin : a ≤ min t b := le_min hat hab
      have hda : P[d | V a] =ᵐ[P] 0 := by
        filter_upwards [hdelta, hM.condExp_ae_eq hamin,
          Filter.Eventually.of_forall (congrFun
            (condExp_of_stronglyMeasurable (V.le a)
              (hM.stronglyMeasurable a) (hM.integrable a)))]
            with omega hd hfuture hpast
        change P[d | V a] omega = 0
        rw [show P[d | V a] omega =
          (P[M (min t b) | V a] - P[M a | V a]) omega by exact hd]
        simp only [Pi.sub_apply, hfuture, hpast, sub_self]
      have hIa : P[d • Z | V a] =ᵐ[P] 0 := by
        filter_upwards [hpull, hda] with omega hp hd
        simpa only [Pi.smul_apply', Pi.zero_apply, hd, zero_smul] using hp
      have htower := condExp_condExp_of_le (μ := P)
        (V.mono hsa) (V.le a) (f := d • Z)
      have hzeroCond : P[d • Z | V s] =ᵐ[P] 0 := by
        filter_upwards [htower, condExp_congr_ae hIa,
          Filter.Eventually.of_forall (congrFun
            (condExp_zero (μ := P) (m := V s) (E := E)))]
            with omega htow hcongr hzero
        rw [← htow, hcongr, hzero]
      rw [hprocess]
      exact hzeroCond
    · rcases le_total b s with hbs | hsb
      · have hconst : elementaryMartingaleSmulProcess M a b Z t =
            elementaryMartingaleSmulProcess M a b Z s := by
          funext omega
          simp [elementaryMartingaleSmulProcess,
            min_eq_right (hbs.trans hst), min_eq_right hbs,
            min_eq_right (has.trans hst), min_eq_right has]
        rw [hconst]
        exact Filter.Eventually.of_forall (congrFun
          (condExp_of_stronglyMeasurable (V.le s) (hadapt s) (hInt s)))
      · let d : W → ℝ := fun omega ↦ M (min t b) omega - M a omega
        have hprocess : elementaryMartingaleSmulProcess M a b Z t = d • Z := by
          funext omega
          simp only [elementaryMartingaleSmulProcess, min_eq_right hat, d,
            Pi.smul_apply']
        have hdInt : Integrable d P :=
          (hM.integrable (min t b)).sub (hM.integrable a)
        have hprod : Integrable (d • Z) P := by
          rw [← hprocess]
          exact hInt t
        have hpull := condExp_smul_of_aestronglyMeasurable_right hdInt hprod
          (hZ.mono (V.mono has)).aestronglyMeasurable
        have hdelta := condExp_sub (hM.integrable (min t b))
          (hM.integrable a) (V s)
        have hsmin : s ≤ min t b := le_min hst hsb
        have hpast := condExp_of_stronglyMeasurable (V.le s)
          ((hM.stronglyMeasurable a).mono (V.mono has)) (hM.integrable a)
        filter_upwards [hpull, hdelta, hM.condExp_ae_eq hsmin,
          Filter.Eventually.of_forall (congrFun hpast)]
            with omega hp hd hfuture hpast'
        have hd' : P[d | V s] omega =
            (P[M (min t b) | V s] - P[M a | V s]) omega := hd
        rw [hprocess, hp]
        change P[d | V s] omega • Z omega = _
        rw [hd', Pi.sub_apply, hfuture, hpast']
        simp only [elementaryMartingaleSmulProcess, min_eq_right has,
          min_eq_left hsb]

/-- A bounded Banach-valued coefficient known at the left endpoint defines a
martingale transform against any real martingale. -/
theorem martingale_elementaryMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ}
    (hM : Martingale M V P) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → E} (hZ : StronglyMeasurable[V a] Z)
    (C : ℝ) (hZbound : ∀ omega, ‖Z omega‖ ≤ C) :
    Martingale (elementaryMartingaleSmulProcess M a b Z) V P := by
  apply martingale_elementaryMartingaleSmulProcess_of_integrable hM hab hZ
  intro t
  let d : W → ℝ := fun omega ↦
    M (min t b) omega - M (min t a) omega
  have hd : Integrable d P :=
    (hM.integrable (min t b)).sub (hM.integrable (min t a))
  have hmeas : AEStronglyMeasurable
      (elementaryMartingaleSmulProcess M a b Z t) P := by
    exact hd.aestronglyMeasurable.smul
      (hZ.mono (V.le a)).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).1
  apply (hd.norm.const_mul |C|).mono' hmeas.norm
  filter_upwards with omega
  simp only [elementaryMartingaleSmulProcess, d, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_abs]
  have h := mul_le_mul_of_nonneg_left
    ((hZbound omega).trans (le_abs_self C))
    (abs_nonneg (M (min t b) omega - M (min t a) omega))
  simpa only [abs_of_nonneg (norm_nonneg _), mul_comm] using h

/-- A finite sum of Banach-valued elementary transforms against one real
integrator. -/
def elementaryMartingaleSmulSum
    {W E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (S : Finset I)
    (a b : I → ℝ≥0) (Z : I → W → E) : ℝ≥0 → W → E :=
  ∑ i ∈ S, elementaryMartingaleSmulProcess M (a i) (b i) (Z i)

/-- Finite sums of bounded predictable Banach-valued transforms are
martingales. -/
theorem martingale_elementaryMartingaleSmulSum
    {W E I : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} (hM : Martingale M V P)
    (S : Finset I) {a b : I → ℝ≥0} (hab : ∀ i ∈ S, a i ≤ b i)
    {Z : I → W → E}
    (hZ : ∀ i ∈ S, StronglyMeasurable[V (a i)] (Z i))
    (C : I → ℝ) (hZbound : ∀ i ∈ S, ∀ omega, ‖Z i omega‖ ≤ C i) :
    Martingale (elementaryMartingaleSmulSum M S a b Z) V P := by
  classical
  unfold elementaryMartingaleSmulSum
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using martingale_zero E V P
  | @insert i S hi ih =>
      have hhead : Martingale
          (elementaryMartingaleSmulProcess M (a i) (b i) (Z i)) V P :=
        martingale_elementaryMartingaleSmulProcess (E := E) hM
          (hab i (Finset.mem_insert_self i S))
          (hZ i (Finset.mem_insert_self i S)) (C i)
          (hZbound i (Finset.mem_insert_self i S))
      have htail : Martingale
          (∑ j ∈ S, elementaryMartingaleSmulProcess M (a j) (b j) (Z j))
          V P :=
        ih (fun j hj ↦ hab j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hZbound j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using hhead.add htail

/-- The coherent uniform-grid Banach-valued transform of a time-dependent
adapted coefficient against a real martingale. -/
def uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  elementaryMartingaleSmulSum M (Finset.range n)
    (fun i ↦ uniformPartitionTime T n i)
    (fun i ↦ uniformPartitionTime T n (i + 1))
    (fun i ↦ H (uniformPartitionTime T n i))

/-- Uniform-grid transforms of a bounded adapted Banach-valued coefficient
against a real martingale are martingales. -/
theorem martingale_uniformAdaptedMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hH : StronglyAdapted V H)
    (K : ℝ) (hHK : ∀ t omega, ‖H t omega‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (uniformAdaptedMartingaleSmulProcess M H T n) V P := by
  apply martingale_elementaryMartingaleSmulSum hM (Finset.range n)
    (fun i hi ↦ monotone_uniformPartitionTime_general T n (Nat.le_succ i))
    (fun i hi ↦ hH (uniformPartitionTime T n i))
    (fun _ ↦ K) (fun i hi omega ↦ hHK _ _)

/-- The sum of two coherent Banach-valued left transforms, allowing two
different real martingale integrators and two adapted coefficients. -/
def uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : ℝ≥0 → W → ℝ) (H K : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) : ℝ≥0 → W → E :=
  uniformAdaptedMartingaleSmulProcess M H T n +
    uniformAdaptedMartingaleSmulProcess N K T n

/-- Bounded adapted coefficients against two real martingales give a
Banach-valued martingale on every deterministic grid. -/
theorem martingale_uniformAdaptedTwoMartingaleSmulProcess
    {W E : Type*} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → E}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (T : ℝ≥0) (n : ℕ) :
    Martingale
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T n) V P := by
  exact (martingale_uniformAdaptedMartingaleSmulProcess
    hM hH CH hHbound T n).add
      (martingale_uniformAdaptedMartingaleSmulProcess
        hN hK CK hKbound T n)

/-- At the terminal horizon, the coherent Banach-valued transform is the
usual uniform-partition left sum. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T omega =
      ∑ i ∈ Finset.range (n + 1),
        (M (uniformPartitionTime T (n + 1) (i + 1)) omega -
          M (uniformPartitionTime T (n + 1) i) omega) •
            H (uniformPartitionTime T (n + 1) i) omega := by
  simp only [uniformAdaptedMartingaleSmulProcess,
    elementaryMartingaleSmulSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  simp only [elementaryMartingaleSmulProcess,
    min_eq_right hright.2, min_eq_right hleft.2]

/-- For real coefficients, the Banach-valued scalar-action construction is
the existing real left-sum process at the terminal horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum
    {W : Type*} (M H : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T =
      uniformAdaptedMartingaleLeftSumProcess M H T (n + 1) T := by
  funext omega
  rw [uniformAdaptedMartingaleSmulProcess_terminal,
    uniformAdaptedMartingaleLeftSumProcess_terminal]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [smul_eq_mul, mul_comm]

/-- Taking real parts commutes with the coherent uniform-grid transform. -/
theorem uniformAdaptedMartingaleSmulProcess_re
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).re) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).re) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.reCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.reCLM_apply]

/-- Taking imaginary parts commutes with the coherent uniform-grid
transform. -/
theorem uniformAdaptedMartingaleSmulProcess_im
    {W : Type*} (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → ℂ)
    (T : ℝ≥0) (n : ℕ) :
    (fun t omega =>
      (uniformAdaptedMartingaleSmulProcess M H T n t omega).im) =
      uniformAdaptedMartingaleSmulProcess M
        (fun t omega => (H t omega).im) T n := by
  funext t omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply, elementaryMartingaleSmulProcess]
  change Complex.imCLM (∑ c ∈ Finset.range n, _) = _
  rw [map_sum]
  simp only [map_smul, Complex.imCLM_apply]

/-- A bounded complex coefficient has a grid-independent terminal `L²`
transform bound.  Splitting into real and imaginary parts loses only the
harmless factor two and reuses the real martingale-transform isometry. -/
theorem
    eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M : ℝ≥0 → W → ℝ} {H : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (T : ℝ≥0) (hMT : MemLp (M T) 2 P)
    (hH : StronglyAdapted V H) (K : ℝ≥0)
    (hHK : ∀ t omega, ‖H t omega‖ ≤ K) (n : ℕ) :
    eLpNorm
      (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P ≤
      2 * K * eLpNorm (M T - M 0) 2 P := by
  let F : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let Fre : W → ℝ := fun omega => (F omega).re
  let Fim : W → ℝ := fun omega => (F omega).im
  have hHre : StronglyAdapted V (fun t omega => (H t omega).re) :=
    fun t => Complex.continuous_re.comp_stronglyMeasurable (hH t)
  have hHim : StronglyAdapted V (fun t omega => (H t omega).im) :=
    fun t => Complex.continuous_im.comp_stronglyMeasurable (hH t)
  have hHreBound (t : ℝ≥0) (omega : W) : ‖(H t omega).re‖ ≤ K :=
    (Complex.abs_re_le_norm (H t omega)).trans (hHK t omega)
  have hHimBound (t : ℝ≥0) (omega : W) : ‖(H t omega).im‖ ≤ K :=
    (Complex.abs_im_le_norm (H t omega)).trans (hHK t omega)
  have hRe :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHre K hHreBound n
  have hIm :=
    eLpNorm_uniformAdaptedMartingaleLeftSumProcess_terminal_le_of_memLp_terminal
      hM T hMT hHim K hHimBound n
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hRe
  rw [← uniformAdaptedMartingaleSmulProcess_terminal_eq_leftSum] at hIm
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_re M H T (n + 1)) T]
    at hRe
  rw [← congrFun (uniformAdaptedMartingaleSmulProcess_im M H T (n + 1)) T]
    at hIm
  have hFmeas : AEStronglyMeasurable F P :=
    ((martingale_uniformAdaptedMartingaleSmulProcess
      hM hH K hHK T (n + 1)).integrable T).1
  have hRemeas : AEStronglyMeasurable Fre P :=
    Complex.continuous_re.comp_aestronglyMeasurable hFmeas
  have hImmeas : AEStronglyMeasurable Fim P :=
    Complex.continuous_im.comp_aestronglyMeasurable hFmeas
  have hcastRe : AEStronglyMeasurable (fun omega => (Fre omega : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hRemeas
  have hcastIm : AEStronglyMeasurable
      (fun omega => (Fim omega : ℂ) * Complex.I) P :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hImmeas).mul_const _
  have hdecomp : F = fun omega =>
      (Fre omega : ℂ) + (Fim omega : ℂ) * Complex.I := by
    funext omega
    apply Complex.ext
    · simp [Fre, Fim]
    · rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im,
        Complex.ofReal_re, zero_add]
  calc
    eLpNorm
        (uniformAdaptedMartingaleSmulProcess M H T (n + 1) T) 2 P =
        eLpNorm F 2 P := by rfl
    _ = eLpNorm
        ((fun omega => (Fre omega : ℂ)) +
          fun omega => (Fim omega : ℂ) * Complex.I) 2 P := by
      rw [hdecomp]
      rfl
    _ ≤ eLpNorm (fun omega => (Fre omega : ℂ)) 2 P +
          eLpNorm (fun omega => (Fim omega : ℂ) * Complex.I) 2 P :=
      eLpNorm_add_le (by norm_num)
    _ = eLpNorm Fre 2 P + eLpNorm Fim 2 P := by
      congr 1
      · apply eLpNorm_congr_norm_ae hcastRe hRemeas
        filter_upwards with omega
        exact Complex.norm_real (Fre omega)
      · apply eLpNorm_congr_norm_ae hcastIm hImmeas
        filter_upwards with omega
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    _ ≤ K * eLpNorm (M T - M 0) 2 P +
          K * eLpNorm (M T - M 0) 2 P := add_le_add hRe hIm
    _ = 2 * K * eLpNorm (M T - M 0) 2 P := by ring

/-- A coherent uniform-grid transform is constant after its deterministic
horizon. -/
theorem uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le
    {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ≥0 → W → ℝ) (H : ℝ≥0 → W → E)
    (T t : ℝ≥0) (n : ℕ) (ht : T ≤ t) :
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) t =
      uniformAdaptedMartingaleSmulProcess M H T (n + 1) T := by
  funext omega
  unfold uniformAdaptedMartingaleSmulProcess elementaryMartingaleSmulSum
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  unfold elementaryMartingaleSmulProcess
  have hi1 : i + 1 ≤ n + 1 := Finset.mem_range.mp hi
  have hi0 : i ≤ n + 1 := (Nat.le_succ i).trans hi1
  have hleft := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi0
  have hright := uniformPartitionTime_mem_Icc_of_le T
    (Nat.zero_lt_succ n) hi1
  rw [min_eq_right (hright.2.trans ht), min_eq_right (hleft.2.trans ht),
    min_eq_right hright.2, min_eq_right hleft.2]

/-- Two complex martingale transforms admit the sum of their terminal
grid-independent `L²` bounds. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK) (n : ℕ) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  let A : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess M H T (n + 1) T
  let D : W → ℂ :=
    uniformAdaptedMartingaleSmulProcess N K T (n + 1) T
  calc
    eLpNorm
        (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T)
          2 P = eLpNorm (A + D) 2 P := by rfl
    _ ≤ eLpNorm A 2 P + eLpNorm D 2 P :=
      eLpNorm_add_le (by norm_num)
    _ ≤ 2 * CH * eLpNorm (M T - M 0) 2 P +
          2 * CK * eLpNorm (N T - N 0) 2 P := by
      exact add_le_add
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hM T hMT hH CH hHbound n)
        (eLpNorm_uniformAdaptedMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
          hN T hNT hK CK hKbound n)

/-- The two-transform `L²` bound holds at every observation time because
the transform is a martingale before the grid horizon and constant after it. -/
theorem
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_le_of_memLp_terminal
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {V : Filtration ℝ≥0 ‹MeasurableSpace W›} [SigmaFiniteFiltration P V]
    {M N : ℝ≥0 → W → ℝ} {H K : ℝ≥0 → W → ℂ}
    (hM : Martingale M V P) (hN : Martingale N V P)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hH : StronglyAdapted V H) (hK : StronglyAdapted V K)
    (CH CK : ℝ≥0) (hHbound : ∀ t omega, ‖H t omega‖ ≤ CH)
    (hKbound : ∀ t omega, ‖K t omega‖ ≤ CK)
    (n : ℕ) (t : ℝ≥0) :
    eLpNorm
      (uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t) 2 P ≤
      2 * CH * eLpNorm (M T - M 0) 2 P +
        2 * CK * eLpNorm (N T - N 0) 2 P := by
  have hterminal :=
    eLpNorm_uniformAdaptedTwoMartingaleSmulProcess_complex_terminal_le_of_memLp_terminal
      hM hN T hMT hNT hH hK CH CK hHbound hKbound n
  rcases le_total t T with ht | ht
  · exact (martingale_eLpNorm_le_of_le
      (martingale_uniformAdaptedTwoMartingaleSmulProcess
        hM hN hH hK CH CK hHbound hKbound T (n + 1))
      ht (by norm_num)).trans hterminal
  · have heq :
        uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) t =
          uniformAdaptedTwoMartingaleSmulProcess M N H K T (n + 1) T := by
      unfold uniformAdaptedTwoMartingaleSmulProcess
      simp only [Pi.add_apply]
      rw [uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le M H T t n ht,
        uniformAdaptedMartingaleSmulProcess_eq_terminal_of_le N K T t n ht]
    rw [heq]
    exact hterminal

/-- Covariation sum on a fixed uniform grid, with every grid endpoint
stopped at the current time.  Unlike a separately repartitioned sum at each
time, this gives a coherent process for martingale approximation. -/
def uniformStoppedCovariationApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range n,
    (X (min t (uniformPartitionTime T n (i + 1))) omega -
      X (min t (uniformPartitionTime T n i)) omega) *
    (Y (min t (uniformPartitionTime T n (i + 1))) omega -
      Y (min t (uniformPartitionTime T n i)) omega)

/-- Covariation carried by the first `k` cells of one uniform grid. -/
def quadraticCovariationPrefixApprox
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (omega : W) : ℝ :=
  ∑ i ∈ Finset.range k,
    (X (uniformPartitionTime T n (i + 1)) omega -
      X (uniformPartitionTime T n i) omega) *
    (Y (uniformPartitionTime T n (i + 1)) omega -
      Y (uniformPartitionTime T n i) omega)

@[simp]
theorem quadraticCovariationPrefixApprox_zero
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n 0 omega = 0 := by
  simp [quadraticCovariationPrefixApprox]

/-- Fixed-time measurability of both processes makes every covariation
prefix measurable. -/
theorem aestronglyMeasurable_quadraticCovariationPrefixApprox
    {W : Type*} [MeasurableSpace W] {P : Measure W}
    {X Y : ℝ≥0 → W → ℝ}
    (hXmeas : ∀ s, AEStronglyMeasurable (X s) P)
    (hYmeas : ∀ s, AEStronglyMeasurable (Y s) P)
    (T : ℝ≥0) (n k : ℕ) :
    AEStronglyMeasurable (quadraticCovariationPrefixApprox X Y T n k) P := by
  unfold quadraticCovariationPrefixApprox
  have hs := Finset.aestronglyMeasurable_sum (Finset.range k)
    (fun i _hi ↦ ((hXmeas (uniformPartitionTime T n (i + 1))).sub
      (hXmeas (uniformPartitionTime T n i))).mul
      ((hYmeas (uniformPartitionTime T n (i + 1))).sub
        (hYmeas (uniformPartitionTime T n i))))
  convert hs using 1
  funext omega
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]

@[simp]
theorem quadraticCovariationPrefixApprox_full
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n : ℕ) (omega : W) :
    quadraticCovariationPrefixApprox X Y T n n omega =
      quadraticCovariationApprox X Y T n omega := by
  rfl

/-- Stopping a coherent covariation sum exactly at its `k`-th grid point
turns it into the corresponding prefix sum. -/
theorem uniformStoppedCovariationApprox_uniformPartitionTime
    {W : Type*} (X Y : ℝ≥0 → W → ℝ)
    (T : ℝ≥0) (n k : ℕ) (hk : k ≤ n) (omega : W) :
    uniformStoppedCovariationApprox X Y T n
        (uniformPartitionTime T n k) omega =
      quadraticCovariationPrefixApprox X Y T n k omega := by
  let increment : ℕ → ℝ := fun i ↦
    (X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        X (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega) *
      (Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n (i + 1))) omega -
        Y (min (uniformPartitionTime T n k)
          (uniformPartitionTime T n i)) omega)
  have htime : ∀ {i j : ℕ}, i ≤ j →
      uniformPartitionTime T n i ≤ uniformPartitionTime T n j := by
    intro i j hij
    unfold uniformPartitionTime
    gcongr
  have hhead :
      (∑ i ∈ Finset.range k, increment i) =
        quadraticCovariationPrefixApprox X Y T n k omega := by
    unfold quadraticCovariationPrefixApprox
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : i + 1 ≤ k := Finset.mem_range.mp hi
    simp only [increment, min_eq_right (htime hi1),
      min_eq_right (htime ((Nat.le_add_right i 1).trans hi1))]
  have htail : (∑ i ∈ Finset.Ico k n, increment i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k ≤ i := (Finset.mem_Ico.mp hi).1
    simp only [increment, min_eq_left (htime hki),
      min_eq_left (htime (hki.trans (Nat.le_add_right i 1))),
      sub_self, zero_mul]
  unfold uniformStoppedCovariationApprox
  change (∑ i ∈ Finset.range n, increment i) = _
  rw [← Finset.sum_range_add_sum_Ico increment hk, hhead, htail, add_zero]

/-- A point on a rational coarse grid has the same time coordinates on all
of its common uniform refinements. -/
theorem uniformPartitionTime_common_refinement_covariation
    (T : ℝ≥0) {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (i : ℕ) :
    uniformPartitionTime T (k * N) i =
      uniformPartitionTime
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) i := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hj0 : (j : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- A point in the `j`-th coarse block, sampled on an `N`-fold uniform
subdivision, is exactly the corresponding point of the `k*N` common
refinement. -/
theorem uniformPartitionTime_block_common_refinement
    (T : ℝ≥0) {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (j r : ℕ) :
    uniformPartitionTime T k j +
        uniformPartitionTime (T / (k : ℝ≥0)) N r =
      uniformPartitionTime T (k * N) (j * N + r) := by
  unfold uniformPartitionTime
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp

/-- On a nondegenerate common refinement, the left endpoint of every fine
cell active in a coarse right-endpoint block is one of that block's sampled
subdivision points. -/
theorem uniformPartitionTime_active_block_common_refinement
    (T : ℝ≥0) {k n i j : ℕ} (hT : 0 < T) (hk : 0 < k) (hn : 0 < n)
    (hactive : uniformPartitionTime T k j <
        uniformPartitionTime T (k * n) (i + 1) ∧
      uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T k (j + 1)) :
    ∃ r ∈ Finset.range (n + 1),
      uniformPartitionTime T (k * n) i =
        uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r := by
  have hstrict : StrictMono (uniformPartitionTime T (k * n)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
    gcongr
  have hleftTime : uniformPartitionTime T (k * n) (j * n) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hn j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hrightTime : uniformPartitionTime T (k * n) ((j + 1) * n) =
      uniformPartitionTime T k (j + 1) := by
    have h := uniformPartitionTime_block_common_refinement T hk hn (j + 1) 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hlo : j * n ≤ i := by
    have hltTime : uniformPartitionTime T (k * n) (j * n) <
        uniformPartitionTime T (k * n) (i + 1) := by
      rw [hleftTime]
      exact hactive.1
    have hlt : j * n < i + 1 := hstrict.lt_iff_lt.mp hltTime
    omega
  have hhi : i < (j + 1) * n := by
    have hleTime : uniformPartitionTime T (k * n) (i + 1) ≤
        uniformPartitionTime T (k * n) ((j + 1) * n) := by
      rw [hrightTime]
      exact hactive.2
    have hle : i + 1 ≤ (j + 1) * n := hstrict.le_iff_le.mp hleTime
    omega
  let r := i - j * n
  have hr : r < n := by
    dsimp only [r]
    rw [add_mul] at hhi
    simp only [one_mul] at hhi
    omega
  have hir : i = j * n + r := by
    dsimp only [r]
    omega
  refine ⟨r, Finset.mem_range.mpr (hr.trans (Nat.lt_succ_self n)), ?_⟩
  rw [hir]
  exact (uniformPartitionTime_block_common_refinement T hk hn j r).symm

/-- A continuous Banach-valued coefficient is uniformly close to its frozen
coarse left-endpoint value on every common refinement.  The bound is uniform
in the number of fine subdivisions inside each coarse cell. -/
theorem commonRefinement_continuousWeight_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E) (hA : Continuous A) (T : ℝ≥0) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ, ∀ k, K ≤ k → 0 < k →
      ∀ n, 0 < n → ∀ i ∈ Finset.range (k * n), ∀ j ∈ Finset.range k,
        uniformPartitionTime T k j <
            uniformPartitionTime T (k * n) (i + 1) ∧
          uniformPartitionTime T (k * n) (i + 1) ≤
            uniformPartitionTime T k (j + 1) →
        ‖A (uniformPartitionTime T (k * n) i) -
          A (uniformPartitionTime T k j)‖ < epsilon := by
  intro epsilon hepsilon
  have huc : UniformContinuousOn A (Set.Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hA.continuousOn
  obtain ⟨eta, heta, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  have hdivNN : Tendsto
      (fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp
      (tendsto_add_atTop_nat 1)
  have hdiv : Tendsto
      (fun k : ℕ ↦ ((T / ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ))
      atTop (nhds (0 : ℝ)) := by
    change Tendsto
      (NNReal.toReal ∘ fun k : ℕ ↦ T / ((k + 1 : ℕ) : ℝ≥0))
      atTop (nhds (0 : ℝ))
    simpa only [NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto 0).comp hdivNN
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hdiv eta heta
  refine ⟨K + 1, fun k hk hkpos n hn i hi j hj hactive ↦ ?_⟩
  have hkK : K ≤ k - 1 := by omega
  have hmeshNear := hK (k - 1) hkK
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hmesh : ((T / (k : ℝ≥0) : ℝ≥0) : ℝ) < eta := by
    rw [← hkpred]
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] using hmeshNear
  obtain ⟨r, hr, htime⟩ :=
    uniformPartitionTime_active_block_common_refinement
      T (by by_contra hT; simp_all [uniformPartitionTime]) hkpos hn hactive
  have hkn : 0 < k * n := Nat.mul_pos hkpos hn
  have hi0 : i ≤ k * n := (Finset.mem_range.mp hi).le
  have hfineMem := uniformPartitionTime_mem_Icc_of_le T hkn hi0
  have hj0 : j ≤ k := (Finset.mem_range.mp hj).le
  have hcoarseMem := uniformPartitionTime_mem_Icc_of_le T hkpos hj0
  rw [← dist_eq_norm]
  apply hmod (uniformPartitionTime T (k * n) i) hfineMem
    (uniformPartitionTime T k j) hcoarseMem
  have hstep :
      uniformPartitionTime (T / (k : ℝ≥0)) n r ≤ T / (k : ℝ≥0) := by
    have hrlt : r < n + 1 := Finset.mem_range.mp hr
    exact (uniformPartitionTime_mem_Icc_of_le (T / (k : ℝ≥0)) hn
      (by omega)).2
  rw [htime]
  simp only [NNReal.dist_eq]
  have hnonneg : 0 ≤
      (((uniformPartitionTime T k j +
          uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ≥0) : ℝ) -
        (uniformPartitionTime T k j : ℝ)) := by
    apply sub_nonneg.mpr
    exact_mod_cast (le_add_right (le_refl (uniformPartitionTime T k j)) :
        uniformPartitionTime T k j ≤
          uniformPartitionTime T k j +
            uniformPartitionTime (T / (k : ℝ≥0)) n r)
  rw [abs_of_nonneg hnonneg]
  have hstepReal :
      (uniformPartitionTime (T / (k : ℝ≥0)) n r : ℝ) ≤
        (T / (k : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hstep
  simpa only [NNReal.coe_add, add_sub_cancel_left] using
    hstepReal.trans_lt hmesh

/-- Freezing a continuous complex coefficient times a Lipschitz Brownian
factor separates into a continuous-coefficient error and a Brownian
oscillation error. -/
theorem norm_continuousCoefficient_mul_lipschitzWeight_sub_frozen_le
    {W : Type*} (A : ℝ≥0 → W → ℂ) (B : ℝ≥0 → W → ℝ)
    (g : ℝ → ℂ) {L : ℝ≥0} (hg : LipschitzWith L g)
    (T : ℝ≥0) {k n i j : ℕ} (omega : W)
    (alpha R G delta : ℝ)
    (hAclose : ‖A (uniformPartitionTime T (k * n) i) omega -
        A (uniformPartitionTime T k j) omega‖ ≤ alpha)
    (hAbound : ‖A (uniformPartitionTime T k j) omega‖ ≤ R)
    (hgbound : ‖g (B (uniformPartitionTime T (k * n) i) omega)‖ ≤ G)
    (hBclose : |B (uniformPartitionTime T (k * n) i) omega -
        B (uniformPartitionTime T k j) omega| ≤ delta) :
    ‖A (uniformPartitionTime T (k * n) i) omega *
          g (B (uniformPartitionTime T (k * n) i) omega) -
        A (uniformPartitionTime T k j) omega *
          g (B (uniformPartitionTime T k j) omega)‖ ≤
      alpha * G + R * (L : ℝ) * delta := by
  let Af := A (uniformPartitionTime T (k * n) i) omega
  let Ac := A (uniformPartitionTime T k j) omega
  let gf := g (B (uniformPartitionTime T (k * n) i) omega)
  let gc := g (B (uniformPartitionTime T k j) omega)
  have hgclose : ‖gf - gc‖ ≤ (L : ℝ) * delta := by
    have hraw := hg.dist_le_mul
      (B (uniformPartitionTime T (k * n) i) omega)
      (B (uniformPartitionTime T k j) omega)
    rw [Real.dist_eq, dist_eq_norm] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_left hBclose L.coe_nonneg)
  have halpha : 0 ≤ alpha := (norm_nonneg (Af - Ac)).trans hAclose
  have hR : 0 ≤ R := (norm_nonneg Ac).trans hAbound
  calc
    ‖Af * gf - Ac * gc‖ = ‖(Af - Ac) * gf + Ac * (gf - gc)‖ := by
      congr 1
      ring
    _ ≤ ‖(Af - Ac) * gf‖ + ‖Ac * (gf - gc)‖ := norm_add_le _ _
    _ = ‖Af - Ac‖ * ‖gf‖ + ‖Ac‖ * ‖gf - gc‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ alpha * G + R * ((L : ℝ) * delta) := by
      exact add_le_add
        (mul_le_mul hAclose hgbound (norm_nonneg _) halpha)
        (mul_le_mul hAbound hgclose (norm_nonneg _) hR)
    _ = alpha * G + R * (L : ℝ) * delta := by ring

/-- At a coarse boundary of a common refinement, the completed-cell
covariation is exactly the corresponding index prefix. -/
theorem quadraticCovariationBeforeStopApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k N j : ℕ} (hk : 0 < k) (hN : 0 < N) (hj : j ≤ k)
    (omega : W) :
    quadraticCovariationBeforeStopApprox X Y T (k * N)
        (uniformPartitionTime T k j) omega =
      quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega := by
  by_cases hT0 : T = 0
  · subst T
    simp [quadraticCovariationBeforeStopApprox,
      quadraticCovariationPrefixApprox, uniformPartitionTime]
  have hT : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hT0)
  have hkn : 0 < k * N := Nat.mul_pos hk hN
  have hstrict : StrictMono (uniformPartitionTime T (k * N)) := by
    intro a b hab
    unfold uniformPartitionTime
    have hden : (0 : ℝ≥0) < (k * N : ℕ) := by exact_mod_cast hkn
    gcongr
  have hboundary : uniformPartitionTime T (k * N) (j * N) =
      uniformPartitionTime T k j := by
    have h := uniformPartitionTime_block_common_refinement T hk hN j 0
    simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
      add_zero] using h.symm
  have hcond (i : ℕ) :
      uniformPartitionTime T (k * N) (i + 1) ≤
          uniformPartitionTime T k j ↔
        i + 1 ≤ j * N := by
    rw [← hboundary]
    exact hstrict.le_iff_le
  have hjN : j * N ≤ k * N := Nat.mul_le_mul_right N hj
  unfold quadraticCovariationBeforeStopApprox
    quadraticCovariationPrefixApprox
  simp_rw [hcond]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A rational covariation prefix on a common refinement is literally the
ordinary covariation sum at the corresponding shorter horizon. -/
theorem quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (omega : W) :
    quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  unfold quadraticCovariationPrefixApprox quadraticCovariationApprox
  apply Finset.sum_congr rfl
  intro i _hi
  rw [uniformPartitionTime_common_refinement_covariation T hk hj hN i,
    uniformPartitionTime_common_refinement_covariation T hk hj hN (i + 1)]

/-- At a rational sub-horizon, a coherent stopped common-refinement sum is
exactly the ordinary covariation sum on the shorter horizon. -/
theorem uniformStoppedCovariationApprox_common_refinement
    {W : Type*} (X Y : ℝ≥0 → W → ℝ) (T : ℝ≥0)
    {k j N : ℕ} (hk : 0 < k) (hj : 0 < j) (hN : 0 < N)
    (hjk : j ≤ k) (omega : W) :
    uniformStoppedCovariationApprox X Y T (k * N)
        (T * (j : ℝ≥0) / (k : ℝ≥0)) omega =
      quadraticCovariationApprox X Y
        (T * (j : ℝ≥0) / (k : ℝ≥0)) (j * N) omega := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  have hstop := uniformStoppedCovariationApprox_uniformPartitionTime
    X Y T (k * N) (j * N) (Nat.mul_le_mul_right N hjk) omega
  have hprefix := quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj hN omega
  have htime : uniformPartitionTime T (k * N) (j * N) = a := by
    rw [uniformPartitionTime]
    dsimp only [a]
    have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    push_cast
    field_simp
  change uniformStoppedCovariationApprox X Y T (k * N) a omega =
    quadraticCovariationApprox X Y a (j * N) omega
  calc
    uniformStoppedCovariationApprox X Y T (k * N) a omega =
        uniformStoppedCovariationApprox X Y T (k * N)
          (uniformPartitionTime T (k * N) (j * N)) omega := by rw [htime]
    _ = quadraticCovariationPrefixApprox X Y T (k * N) (j * N) omega :=
      hstop
    _ = quadraticCovariationApprox X Y a (j * N) omega := by
      simpa only [a] using hprefix

/-- Cross variation at a rational sub-horizon also controls the corresponding
prefix of every common refinement.  Unlike a stopped-process formulation,
this form can be multiplied by random coarse-grid coefficients. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  let a : ℝ≥0 := T * (j : ℝ≥0) / (k : ℝ≥0)
  let ns : ℕ → ℕ := fun n ↦ j * n + (j - 1)
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun n ↦ by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  have hcomp := (h a).comp hns.tendsto_atTop
  apply hcomp.congr_left
  intro n
  filter_upwards with omega
  have hcount : ns n + 1 = j * (n + 1) := by
    dsimp only [ns]
    rw [mul_add, mul_one]
    omega
  change quadraticCovariationApprox X Y a (ns n + 1) omega = _
  rw [hcount]
  exact (StochasticCalculus.quadraticCovariationPrefixApprox_common_refinement
    X Y T hk hj (Nat.zero_lt_succ n) omega).symm

/-- The common-refinement prefix limit, including its zero prefix. -/
theorem
    HasCrossVariationProcessInProbability.quadraticCovariationPrefixApprox_common_refinement_all
    {W : Type*} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    {X Y C : ℝ≥0 → W → ℝ}
    (h : HasCrossVariationProcessInProbability X Y C P)
    (T : ℝ≥0) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    TendstoInMeasure P
      (fun n ↦ quadraticCovariationPrefixApprox X Y T (k * (n + 1))
        (j * (n + 1))) atTop
      (C (T * (j : ℝ≥0) / (k : ℝ≥0))) := by
  by_cases hj : j = 0
  · subst j
    have hzero : TendstoInMeasure P
        (fun n ↦ quadraticCovariationPrefixApprox X Y T
          (k * (n + 1)) 0) atTop (C 0) := by
      apply (h 0).congr_left
      intro n
      filter_upwards with omega
      rw [quadraticCovariationPrefixApprox_zero]
      unfold quadraticCovariationApprox uniformPartitionTime
      simp
    simpa only [Nat.cast_zero, mul_zero, zero_div, zero_mul] using hzero
  · exact h.quadraticCovariationPrefixApprox_common_refinement T hk
      (Nat.pos_of_ne_zero hj)

end StochasticCalculus
