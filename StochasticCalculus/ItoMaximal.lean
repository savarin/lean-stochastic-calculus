/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import StochasticCalculus.QuadraticVariationDensity
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Finite-grid maximal estimates for the natural Itô process

This file supplies the quantitative bridge from the continuous elementary
Itô integrals to a continuous modification for an arbitrary predictable
`L²` integrand.  It first packages conditional Jensen's inequality as the
fact that the square of a real `L²` martingale is a submartingale.  Doob's
maximal inequality then gives a bound on every deterministic finite time
grid which is independent of the number of grid points.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace StochasticCalculus

variable {Ω ι κ : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Restrict a filtration along a monotone deterministic time change. -/
def monotoneReindexFiltration [Preorder ι] [Preorder κ]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (u : κ → ι)
    (hu : Monotone u) : Filtration κ ‹MeasurableSpace Ω› where
  seq k := 𝓕 (u k)
  mono' _ _ hkl := 𝓕.mono (hu hkl)
  le' k := 𝓕.le (u k)

omit [IsFiniteMeasure μ] in
/-- Sigma-finiteness of every filtration slice is preserved by deterministic
monotone reindexing. -/
instance sigmaFiniteFiltration_monotoneReindex [Preorder ι] [Preorder κ]
    {𝓕 : Filtration ι ‹MeasurableSpace Ω›} {u : κ → ι} {hu : Monotone u}
    [SigmaFiniteFiltration μ 𝓕] :
    SigmaFiniteFiltration μ (monotoneReindexFiltration 𝓕 u hu) where
  SigmaFinite k := by
    change SigmaFinite (μ.trim (𝓕.le (u k)))
    infer_instance

omit [IsFiniteMeasure μ] in
/-- A martingale remains a martingale after a monotone deterministic time
change, with the filtration restricted along the same map. -/
theorem martingale_comp_monotone [Preorder ι] [Preorder κ]
    {𝓕 : Filtration ι ‹MeasurableSpace Ω›} {M : ι → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) (u : κ → ι) (hu : Monotone u) :
    Martingale (fun k => M (u k)) (monotoneReindexFiltration 𝓕 u hu) μ := by
  refine ⟨fun k => hM.stronglyAdapted (u k), ?_⟩
  intro k l hkl
  exact hM.condExp_ae_eq (hu hkl)

/-- The square of a real martingale with integrable second moments is a
submartingale.  This is conditional Jensen specialized to `x ↦ x²`. -/
theorem martingale_sq_submartingale_of_integrable_sq [Preorder ι]
    {𝓕 : Filtration ι ‹MeasurableSpace Ω›} {M : ι → Ω → ℝ}
    (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ i, Integrable (fun ω => (M i ω) ^ 2) μ) :
    Submartingale (fun i ω => (M i ω) ^ 2) 𝓕 μ := by
  have hadapt : StronglyAdapted 𝓕 (fun i ω => (M i ω) ^ 2) := by
    intro i
    exact (hM.stronglyAdapted i).pow 2
  refine ⟨hadapt, ?_, hM2⟩
  intro i j hij
  have hJensen :
      (fun ω => (μ[M j | 𝓕 i] ω) ^ 2) ≤ᵐ[μ]
        μ[(fun ω => (M j ω) ^ 2) | 𝓕 i] := by
    have h := (even_two.convexOn_pow :
        ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2)).map_condExp_le_univ
      (𝓕.le i) (continuous_pow 2).lowerSemicontinuous
      (hM.integrable j) (by simpa only [Function.comp_def] using hM2 j)
    simpa only [Function.comp_def] using h
  filter_upwards [hM.condExp_ae_eq hij, hJensen] with ω hcond hle
  rw [← hcond]
  exact hle

/-- The fourth power of a real martingale with integrable fourth moments is
a submartingale. -/
theorem martingale_pow_four_submartingale_of_integrable_pow_four [Preorder ι]
    {𝒱 : Filtration ι ‹MeasurableSpace Ω›} {M : ι → Ω → ℝ}
    (hM : Martingale M 𝒱 μ)
    (hM4 : ∀ i, Integrable (fun omega => (M i omega) ^ 4) μ) :
    Submartingale (fun i omega => (M i omega) ^ 4) 𝒱 μ := by
  have hadapt : StronglyAdapted 𝒱 (fun i omega => (M i omega) ^ 4) := by
    intro i
    exact (hM.stronglyAdapted i).pow 4
  refine ⟨hadapt, ?_, hM4⟩
  intro i j hij
  have hJensen :
      (fun omega => (μ[M j | 𝒱 i] omega) ^ 4) ≤ᵐ[μ]
        μ[(fun omega => (M j omega) ^ 4) | 𝒱 i] := by
    have h := ((show Even 4 by exact ⟨2, by norm_num⟩).convexOn_pow :
        ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4)).map_condExp_le_univ
      (𝒱.le i) (continuous_pow 4).lowerSemicontinuous
      (hM.integrable j) (by simpa only [Function.comp_def] using hM4 j)
    simpa only [Function.comp_def] using h
  filter_upwards [hM.condExp_ae_eq hij, hJensen] with omega hcond hle
  rw [← hcond]
  exact hle

/-- Doob's finite-horizon `L²` maximal estimate, stated for the square
threshold so it directly matches Mathlib's nonnegative-submartingale API. -/
theorem martingale_maximal_sq_ineq [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ i, Integrable (fun ω => (M i ω) ^ 2) μ)
    (ε : ℝ≥0) (n : ℕ) :
    ε * μ {ω |
        (ε : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k => (M k ω) ^ 2)} ≤
      ENNReal.ofReal (∫ ω, (M n ω) ^ 2 ∂μ) := by
  let Q : ℕ → Ω → ℝ := fun i ω => (M i ω) ^ 2
  have hQ : Submartingale Q 𝓕 μ :=
    martingale_sq_submartingale_of_integrable_sq hM hM2
  have hnonneg : 0 ≤ Q := fun _ _ => sq_nonneg _
  calc
    ε * μ {ω |
          (ε : ℝ) ≤ (Finset.range (n + 1)).sup'
            Finset.nonempty_range_add_one (fun k => (M k ω) ^ 2)} ≤
        ENNReal.ofReal
          (∫ ω in {ω |
              (ε : ℝ) ≤ (Finset.range (n + 1)).sup'
                Finset.nonempty_range_add_one (fun k => (M k ω) ^ 2)},
            (M n ω) ^ 2 ∂μ) := by
      simpa only [Q] using maximal_ineq hQ hnonneg n
    _ ≤ ENNReal.ofReal (∫ ω, (M n ω) ^ 2 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral (hM2 n)
        (Filter.Eventually.of_forall fun ω => sq_nonneg (M n ω))

/-- Doob's finite-horizon `L⁴` maximal estimate, stated with a fourth-power
threshold. -/
theorem martingale_maximal_pow_four_ineq [IsProbabilityMeasure μ]
    {𝒱 : Filtration ℕ ‹MeasurableSpace Ω›} {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝒱 μ)
    (hM4 : ∀ i, Integrable (fun omega => (M i omega) ^ 4) μ)
    (epsilon : ℝ≥0) (n : ℕ) :
    epsilon * μ {omega |
        (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k => (M k omega) ^ 4)} ≤
      ENNReal.ofReal (∫ omega, (M n omega) ^ 4 ∂μ) := by
  let Q : ℕ → Ω → ℝ := fun i omega => (M i omega) ^ 4
  have hQ : Submartingale Q 𝒱 μ :=
    martingale_pow_four_submartingale_of_integrable_pow_four hM hM4
  have hnonneg : 0 ≤ Q := fun _ _ => by positivity
  calc
    epsilon * μ {omega |
          (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
            Finset.nonempty_range_add_one (fun k => (M k omega) ^ 4)} ≤
        ENNReal.ofReal
          (∫ omega in {omega |
              (epsilon : ℝ) ≤ (Finset.range (n + 1)).sup'
                Finset.nonempty_range_add_one (fun k => (M k omega) ^ 4)},
            (M n omega) ^ 4 ∂μ) := by
      simpa only [Q] using maximal_ineq hQ hnonneg n
    _ ≤ ENNReal.ofReal (∫ omega, (M n omega) ^ 4 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral (hM4 n)
        (Filter.Eventually.of_forall fun omega => by positivity)

/-- An eventually summable uniform bound on successive distances makes a
sequence uniformly Cauchy on the specified set.  Allowing an arbitrary
finite prefix is convenient after a Borel--Cantelli argument. -/
theorem uniformCauchySeqOn_of_eventually_dist_le_of_summable
    {α : Type*} (F : ℕ → α → ℝ) (S : Set α) (d : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n) (hsum : Summable d)
    (hstep : ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ S,
      dist (F n x) (F (n + 1) x) ≤ d n) :
    UniformCauchySeqOn F Filter.atTop S := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hpartial : CauchySeq (fun n => ∑ i ∈ Finset.range n, d i) :=
    ((hsum.hasSum_iff_tendsto_nat.mp hsum.hasSum).cauchySeq)
  rw [Metric.cauchySeq_iff] at hpartial
  obtain ⟨Nsum, hNsum⟩ := hpartial ε hε
  obtain ⟨Nstep, hNstep⟩ := Filter.eventually_atTop.mp hstep
  refine ⟨max Nsum Nstep, ?_⟩
  intro m hm n hn x hx
  have hmSum : Nsum ≤ m := (le_max_left _ _).trans hm
  have hnSum : Nsum ≤ n := (le_max_left _ _).trans hn
  have hmStep : Nstep ≤ m := (le_max_right _ _).trans hm
  have hnStep : Nstep ≤ n := (le_max_right _ _).trans hn
  have hforward : ∀ {a b : ℕ}, Nsum ≤ a → Nsum ≤ b →
      Nstep ≤ a → a ≤ b →
      dist (F a x) (F b x) < ε := by
    intro a b haSum hbSum haStep hab
    have hdist : dist (F a x) (F b x) ≤
        ∑ i ∈ Finset.Ico a b, d i := by
      apply dist_le_Ico_sum_of_dist_le hab
      intro k hak hkb
      exact hNstep k (haStep.trans hak) x hx
    have hsumNonneg : 0 ≤ ∑ i ∈ Finset.Ico a b, d i :=
      Finset.sum_nonneg fun i _ => hd i
    have hpartialDist :
        dist (∑ i ∈ Finset.range a, d i)
          (∑ i ∈ Finset.range b, d i) =
            ∑ i ∈ Finset.Ico a b, d i := by
      rw [Real.dist_eq, abs_sub_comm,
        ← Finset.sum_Ico_eq_sub d hab, abs_of_nonneg hsumNonneg]
    exact hdist.trans_lt (hpartialDist ▸
      hNsum a haSum b hbSum)
  by_cases hmn : m ≤ n
  · exact hforward hmSum hnSum hmStep hmn
  · rw [dist_comm]
    exact hforward hnSum hmSum hnStep (le_of_not_ge hmn)

/-- A canonical choice of limit for a Cauchy sequence in a complete uniform
space, with an arbitrary fallback value for non-Cauchy sequences. -/
noncomputable def completeCauchySeqLimit
    {β : Type*} [UniformSpace β] [CompleteSpace β] [Nonempty β]
    (f : ℕ → β) : β := by
  classical
  exact if h : CauchySeq f then
      Classical.choose (cauchySeq_tendsto_of_complete h)
    else Classical.choice inferInstance

/-- A Cauchy sequence converges to `completeCauchySeqLimit`. -/
theorem tendsto_completeCauchySeqLimit
    {β : Type*} [UniformSpace β] [CompleteSpace β] [Nonempty β]
    {f : ℕ → β} (hf : CauchySeq f) :
    Tendsto f Filter.atTop (nhds (completeCauchySeqLimit f)) := by
  classical
  rw [completeCauchySeqLimit, dif_pos hf]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete hf)

/-- The canonical pointwise limit of a uniformly Cauchy sequence of
continuous functions is continuous. -/
theorem continuousOn_completeCauchySeqLimit
    {α β : Type*} [TopologicalSpace α]
    [UniformSpace β] [CompleteSpace β] [Nonempty β]
    (F : ℕ → α → β) (S : Set α)
    (hF : UniformCauchySeqOn F Filter.atTop S)
    (hcontinuous : ∀ n, ContinuousOn (F n) S) :
    ContinuousOn (fun x => completeCauchySeqLimit (fun n => F n x)) S := by
  have htendsto : ∀ x ∈ S,
      Tendsto (fun n => F n x) Filter.atTop
        (nhds (completeCauchySeqLimit (fun n => F n x))) := by
    intro x hx
    exact tendsto_completeCauchySeqLimit (hF.cauchySeq hx)
  exact (hF.tendstoUniformlyOn_of_tendsto htendsto).continuousOn
    (Frequently.of_forall hcontinuous)

/-- Maximum squared value on the dyadic grid with denominator `2ⁿ`. -/
noncomputable def dyadicPartitionSqMax
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => (X (uniformPartitionTime t (2 ^ n) k) ω) ^ 2)

omit [IsFiniteMeasure μ] in
/-- Fixed-time almost-everywhere equality transfers to every dyadic-grid
maximum. -/
theorem dyadicPartitionSqMax_congr_ae
    {X Y : ℝ≥0 → Ω → ℝ} (hXY : ∀ s, X s =ᵐ[μ] Y s)
    (t : ℝ≥0) (n : ℕ) :
    dyadicPartitionSqMax X t n =ᵐ[μ] dyadicPartitionSqMax Y t n := by
  have hgrid : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      X (uniformPartitionTime t (2 ^ n) k) ω =
        Y (uniformPartitionTime t (2 ^ n) k) ω := by
    apply ae_all_iff.mpr
    intro k
    exact hXY (uniformPartitionTime t (2 ^ n) k)
  filter_upwards [hgrid] with ω hω
  unfold dyadicPartitionSqMax
  congr 1
  funext k
  rw [hω k]

/-- Index of the dyadic grid point immediately to the left of `s`. -/
noncomputable def dyadicApproxIndex (s t : ℝ≥0) (n : ℕ) : ℕ :=
  ⌊((s : ℝ) / (t : ℝ)) * (2 : ℝ) ^ n⌋₊

/-- For `s ≤ t`, its left dyadic approximation is a valid grid index. -/
theorem dyadicApproxIndex_le_pow {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    dyadicApproxIndex s t n ≤ 2 ^ n := by
  by_cases ht : t = 0
  · have hs : s = 0 := le_antisymm (ht ▸ hst) bot_le
    simp [dyadicApproxIndex, ht, hs]
  have htR : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  calc
    dyadicApproxIndex s t n ≤
        ⌊(((2 ^ n : ℕ) : ℝ))⌋₊ := by
      apply Nat.floor_mono
      change (s : ℝ) / (t : ℝ) * (2 : ℝ) ^ n ≤
        ((2 ^ n : ℕ) : ℝ)
      rw [Nat.cast_pow]
      norm_num only [Nat.cast_ofNat]
      calc
        (s : ℝ) / (t : ℝ) * (2 : ℝ) ^ n ≤
            1 * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right
            ((div_le_one htR).2 (by exact_mod_cast hst)) (by positivity)
        _ = (2 : ℝ) ^ n := one_mul _
    _ = 2 ^ n := Nat.floor_natCast _

/-- Left dyadic grid points converge to every time in the compact interval. -/
theorem tendsto_uniformPartitionTime_dyadicApproxIndex
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto
      (fun n => uniformPartitionTime t (2 ^ n) (dyadicApproxIndex s t n))
      Filter.atTop (nhds s) := by
  by_cases ht : t = 0
  · have hs : s = 0 := le_antisymm (ht ▸ hst) bot_le
    subst t
    subst s
    simp [uniformPartitionTime]
  rw [← NNReal.tendsto_coe]
  let a : ℝ := (s : ℝ) / (t : ℝ)
  have ha : 0 ≤ a := div_nonneg (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hratio : Tendsto
      (fun n : ℕ =>
        (⌊a * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n)
      Filter.atTop (nhds a) :=
    (tendsto_nat_floor_mul_div_atTop ha).comp hpow
  have hscaled := hratio.const_mul (t : ℝ)
  have htR : (t : ℝ) ≠ 0 := by
    exact NNReal.coe_ne_zero.mpr ht
  have hlimit : (t : ℝ) * a = (s : ℝ) := by
    dsimp only [a]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (s : ℝ) htR
  rw [← hlimit]
  convert hscaled using 1
  funext n
  simp only [uniformPartitionTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, Nat.cast_pow, Nat.cast_ofNat, dyadicApproxIndex, a]
  norm_num [Nat.cast_pow]
  rw [mul_div_assoc]

omit [MeasurableSpace Ω] in
/-- Dyadic grid maxima increase with the refinement level. -/
theorem monotone_dyadicPartitionSqMax
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    Monotone (fun n => dyadicPartitionSqMax X t n ω) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ihm =>
      apply ihm.trans
      unfold dyadicPartitionSqMax
      apply Finset.sup'_le Finset.nonempty_range_add_one
      intro k hk
      have hk' : 2 * k ∈ Finset.range (2 ^ (m + 1) + 1) := by
        simp only [Finset.mem_range] at hk ⊢
        rw [pow_succ]
        omega
      calc
        (X (uniformPartitionTime t (2 ^ m) k) ω) ^ 2 =
            (X (uniformPartitionTime t (2 ^ (m + 1)) (2 * k)) ω) ^ 2 := by
          congr 2
          unfold uniformPartitionTime
          rw [pow_succ]
          norm_num
          ring
        _ ≤ (Finset.range (2 ^ (m + 1) + 1)).sup'
            Finset.nonempty_range_add_one
            (fun j => (X (uniformPartitionTime t (2 ^ (m + 1)) j) ω) ^ 2) :=
          Finset.le_sup'
            (fun j => (X (uniformPartitionTime t (2 ^ (m + 1)) j) ω) ^ 2) hk'

omit [MeasurableSpace Ω] in
/-- A continuous path which exceeds a square threshold somewhere on
`[0,t]` exceeds the same threshold on some dyadic grid. -/
theorem exists_lt_dyadicPartitionSqMax_of_continuous
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (hX : Continuous (fun s => X s ω)) {s : ℝ≥0} (hst : s ≤ t)
    {ε : ℝ} (hε : ε < (X s ω) ^ 2) :
    ∃ n : ℕ, ε < dyadicPartitionSqMax X t n ω := by
  have htime := tendsto_uniformPartitionTime_dyadicApproxIndex hst
  have hvalue : Tendsto
      (fun n =>
        (X (uniformPartitionTime t (2 ^ n) (dyadicApproxIndex s t n)) ω) ^ 2)
      Filter.atTop (nhds ((X s ω) ^ 2)) :=
    ((hX.tendsto s).comp htime).pow 2
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      ε < (X (uniformPartitionTime t (2 ^ n)
        (dyadicApproxIndex s t n)) ω) ^ 2 :=
    hvalue.eventually (Ioi_mem_nhds hε)
  obtain ⟨n, hn⟩ := heventually.exists
  refine ⟨n, hn.trans_le ?_⟩
  unfold dyadicPartitionSqMax
  apply Finset.le_sup'
    (fun k => (X (uniformPartitionTime t (2 ^ n) k) ω) ^ 2)
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (dyadicApproxIndex_le_pow hst n)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Uniform partition times are monotone in the grid index.  The analogous
lemma in the original quadratic-variation development is private, so the
maximal-estimate layer exposes the fact as public infrastructure. -/
theorem monotone_uniformPartitionTime_general (t : ℝ≥0) (n : ℕ) :
    Monotone (uniformPartitionTime t n) := by
  intro i j hij
  unfold uniformPartitionTime
  gcongr

/-- The natural filtration sampled on a uniform deterministic time grid. -/
def uniformPartitionFiltration
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (n : ℕ) :
    Filtration ℕ ‹MeasurableSpace W› :=
  monotoneReindexFiltration 𝓕 (uniformPartitionTime t n)
    (monotone_uniformPartitionTime_general t n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Sampling the selected natural Itô process on a uniform deterministic
grid gives a discrete-time martingale for the sampled filtration. -/
theorem martingale_naturalItoProcessRepresentative_uniformPartition
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) (n : ℕ) :
    Martingale
      (fun k => naturalItoProcessRepresentative hB hsm rfl U
        (uniformPartitionTime t n k))
      (uniformPartitionFiltration (Filtration.natural B hsm) t n) P := by
  exact martingale_comp_monotone
    (martingale_naturalItoProcessRepresentative hB hsm rfl U)
    (uniformPartitionTime t n) (monotone_uniformPartitionTime_general t n)

omit [CompleteSpace W] [BorelSpace W] in
/-- Every fixed-time value of the selected representative of a natural Itô
process has an integrable square. -/
theorem integrable_sq_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) :
    Integrable (fun ω =>
      (naturalItoProcessRepresentative hB hsm rfl U t ω) ^ 2) P := by
  let It := naturalItoProcess hB hsm rfl U t
  have hbase : Integrable (fun ω => (((It : RandomL2 P) : W → ℝ) ω) ^ 2) P :=
    (Lp.memLp It).integrable_sq
  apply hbase.congr
  filter_upwards [naturalItoProcess_ae_eq_representative hB hsm rfl U t]
    with ω ht
  change ((It : W → ℝ) ω) =
    naturalItoProcessRepresentative hB hsm rfl U t ω at ht
  rw [ht]

omit [CompleteSpace W] [BorelSpace W] in
/-- Representative-level fixed-time Itô isometry. -/
theorem integral_sq_naturalItoProcessRepresentative
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (t : ℝ≥0) :
    ∫ ω, (naturalItoProcessRepresentative hB hsm rfl U t ω) ^ 2 ∂P =
      ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 := by
  calc
    ∫ ω, (naturalItoProcessRepresentative hB hsm rfl U t ω) ^ 2 ∂P =
        ∫ ω, ((naturalItoProcess hB hsm rfl U t : RandomL2 P) : W → ℝ) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [naturalItoProcess_ae_eq_representative hB hsm rfl U t]
        with ω ht
      rw [ht]
    _ = inner ℝ (naturalItoProcess hB hsm rfl U t)
        (naturalItoProcess hB hsm rfl U t) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with ω
      simp [pow_two]
    _ = ‖naturalItoProcess hB hsm rfl U t‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

omit [CompleteSpace W] [BorelSpace W] in
/-- Doob's `L²` estimate for the selected natural Itô process on every
uniform grid.  The right side is independent of the mesh size; this is the
key estimate needed for the elementary-density continuous-modification
argument. -/
theorem naturalItoProcessRepresentative_uniformPartition_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (ε : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ε * P {ω |
        (ε : ℝ) ≤ (Finset.range (n + 2)).sup'
          Finset.nonempty_range_add_one
          (fun k =>
            (naturalItoProcessRepresentative hB hsm rfl U
              (uniformPartitionTime t (n + 1) k) ω) ^ 2)} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let M : ℕ → W → ℝ := fun k =>
    naturalItoProcessRepresentative hB hsm rfl U
      (uniformPartitionTime t (n + 1) k)
  have hM : Martingale M
      (uniformPartitionFiltration (Filtration.natural B hsm) t (n + 1)) P := by
    simpa only [M] using
      martingale_naturalItoProcessRepresentative_uniformPartition
        hB hsm U t (n + 1)
  have hM2 : ∀ k, Integrable (fun ω => (M k ω) ^ 2) P := by
    intro k
    simpa only [M] using integrable_sq_naturalItoProcessRepresentative
      hB hsm U (uniformPartitionTime t (n + 1) k)
  have hDoob := martingale_maximal_sq_ineq hM hM2 ε (n + 1)
  have hn : (((n + 1 : ℕ) : ℝ≥0)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : uniformPartitionTime t (n + 1) (n + 1) = t := by
    rw [uniformPartitionTime]
    exact mul_div_cancel_right₀ t hn
  calc
    ε * P {ω |
          (ε : ℝ) ≤ (Finset.range (n + 2)).sup'
            Finset.nonempty_range_add_one
            (fun k =>
              (naturalItoProcessRepresentative hB hsm rfl U
                (uniformPartitionTime t (n + 1) k) ω) ^ 2)} ≤
        ENNReal.ofReal (∫ ω, (M (n + 1) ω) ^ 2 ∂P) := by
      simpa only [M, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hDoob
    _ = ENNReal.ofReal
        (‖naturalItoProcess hB hsm rfl U t‖ ^ 2) := by
      rw [show M (n + 1) = naturalItoProcessRepresentative hB hsm rfl U t by
        funext ω
        simp only [M, htop]]
      rw [integral_sq_naturalItoProcessRepresentative]
    _ ≤ ENNReal.ofReal (‖U‖ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (norm_naturalItoProcess_le hB hsm rfl U t)

omit [CompleteSpace W] [BorelSpace W] in
/-- The mesh-independent maximal estimate on the nested dyadic grids. -/
theorem naturalItoProcessRepresentative_dyadicPartition_maximal_sq_ineq
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (ε : ℝ≥0) (t : ℝ≥0) (n : ℕ) :
    ε * P {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
        (naturalItoProcessRepresentative hB hsm rfl U) t n ω} ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hdenom : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hone
  have hrange : 2 ^ n - 1 + 2 = 2 ^ n + 1 := by omega
  simpa only [dyadicPartitionSqMax, hdenom, hrange] using
    naturalItoProcessRepresentative_uniformPartition_maximal_sq_ineq
      hB hsm U ε t (2 ^ n - 1)

omit [CompleteSpace W] [BorelSpace W] in
/-- Doob's estimate on the union of all nested dyadic-grid events.  This is
the countable event that becomes a compact-time supremum event for a
continuous representative. -/
theorem naturalItoProcessRepresentative_dyadicPartition_maximal_sq_iUnion
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (U : PredictableProcessL2 (Filtration.natural B hsm) P)
    (ε : ℝ≥0) (t : ℝ≥0) :
    ε * P (⋃ n : ℕ, {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
        (naturalItoProcessRepresentative hB hsm rfl U) t n ω}) ≤
      ENNReal.ofReal (‖U‖ ^ 2) := by
  let S : ℕ → Set W := fun n => {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
    (naturalItoProcessRepresentative hB hsm rfl U) t n ω}
  have hS : Monotone S := by
    intro n m hnm ω hω
    exact hω.trans (monotone_dyadicPartitionSqMax
      (naturalItoProcessRepresentative hB hsm rfl U) t ω hnm)
  rw [show (⋃ n : ℕ, {ω | (ε : ℝ) ≤ dyadicPartitionSqMax
      (naturalItoProcessRepresentative hB hsm rfl U) t n ω}) =
      ⋃ n, S n by rfl]
  rw [hS.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  exact naturalItoProcessRepresentative_dyadicPartition_maximal_sq_ineq
    hB hsm U ε t n

end StochasticCalculus
