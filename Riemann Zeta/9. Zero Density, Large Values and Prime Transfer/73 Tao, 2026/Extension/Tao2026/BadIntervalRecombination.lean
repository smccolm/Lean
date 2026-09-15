import Tao2026.BadIntervalBackwardTypicalUnion
import Tao2026.BadIntervalSlowCutoffLogSaving

/-!
# Typical/non-typical recombination

This module recombines the two endpoint orientations of the typical branch
with the selected Proposition 6.5 non-typical branch.  It then feeds that
literal partition through the finite maximal-function reduction and records
the resulting bound on nontrivial bad values in one dyadic window.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

/-- Every comparable normalized bad interval is either typical at the moving
cutoffs or belongs to the matching selected non-typical family. -/
theorem scaleNormalizedBadIntervalIndices_subset_typical_union_nonTypical
    (q : ℕ → ℕ) (x : ℕ) :
    scaleNormalizedBadIntervalIndices x ⊆
      taoTypicalBadIntervalIndices q x ∪
        taoSlowNonTypicalFailureIndices (q x) x := by
  intro NH hNH
  obtain ⟨_hN, _hH, p₀, k, m, hnorm, hleft, hright⟩ :=
    mem_scaleNormalizedBadIntervalIndices.mp hNH
  rcases typical_or_nonTypical_of_scaleNormalized
      (lengthCutoff := taoTypicalLengthCutoff x)
      (squareThreshold := taoTypicalSquareThreshold x)
      (lowerPrime := taoPrimeTupleSlowLowerCutoff q x)
      (upperPrime := taoPrimeTupleSlowUpperCutoff q x)
      hnorm hleft hright with htyp | hnon
  · apply Finset.mem_union_left
    apply mem_taoTypicalBadIntervalIndices.mpr
    exact ⟨hNH, p₀, k, m, htyp⟩
  · apply Finset.mem_union_right
    apply mem_taoSlowNonTypicalFailureIndices.mpr
    exact ⟨hNH, p₀, k, m, hnon⟩

/-- Literal interval-union version of the typical/non-typical partition. -/
theorem scaleNormalizedBadIntervalUnion_subset_typical_union_nonTypical
    (q : ℕ → ℕ) (x : ℕ) :
    scaleNormalizedBadIntervalUnion x ⊆
      taoTypicalBadIntervalUnion q x ∪
        taoSlowNonTypicalFailureUnion (q x) x := by
  intro n hn
  rw [scaleNormalizedBadIntervalUnion, Finset.mem_biUnion] at hn
  obtain ⟨NH, hNH, hnInterval⟩ := hn
  have hsplit :=
    scaleNormalizedBadIntervalIndices_subset_typical_union_nonTypical q x hNH
  rw [Finset.mem_union] at hsplit
  rcases hsplit with htyp | hnon
  · apply Finset.mem_union_left
    rw [taoTypicalBadIntervalUnion, Finset.mem_biUnion]
    exact ⟨NH, htyp, hnInterval⟩
  · apply Finset.mem_union_right
    rw [taoSlowNonTypicalFailureUnion, Finset.mem_biUnion]
    exact ⟨NH, hnon, hnInterval⟩

theorem card_scaleNormalizedBadIntervalUnion_le_typical_add_nonTypical
    (q : ℕ → ℕ) (x : ℕ) :
    (scaleNormalizedBadIntervalUnion x).card ≤
      (taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card := by
  exact (Finset.card_le_card
    (scaleNormalizedBadIntervalUnion_subset_typical_union_nonTypical q x)).trans
      (Finset.card_union_le
        (taoTypicalBadIntervalUnion q x)
        (taoSlowNonTypicalFailureUnion (q x) x))

/-- The source's selected slow cutoff gives a normalized-union estimate whose
two summands are now exactly the full typical and non-typical branches. -/
theorem exists_eventually_card_scaleNormalizedBadIntervalUnion_le_typical_add_sourceError :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ᶠ x : ℕ in atTop,
        ((scaleNormalizedBadIntervalUnion x).card : ℝ) ≤
          (taoTypicalBadIntervalUnion q x).card +
            (x : ℝ) / (taoZ x) ^ (2 : ℝ) := by
  obtain ⟨q, hq, hlower, hupper, hnon⟩ :=
    exists_taoProposition65_slowCutoff_union_bound
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · simpa only [taoPrimeTupleSlowLowerCutoff] using hlower
  · simpa only [taoPrimeTupleSlowUpperCutoff] using hupper
  · filter_upwards [hnon] with x hx
    have hsplit := card_scaleNormalizedBadIntervalUnion_le_typical_add_nonTypical q x
    have hsplitReal :
        ((scaleNormalizedBadIntervalUnion x).card : ℝ) ≤
          (taoTypicalBadIntervalUnion q x).card +
            (taoSlowNonTypicalFailureUnion (q x) x).card := by
      exact_mod_cast hsplit
    exact hsplitReal.trans
      (add_le_add
        (le_refl ((taoTypicalBadIntervalUnion q x).card : ℝ)) hx)

/-- The maximal-function reduction transfers the recombined normalized bound
back to all admissible bad intervals. -/
theorem card_admissibleBadIntervalUnion_le_thirty_mul_typical_add_nonTypical_of_scale
    (x : ℕ) (hscale : AdmissibleSylvesterSchurAtScale x) (q : ℕ → ℕ) :
    (admissibleBadIntervalUnion x).card ≤
      30 * ((taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card) := by
  calc
    (admissibleBadIntervalUnion x).card ≤
        30 * (scaleNormalizedBadIntervalUnion x).card :=
      card_admissibleBadIntervalUnion_le_thirty_mul_normalized_of_scale x hscale
    _ ≤ 30 * ((taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card) :=
      Nat.mul_le_mul_left 30
        (card_scaleNormalizedBadIntervalUnion_le_typical_add_nonTypical q x)

/-- Compatibility recombination bound from unrestricted Sylvester--Schur. -/
theorem card_admissibleBadIntervalUnion_le_thirty_mul_typical_add_nonTypical
    (hSS : SylvesterSchurConclusion) (q : ℕ → ℕ) (x : ℕ) :
    (admissibleBadIntervalUnion x).card ≤
      30 * ((taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card) :=
  card_admissibleBadIntervalUnion_le_thirty_mul_typical_add_nonTypical_of_scale
    x (fun hadm => hadm.exists_largePrime_of_sylvesterSchur hSS) q

/-- Literal nontrivial bad values lying in the dyadic window inspected by an
admissible interval at parameter `x`. -/
def nontrivialBadNumbersInDyadicWindow (x : ℕ) : Finset ℕ :=
  (Finset.Icc (x / 2) x).filter fun n => n ∈ badSet \ badOneTermSet

theorem mem_nontrivialBadNumbersInDyadicWindow {x n : ℕ} :
    n ∈ nontrivialBadNumbersInDyadicWindow x ↔
      x / 2 ≤ n ∧ n ≤ x ∧ n ∈ badSet ∧ n ∉ badOneTermSet := by
  simp [nontrivialBadNumbersInDyadicWindow, and_assoc]

theorem nontrivialBadNumbersInDyadicWindow_subset_admissibleBadIntervalUnion
    (x : ℕ) :
    nontrivialBadNumbersInDyadicWindow x ⊆ admissibleBadIntervalUnion x := by
  intro n hn
  obtain ⟨hxHalf, hnx, ⟨N, H, hnInterval, hbad⟩, hnOne⟩ :=
    mem_nontrivialBadNumbersInDyadicWindow.mp hn
  have hHTwo : 2 ≤ H := by
    have hHpos := hbad.length_pos
    by_contra hnot
    have hHone : H = 1 := by omega
    subst H
    have hnEq : n = N + 1 := by
      have hnBounds := Finset.mem_Ioc.mp hnInterval
      omega
    apply hnOne
    refine ⟨?_, ?_⟩
    · have := (Finset.mem_Ioc.mp hnInterval).1
      omega
    · simpa [hnEq] using hbad
  have hHleN := hbad.length_le_start hHTwo
  have hnBounds := Finset.mem_Ioc.mp hnInterval
  have hNltx : N < x := hnBounds.1.trans_le hnx
  have hHltx : H < x := hHleN.trans_lt hNltx
  apply mem_admissibleBadIntervalUnion.mpr
  exact ⟨N, H, hNltx, hHltx,
    ⟨hHTwo, hbad, n, hnInterval, hxHalf, hnx⟩, hnInterval⟩

theorem card_nontrivialBadNumbersInDyadicWindow_le_thirty_mul_typical_add_nonTypical_of_scale
    (x : ℕ) (hscale : AdmissibleSylvesterSchurAtScale x) (q : ℕ → ℕ) :
    (nontrivialBadNumbersInDyadicWindow x).card ≤
      30 * ((taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card) :=
  (Finset.card_le_card
    (nontrivialBadNumbersInDyadicWindow_subset_admissibleBadIntervalUnion x)).trans
      (card_admissibleBadIntervalUnion_le_thirty_mul_typical_add_nonTypical_of_scale
        x hscale q)

/-- Compatibility dyadic-window bound from unrestricted Sylvester--Schur. -/
theorem card_nontrivialBadNumbersInDyadicWindow_le_thirty_mul_typical_add_nonTypical
    (hSS : SylvesterSchurConclusion) (q : ℕ → ℕ) (x : ℕ) :
    (nontrivialBadNumbersInDyadicWindow x).card ≤
      30 * ((taoTypicalBadIntervalUnion q x).card +
        (taoSlowNonTypicalFailureUnion (q x) x).card) :=
  card_nontrivialBadNumbersInDyadicWindow_le_thirty_mul_typical_add_nonTypical_of_scale
    x (fun hadm => hadm.exists_largePrime_of_sylvesterSchur hSS) q

/-! ## Quantitative logarithmic recombination -/

theorem taoNaturalDilation_natCast (c x : ℕ) :
    taoNaturalDilation (c : ℝ) x = c * x := by
  simp [taoNaturalDilation, ← Nat.cast_mul]

/-- Conditional quantitative dyadic-window conclusion.  The explicit
Burgess input closes Proposition 6.6, Sylvester--Schur supplies the maximal
reduction, and Lemma 1.6(ii) removes the fixed enlargement of the one-term
count. -/
theorem exists_taoBadIntervalDyadicWindow_logSaving_of_eventually_scale
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hscale : ∀ᶠ x : ℕ in atTop, AdmissibleSylvesterSchurAtScale x)
    (h16ii : TaoLemma16iiConclusion) :
    ∃ q : ℕ → ℕ, ∃ K : ℝ,
      0 < K ∧
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℕ in atTop,
          ((nontrivialBadNumbersInDyadicWindow x).card : ℝ) ≤
            K * ((badOneTermCount x : ℝ) /
              Real.log x ^ (1 - ε)) := by
  obtain ⟨q, hq, hlower, hupper, hnon⟩ :=
    exists_taoProposition65_slowDiagonal_badOneTerm_every_logSaving
  let c : ℝ := (2 * taoPrimeTupleEnlargementFactor : ℕ)
  have hc : 0 < c := by
    dsimp only [c]
    have hfactor : 0 < taoPrimeTupleEnlargementFactor := by
      unfold taoPrimeTupleEnlargementFactor
      positivity
    exact_mod_cast (Nat.mul_pos (by norm_num) hfactor)
  have hdilationTheta := (h16ii c hc).isBigO
  obtain ⟨D, hDpos, hD⟩ := hdilationTheta.exists_pos
  let A : ℝ :=
    2 * (100 * taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        8 ^ (50 : ℕ) * 8 ^ (1001 : ℕ)) *
      (1000 : ℝ) ^ (1000 : ℕ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hsource := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  refine ⟨q, 30 * (A * D + 1), by positivity, hq, ?_, ?_, ?_⟩
  · simpa only [taoPrimeTupleSlowLowerCutoff] using hlower
  · simpa only [taoPrimeTupleSlowUpperCutoff] using hupper
  · intro ε hε
    filter_upwards
      [hscale,
       eventually_card_taoTypicalBadIntervalUnion_le_logSaving_mul_dilatedBadOneTermCount
        hC hburgess hq hε,
       hnon ε hε,
       hD.bound,
       (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
         (eventually_gt_atTop (0 : ℝ))]
        with x hscaleX htyp hnonX hDilation hlog
    have hsplit :=
      card_nontrivialBadNumbersInDyadicWindow_le_thirty_mul_typical_add_nonTypical_of_scale
        x hscaleX q
    have hsplitReal :
        ((nontrivialBadNumbersInDyadicWindow x).card : ℝ) ≤
          30 * (((taoTypicalBadIntervalUnion q x).card : ℝ) +
            (taoSlowNonTypicalFailureUnion (q x) x).card) := by
      exact_mod_cast hsplit
    have hDilation' :
        (badOneTermCount (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) ≤
          D * (badOneTermCount x : ℝ) := by
      have hdilationEq :
          taoNaturalDilation c x =
            2 * taoPrimeTupleEnlargementFactor * x := by
        dsimp only [c]
        rw [taoNaturalDilation_natCast]
      rw [← hdilationEq]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (badOneTermCount
          (taoNaturalDilation c x) : ℝ) by positivity),
        Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (badOneTermCount x : ℝ) by positivity)] at hDilation
      exact hDilation
    have hdenPos : 0 < Real.log x ^ (1 - ε) :=
      Real.rpow_pos_of_pos hlog _
    have htyp' :
        ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
          A * (D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε))) := by
      calc
        ((taoTypicalBadIntervalUnion q x).card : ℝ) ≤
            A * ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) /
                Real.log x ^ (1 - ε)) := by
          simpa only [A] using htyp
        _ ≤ A * ((D * (badOneTermCount x : ℝ)) /
            Real.log x ^ (1 - ε)) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hDilation' hdenPos.le) hA
        _ = A * (D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε))) := by
          rw [mul_div_assoc]
    calc
      ((nontrivialBadNumbersInDyadicWindow x).card : ℝ) ≤
          30 * (((taoTypicalBadIntervalUnion q x).card : ℝ) +
            (taoSlowNonTypicalFailureUnion (q x) x).card) := hsplitReal
      _ ≤ 30 * (A * (D * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε))) +
          (badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε)) := by
        gcongr
      _ = 30 * (A * D + 1) * ((badOneTermCount x : ℝ) /
          Real.log x ^ (1 - ε)) := by
        simp only [add_mul, one_mul, mul_assoc]

/-- Compatibility quantitative dyadic-window conclusion from unrestricted
Sylvester--Schur. -/
theorem exists_taoBadIntervalDyadicWindow_logSaving
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hSS : SylvesterSchurConclusion)
    (h16ii : TaoLemma16iiConclusion) :
    ∃ q : ℕ → ℕ, ∃ K : ℝ,
      0 < K ∧
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowLowerCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log (taoPrimeTupleSlowUpperCutoff q x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℕ in atTop,
          ((nontrivialBadNumbersInDyadicWindow x).card : ℝ) ≤
            K * ((badOneTermCount x : ℝ) /
              Real.log x ^ (1 - ε)) :=
  exists_taoBadIntervalDyadicWindow_logSaving_of_eventually_scale
    hC hburgess
    (Filter.Eventually.of_forall fun _ _ _ hadm =>
      hadm.exists_largePrime_of_sylvesterSchur hSS)
    h16ii

/-- The dyadic-window logarithmic-saving conclusion, packaged for reuse by
the final dyadic summation. -/
def TaoBadIntervalDyadicWindowLogSavingConclusion : Prop :=
  ∃ q : ℕ → ℕ, ∃ K : ℝ,
    0 < K ∧
    Tendsto q atTop atTop ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowLowerCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    Tendsto (fun x =>
      Real.log (taoPrimeTupleSlowUpperCutoff q x) /
        Real.log (taoZ x)) atTop (𝓝 1) ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        ((nontrivialBadNumbersInDyadicWindow x).card : ℝ) ≤
          K * ((badOneTermCount x : ℝ) /
            Real.log x ^ (1 - ε))

/-- The local dyadic-window estimate no longer requires unrestricted
Sylvester--Schur: its eventual admissible-scale form is already proved. -/
theorem taoBadIntervalDyadicWindowLogSaving_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (h16ii : TaoLemma16iiConclusion) :
    TaoBadIntervalDyadicWindowLogSavingConclusion := by
  simpa [TaoBadIntervalDyadicWindowLogSavingConclusion] using
    exists_taoBadIntervalDyadicWindow_logSaving_of_eventually_scale
      hC hburgess eventually_admissibleSylvesterSchurAtScale h16ii

/-! ## Exact dyadic assembly bridge -/

set_option maxHeartbeats 100000

/-- Literal finite realization of the global nontrivial count. -/
def nontrivialBadNumbersUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n => n ∈ badSet \ badOneTermSet

theorem card_nontrivialBadNumbersUpTo (x : ℕ) :
    (nontrivialBadNumbersUpTo x).card = nontrivialBadCount x := by
  unfold nontrivialBadNumbersUpTo nontrivialBadCount countUpTo
  congr 1
  ext n
  simp only [Finset.mem_filter]

/-- Dyadic endpoint exponents sufficient to cover `[1,x]`. -/
def nontrivialBadDyadicExponents (x : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 x + 2)

/-- Union of the dyadic windows at power-of-two endpoints up to `2x`. -/
def nontrivialBadDyadicWindowCover (x : ℕ) : Finset ℕ :=
  (nontrivialBadDyadicExponents x).biUnion fun r =>
    nontrivialBadNumbersInDyadicWindow (2 ^ r)

theorem nontrivialBadNumbersUpTo_subset_dyadicWindowCover (x : ℕ) :
    nontrivialBadNumbersUpTo x ⊆ nontrivialBadDyadicWindowCover x := by
  intro n hn
  have hnData : 1 ≤ n ∧ n ≤ x ∧ n ∈ badSet ∧ n ∉ badOneTermSet := by
    simpa [nontrivialBadNumbersUpTo, and_assoc] using hn
  let r : ℕ := Nat.log 2 n + 1
  have hnPos : 0 < n := by omega
  have hlogLe : Nat.log 2 n ≤ Nat.log 2 x :=
    Nat.log_mono_right hnData.2.1
  have hrMem : r ∈ nontrivialBadDyadicExponents x := by
    simp only [nontrivialBadDyadicExponents, Finset.mem_range, r]
    omega
  rw [nontrivialBadDyadicWindowCover, Finset.mem_biUnion]
  refine ⟨r, hrMem, mem_nontrivialBadNumbersInDyadicWindow.mpr ?_⟩
  have hlower : 2 ^ r / 2 ≤ n := by
    have hpow := Nat.pow_log_le_self 2 hnPos.ne'
    simp only [r, pow_succ]
    omega
  have hupper : n ≤ 2 ^ r := by
    have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    simpa only [r] using hpow.le
  exact ⟨hlower, hupper, hnData.2.2.1, hnData.2.2.2⟩

/-- Exact finite dyadic summation bound for the global nontrivial count. -/
theorem nontrivialBadCount_le_sum_dyadicWindowCards (x : ℕ) :
    nontrivialBadCount x ≤
      ∑ r ∈ nontrivialBadDyadicExponents x,
        (nontrivialBadNumbersInDyadicWindow (2 ^ r)).card := by
  rw [← card_nontrivialBadNumbersUpTo]
  exact (Finset.card_le_card
    (nontrivialBadNumbersUpTo_subset_dyadicWindowCover x)).trans
      Finset.card_biUnion_le

end

end Tao2026
