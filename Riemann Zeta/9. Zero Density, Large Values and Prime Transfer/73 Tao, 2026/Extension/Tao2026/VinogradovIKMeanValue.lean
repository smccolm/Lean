import Tao2026.VinogradovIKDegree
import Tao2026.VinogradovMeanValue

/-!
# Mean-value preparation at the effective IK degree

This module reindexes the existing medium-coordinate machinery by
`vinogradovIKDegree`.  It keeps the source quarter-window and records its
weighted mass relative to the smaller degree.
-/

namespace Tao2026

open scoped BigOperators NNReal

/-- Every degree in the quarter-window lies between one and the effective
IK degree. -/
theorem mem_vinogradovQuarterMediumDegreeBlock_IKDegree
    {X F : ℝ} {r : ℕ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F)
    (hr : r ∈ vinogradovQuarterMediumDegreeBlock X F) :
    1 ≤ r ∧ r ≤ vinogradovIKDegree X F := by
  have hs := four_le_vinogradov_log_ratio hX hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by linarith
  obtain ⟨hrlow, hrupp⟩ :=
    mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr
  constructor
  · exact_mod_cast (show (1 : ℝ) ≤ r by nlinarith)
  · have hk := two_mul_vinogradov_log_ratio_le_IKDegree hX hFhigh
    exact_mod_cast (show (r : ℝ) ≤ (vinogradovIKDegree X F : ℝ) by
      nlinarith)

/-- The quarter-window has weighted mass at least `k²/31` when measured
against the effective degree.  This follows from the already verified exact
floor/ceiling mass calculation and the comparison `R ≥ (5/2)k`. -/
theorem vinogradovIKDegree_sq_div_31_le_sum_quarterMediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovIKDegree X F : ℝ) ^ 2 / 31 ≤
      ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
  let s := Real.log F / Real.log X
  let K : ℝ := vinogradovIKDegree X F
  let R : ℝ := vinogradovTaylorDegree X F
  have hs : 4 ≤ s := by
    simpa only [s] using four_le_vinogradov_log_ratio hX hFhigh
  have hK : K ≤ 4 * s := by
    simpa only [K, s] using vinogradovIKDegree_cast_le hX hFhigh
  have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hR : 10 * s ≤ R := by
    dsimp only [R, s]
    rw [vinogradovTaylorDegree]
    push_cast
    dsimp only [s] at hceil ⊢
    nlinarith
  have hRK : (5 / 2 : ℝ) * K ≤ R := by nlinarith
  have hK0 : 0 ≤ K := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hsq := pow_le_pow_left₀
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2) hK0) hRK 2
  have hcompare : K ^ 2 / 31 ≤ R ^ 2 / 193 := by
    nlinarith [sq_nonneg R, sq_nonneg K]
  have hmass :=
    vinogradovTaylorDegree_sq_div_193_le_sum_quarterMediumDegreeBlock
      (X := X) (F := F) hX hFhigh
  exact hcompare.trans (by simpa only [K, R] using hmass)

set_option maxHeartbeats 800000 in
/-- Direct floor/ceiling bookkeeping improves the effective-degree mass to
`k²/25`.  The small range is a finite ceiling certificate; for `s ≥ 18` the
cardinality and lower endpoint of the source block suffice. -/
theorem vinogradovIKDegree_sq_div_25_le_sum_quarterMediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovIKDegree X F : ℝ) ^ 2 / 25 ≤
      ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
  let s : ℝ := Real.log F / Real.log X
  let K : ℝ := vinogradovIKDegree X F
  change K ^ 2 / 25 ≤
    ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ)
  have hs : 4 ≤ s := by
    simpa only [s] using four_le_vinogradov_log_ratio hX hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by
    dsimp only [s] at hs
    linarith
  have hK : K ≤ 4 * s := by
    simpa only [K, s] using vinogradovIKDegree_cast_le hX hFhigh
  have hK0 : 0 ≤ K := by positivity
  have hKsq : K ^ 2 ≤ (4 * s) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  have hmem {r : ℕ} (hlow : (9 / 8 : ℝ) * s ≤ (r : ℝ))
      (hupp : (r : ℝ) ≤ (7 / 4 : ℝ) * s) :
      r ∈ vinogradovQuarterMediumDegreeBlock X F := by
    rw [vinogradovQuarterMediumDegreeBlock, Finset.mem_Icc]
    constructor
    · apply Nat.ceil_le.mpr
      simpa only [s] using hlow
    · apply Nat.le_floor
      simpa only [s] using hupp
  have hsubsetIcc (a b : ℕ)
      (hlow : (9 / 8 : ℝ) * s ≤ (a : ℝ))
      (hupp : (b : ℝ) ≤ (7 / 4 : ℝ) * s) :
      Finset.Icc a b ⊆ vinogradovQuarterMediumDegreeBlock X F := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    apply hmem
    · exact hlow.trans (by exact_mod_cast hr.1)
    · exact (by exact_mod_cast hr.2 : (r : ℝ) ≤ b) |>.trans hupp
  have hsumIcc (a b : ℕ)
      (hsub : Finset.Icc a b ⊆ vinogradovQuarterMediumDegreeBlock X F) :
      (∑ r ∈ Finset.Icc a b, (r : ℝ)) ≤
        ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun r hr hnot => Nat.cast_nonneg r)
  by_cases hslarge : 18 ≤ s
  · let a := ⌈(9 / 8 : ℝ) * s⌉₊
    let b := ⌊(7 / 4 : ℝ) * s⌋₊
    have ha : (a : ℝ) < (9 / 8 : ℝ) * s + 1 := by
      dsimp only [a]
      exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (by linarith))
    have hb : (7 / 4 : ℝ) * s < (b : ℝ) + 1 := by
      dsimp only [b]
      exact Nat.lt_floor_add_one _
    have hab : a ≤ b := by
      have : (a : ℝ) ≤ (7 / 4 : ℝ) * s := by nlinarith
      exact Nat.le_floor this
    have hcard : ((vinogradovQuarterMediumDegreeBlock X F).card : ℝ) =
        (b : ℝ) + 1 - (a : ℝ) := by
      change ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ)
      rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hcardLower : (5 / 8 : ℝ) * s - 1 <
        (vinogradovQuarterMediumDegreeBlock X F).card := by
      rw [hcard]
      nlinarith
    have hblockSum :
        ((vinogradovQuarterMediumDegreeBlock X F).card : ℝ) *
            ((9 / 8 : ℝ) * s) ≤
          ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
      calc
        ((vinogradovQuarterMediumDegreeBlock X F).card : ℝ) *
            ((9 / 8 : ℝ) * s) =
            ∑ _r ∈ vinogradovQuarterMediumDegreeBlock X F,
              ((9 / 8 : ℝ) * s) := by simp
        _ ≤ ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          exact (mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr).1
    have hproduct :
        ((5 / 8 : ℝ) * s - 1) * ((9 / 8 : ℝ) * s) <
          ((vinogradovQuarterMediumDegreeBlock X F).card : ℝ) *
            ((9 / 8 : ℝ) * s) :=
      mul_lt_mul_of_pos_right hcardLower (by positivity)
    have hquad : K ^ 2 / 25 ≤
        ((5 / 8 : ℝ) * s - 1) * ((9 / 8 : ℝ) * s) := by
      nlinarith [hKsq]
    exact hquad.trans (hproduct.le.trans hblockSum)
  · have hsupper : s < 18 := lt_of_not_ge hslarge
    let k := vinogradovIKDegree X F
    let a := ⌈(9 / 32 : ℝ) * ((k : ℝ) + 1)⌉₊
    let b := ⌊(7 / 16 : ℝ) * (k : ℝ)⌋₊
    have hkLow : 16 ≤ k := by
      simpa only [k] using sixteen_le_vinogradovIKDegree hX hFhigh
    have hkUpperReal : (k : ℝ) < 72 := by
      have := vinogradovIKDegree_cast_le hX hFhigh
      dsimp only [s] at hsupper
      dsimp only [k]
      nlinarith
    have hkHigh : k ≤ 71 := by
      have : k < 72 := by exact_mod_cast hkUpperReal
      omega
    have hks : (k : ℝ) ≤ 4 * s := by
      simpa only [k, s] using vinogradovIKDegree_cast_le hX hFhigh
    have hsk : 4 * s < (k : ℝ) + 1 := by
      simpa only [k, s] using
        four_mul_vinogradov_log_ratio_lt_IKDegree_add_one X F
    have haLow : (9 / 8 : ℝ) * s ≤ (a : ℝ) := by
      apply le_trans (by nlinarith : (9 / 8 : ℝ) * s ≤
        (9 / 32 : ℝ) * ((k : ℝ) + 1))
      exact Nat.le_ceil _
    have hbUpp : (b : ℝ) ≤ (7 / 4 : ℝ) * s := by
      exact (Nat.floor_le (by positivity)).trans (by nlinarith)
    have hb := hsumIcc a b (hsubsetIcc a b haLow hbUpp)
    dsimp only [a, b] at hb
    change ((k : ℝ) ^ 2 / 25) ≤ _
    interval_cases k <;>
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢ <;>
      linarith

/-- Weighted quarter-window mass inside the effective-degree medium
coordinate set. -/
theorem vinogradovIKDegree_sq_div_31_le_sum_mediumDegrees_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovIKDegree X F : ℝ) ^ 2 / 31 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovIKDegree X F), (r : ℝ) := by
  have hratio : 0 ≤ Real.log F / Real.log X := by
    linarith [four_le_vinogradov_log_ratio hX hFhigh]
  have hsubset : vinogradovQuarterMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovIKDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrK⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_IKDegree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrK,
      isVinogradovMediumCoefficient_quarter_of_sharpBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrK) hsmall⟩
  exact (vinogradovIKDegree_sq_div_31_le_sum_quarterMediumDegreeBlock
      hX hFhigh).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r))

/-- Strengthened effective-degree medium-coordinate mass using the direct
`k²/25` block calculation. -/
theorem vinogradovIKDegree_sq_div_25_le_sum_mediumDegrees_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovIKDegree X F : ℝ) ^ 2 / 25 ≤
      ∑ r ∈ vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovIKDegree X F), (r : ℝ) := by
  have hratio : 0 ≤ Real.log F / Real.log X := by
    linarith [four_le_vinogradov_log_ratio hX hFhigh]
  have hsubset : vinogradovQuarterMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 4) c
        (vinogradovIKDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrK⟩ :=
      mem_vinogradovQuarterMediumDegreeBlock_IKDegree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrK,
      isVinogradovMediumCoefficient_quarter_of_sharpBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrK) hsmall⟩
  exact (vinogradovIKDegree_sq_div_25_le_sum_quarterMediumDegreeBlock
      hX hFhigh).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r hr hnot => Nat.cast_nonneg r))

/-- The effective-degree quarter-window coordinate product.  The direct
mass calculation leaves the scale exponent `-255 k² / 25600`. -/
theorem source_prod_mediumSavingFactor_le_IKDegree_quarter
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovIKDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) ≤
      (vinogradovAveragingRange X : ℝ) ^
        (-(255 * (vinogradovIKDegree X F : ℝ) ^ 2) / 25600) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hKR := vinogradovIKDegree_le_vinogradovTaylorDegree hX hFhigh
  have hgrowthR := sourceVinogradovScalarGrowth_quarter_of_nontrivialScale
    hX hFhigh hα hsmall
  have hgrowth : ∀ j : Fin (vinogradovIKDegree X F),
      72 * (1 + Real.log 2 +
        ((2 - (1 / 4 : ℝ)) * ((j.1 + 1 : ℕ) : ℝ)) *
          Real.log (vinogradovAveragingRange X)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          ((1 / 1024 : ℝ) * ((j.1 + 1 : ℕ) : ℝ)) := by
    intro j
    exact hgrowthR ⟨j.1, lt_of_lt_of_le j.2 hKR⟩
  calc
    (∏ j : Fin (vinogradovIKDegree X F),
      vinogradovMediumCoordinateSavingFactor c
        (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) ≤
        (vinogradovAveragingRange X : ℝ) ^
          (-((1 / 4 : ℝ) - 1 / 1024) *
            ((vinogradovIKDegree X F : ℝ) ^ 2 / 25)) := by
      exact prod_mediumSavingFactor_le_rpow_of_sum_lower_of_absorption
        c (vinogradovAveragingRange X) ell (vinogradovIKDegree X F)
        (1 / 4) (1 / 1024) ((vinogradovIKDegree X F : ℝ) ^ 2 / 25)
        hV hell (by norm_num) (by norm_num) hgrowth
        (vinogradovIKDegree_sq_div_25_le_sum_mediumDegrees_quarter
          hX hFhigh hα hn hcoeff hsmall)
    _ = (vinogradovAveragingRange X : ℝ) ^
        (-(255 * (vinogradovIKDegree X F : ℝ) ^ 2) / 25600) := by
      congr 1
      ring

/-- Lemma 12 at the effective degree, including the exact critical box
power. -/
theorem source_prod_coordinateSums_le_IKDegree_quarterSaving_mul_criticalPower
    {X F α : ℝ} {n ell : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hell : 1 ≤ ell)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (∏ j : Fin (vinogradovIKDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovIKDegree X F : ℝ) ^ 2) / 25600) *
        ((((3 * ell : ℕ) : ℝ)) ^ (2 * vinogradovIKDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovIKDegree X F * (vinogradovIKDegree X F + 1))) := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  calc
    (∏ j : Fin (vinogradovIKDegree X F),
      ∑ x ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell (vinogradovAveragingRange X) (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
        (∏ j : Fin (vinogradovIKDegree X F),
          vinogradovMediumCoordinateSavingFactor c
            (vinogradovAveragingRange X) ell (j.1 + 1) (1 / 4)) *
          ∏ j : Fin (vinogradovIKDegree X F),
            (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      exact prod_coordinateSums_le_prod_mediumSaving_mul_prod_side_sq
        c (vinogradovAveragingRange X) ell (vinogradovIKDegree X F)
        (1 / 4) hV hell (by norm_num)
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovIKDegree X F : ℝ) ^ 2) / 25600) *
        ∏ j : Fin (vinogradovIKDegree X F),
          (((2 * (ell * vinogradovAveragingRange X ^ (j.1 + 1)) + 1 : ℕ) : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact source_prod_mediumSavingFactor_le_IKDegree_quarter
          hX hFhigh hα hn hell hcoeff hsmall
      · positivity
    _ ≤ (vinogradovAveragingRange X : ℝ) ^
          (-(255 * (vinogradovIKDegree X F : ℝ) ^ 2) / 25600) *
        ((((3 * ell : ℕ) : ℝ)) ^ (2 * vinogradovIKDegree X F) *
          (vinogradovAveragingRange X : ℝ) ^
            (vinogradovIKDegree X F * (vinogradovIKDegree X F + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · exact prod_powerBoxSide_card_sq_le
          (vinogradovAveragingRange X) ell (vinogradovIKDegree X F) hV hell
      · positivity

end Tao2026
