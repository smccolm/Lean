import Tao2026.Vinogradov

namespace Tao2026

open scoped BigOperators NNReal

/-- A wide block lying strictly inside the genuine `c₀=1/8` coefficient
window, with enough floor-rounded weighted mass for the final constant. -/
noncomputable def vinogradovSharpMediumDegreeBlock (X F : ℝ) : Finset ℕ :=
  Finset.Icc
    ⌈(17 / 16 : ℝ) * (Real.log F / Real.log X)⌉₊
    ⌊(59 / 32 : ℝ) * (Real.log F / Real.log X)⌋₊

theorem mem_vinogradovSharpMediumDegreeBlock_bounds {X F : ℝ} {r : ℕ}
    (hratio : 0 ≤ Real.log F / Real.log X)
    (hr : r ∈ vinogradovSharpMediumDegreeBlock X F) :
    (17 / 16 : ℝ) * (Real.log F / Real.log X) ≤ (r : ℝ) ∧
      (r : ℝ) ≤ (59 / 32 : ℝ) * (Real.log F / Real.log X) := by
  rw [vinogradovSharpMediumDegreeBlock, Finset.mem_Icc] at hr
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hr.1)
  · exact (by exact_mod_cast hr.2 : (r : ℝ) ≤
      (⌊(59 / 32 : ℝ) * (Real.log F / Real.log X)⌋₊ : ℝ)) |>.trans
        (Nat.floor_le (mul_nonneg (by norm_num) hratio))

theorem mem_vinogradovSharpMediumDegreeBlock_degree {X F : ℝ} {r : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F)
    (hr : r ∈ vinogradovSharpMediumDegreeBlock X F) :
    1 ≤ r ∧ r ≤ vinogradovTaylorDegree X F := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hs : 4 ≤ Real.log F / Real.log X := by
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  obtain ⟨hrlow, hrupp⟩ :=
    mem_vinogradovSharpMediumDegreeBlock_bounds (by linarith) hr
  constructor
  · exact_mod_cast (show (1 : ℝ) ≤ r by nlinarith)
  · have hceil : Real.log F / Real.log X ≤
        (⌈Real.log F / Real.log X⌉₊ : ℝ) := Nat.le_ceil _
    have hrR : (r : ℝ) ≤
        (10 * ⌈Real.log F / Real.log X⌉₊ : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hrR

/-- The sharp block has uniform weighted mass at least `R²/160`, including
all floor/ceiling boundary cases for `4 ≤ log F/log X < 12`. -/
theorem vinogradovTaylorDegree_sq_div_160_le_sum_sharpMediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 160 ≤
      ∑ r ∈ vinogradovSharpMediumDegreeBlock X F, (r : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  let s : ℝ := Real.log F / Real.log X
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by
    dsimp only [s] at hs
    linarith
  have hmem {r : ℕ} (hlow : (17 / 16 : ℝ) * s ≤ (r : ℝ))
      (hupp : (r : ℝ) ≤ (59 / 32 : ℝ) * s) :
      r ∈ vinogradovSharpMediumDegreeBlock X F := by
    rw [vinogradovSharpMediumDegreeBlock, Finset.mem_Icc]
    constructor
    · apply Nat.ceil_le.mpr
      simpa only [s] using hlow
    · apply Nat.le_floor
      simpa only [s] using hupp
  have hsubsetIcc (a b : ℕ)
      (hlow : (17 / 16 : ℝ) * s ≤ (a : ℝ))
      (hupp : (b : ℝ) ≤ (59 / 32 : ℝ) * s) :
      Finset.Icc a b ⊆ vinogradovSharpMediumDegreeBlock X F := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    apply hmem
    · exact hlow.trans (by exact_mod_cast hr.1)
    · have hrb : (r : ℝ) ≤ b := by exact_mod_cast hr.2
      exact hrb.trans hupp
  have hsumIcc (a b : ℕ)
      (hsub : Finset.Icc a b ⊆ vinogradovSharpMediumDegreeBlock X F) :
      (∑ r ∈ Finset.Icc a b, (r : ℝ)) ≤
        ∑ r ∈ vinogradovSharpMediumDegreeBlock X F, (r : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun r hr hnot => Nat.cast_nonneg r)
  by_cases hslarge : 12 ≤ s
  · let a := ⌈(17 / 16 : ℝ) * s⌉₊
    let b := ⌊(59 / 32 : ℝ) * s⌋₊
    have ha : (a : ℝ) < (17 / 16 : ℝ) * s + 1 := by
      dsimp only [a]
      exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (by linarith))
    have hb : (59 / 32 : ℝ) * s < (b : ℝ) + 1 := by
      dsimp only [b]
      exact Nat.lt_floor_add_one _
    have hab : a ≤ b := by
      have : (a : ℝ) ≤ (59 / 32 : ℝ) * s := by nlinarith
      exact Nat.le_floor this
    have hcard : ((vinogradovSharpMediumDegreeBlock X F).card : ℝ) =
        (b : ℝ) + 1 - (a : ℝ) := by
      change ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ)
      rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hcardLower : (25 / 32 : ℝ) * s - 1 <
        (vinogradovSharpMediumDegreeBlock X F).card := by
      rw [hcard]
      nlinarith
    have hblockSum :
        ((vinogradovSharpMediumDegreeBlock X F).card : ℝ) *
            ((17 / 16 : ℝ) * s) ≤
          ∑ r ∈ vinogradovSharpMediumDegreeBlock X F, (r : ℝ) := by
      calc
        ((vinogradovSharpMediumDegreeBlock X F).card : ℝ) *
            ((17 / 16 : ℝ) * s) =
            ∑ r ∈ vinogradovSharpMediumDegreeBlock X F,
              ((17 / 16 : ℝ) * s) := by simp
        _ ≤ ∑ r ∈ vinogradovSharpMediumDegreeBlock X F, (r : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          exact (mem_vinogradovSharpMediumDegreeBlock_bounds hratio hr).1
    have hceil : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
    have hRupper : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
      rw [vinogradovTaylorDegree]
      push_cast
      dsimp only [s] at hceil ⊢
      linarith
    have hscale : 0 ≤ (17 / 16 : ℝ) * s := by positivity
    have hproduct :
        ((25 / 32 : ℝ) * s - 1) * ((17 / 16 : ℝ) * s) <
          ((vinogradovSharpMediumDegreeBlock X F).card : ℝ) *
            ((17 / 16 : ℝ) * s) :=
      mul_lt_mul_of_pos_right hcardLower (by positivity)
    have hquad : (vinogradovTaylorDegree X F : ℝ) ^ 2 / 160 ≤
        ((25 / 32 : ℝ) * s - 1) * ((17 / 16 : ℝ) * s) := by
      nlinarith [sq_nonneg ((vinogradovTaylorDegree X F : ℝ) - 10 * (s + 1))]
    exact hquad.trans (hproduct.le.trans hblockSum)
  · have hsupper : s < 12 := lt_of_not_ge hslarge
    let q := ⌈s⌉₊
    have hqLow : 4 ≤ q := by exact_mod_cast hs.trans (Nat.le_ceil s)
    have hqHigh : q ≤ 12 := by
      exact Nat.ceil_le.mpr hsupper.le
    have hsq : s ≤ (q : ℝ) := Nat.le_ceil s
    have hqs : (q : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
    have hR : vinogradovTaylorDegree X F = 10 * q := by
      simp only [vinogradovTaylorDegree, q, s]
    interval_cases q <;> norm_num at hqLow hqHigh
    · have hs4 : s = 4 := by norm_num at hsq; linarith
      have hb := hsumIcc 5 7 (hsubsetIcc 5 7 (by rw [hs4]; norm_num)
        (by rw [hs4]; norm_num))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · by_cases hs5 : s ≤ 80 / 17
      · have hb := hsumIcc 5 7 (hsubsetIcc 5 7 (by nlinarith)
          (by norm_num at hqs; nlinarith))
        rw [hR]
        norm_num [Finset.sum_Icc_succ_top] at hb ⊢
        linarith
      · have hs5' : 80 / 17 < s := lt_of_not_ge hs5
        have hb := hsumIcc 6 8 (hsubsetIcc 6 8 (by norm_num at hsq; nlinarith)
          (by nlinarith))
        rw [hR]
        norm_num [Finset.sum_Icc_succ_top] at hb ⊢
        linarith
    · have hb := hsumIcc 7 9 (hsubsetIcc 7 9 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 8 11 (hsubsetIcc 8 11 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 9 12 (hsubsetIcc 9 12 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 10 14 (hsubsetIcc 10 14 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 11 16 (hsubsetIcc 11 16 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 12 18 (hsubsetIcc 12 18 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 13 20 (hsubsetIcc 13 20 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith

/-- The degree block used with the stronger separation constant `c₀=1/4`. -/
noncomputable def vinogradovQuarterMediumDegreeBlock (X F : ℝ) : Finset ℕ :=
  Finset.Icc
    ⌈(9 / 8 : ℝ) * (Real.log F / Real.log X)⌉₊
    ⌊(7 / 4 : ℝ) * (Real.log F / Real.log X)⌋₊

theorem mem_vinogradovQuarterMediumDegreeBlock_bounds {X F : ℝ} {r : ℕ}
    (hratio : 0 ≤ Real.log F / Real.log X)
    (hr : r ∈ vinogradovQuarterMediumDegreeBlock X F) :
    (9 / 8 : ℝ) * (Real.log F / Real.log X) ≤ (r : ℝ) ∧
      (r : ℝ) ≤ (7 / 4 : ℝ) * (Real.log F / Real.log X) := by
  rw [vinogradovQuarterMediumDegreeBlock, Finset.mem_Icc] at hr
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hr.1)
  · exact (by exact_mod_cast hr.2 : (r : ℝ) ≤
      (⌊(7 / 4 : ℝ) * (Real.log F / Real.log X)⌋₊ : ℝ)) |>.trans
        (Nat.floor_le (mul_nonneg (by norm_num) hratio))

theorem mem_vinogradovQuarterMediumDegreeBlock_degree {X F : ℝ} {r : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F)
    (hr : r ∈ vinogradovQuarterMediumDegreeBlock X F) :
    1 ≤ r ∧ r ≤ vinogradovTaylorDegree X F := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hs : 4 ≤ Real.log F / Real.log X := by
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  obtain ⟨hrlow, hrupp⟩ :=
    mem_vinogradovQuarterMediumDegreeBlock_bounds (by linarith) hr
  constructor
  · exact_mod_cast (show (1 : ℝ) ≤ r by nlinarith)
  · have hceil : Real.log F / Real.log X ≤
        (⌈Real.log F / Real.log X⌉₊ : ℝ) := Nat.le_ceil _
    have hrR : (r : ℝ) ≤
        (10 * ⌈Real.log F / Real.log X⌉₊ : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hrR

/-- The quarter-window block has weighted mass at least `R²/193`, with all
floor/ceiling boundary cases included. -/
theorem vinogradovTaylorDegree_sq_div_193_le_sum_quarterMediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovTaylorDegree X F : ℝ) ^ 2 / 193 ≤
      ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  let s : ℝ := Real.log F / Real.log X
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X := by
    dsimp only [s] at hs
    linarith
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
    · have hrb : (r : ℝ) ≤ b := by exact_mod_cast hr.2
      exact hrb.trans hupp
  have hsumIcc (a b : ℕ)
      (hsub : Finset.Icc a b ⊆ vinogradovQuarterMediumDegreeBlock X F) :
      (∑ r ∈ Finset.Icc a b, (r : ℝ)) ≤
        ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun r hr hnot => Nat.cast_nonneg r)
  by_cases hslarge : 12 ≤ s
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
            ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F,
              ((9 / 8 : ℝ) * s) := by simp
        _ ≤ ∑ r ∈ vinogradovQuarterMediumDegreeBlock X F, (r : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          exact (mem_vinogradovQuarterMediumDegreeBlock_bounds hratio hr).1
    have hceil : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
    have hRupper : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
      rw [vinogradovTaylorDegree]
      push_cast
      dsimp only [s] at hceil ⊢
      linarith
    have hproduct :
        ((5 / 8 : ℝ) * s - 1) * ((9 / 8 : ℝ) * s) <
          ((vinogradovQuarterMediumDegreeBlock X F).card : ℝ) *
            ((9 / 8 : ℝ) * s) :=
      mul_lt_mul_of_pos_right hcardLower (by positivity)
    have hquad : (vinogradovTaylorDegree X F : ℝ) ^ 2 / 193 ≤
        ((5 / 8 : ℝ) * s - 1) * ((9 / 8 : ℝ) * s) := by
      nlinarith [sq_nonneg ((vinogradovTaylorDegree X F : ℝ) - 10 * (s + 1))]
    exact hquad.trans (hproduct.le.trans hblockSum)
  · have hsupper : s < 12 := lt_of_not_ge hslarge
    let q := ⌈s⌉₊
    have hqLow : 4 ≤ q := by exact_mod_cast hs.trans (Nat.le_ceil s)
    have hqHigh : q ≤ 12 := Nat.ceil_le.mpr hsupper.le
    have hsq : s ≤ (q : ℝ) := Nat.le_ceil s
    have hqs : (q : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
    have hR : vinogradovTaylorDegree X F = 10 * q := by
      simp only [vinogradovTaylorDegree, q, s]
    interval_cases q <;> norm_num at hqLow hqHigh
    · have hs4 : s = 4 := by norm_num at hsq; linarith
      have hb := hsumIcc 5 7 (hsubsetIcc 5 7 (by rw [hs4]; norm_num)
        (by rw [hs4]; norm_num))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 6 7 (hsubsetIcc 6 7 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · by_cases hs6 : s ≤ 16 / 3
      · have hb := hsumIcc 6 8 (hsubsetIcc 6 8 (by nlinarith)
          (by norm_num at hqs; nlinarith))
        rw [hR]
        norm_num [Finset.sum_Icc_succ_top] at hb ⊢
        linarith
      · have hs6' : 16 / 3 < s := lt_of_not_ge hs6
        have hb := hsumIcc 7 9 (hsubsetIcc 7 9 (by norm_num at hsq; nlinarith)
          (by nlinarith))
        rw [hR]
        norm_num [Finset.sum_Icc_succ_top] at hb ⊢
        linarith
    · have hb := hsumIcc 8 10 (hsubsetIcc 8 10 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 9 12 (hsubsetIcc 9 12 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 11 14 (hsubsetIcc 11 14 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 12 15 (hsubsetIcc 12 15 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 13 17 (hsubsetIcc 13 17 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith
    · have hb := hsumIcc 14 19 (hsubsetIcc 14 19 (by norm_num at hsq; nlinarith)
        (by norm_num at hqs; nlinarith))
      rw [hR]
      norm_num [Finset.sum_Icc_succ_top] at hb ⊢
      linarith

end Tao2026
