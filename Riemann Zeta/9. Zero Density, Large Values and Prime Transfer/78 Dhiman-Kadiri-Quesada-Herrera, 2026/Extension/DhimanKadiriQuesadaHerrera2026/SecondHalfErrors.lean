import DhimanKadiriQuesadaHerrera2026.AFESecondClosed

/-! # Half-integer square and cube error coefficients -/

namespace DhimanKadiriQuesadaHerrera2026

/-- The sum of the two actual square majorants at a half-integer frequency parameter. -/
theorem squareBounds_half {y : ℝ} (hy : 1 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    minusSquareBound ⌊y⌋₊ y + plusSquareBound y =
      (46 / 9) / y +
        (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2 := by
  obtain ⟨k, hk⟩ := hyhalf
  have hf := half_integer_eq_nat_floor_add_half hy k hk
  have hm : (⌊y⌋₊ : ℝ) + 1 = y + 1 / 2 := by linarith
  dsimp only [minusSquareBound, plusSquareBound]
  rw [hm, show y + 1 / 2 - y = 1 / 2 by ring]
  norm_num [real_digamma_half]
  have hypos : 0 < y := by linarith
  have h1 : y + 1 ≠ 0 := by positivity
  have hhalf : y + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring_nf

/-- The sum of the two actual cube majorants at a half-integer frequency parameter. -/
theorem cubeBounds_half {y : ℝ} (hy : 1 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    minusCubeBound ⌊y⌋₊ y + plusCubeBound y =
      (230 / 27) / y - (14 / 3) / y ^ 2 +
        (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
          2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
          (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3 := by
  obtain ⟨k, hk⟩ := hyhalf
  have hf := half_integer_eq_nat_floor_add_half hy k hk
  have hm : (⌊y⌋₊ : ℝ) + 1 = y + 1 / 2 := by linarith
  dsimp only [minusCubeBound, plusCubeBound]
  rw [hm, show y + 1 / 2 - y = 1 / 2 by ring]
  norm_num [real_digamma_half]
  have hypos : 0 < y := by linarith
  have h1 : y + 1 ≠ 0 := by positivity
  have hhalf : y + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring_nf

/-- The combined square coefficients satisfy the source's 46/9 bound without a sign-changing substitution. -/
theorem squareBounds_half_le {y : ℝ} (hy : 1 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    minusSquareBound ⌊y⌋₊ y + plusSquareBound y ≤ (46 / 9) / y := by
  have hypos : 0 < y := by linarith
  have hl := Real.log_le_log (by positivity : 0 < y + 1) (by linarith : y + 1 ≤ 2 * (y + 1 / 2))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : y + 1 / 2 ≠ 0)] at hl
  have hi : 1 / (y + 1 / 2) ≤ 2 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < y + 1 / 2)).mpr
    linarith
  have hj : 3 / 4 ≤ (1 + 2 * y) / (2 * (y + 1)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (y + 1))).mpr
    linarith
  have he : Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
      2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1)) ≤ 0 := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  rw [squareBounds_half hy hyhalf]
  exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg he (sq_nonneg y))

/-- The combined cube coefficients satisfy the source's 230/27 bound on the actual half-integer cutoff domain. -/
theorem cubeBounds_half_le {y : ℝ} (hy : 3 / 2 ≤ y)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    minusCubeBound ⌊y⌋₊ y + plusCubeBound y ≤ (230 / 27) / y := by
  have hypos : 0 < y := by linarith
  have hlog1 := Real.log_le_sub_one_of_pos (by positivity : 0 < y + 1 / 2)
  have hlog2 := Real.log_le_sub_one_of_pos (by positivity : 0 < y + 1)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hrec : 0 ≤ 1 / (2 * (y + 1 / 2)) := by positivity
  have hr : 0 ≤ (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2) := by positivity
  have he : Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
      2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
      (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2) ≤ (14 / 3) * y := by linarith
  have hd := div_le_div_of_nonneg_right he (by positivity : 0 ≤ y ^ 3)
  have hid : (14 / 3) * y / y ^ 3 = (14 / 3) / y ^ 2 := by field_simp
  rw [hid] at hd
  rw [cubeBounds_half (by linarith : 1 ≤ y) hyhalf]
  linarith only [hd]

end DhimanKadiriQuesadaHerrera2026
