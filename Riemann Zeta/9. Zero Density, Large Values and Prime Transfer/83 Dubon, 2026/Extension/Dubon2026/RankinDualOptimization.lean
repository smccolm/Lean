import Dubon2026.RankinGammaDualSeries

/-! # Exact three-fifths optimization for the genuine Rankin dual Gamma series -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual natural split at floor(x^(3/5)) has both endpoint comparisons needed for sharp optimization. -/
theorem rieszOptimization_floor {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ⌊x ^ (3 / 5 : ℝ)⌋₊ ∧
      (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ≤ x ^ (3 / 5 : ℝ) ∧
      x ^ (3 / 5 : ℝ) / 2 ≤ (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ∧
      x ^ (3 / 5 : ℝ) ≤ x := by
  have hh : 1 ≤ x ^ (3 / 5 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hn : 1 ≤ ⌊x ^ (3 / 5 : ℝ)⌋₊ := (Nat.one_le_floor_iff _).mpr hh
  refine ⟨hn, Nat.floor_le (by linarith), ?_, Real.rpow_le_self_of_one_le hx (by norm_num)⟩
  have hnR : (1 : ℝ) ≤ ⌊x ^ (3 / 5 : ℝ)⌋₊ := by exact_mod_cast hn
  linarith [Nat.lt_floor_add_one (x ^ (3 / 5 : ℝ))]

/-- The actual low-frequency cutoff gives the exact three-fifths power with no epsilon loss. -/
theorem rieszOptimization_low_power {x : ℝ} (hx : 1 ≤ x) :
    x ^ (3 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (3 / 8 : ℝ) ≤ x ^ (3 / 5 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hn := rieszOptimization_floor hx
  calc
    _ ≤ x ^ (3 / 8 : ℝ) * (x ^ (3 / 5 : ℝ)) ^ (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hn.2.1 (by norm_num)) (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; norm_num

/-- The actual high tail at the floor cutoff gives the same exact three-fifths power after unsmoothing. -/
theorem rieszOptimization_high_power {x : ℝ} (hx : 1 ≤ x) :
    x ^ (15 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (-(1 / 8 : ℝ)) /
      (x ^ (3 / 5 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (1 / 8 : ℝ) * x ^ (3 / 5 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hn := rieszOptimization_floor hx
  have hb := Real.rpow_le_rpow_of_nonpos (half_pos hh) hn.2.2.1 (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  have hh2 : (x ^ (3 / 5 : ℝ)) ^ 2 = x ^ (6 / 5 : ℝ) := by
    rw [← Real.rpow_natCast (x ^ (3 / 5 : ℝ)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  have hhneg : (x ^ (3 / 5 : ℝ)) ^ (-(1 / 8 : ℝ)) = x ^ (-(3 / 40 : ℝ)) := by
    rw [← Real.rpow_mul hx0.le]
    norm_num
  calc
    _ ≤ x ^ (15 / 8 : ℝ) * (x ^ (3 / 5 : ℝ) / 2) ^ (-(1 / 8 : ℝ)) /
        (x ^ (3 / 5 : ℝ)) ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le _)) (sq_nonneg _)
    _ = (2 : ℝ) ^ (1 / 8 : ℝ) *
        (x ^ (15 / 8 : ℝ) * (x ^ (3 / 5 : ℝ)) ^ (-(1 / 8 : ℝ)) / (x ^ (3 / 5 : ℝ)) ^ 2) := by
      rw [Real.div_rpow hh.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    _ = (2 : ℝ) ^ (1 / 8 : ℝ) * (x ^ (9 / 5 : ℝ) / x ^ (6 / 5 : ℝ)) := by
      rw [hhneg, hh2, ← Real.rpow_add hx0]
      norm_num
    _ = _ := by rw [← Real.rpow_sub hx0]; norm_num

/-- The actual Rankin dual Gamma series has the exact optimized three-fifths second-difference bound. -/
theorem exists_rankinGammaDualSeries_three_fifths_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖rankinGammaDualSeries f A (x + 2 * h) - 2 * rankinGammaDualSeries f A (x + h) +
        rankinGammaDualSeries f A x‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨L, H, hL, hH, hb⟩ := exists_rankinGammaDualSeries_difference_bound f hk hA
  refine ⟨L + (2 : ℝ) ^ (1 / 8 : ℝ) * H, by positivity, ?_⟩
  intro x hx
  dsimp only
  have hx0 : 0 < x := by linarith
  have hh : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hn := rieszOptimization_floor hx
  have hd := hb x (x ^ (3 / 5 : ℝ)) ⌊x ^ (3 / 5 : ℝ)⌋₊ hx0 hh.le hn.2.2.2 hn.1
  have he :
      (L * (x ^ (3 / 5 : ℝ)) ^ 2 * x ^ (3 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (3 / 8 : ℝ) +
        H * x ^ (15 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (-(1 / 8 : ℝ))) /
          (x ^ (3 / 5 : ℝ)) ^ 2 =
      L * (x ^ (3 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (3 / 8 : ℝ)) +
        H * (x ^ (15 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (-(1 / 8 : ℝ)) /
          (x ^ (3 / 5 : ℝ)) ^ 2) := by field_simp [hh.ne']
  apply (div_le_div_of_nonneg_right hd (sq_nonneg _)).trans
  rw [he]
  have hl := mul_le_mul_of_nonneg_left (rieszOptimization_low_power hx) hL.le
  have hr := mul_le_mul_of_nonneg_left (rieszOptimization_high_power hx) hH.le
  exact (add_le_add hl hr).trans_eq (by ring)

end
end Dubon2026
