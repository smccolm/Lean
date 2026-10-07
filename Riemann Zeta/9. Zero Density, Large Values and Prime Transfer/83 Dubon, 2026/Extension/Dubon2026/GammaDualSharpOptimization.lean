import Dubon2026.RankinDualShiftedOptimization

/-! # Sharp three-fifths differences for genuine nonnegative linear-mean coefficient series -/

namespace Dubon2026

noncomputable section

/-- A true nonnegative linear coefficient mean gives the exact low and high powers required by the degree-four kernel. -/
theorem exists_linearMeanDual_power_bounds (a : ℕ → ℝ) (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    {B : ℝ} (hB : 0 < B) (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-(5 / 8 : ℝ))) ≤ C * (N : ℝ) ^ (3 / 8 : ℝ) ∧
      Summable (fun n : ℕ => if N < n then a n * (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ∧
      (∑' n : ℕ, if N < n then a n * (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) ≤ C * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  refine ⟨10 * B, by positivity, fun N hN => ?_⟩
  have hl := linearPowerSum_le ha0 hB.le hb (by norm_num : (0 : ℝ) < 5 / 8)
    (by norm_num : (5 / 8 : ℝ) < 1) hN
  rw [sum_Icc_zero_eq_positive (by simp only [ha0, zero_mul])] at hl
  have ht := linearPowerTail_summable_bound ha hB.le hb (by norm_num : (1 : ℝ) < 9 / 8) hN
  norm_num at hl ht
  refine ⟨?_, ht.1, ?_⟩
  · exact hl.trans (by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 8 : ℝ)])
  · convert ht.2 using 1
    ring

/-- The actual generic Gamma dual series has both sharp difference terms from its genuine nonnegative linear coefficient mean. -/
theorem exists_gammaRieszDualSeries_power_difference_bound (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha : ∀ n, 0 ≤ a n) {B k A : ℝ} (hB : 0 < B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧ ∀ (x h : ℝ) (N : ℕ), 0 < x → 0 ≤ h → h ≤ x → 1 ≤ N →
      ‖gammaRieszDualSeries a k A (x + 2 * h) - 2 * gammaRieszDualSeries a k A (x + h) +
        gammaRieszDualSeries a k A x‖ ≤
        C₀ * h ^ 2 * x ^ (3 / 8 : ℝ) * (N : ℝ) ^ (3 / 8 : ℝ) +
        C₂ * x ^ (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨C, hC, hpower⟩ := exists_linearMeanDual_power_bounds a ha0 ha hB hb
  obtain ⟨L, H, hL, hH, hsplit⟩ := exists_gammaRieszDualSeries_split_bound hk hA
  refine ⟨L * C, H * C, mul_pos hL hC, mul_pos hH hC, ?_⟩
  intro x h N hx hh hhx hN
  have hbnd := hsplit a B ha hB.le hb x h N hx hh hhx hN
  have hp := hpower N hN
  apply hbnd.trans
  have hlow := mul_le_mul_of_nonneg_left hp.1 (show 0 ≤ L * h ^ 2 * x ^ (3 / 8 : ℝ) by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hp.2.2 (show 0 ≤ H * x ^ (15 / 8 : ℝ) by positivity)
  convert add_le_add hlow hhigh using 1
  ring

/-- The actual generic dual second difference has the exact three-fifths bound at both unsmoothing base points, with the natural cutoff proved in the existing optimization. -/
theorem exists_gammaRieszDualSeries_shifted_three_fifths_bound (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha : ∀ n, 0 ≤ a n) {B k A : ℝ} (hB : 0 < B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖gammaRieszDualSeries a k A (y + 2 * h) - 2 * gammaRieszDualSeries a k A (y + h) +
        gammaRieszDualSeries a k A y‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨L, H, hL, hH, hdiff⟩ := exists_gammaRieszDualSeries_power_difference_bound a ha0 ha hB hb hk hA
  refine ⟨L + (2 : ℝ) ^ (1 / 8 : ℝ) * H, by positivity, ?_⟩
  intro x y hx hy hyx hhy
  dsimp only
  have hx0 : 0 < x := by linarith
  have hh : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hn := rieszOptimization_floor hx
  have hdy := hdiff y (x ^ (3 / 5 : ℝ)) ⌊x ^ (3 / 5 : ℝ)⌋₊ hy hh.le hhy hn.1
  have hlow : L * (x ^ (3 / 5 : ℝ)) ^ 2 * y ^ (3 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (3 / 8 : ℝ) ≤
      L * (x ^ (3 / 5 : ℝ)) ^ 2 * x ^ (3 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (3 / 8 : ℝ) := by
    gcongr
  have hhigh : H * y ^ (15 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      H * x ^ (15 / 8 : ℝ) * (⌊x ^ (3 / 5 : ℝ)⌋₊ : ℝ) ^ (-(1 / 8 : ℝ)) := by
    gcongr
  have hd := hdy.trans (add_le_add hlow hhigh)
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
