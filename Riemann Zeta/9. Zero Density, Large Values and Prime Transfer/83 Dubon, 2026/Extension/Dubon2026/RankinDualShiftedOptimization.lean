import Dubon2026.RankinDualOptimization

/-! # Uniform three-fifths optimization for the actual forward and backward dual differences -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The genuine dual second difference has the same sharp bound at every positive base point below x for which the chosen smoothing scale fits. -/
theorem exists_rankinGammaDualSeries_shifted_three_fifths_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 1 ≤ x → 0 < y → y ≤ x → x ^ (3 / 5 : ℝ) ≤ y →
      let h : ℝ := x ^ (3 / 5 : ℝ)
      ‖rankinGammaDualSeries f A (y + 2 * h) - 2 * rankinGammaDualSeries f A (y + h) +
        rankinGammaDualSeries f A y‖ / h ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨L, H, hL, hH, hb⟩ := exists_rankinGammaDualSeries_difference_bound f hk hA
  refine ⟨L + (2 : ℝ) ^ (1 / 8 : ℝ) * H, by positivity, ?_⟩
  intro x y hx hy hyx hhy
  dsimp only
  have hx0 : 0 < x := by linarith
  have hh : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hn := rieszOptimization_floor hx
  have hdy := hb y (x ^ (3 / 5 : ℝ)) ⌊x ^ (3 / 5 : ℝ)⌋₊ hy hh.le hhy hn.1
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


/-- At the explicit threshold the genuine smoothing scale is at most one quarter of x. -/
theorem rieszOptimization_scale_le_quarter {x : ℝ} (hx : 32 ≤ x) :
    4 * x ^ (3 / 5 : ℝ) ≤ x := by
  have hx0 : 0 < x := by linarith
  have hp : (32 : ℝ) ^ (2 / 5 : ℝ) = 4 := by
    calc
      _ = ((2 : ℝ) ^ (5 : ℝ)) ^ (2 / 5 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ (2 : ℝ) := by rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      _ = 4 := by norm_num
  have hfour : 4 ≤ x ^ (2 / 5 : ℝ) := by
    rw [← hp]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  calc
    _ ≤ x ^ (2 / 5 : ℝ) * x ^ (3 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hx0.le _)
    _ = x := by rw [← Real.rpow_add hx0]; norm_num

end
end Dubon2026
