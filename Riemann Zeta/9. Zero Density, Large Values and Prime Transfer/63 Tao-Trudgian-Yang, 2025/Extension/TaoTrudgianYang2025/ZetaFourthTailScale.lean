import TaoTrudgianYang2025.ZetaFourthTailPower

/-!
# A bounded actual contour-tail error at the fourth-moment cutoff

The right line is selected before the height. For any positive excess
in the cutoff exponent, a sufficiently far line makes the actual
source-minus-prefix error bounded uniformly on the dyadic height interval.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem fourth_tail_scale_le {δ b H t x : ℝ}
    (hH : 1 ≤ H) (ht : 0 ≤ t) (htH : t ≤ 2*H)
    (hb : 3/2 < b) (hbudget : b+(1+δ)*(3/2-b) ≤ 0)
    (hx : H^(1+δ) ≤ x) :
    t^b*x^(3/2-b) ≤ 2^b := by
  have hH0 : 0 < H := by linarith
  have hx0 : 0 < H^(1+δ) := Real.rpow_pos_of_pos hH0 _
  have hbp : 0 ≤ b := by linarith
  have hbn : 3/2-b ≤ 0 := by linarith
  calc
    _ ≤ (2*H)^b*(H^(1+δ))^(3/2-b) :=
      mul_le_mul (Real.rpow_le_rpow ht htH hbp)
        (Real.rpow_le_rpow_of_nonpos hx0 hx hbn)
        (Real.rpow_nonneg (hx0.le.trans hx) _) (by positivity)
    _ = 2^b*H^(b+(1+δ)*(3/2-b)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH0.le,
        ← Real.rpow_mul hH0.le,mul_assoc,← Real.rpow_add hH0]
    _ ≤ 2^b*1 :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hH hbudget)
        (by positivity)
    _ = _ := mul_one _

theorem exists_norm_fourthRightPiece_sub_cutoff_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℝ, 4 ≤ H₀ ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ t : ℝ, H ≤ t → t ≤ 2*H →
      ∀ N : ℕ, H^(1+δ) ≤ (N:ℝ) → ∀ a : ℝ, 0 < a →
      ‖zetaFourthRightPiece t-zetaFourthPrefix t a (Finset.range (N+1))‖ ≤ K := by
  let b : ℝ := 2+2/δ
  have hb : 3/2 < b := by
    have h := div_pos (by norm_num : (0:ℝ)<2) hδ
    dsimp [b]
    linarith
  have hbudget : b+(1+δ)*(3/2-b) ≤ 0 := by
    have heq : b+(1+δ)*(3/2-b) = -(1+δ)/2 := by
      dsimp [b]
      field_simp [hδ.ne']
      ring
    rw [heq]
    linarith
  obtain ⟨A,hA,hbound⟩ := exists_norm_zetaFourthTail_cutoff_le hb
  refine ⟨A*2^b,by positivity,max 4 (4*b),le_max_left _ _,?_⟩
  intro H hH t ht htH N hN a ha
  have hH4 : 4 ≤ H := (le_max_left _ _).trans hH
  have hHt : 4*b ≤ H := (le_max_right _ _).trans hH
  have ht0 : 0 ≤ t := by linarith
  have hNpos : 0 < N := by
    have hNreal : (0:ℝ) < N :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith : 0 < H) _) hN
    exact_mod_cast hNreal
  rw [zetaFourthRightPiece_eq_prefix_add_tail ht0 ha (by linarith : 0 < b)
    (Finset.range (N+1)),add_sub_cancel_left]
  calc
    _ ≤ A*t^b*(N:ℝ)^(3/2-b) :=
      hbound t (hH4.trans ht) (hHt.trans ht) N hNpos
    _ = A*(t^b*(N:ℝ)^(3/2-b)) := by ring
    _ ≤ A*2^b :=
      mul_le_mul_of_nonneg_left
        (fourth_tail_scale_le (by linarith) ht0 htH hb hbudget hN) hA.le

end TaoTrudgianYang2025
