import TaoTrudgianYang2025.AtkinsonPairPackets
import TaoTrudgianYang2025.IvicSixthPair
import TaoTrudgianYang2025.AtkinsonHeightCover

/-! Exact absorption length for the classical restricted-sixth pair. -/

noncomputable section
namespace TaoTrudgianYang2025

def ivicSixthAbsorptionLength (A H Y : ℝ) : ℝ :=
  (Y^2/(4*A*H^(7/18:ℝ)))^(9/2:ℝ)

theorem ivicSixthAbsorptionLength_pos {A H Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hY : 0 < Y) :
    0 < ivicSixthAbsorptionLength A H Y := by
  unfold ivicSixthAbsorptionLength
  positivity

theorem ivicSixthAbsorptionLength_absorbs {A H Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) :
    2*A*(ivicSixthAbsorptionLength A H Y)^(2/9:ℝ)*H^(7/18:ℝ) ≤ Y^2 := by
  have hp : 0 ≤ Y^2/(4*A*H^(7/18:ℝ)) := by positivity
  unfold ivicSixthAbsorptionLength
  rw [← Real.rpow_mul hp]
  norm_num only [show (9/2:ℝ)*(2/9)=1 by norm_num,Real.rpow_one]
  have he : 2*A*(Y^2/(4*A*H^(7/18:ℝ)))*H^(7/18:ℝ) = Y^2/2 := by
    have hHp : H^(7/18:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg Y]

theorem ivicSixthAbsorptionLength_eq {A H Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hY : 0 < Y) :
    ivicSixthAbsorptionLength A H Y =
      Y^9/(512*A^(9/2:ℝ)*H^(7/4:ℝ)) := by
  have hc : (4:ℝ)^(9/2:ℝ) = 512 := by
    calc
      _ = ((2:ℝ)^(2:ℝ))^(9/2:ℝ) := by norm_num
      _ = (2:ℝ)^(9:ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ = _ := by norm_num
  unfold ivicSixthAbsorptionLength
  rw [Real.div_rpow (sq_nonneg Y) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ 4*A) (by positivity),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hA.le,hc,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le,← Real.rpow_mul hH.le]
  norm_num

theorem atkinson_card_le_of_quadratic_packet {A H G Q Y : ℝ}
    {W : Finset ℝ} {f : ℝ → ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hG : 0 < G) (hY : 0 < Y)
    (hlarge : ∀ t ∈ W, Y ≤ f t)
    (hpacket : (∑ t ∈ W, f t)^2 ≤
      A*((W.card : ℝ)*H/G+(W.card : ℝ)^2*Q))
    (habsorb : 2*A*Q ≤ Y^2) :
    (W.card : ℝ) ≤ 2*A*H/(G*Y^2) := by
  by_cases hW : W.Nonempty
  · have hR : (0:ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hsum : (W.card:ℝ)*Y ≤ ∑ t ∈ W, f t := by
      simpa using Finset.sum_le_sum hlarge
    have hsq := (pow_le_pow_left₀ (by positivity : 0 ≤ (W.card:ℝ)*Y) hsum 2).trans hpacket
    have hhalf := mul_le_mul_of_nonneg_right habsorb (sq_nonneg (W.card:ℝ))
    have hquad : (W.card:ℝ)*((W.card:ℝ)*Y^2) ≤
        (W.card:ℝ)*(2*A*(H/G)) := by
      ring_nf at hsq hhalf ⊢
      nlinarith
    have hc := (mul_le_mul_iff_right₀ hR).mp hquad
    apply (le_div_iff₀ (mul_pos hG (sq_pos_of_pos hY))).2
    have he := (le_div_iff₀ hG).mp (show (W.card:ℝ)*Y^2 ≤ (2*A*H)/G by
      convert hc using 1; ring)
    nlinarith
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem ivicSixth_covered_card_budget {A H G Y : ℝ}
    (hA : 0 < A) (hH : 0 < H) (hG : 0 < G) (hY : 0 < Y) :
    ((Nat.floor (H/ivicSixthAbsorptionLength A H Y)+1:ℕ):ℝ)*
      (2*A*H/(G*Y^2)) ≤
      2*A*H/(G*Y^2)+1024*A^(11/2:ℝ)*H^(15/4:ℝ)/(G*Y^11) := by
  have hL := ivicSixthAbsorptionLength_pos hA hH hY
  have hfloor := Nat.floor_le (div_nonneg hH.le hL.le)
  have hc : ((Nat.floor (H/ivicSixthAbsorptionLength A H Y)+1:ℕ):ℝ) ≤
      H/ivicSixthAbsorptionLength A H Y+1 := by
    push_cast
    linarith
  have ha : A^(11/2:ℝ) = A*A^(9/2:ℝ) := by
    calc
      _ = A^(1+(9/2:ℝ)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hA,Real.rpow_one]
  have hh : H^(15/4:ℝ) = H^2*H^(7/4:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_add hH]
    congr 1
    ring
  calc
    _ ≤ (H/ivicSixthAbsorptionLength A H Y+1)*(2*A*H/(G*Y^2)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [ivicSixthAbsorptionLength_eq hA hH hY,ha,hh]
      have hAp : A^(9/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
      have hHp : H^(7/4:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hH _).ne'
      field_simp
      ring

end TaoTrudgianYang2025
