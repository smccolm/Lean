import TaoTrudgianYang2025.LargeValueBlockPattern

/-! Exact integer block-length and physical exponent comparisons. -/

noncomputable section

namespace TaoTrudgianYang2025

def exponentBlockLength (N σ : ℝ) : ℕ := Nat.floor (N^(2*σ-1))

theorem exponentBlockLength_bounds {N σ : ℝ} (hN : 1 ≤ N)
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    1 ≤ exponentBlockLength N σ ∧
      N^(2*σ-1)/2 ≤ (exponentBlockLength N σ:ℝ) ∧
      (exponentBlockLength N σ:ℝ) ≤ N^(2*σ-1) ∧
      (exponentBlockLength N σ:ℝ) ≤ N := by
  have hx : 1 ≤ N^(2*σ-1) := Real.one_le_rpow hN (by linarith)
  have hf : 1 ≤ exponentBlockLength N σ := (Nat.one_le_floor_iff _).mpr hx
  have hfl : (exponentBlockLength N σ:ℝ) ≤ N^(2*σ-1) :=
    Nat.floor_le (zero_le_one.trans hx)
  have hfu : N^(2*σ-1) < (exponentBlockLength N σ:ℝ)+1 := Nat.lt_floor_add_one _
  have hfr : (1:ℝ) ≤ exponentBlockLength N σ := by exact_mod_cast hf
  refine ⟨hf,by linarith,hfl,hfl.trans ?_⟩
  calc
    N^(2*σ-1) ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = N := Real.rpow_one N

theorem exponentBlockLength_value_sandwich {N σ : ℝ} (hN : 1 ≤ N)
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    (1/8)*N^σ ≤ Real.sqrt (N*(exponentBlockLength N σ:ℝ)/16) ∧
      Real.sqrt (N*(exponentBlockLength N σ:ℝ)/16) ≤ N^σ := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hb := exponentBlockLength_bounds hN hσ hσ₁
  have hx : 0 < N^σ := Real.rpow_pos_of_pos hp _
  have hsq : (N^σ)^2 = N*N^(2*σ-1) := by
    rw [← Real.rpow_mul_natCast hp.le]
    calc
      N^(σ*(2:ℕ)) = N^(1+(2*σ-1)) := by congr 1; push_cast; ring
      _ = _ := by rw [Real.rpow_add hp,Real.rpow_one]
  have hlo := mul_le_mul_of_nonneg_left hb.2.1 hp.le
  have hhi := mul_le_mul_of_nonneg_left hb.2.2.1 hp.le
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (N^σ)]
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨hx.le,by nlinarith [sq_nonneg (N^σ)]⟩

theorem exponentBlockLength_height_lower {N σ τ : ℝ} (hN : 1 ≤ N)
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    (1/2)*N^(min τ (2-2*σ)) ≤
      min (N^τ) (N/(2*(exponentBlockLength N σ:ℝ))) := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hb := exponentBlockLength_bounds hN hσ hσ₁
  have hLp : (0:ℝ) < exponentBlockLength N σ := by exact_mod_cast (show 0 < exponentBlockLength N σ by omega)
  apply le_min
  · have hm := Real.rpow_le_rpow_of_exponent_le hN (min_le_left τ (2-2*σ))
    have hx := Real.rpow_nonneg hp.le (min τ (2-2*σ))
    linarith
  · calc
      _ ≤ (1/2)*N^(2-2*σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (min_le_right τ (2-2*σ))) (by norm_num)
      _ = N/(2*N^(2*σ-1)) := by
        rw [show 2-2*σ = 1-(2*σ-1) by ring,Real.rpow_sub hp,Real.rpow_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left hp.le (by positivity)
        (mul_le_mul_of_nonneg_left hb.2.2.1 (by norm_num))

end TaoTrudgianYang2025

