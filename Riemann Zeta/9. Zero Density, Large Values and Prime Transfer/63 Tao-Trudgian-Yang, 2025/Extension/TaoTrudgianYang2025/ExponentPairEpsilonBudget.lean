import TaoTrudgianYang2025.ExponentPairOptimizationScale

/-! Explicit epsilon budgets for the A-process output exponents. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem aProcess_first_exponent_loss {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 ≤ ε) :
    (k+ε)/(k+ε+1) ≤ k/(k+1)+ε := by
  have hd₁ : 0 < k+1 := by linarith
  have hd₂ : 0 < k+ε+1 := by linarith
  have hprod : 1 ≤ (k+1)*(k+ε+1) := by nlinarith
  have heq : (k+ε)/(k+ε+1) = k/(k+1)+ε/((k+1)*(k+ε+1)) := by
    field_simp
    ring
  rw [heq]
  exact add_le_add le_rfl (div_le_self hε hprod)

theorem aProcess_second_exponent_loss {k l ε : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hε : 0 ≤ ε) :
    (l+ε)/(k+ε+1) ≤ l/(k+1)+ε := by
  have hd₁ : 0 < k+1 := by linarith
  calc
    _ ≤ (l+ε)/(k+1) :=
      div_le_div_of_nonneg_left (by linarith) hd₁ (by linarith)
    _ = l/(k+1)+ε/(k+1) := by ring
    _ ≤ _ := add_le_add le_rfl (div_le_self hε (by linarith))

theorem one_add_log_le_rpow_budget {N ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) :
    1+Real.log N ≤ (1+1/ε)*N^ε := by
  have hp := Real.one_le_rpow hN hε.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hN) hε
  ring_nf at hl ⊢
  linarith

theorem aProcess_power_budget {k l ε U N : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hε : 0 < ε) (hU : 1 ≤ U) (hN : 1 ≤ N) :
    U^((k+ε)/(k+ε+1))*N^(1+(l+ε)/(k+ε+1))*(1+Real.log N) ≤
      (1+1/ε)*(U^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε))^2 := by
  have hUp := zero_lt_one.trans_le hU
  have hNp := zero_lt_one.trans_le hN
  have hp₁ := Real.rpow_le_rpow_of_exponent_le hU
    ((aProcess_first_exponent_loss hk hε.le).trans
      (show k/(k+1)+ε ≤ k/(k+1)+2*ε by linarith))
  have hp₂ := Real.rpow_le_rpow_of_exponent_le hN
    (add_le_add (le_refl (1 : ℝ)) (aProcess_second_exponent_loss hk hl hε.le))
  have hlog := one_add_log_le_rpow_budget hN hε
  have hlogpos : 0 ≤ 1+Real.log N := by have := Real.log_nonneg hN; linarith
  have heq : U^(k/(k+1)+2*ε)*N^(1+(l/(k+1)+ε))*((1+1/ε)*N^ε) =
      (1+1/ε)*(U^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε))^2 := by
    rw [mul_pow,← Real.rpow_mul_natCast hUp.le,← Real.rpow_mul_natCast hNp.le]
    have h₁ : (k/(2*k+2)+ε)*(2 : ℝ) = k/(k+1)+2*ε := by
      field_simp
    have h₂ : (l/(2*k+2)+1/2+ε)*(2 : ℝ) = 1+(l/(k+1)+ε)+ε := by
      field_simp
      ring
    simp only [Nat.cast_ofNat]
    rw [h₁,h₂,Real.rpow_add hNp (1+(l/(k+1)+ε)) ε]
    ring
  calc
    _ ≤ (U^(k/(k+1)+2*ε)*N^(1+(l/(k+1)+ε)))*((1+1/ε)*N^ε) :=
      mul_le_mul (mul_le_mul hp₁ hp₂ (by positivity) (by positivity)) hlog hlogpos (by positivity)
    _ = _ := heq

end TaoTrudgianYang2025
