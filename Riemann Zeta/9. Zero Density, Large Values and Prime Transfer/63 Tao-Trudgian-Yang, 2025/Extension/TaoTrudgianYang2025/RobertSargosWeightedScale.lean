import TaoTrudgianYang2025.RobertSargosWeightedFiberCount

/-! Explicit scale conversion for the weighted displacement sum. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_weighted_sum_scale
    {Q B ε A : ℝ} (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (hε : 0 < ε) (hA : 0 ≤ A) :
    2*(1+2/ε)*(4*Q+1)*(2*B+1)*(⌊9*Q⌋₊:ℝ)^ε*((⌊9*Q⌋₊:ℝ)+A) ≤
      (180*(1+2/ε)*(9:ℝ)^ε)*Q^ε*Q*(1+B)*(Q+A) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hN : (⌊9*Q⌋₊:ℝ) ≤ 9*Q := Nat.floor_le (by positivity)
  have hpow : (⌊9*Q⌋₊:ℝ)^ε ≤ (9*Q)^ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hN hε.le
  have hprod : (4*Q+1)*(2*B+1) ≤ (5*Q)*(2*(1+B)) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hlast : (⌊9*Q⌋₊:ℝ)+A ≤ 9*(Q+A) := by linarith
  have hall := mul_le_mul
    (mul_le_mul hprod hpow (by positivity) (by positivity))
    hlast (by positivity) (by positivity)
  calc
    _ = (2*(1+2/ε))*(((4*Q+1)*(2*B+1))*(⌊9*Q⌋₊:ℝ)^ε*
        ((⌊9*Q⌋₊:ℝ)+A)) := by ring
    _ ≤ (2*(1+2/ε))*(((5*Q)*(2*(1+B)))*(9*Q)^ε*(9*(Q+A))) :=
      mul_le_mul_of_nonneg_left hall (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 9) hQ0]
      ring

end TaoTrudgianYang2025

