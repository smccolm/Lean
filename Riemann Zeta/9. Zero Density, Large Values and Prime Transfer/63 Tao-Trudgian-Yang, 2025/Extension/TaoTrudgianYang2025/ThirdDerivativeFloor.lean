import TaoTrudgianYang2025.SecondDerivativeScale
import Mathlib.Algebra.Order.Floor.Semiring

/-! A positive integral shift at the physical cube-root scale. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_floor_shift {R μ : ℝ} (N : ℕ)
    (hR : 1 ≤ R) (hRN : R ≤ N) (hμ : 0 < μ) (hscale : R^3*μ = 1) :
    0 < ⌊R⌋₊ ∧ ⌊R⌋₊ ≤ N ∧
      R/2 ≤ (⌊R⌋₊:ℝ) ∧ (⌊R⌋₊:ℝ) ≤ R ∧ (⌊R⌋₊:ℝ)*μ ≤ 1 := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hpos : 0 < ⌊R⌋₊ := Nat.floor_pos.mpr hR
  have hfloor := Nat.floor_le hRp.le
  have hnear : R < (⌊R⌋₊:ℝ)+1 := Nat.lt_floor_add_one R
  have hfloor1 : (1:ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hpos
  have hRcube : R ≤ R^3 := by nlinarith [sq_nonneg (R-1)]
  have hscale1 : R*μ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hRcube hμ.le]
  exact ⟨hpos,Nat.floor_le_of_le hRN,by linarith,hfloor,
    (mul_le_mul_of_nonneg_right hfloor hμ.le).trans hscale1⟩

end TaoTrudgianYang2025
