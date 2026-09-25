import TaoTrudgianYang2025.ThirdDerivativeRpowScale
import Mathlib.Algebra.Order.Floor.Semiring

/-! The initial differencing parameter at the physical two-thirteenths scale. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_physical_shift_scale {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192) :
    4 ≤ lam^(-(2:ℝ)/13) := by
  have he : (1/8192:ℝ) = (2:ℝ)^(-(13:ℝ)) := by norm_num
  have hb := Real.rpow_le_rpow_of_nonpos hlam hsmall
    (show -(2:ℝ)/13 ≤ 0 by norm_num)
  rw [he,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at hb
  norm_num at hb
  simpa only [neg_div] using hb

theorem robertSargos_physical_floor_shift
    (M : ℕ) {lam : ℝ} (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) :
    2 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ ∧
      ⌊lam^(-(2:ℝ)/13)⌋₊ ≤ M ∧
      lam^(-(2:ℝ)/13)/2 ≤ (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ) ∧
      (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ) ≤ lam^(-(2:ℝ)/13) := by
  have hR := robertSargos_physical_shift_scale hlam hsmall
  have hRp : 0 < lam^(-(2:ℝ)/13) := by positivity
  have htwo : 2 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ :=
    Nat.le_floor (by norm_num; linarith)
  have hfloor := Nat.floor_le hRp.le
  have hnear := Nat.lt_floor_add_one (lam^(-(2:ℝ)/13))
  have hfloor1 : (1:ℝ) ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ := by
    exact_mod_cast (show 1 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ by omega)
  have hRM := (Real.rpow_le_rpow_of_exponent_ge hlam
    (show lam ≤ 1 by linarith) (show -(8:ℝ)/13 ≤ -(2:ℝ)/13 by norm_num)).trans hM
  exact ⟨htwo,Nat.floor_le_of_le hRM,by linarith,hfloor⟩

end TaoTrudgianYang2025
