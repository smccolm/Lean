import TaoTrudgianYang2025.SargosQuarticMaximalMoment
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative control of the literal slow phase on the source interval. -/

noncomputable section

open GafniTao Set

namespace TaoTrudgianYang2025

theorem sargos_character_sub_norm_le (x y : ℝ) :
    ‖fordAdditiveCharacter y-fordAdditiveCharacter x‖ ≤ 2*Real.pi*|y-x| := by
  have he : fordAdditiveCharacter y-fordAdditiveCharacter x =
      fordAdditiveCharacter x*(fordAdditiveCharacter (y-x)-1) := by
    rw [mul_sub,mul_one,← fordAdditiveCharacter_add,show x+(y-x) = y by ring]
  rw [he,norm_mul,sargos_character_norm,one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(y-x))
  have hp : Complex.I*((2*Real.pi*(y-x) : ℝ) : ℂ) =
      2*Real.pi*Complex.I*((y-x : ℝ) : ℂ) := by push_cast; ring
  rw [hp] at h
  simpa only [fordAdditiveCharacter,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi)] using h

theorem sargos_slow_phase_lipschitz {N : ℕ} {K : ℝ} {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N)
    {x y : ℝ} (hx : x ∈ Icc (N : ℝ) (2*N)) (hy : y ∈ Icc (N : ℝ) (2*N)) :
    |φ y-φ x| ≤ K/N*|y-x| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hφ' (convex_Icc _ _) hx hy

theorem sargos_slow_character_adjacent {N : ℕ} {K : ℝ} {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N)
    {j : ℕ} (hj : j+2 ≤ N) :
    ‖fordAdditiveCharacter (φ ((N : ℝ)+(j+1)+1))-
      fordAdditiveCharacter (φ ((N : ℝ)+j+1))‖ ≤ 2*Real.pi*K/N := by
  have hjr : (j : ℝ)+2 ≤ N := by exact_mod_cast hj
  have hx : (N : ℝ)+j+1 ∈ Icc (N : ℝ) (2*N) := by
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hy : (N : ℝ)+(j+1)+1 ∈ Icc (N : ℝ) (2*N) := by
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hp := sargos_slow_phase_lipschitz hφ hφ' hx hy
  have hd : (N : ℝ)+(j+1)+1-((N : ℝ)+j+1) = 1 := by ring
  rw [hd,abs_one,mul_one] at hp
  calc
    _ ≤ 2*Real.pi*|φ ((N : ℝ)+(j+1)+1)-φ ((N : ℝ)+j+1)| :=
      sargos_character_sub_norm_le _ _
    _ ≤ 2*Real.pi*(K/N) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
