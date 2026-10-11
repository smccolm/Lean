import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The actual invariant line of a triangular two-dimensional action -/

namespace Dubon2026
open Matrix

variable {G R : Type*} [CommRing R]

/-- When an original matrix family fixes the first axis and a genuine unit entry detects its nontrivial second column, its entire original invariant module consists precisely of the first axis. -/
theorem matrixTwo_fixed_iff_second_zero
    (A : G → Matrix (Fin 2) (Fin 2) R)
    (hfirst : ∀ g, A g 0 0 = 1 ∧ A g 1 0 = 0)
    (g₀ : G) (hunit : IsUnit (A g₀ 0 1) ∨ IsUnit (A g₀ 1 1 - 1))
    (v : Fin 2 → R) :
    (∀ g, A g *ᵥ v = v) ↔ v 1 = 0 := by
  constructor
  · intro hv
    have hzero := congrFun (hv g₀) 0
    have hone := congrFun (hv g₀) 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      (hfirst g₀).1, (hfirst g₀).2, one_mul, zero_mul, zero_add] at hzero hone
    rcases hunit with h | h
    · apply h.mul_right_inj.mp
      simpa only [mul_zero] using
        (add_left_cancel (hzero.trans (add_zero (v 0)).symm))
    · apply h.mul_right_inj.mp
      simp only [sub_mul, one_mul, hone, sub_self, mul_zero]
  · intro hv g
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv,
        (hfirst g).1, (hfirst g).2]

end Dubon2026
