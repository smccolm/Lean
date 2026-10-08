import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Real.Irrational

/-! # Distinct actual rotation characters at one genuine irrational angle -/

namespace Dubon2026

noncomputable section

/-- Evaluate the exact weight-k+2n rotation character at the original real angle pi sqrt(2). -/
def irrationalRotationCharacter (k : ℤ) (n : ℕ) : ℂ :=
  Complex.exp (((Real.pi * Real.sqrt 2 : ℝ) : ℂ) * (Complex.I * ((k : ℂ) + 2 * n)))

/-- Each original irrational-angle character has genuine unit modulus. -/
theorem irrationalRotationCharacter_norm (k : ℤ) (n : ℕ) :
    ‖irrationalRotationCharacter k n‖ = 1 := by
  rw [irrationalRotationCharacter, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The literal original rotation eigenvalues are pairwise distinct, by irrationality of sqrt(2). -/
theorem irrationalRotationCharacter_injective (k : ℤ) :
    Function.Injective (irrationalRotationCharacter k) := by
  intro m n he
  obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hi := congrArg Complex.im hz
  norm_num [Complex.mul_re, Complex.mul_im] at hi
  have hp : Real.pi * (Real.sqrt 2 * ((m : ℝ) - (n : ℝ)) - z) = 0 := by
    linear_combination hi / 2
  have hr : Real.sqrt 2 * ((m : ℝ) - (n : ℝ)) = z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left Real.pi_pos.ne')
  by_contra hmn
  have hn : (m : ℤ) - (n : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hir := irrational_sqrt_two.mul_intCast hn
  apply hir.ne_int z
  simpa only [Int.cast_sub, Int.cast_natCast] using hr

end
end Dubon2026
