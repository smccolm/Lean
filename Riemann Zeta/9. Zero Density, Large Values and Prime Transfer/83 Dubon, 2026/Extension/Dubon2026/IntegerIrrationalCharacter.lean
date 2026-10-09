import Dubon2026.IrrationalRotationCharacter

/-! # Separation of all original integer rotation weights at the same irrational angle -/

namespace Dubon2026

noncomputable section

/-- The actual integer-weight rotation character at the original angle pi sqrt(2). -/
def integerIrrationalCharacter (k : ℤ) : ℂ :=
  Complex.exp (((Real.pi * Real.sqrt 2 : ℝ) : ℂ) * (Complex.I * (k : ℂ)))

/-- All original integer weights, positive or negative, have distinct actual irrational-angle characters. -/
theorem integerIrrationalCharacter_injective : Function.Injective integerIrrationalCharacter := by
  intro m n he
  obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hi := congrArg Complex.im hz
  norm_num [Complex.mul_re, Complex.mul_im] at hi
  have hp : Real.pi * (Real.sqrt 2 * ((m : ℝ) - (n : ℝ)) - 2 * z) = 0 := by
    linear_combination hi
  have hr : Real.sqrt 2 * ((m : ℝ) - (n : ℝ)) = 2 * z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left Real.pi_pos.ne')
  by_contra hmn
  have hir := irrational_sqrt_two.mul_intCast (sub_ne_zero.mpr hmn)
  apply hir.ne_int (2 * z)
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using hr

/-- The original raising eigenvalue is precisely its genuine integer weight's irrational character. -/
theorem irrationalRotationCharacter_integer (k : ℤ) (n : ℕ) :
    irrationalRotationCharacter k n = integerIrrationalCharacter (k + 2 * (n : ℤ)) := by
  simp only [irrationalRotationCharacter, integerIrrationalCharacter, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]

/-- Reflection reverses the actual integer character of every original raising vector. -/
theorem irrationalRotationCharacter_negative (k : ℤ) (n : ℕ) :
    Complex.exp (((-(Real.pi * Real.sqrt 2) : ℝ) : ℂ) * (Complex.I * ((k : ℂ) + 2 * n))) =
      integerIrrationalCharacter (-(k + 2 * (n : ℤ))) := by
  unfold integerIrrationalCharacter
  congr 1
  push_cast
  ring

end
end Dubon2026
