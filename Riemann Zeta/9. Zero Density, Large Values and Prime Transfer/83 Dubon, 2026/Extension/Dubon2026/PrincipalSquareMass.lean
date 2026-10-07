import Dubon2026.RankinConvolutionEnergy

/-! # The exact positive reciprocal mass of the principal square coefficients -/

namespace Dubon2026

noncomputable section

/-- The actual absolutely convergent reciprocal sum of the square-supported principal weights. -/
def principalSquareMass (Q : ℕ) : ℝ :=
  ∑' n : ℕ, (principalSquareCoefficients Q n).re / (n : ℝ)

/-- The coefficient at one gives a uniform positive lower bound for the genuine reciprocal mass. -/
theorem one_le_principalSquareMass (Q : ℕ) : 1 ≤ principalSquareMass Q := by
  have hh := (principalSquare_reciprocal_summable Q).sum_le_tsum ({1} : Finset ℕ)
    (fun n _ => div_nonneg (principalSquareCoefficients_re_nonneg Q n) (Nat.cast_nonneg n))
  have h1 : principalSquareCoefficients Q 1 = 1 := by
    simpa using principalSquareCoefficients_sq Q 1
  simpa [principalSquareMass, h1] using hh

/-- The reciprocal mass is strictly positive for every level. -/
theorem principalSquareMass_pos (Q : ℕ) : 0 < principalSquareMass Q :=
  lt_of_lt_of_le zero_lt_one (one_le_principalSquareMass Q)

/-- The true reciprocal mass is precisely the real principal-character value at two. -/
theorem principalSquareMass_eq_LFunction (Q : ℕ) [NeZero Q] :
    (principalSquareMass Q : ℂ) = DirichletCharacter.LFunctionTrivChar Q 2 := by
  have hh := principalSquare_LSeries Q (s := 1) (by norm_num)
  rw [mul_one] at hh
  rw [← hh]
  rw [principalSquareMass, Complex.ofReal_tsum, LSeries]
  apply tsum_congr
  intro n
  have he : ((principalSquareCoefficients Q n).re : ℂ) = principalSquareCoefficients Q n :=
    Complex.ext (by simp) (by simp [principalSquareCoefficients_im])
  by_cases hn : n = 0
  · simp [hn, LSeries.term_def]
  · simp [hn, he]

end
end Dubon2026
