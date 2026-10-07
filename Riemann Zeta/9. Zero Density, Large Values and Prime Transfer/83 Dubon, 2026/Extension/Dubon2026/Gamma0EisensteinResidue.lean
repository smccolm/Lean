import Dubon2026.Gamma0EisensteinContinuation

/-! # Positivity of the actual general-level Eisenstein residue -/

namespace Dubon2026

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-- The actual principal-character L-value at two is a real finite Euler product times zeta(2). -/
theorem LFunctionTrivChar_two_real (Q : ℕ) [NeZero Q] :
    DirichletCharacter.LFunctionTrivChar Q 2 =
      (((∏ p ∈ Q.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹)) * (Real.pi ^ 2 / 6) : ℝ) : ℂ) := by
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num), riemannZeta_two]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Complex.cpow_neg, Complex.cpow_ofNat]

/-- Every factor of the actual real Euler product at two is strictly positive. -/
theorem principalCharacter_eulerProduct_two_pos (Q : ℕ) :
    0 < ∏ p ∈ Q.primeFactors, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp1 : 1 < (p : ℝ) ^ 2 := by nlinarith
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

/-- The true principal-character value at two has positive real part. -/
theorem LFunctionTrivChar_two_re_pos (Q : ℕ) [NeZero Q] :
    0 < (DirichletCharacter.LFunctionTrivChar Q 2).re := by
  rw [LFunctionTrivChar_two_real, Complex.ofReal_re]
  exact mul_pos (principalCharacter_eulerProduct_two_pos Q) (by positivity)

/-- The true principal-character value at two has no imaginary part. -/
theorem LFunctionTrivChar_two_im (Q : ℕ) [NeZero Q] :
    (DirichletCharacter.LFunctionTrivChar Q 2).im = 0 := by
  rw [LFunctionTrivChar_two_real, Complex.ofReal_im]

/-- The explicit real residue of the actual primitive Gamma0(Q) Eisenstein continuation. -/
def gamma0EisensteinResidue (Q : ℕ) [NeZero Q] : ℝ :=
  Real.pi * Q.totient / (2 * (Q : ℝ) ^ 2 * (DirichletCharacter.LFunctionTrivChar Q 2).re)

/-- The actual general-level pole residue is strictly positive for every positive level. -/
theorem gamma0EisensteinResidue_pos (Q : ℕ) [NeZero Q] : 0 < gamma0EisensteinResidue Q := by
  unfold gamma0EisensteinResidue
  exact div_pos (mul_pos Real.pi_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_neZero Q))))
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero Q))))
      (LFunctionTrivChar_two_re_pos Q))

/-- The literal Eisenstein residue limit is the coercion of the proved positive real constant. -/
theorem gamma0EisensteinContinuation_residue_pos (Q : ℕ) [NeZero Q] (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * gamma0EisensteinContinuation Q z s)
      (𝓝[≠] 1) (𝓝 (gamma0EisensteinResidue Q : ℂ)) := by
  have he : (gamma0EisensteinResidue Q : ℂ) =
      (Real.pi : ℂ) * Q.totient / (2 * (Q : ℂ) ^ 2 * DirichletCharacter.LFunctionTrivChar Q 2) := by
    have hL : ((DirichletCharacter.LFunctionTrivChar Q 2).re : ℂ) =
        DirichletCharacter.LFunctionTrivChar Q 2 := by
      apply Complex.ext
      · simp
      · simp [LFunctionTrivChar_two_im]
    rw [gamma0EisensteinResidue]
    push_cast
    rw [hL]
  rw [he]
  exact gamma0EisensteinContinuation_residue_one Q z

end
end Dubon2026
