import Dubon2026.ComplexSl2Basis
import Mathlib.Algebra.Lie.Sl2

/-! # The actual compact-weight sl2 basis of traceless complex matrices -/

namespace Dubon2026

noncomputable section

/-- The original compact Cartan matrix, minus i times the actual rotation tangent. -/
def compactSl2H : ComplexSl2 := (-Complex.I) • (complexSl2U - complexSl2F)

/-- The actual raising matrix for the original compact weights. -/
def compactSl2E : ComplexSl2 := complexSl2A + (Complex.I / 2) • (complexSl2U + complexSl2F)

/-- The actual lowering matrix for the original compact weights. -/
def compactSl2F : ComplexSl2 := complexSl2A - (Complex.I / 2) • (complexSl2U + complexSl2F)

/-- The actual compact Cartan matrix is nonzero. -/
theorem compactSl2H_ne_zero : compactSl2H ≠ 0 := by
  intro he
  have hz := congrArg (fun x : ComplexSl2 => x.val 0 1) he
  simp [compactSl2H, complexSl2U, complexSl2F] at hz

/-- The actual compact-weight raising and lowering matrices have Cartan commutator. -/
theorem compactSl2_bracket_E_F : ⁅compactSl2E, compactSl2F⁆ = compactSl2H := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compactSl2H, compactSl2E, compactSl2F, complexSl2A, complexSl2U, complexSl2F,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- The actual raising matrix has compact weight two. -/
theorem compactSl2_bracket_H_E : ⁅compactSl2H, compactSl2E⁆ = (2 : ℂ) • compactSl2E := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compactSl2H, compactSl2E, complexSl2A, complexSl2U, complexSl2F,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  norm_num [Complex.I_sq]

/-- The actual lowering matrix has compact weight minus two. -/
theorem compactSl2_bracket_H_F : ⁅compactSl2H, compactSl2F⁆ = -((2 : ℂ) • compactSl2F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compactSl2H, compactSl2F, complexSl2A, complexSl2U, complexSl2F,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  norm_num [Complex.I_sq]

/-- These genuine matrices form a literal sl2 triple in the actual complex matrix Lie algebra. -/
theorem compactSl2Triple : IsSl2Triple compactSl2H compactSl2E compactSl2F where
  h_ne_zero := compactSl2H_ne_zero
  lie_e_f := compactSl2_bracket_E_F
  lie_h_e_nsmul := by simpa only [two_smul] using compactSl2_bracket_H_E
  lie_h_f_nsmul := by simpa only [two_smul] using compactSl2_bracket_H_F

/-- The actual lowering matrix is the precise holomorphic derivative combination with the original compact tangent. -/
theorem compactSl2F_holomorphic {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : ComplexSl2 →ₗ[ℂ] W) :
    T compactSl2F = T complexSl2A - Complex.I • T complexSl2U +
      (Complex.I / 2) • T (complexSl2U - complexSl2F) := by
  simp only [compactSl2F, map_sub, map_smul, map_add]
  module

/-- Every actual traceless matrix is the exact linear combination of the genuine compact Cartan, raising and lowering matrices. -/
theorem compactSl2_decomposition (x : ComplexSl2) :
    x = (Complex.I / 2 * (x.val 0 1 - x.val 1 0)) • compactSl2H +
      (x.val 0 0 - Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • compactSl2E +
      (x.val 0 0 + Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • compactSl2F := by
  have ht : x.val 0 0 + x.val 1 1 = 0 := by
    have he : Matrix.trace x.val = 0 := x.property
    simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] using he
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactSl2H, compactSl2E, compactSl2F, complexSl2A, complexSl2U, complexSl2F] <;>
    ring_nf
  · simp [Complex.I_sq]
  · simp [Complex.I_sq]
  · linear_combination ht

end
end Dubon2026
