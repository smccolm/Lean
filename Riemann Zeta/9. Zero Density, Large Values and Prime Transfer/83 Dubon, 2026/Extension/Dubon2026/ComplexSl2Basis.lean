import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # The actual complex traceless matrix Lie algebra and its original half-diagonal basis -/

namespace Dubon2026

noncomputable section

/-- The genuine complex traceless two-by-two matrix Lie algebra. -/
abbrev ComplexSl2 := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

/-- The actual half-diagonal matrix, matching the original geodesic parameter. -/
def complexSl2A : ComplexSl2 := ⟨!![(1 / 2 : ℂ), 0; 0, -(1 / 2)], by
  change Matrix.trace (_ : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace, Fin.sum_univ_two]⟩

/-- The actual upper elementary matrix. -/
def complexSl2U : ComplexSl2 := ⟨!![(0 : ℂ), 1; 0, 0], by
  change Matrix.trace (_ : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace, Fin.sum_univ_two]⟩

/-- The actual lower elementary matrix. -/
def complexSl2F : ComplexSl2 := ⟨!![(0 : ℂ), 0; 1, 0], by
  change Matrix.trace (_ : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace, Fin.sum_univ_two]⟩

/-- Every genuine traceless complex matrix has its exact three-coordinate decomposition. -/
theorem complexSl2_decomposition (x : ComplexSl2) :
    x = (2 * x.val 0 0) • complexSl2A + x.val 0 1 • complexSl2U + x.val 1 0 • complexSl2F := by
  have ht : x.val 0 0 + x.val 1 1 = 0 := by
    have he : Matrix.trace x.val = 0 := x.property
    simpa only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] using he
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexSl2A, complexSl2U, complexSl2F]
  · ring
  · linear_combination ht

/-- The original half-diagonal and upper matrices have precisely the upper bracket. -/
theorem complexSl2_bracket_A_U : ⁅complexSl2A, complexSl2U⁆ = complexSl2U := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LieRing.of_associative_ring_bracket, complexSl2A, complexSl2U,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The original half-diagonal and lower matrices have precisely minus the lower bracket. -/
theorem complexSl2_bracket_A_F : ⁅complexSl2A, complexSl2F⁆ = -complexSl2F := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LieRing.of_associative_ring_bracket, complexSl2A, complexSl2F,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual upper/lower matrix bracket is twice the actual half-diagonal matrix. -/
theorem complexSl2_bracket_U_F : ⁅complexSl2U, complexSl2F⁆ = complexSl2A + complexSl2A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LieRing.of_associative_ring_bracket, complexSl2A, complexSl2U, complexSl2F,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual complex traceless matrix obtained from a real determinant-one tangent's three independent entries. -/
def complexSl2OfRealTangent (a b d : ℝ) : ComplexSl2 := ⟨!![(a : ℂ), (d : ℂ); (b : ℂ), -(a : ℂ)], by
  change Matrix.trace (_ : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace, Fin.sum_univ_two]⟩

end
end Dubon2026
