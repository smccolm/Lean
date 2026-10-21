import Dubon2026.SourcePeriodBinaryDiagonal
import Dubon2026.SourceHeckeCoefficientMorphism

/-! The coefficient comparison at the actual Hecke diagonal.
DUB-17/18 -> residual modular Galois association -> the original column
binary H1 eigenclass. The explicit binomial comparison and the existing
monomial diagonal formula prove agreement with the exact adjugate action.
-/

namespace Dubon2026
noncomputable section
open Matrix MvPolynomial SourceModularSymbols

private theorem adjugateDiagonalMatrix (p : ℕ) :
    (((integralTriangularMatrix 1 p 0).adjugate).map (Int.castRingHom ℂ))ᵀ =
      Matrix.diagonal ![(p : ℂ), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTriangularMatrix, Matrix.adjugate_fin_two]

/-- The original integral adjugate diagonal is precisely column substitution by diag(p,1). -/
theorem sourceHeckeAdjugate_eq_columnDiagonal (w p : ℕ) :
    sourceModularBinaryFormAdjugateRep ℂ w (integralTriangularMatrix 1 p 0) =
      homogeneousMatrixAction w (Matrix.diagonal ![(p : ℂ), 1]) := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  change matrixPolynomialAction
    (((integralTriangularMatrix 1 p 0).adjugate).map (Int.castRingHom ℂ))ᵀ P.val =
      matrixPolynomialAction (Matrix.diagonal ![(p : ℂ), 1]) P.val
  exact congrArg (fun A => matrixPolynomialAction A P.val) (adjugateDiagonalMatrix p)

/-- The original dual Hecke diagonal has the exact native diagonal matrix in the dual monomial basis. -/
theorem sourceHeckeDualDiagonal_toMatrix (w p : ℕ) :
    LinearMap.toMatrix (binaryHomogeneousMonomialBasis (R := ℂ) w).dualBasis
      (binaryHomogeneousMonomialBasis w).dualBasis (sourceHeckeDualDiagonal w p) =
        Matrix.diagonal (fun i : Fin (w + 1) => (p : ℂ) ^ i.val) := by
  rw [sourceHeckeDualDiagonal, LinearMap.toMatrix_transpose,
    sourceHeckeAdjugate_eq_columnDiagonal, homogeneousDiagonal_toMatrix]
  simp

/-- The actual original coefficient equivalence respects the literal column-binary Hecke diagonal. -/
theorem sourcePeriodBinaryEquiv_heckeDiagonal (w p : ℕ) (hw : (w.factorial : ℂ) ≠ 0) :
    (sourcePeriodBinaryEquiv w hw).toLinearMap.comp (sourceHeckeDualDiagonal w p) =
      (homogeneousMatrixAction w (Matrix.diagonal ![(p : ℂ), 1])).comp
        (sourcePeriodBinaryEquiv w hw).toLinearMap := by
  apply (LinearMap.toMatrix (binaryHomogeneousMonomialBasis (R := ℂ) w).dualBasis
    (binaryHomogeneousMonomialBasis w)).injective
  rw [LinearMap.toMatrix_comp _ (binaryHomogeneousMonomialBasis w).dualBasis,
    LinearMap.toMatrix_comp _ (binaryHomogeneousMonomialBasis w),
    sourcePeriodBinaryEquiv_toMatrix, sourceHeckeDualDiagonal_toMatrix,
    homogeneousDiagonal_toMatrix, sourcePeriodBinaryIntertwiner_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [mul_comm]

end
end Dubon2026
