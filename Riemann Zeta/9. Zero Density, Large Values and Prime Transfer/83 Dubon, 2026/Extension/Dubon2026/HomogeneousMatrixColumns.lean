import Dubon2026.HomogeneousSymmetricMatrix

/-! The existing symmetric-power matrix columns are exactly the original
binary polynomial substitutions. This is the entry bridge required to
transport the determinant polynomial identity to those literal matrices
in the DUB-17 polarization construction. -/

namespace Dubon2026
open MvPolynomial Matrix Module
noncomputable section

variable {R : Type*} [CommRing R]

/-- Each original homogeneous matrix column gives the exact substituted binary basis polynomial. -/
theorem homogeneousSymmetricGL_column_polynomial (n : ℕ) (g : GeneralLinearGroup (Fin 2) R)
    (j : Fin (n + 1)) :
    matrixPolynomialAction g.val (binaryHomogeneousMonomialBasis n j).val =
      ∑ i, (homogeneousSymmetricGL n g).val i j • (binaryHomogeneousMonomialBasis n i).val := by
  have he : (homogeneousGLRepresentation n g) (binaryHomogeneousMonomialBasis n j) =
      ∑ i, (homogeneousSymmetricGL n g).val i j • binaryHomogeneousMonomialBasis n i := by
    rw [homogeneousSymmetricGL_val]
    simpa only [LinearMap.toMatrix_apply] using
      ((binaryHomogeneousMonomialBasis n).sum_repr
        ((homogeneousGLRepresentation n g) (binaryHomogeneousMonomialBasis n j))).symm
  have h := congrArg (fun v : homogeneousSubmodule (Fin 2) R n => v.val) he
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using h

end
end Dubon2026
