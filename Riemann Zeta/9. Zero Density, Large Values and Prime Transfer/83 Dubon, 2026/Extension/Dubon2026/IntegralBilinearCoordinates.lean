import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive integral forms in the original basis coordinates

The native matrix equivalence preserves the exact integral form,
symmetry and positivity. These identities let DUB-17 apply finite
sublevel sets to the coordinate columns of the original CM action.
-/

namespace Dubon2026

noncomputable section

open Matrix Module LinearMap.BilinForm

variable {M κ : Type*} [AddCommGroup M] [Fintype κ] [DecidableEq κ]

/-- The Gram-coordinate form is precisely the original form transported by its integral basis. -/
theorem integralBilinForm_coordinates_apply (B : LinearMap.BilinForm ℤ M)
    (b : Basis κ ℤ M) (x y : κ → ℤ) :
    (toMatrix b B).toBilin' x y = B (b.equivFun.symm x) (b.equivFun.symm y) := by
  rw [Matrix.toBilin'_apply', LinearMap.BilinForm.dotProduct_toMatrix_mulVec]

/-- Symmetry is preserved in the actual integral Gram coordinates. -/
theorem integralBilinForm_coordinates_isSymm (B : LinearMap.BilinForm ℤ M)
    (hB : B.IsSymm) (b : Basis κ ℤ M) : (toMatrix b B).toBilin'.IsSymm := by
  apply LinearMap.BilinForm.isSymm_def.mpr
  intro x y
  rw [integralBilinForm_coordinates_apply, integralBilinForm_coordinates_apply]
  exact LinearMap.BilinForm.isSymm_def.mp hB _ _

/-- Positivity is preserved in the actual integral Gram coordinates. -/
theorem integralBilinForm_coordinates_posDef (B : LinearMap.BilinForm ℤ M)
    (hB : B.toQuadraticMap.PosDef) (b : Basis κ ℤ M) :
    (toMatrix b B).toBilin'.toQuadraticMap.PosDef := by
  intro x hx
  change 0 < (toMatrix b B).toBilin' x x
  rw [integralBilinForm_coordinates_apply]
  apply hB
  intro hz
  exact hx (b.equivFun.symm.injective (hz.trans (map_zero _).symm))

end
end Dubon2026
