import Dubon2026.PolarizedRelationMatrix

/-! The actual defining polarized relations specialize along the original
coefficient homomorphisms. This is the kernel criterion required for the
source-compatible quotient of the existing framed matrix ring in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]

/-- The exact original relation matrix commutes with coefficient change. -/
theorem polarizedRelationMatrix_map (f : R →+* A)
    (M : GeneralLinearGroup (ι ⊕ ι) R) (z : Multiplicative (ZMod 2)) (u : Rˣ) :
    (polarizedRelationMatrix M z u).map f =
      polarizedRelationMatrix (GeneralLinearGroup.map f M) z (Units.map f.toMonoidHom u) := by
  have hu : Units.map f.toMonoidHom u * (polarizedComponentSign (R := A) z)⁻¹ =
      Units.map f.toMonoidHom (u * (polarizedComponentSign (R := R) z)⁻¹) := by
    rw [map_mul, map_inv, polarizedComponentSign_map]
  unfold polarizedRelationMatrix
  rw [← polarizedComponentNormalization_map, hu]
  ext i j
  cases i <;> cases j <;>
    simp [GeneralLinearGroup.map, Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      map_sum, apply_ite f]

end Dubon2026
