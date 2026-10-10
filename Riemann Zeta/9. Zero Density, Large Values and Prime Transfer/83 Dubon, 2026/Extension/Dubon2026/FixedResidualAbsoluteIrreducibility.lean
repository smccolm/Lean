import Dubon2026.OriginalResidualFramedFibers
import Dubon2026.MatrixAdjointScalarDescent
import Dubon2026.RepresentationIrreducibilityFromRestriction

/-! # Original absolute residual irreducibility for the genuine fixed-residual quotient -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L]

/-- The actual fixed-residual quotient representation has the same original irreducible scalar extension: its restriction to the original group is literally the given residual representation. -/
theorem fixedResidualOriginalRepresentation_absoluteIrreducible
    (p : ℕ) (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)) := by
  let N := fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)
  let q := QuotientGroup.mk' N
  let τ := matrixStandardRepresentation (matrixCoefficientExtension (L := L)
    (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
  have heq : τ.comp q = matrixStandardRepresentation (matrixCoefficientExtension (L := L) σ) := by
    apply MonoidHom.ext
    intro g
    rfl
  letI : Representation.IsIrreducible (τ.comp q) := by
    rw [heq]
    infer_instance
  exact representation_irreducible_of_restriction q τ

end
end Dubon2026
