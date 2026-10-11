import Dubon2026.TraceZeroAdjointRepresentation
import Dubon2026.CoefficientCharacterTwist

/-! # Exact restriction identities for the original adjoint coefficient actions -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G H ι R : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Restricting the original full adjoint action agrees with conjugation by the
restricted matrices. The inverse is compared using the actual group homomorphism. -/
theorem matrixAdjointRepresentation_comp
    (ρ : G →* GeneralLinearGroup ι R) (j : H →* G) :
    (matrixAdjointRepresentation ρ).comp j = matrixAdjointRepresentation (ρ.comp j) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro X
  change (ρ (j h)).val * X * (ρ ((j h)⁻¹)).val =
    (ρ (j h)).val * X * (ρ (j h⁻¹)).val
  exact congrArg (fun y => (ρ (j h)).val * X * (ρ y).val) (j.map_inv h).symm

/-- The same restriction identity holds in the actual trace-zero submodule,
retaining the original matrices and their trace-zero membership. -/
theorem matrixTraceZeroAdjointRepresentation_comp
    (ρ : G →* GeneralLinearGroup ι R) (j : H →* G) :
    (matrixTraceZeroAdjointRepresentation ρ).comp j =
      matrixTraceZeroAdjointRepresentation (ρ.comp j) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact DFunLike.congr_fun
    (DFunLike.congr_fun (matrixAdjointRepresentation_comp ρ j) h) X.val

/-- Scalar twisting commutes with restriction of both the original action and
the original character. This is the literal composition identity. -/
theorem coefficientCharacterTwist_comp
    {V : Type} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (χ : G →* R) (j : H →* G) :
    (coefficientCharacterTwist ρ χ).comp j =
      coefficientCharacterTwist (ρ.comp j) (χ.comp j) := by
  rfl

end
end Dubon2026
