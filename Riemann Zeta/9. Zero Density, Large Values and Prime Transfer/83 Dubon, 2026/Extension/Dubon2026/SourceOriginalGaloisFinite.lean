import Dubon2026.SourceOriginalGaloisClosure
import Dubon2026.SourceOriginalEssentialFiniteType

/-! DUB-17/18 -> global residue identity -> auxiliary Galois averaging.
The literal normal closure remains a finite extension of the original field,
is essentially of finite type over the original constants, and retains the
same transcendental j-coordinate. These derived properties feed the existing
finite-coordinate local geometry; no new curve package is postulated.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The native inclusion of the original field into its literal normal closure. -/
instance originalGaloisClosureOriginalAlgebra :
    Algebra (modularFunctionFieldOver N L) (originalGaloisClosure N L) :=
  normalClosure.algebra (IntermediateField.adjoin L {jOver N L})
    (modularFunctionFieldOver N L) (AlgebraicClosure (modularFunctionFieldOver N L))

/-- The constant action obtained by composing the actual field inclusions. -/
instance originalGaloisClosureConstantsAlgebra : Algebra L (originalGaloisClosure N L) :=
  ((algebraMap (modularFunctionFieldOver N L) (originalGaloisClosure N L)).comp
    (algebraMap L (modularFunctionFieldOver N L))).toAlgebra

instance originalGaloisClosureConstantsTower :
    IsScalarTower L (modularFunctionFieldOver N L) (originalGaloisClosure N L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The module structure induced by the same native original-field inclusion. -/
local instance originalGaloisClosureOriginalModule :
    Module (modularFunctionFieldOver N L) (originalGaloisClosure N L) :=
  @Algebra.toModule (modularFunctionFieldOver N L) (originalGaloisClosure N L) _ _
    (originalGaloisClosureOriginalAlgebra N L)

theorem finite_originalGaloisClosure_over_original :
    FiniteDimensional (modularFunctionFieldOver N L) (originalGaloisClosure N L) := by
  haveI := finite_originalGaloisClosure_over_j N L
  exact Module.Finite.of_restrictScalars_finite
    (IntermediateField.adjoin L {jOver N L}) (modularFunctionFieldOver N L) _

theorem essFiniteType_originalGaloisClosure :
    Algebra.EssFiniteType L (originalGaloisClosure N L) := by
  haveI := finite_originalGaloisClosure_over_original N L
  haveI := essFiniteType_original N L
  exact Algebra.EssFiniteType.comp L (modularFunctionFieldOver N L) (originalGaloisClosure N L)

omit [NeZero N] in
theorem transcendental_originalGaloisClosure_j :
    Transcendental L (algebraMap (modularFunctionFieldOver N L)
      (originalGaloisClosure N L) (jOver N L)) := by
  exact (transcendental_algebraMap_iff (algebraMap (modularFunctionFieldOver N L)
    (originalGaloisClosure N L)).injective).mpr (transcendental_jOver N L)

end
end Dubon2026.SourceFunctionField
