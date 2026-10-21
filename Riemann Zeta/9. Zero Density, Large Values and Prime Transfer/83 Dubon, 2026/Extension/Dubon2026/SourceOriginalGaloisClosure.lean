import Dubon2026.SourceOriginalDifferentialInjectivity
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! DUB-17/18 -> original regular differential dimension -> global residue
identity -> finite Galois averaging and descent. The auxiliary field is the
literal normal closure of the proved original finite extension over j in
its algebraic closure. Native normal-closure finiteness and characteristic
zero separability supply its Galois property. No normality of the original
modular function field is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The canonical constant-field action on the original rational j-coordinate field. -/
local instance originalClosureJAlgebra :
    Algebra L (IntermediateField.adjoin L {jOver N L}) :=
  (IntermediateField.adjoin L {jOver N L}).toSubalgebra.algebra

/-- The actual normal-closure field inside the algebraic closure of the original field. -/
abbrev originalGaloisClosure :=
  IntermediateField.normalClosure (IntermediateField.adjoin L {jOver N L})
    (modularFunctionFieldOver N L) (AlgebraicClosure (modularFunctionFieldOver N L))

theorem finite_originalGaloisClosure_over_j :
    FiniteDimensional (IntermediateField.adjoin L {jOver N L}) (originalGaloisClosure N L) := by
  haveI := finiteDimensional_original N L
  exact normalClosure.is_finiteDimensional _ _ _

theorem galois_originalGaloisClosure_over_j :
    IsGalois (IntermediateField.adjoin L {jOver N L}) (originalGaloisClosure N L) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero (IntermediateField.adjoin L {jOver N L}) :=
    charZero_of_injective_algebraMap (algebraMap L _).injective
  haveI := finiteDimensional_original N L
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin L {jOver N L})
      (AlgebraicClosure (modularFunctionFieldOver N L)) :=
    Algebra.IsAlgebraic.trans _ (modularFunctionFieldOver N L) _
  haveI : IsAlgClosure (IntermediateField.adjoin L {jOver N L})
      (AlgebraicClosure (modularFunctionFieldOver N L)) := ⟨inferInstance, inferInstance⟩
  exact IsGalois.normalClosure _ _ _

end
end Dubon2026.SourceFunctionField
