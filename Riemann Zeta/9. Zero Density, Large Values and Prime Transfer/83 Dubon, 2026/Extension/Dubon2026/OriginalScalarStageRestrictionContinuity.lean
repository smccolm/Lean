import Dubon2026.OriginalUnramifiedStageInUnion
import Dubon2026.GaloisUnitBaseChangeContinuity

/-! # Continuity of the actual scalar-stage Galois restriction

The existing embedded-normal-field continuity theorem applies to the
original inclusion in the arithmetic union. The original Krull topology
on the infinite Galois group is retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Retain the displayed rational structure of the arithmetic union. -/
local instance scalarStageRestrictionUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the displayed rational structure of each original stage. -/
local instance scalarStageRestrictionFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Restriction from the original arithmetic Galois group to the actual
enlarged scalar stage is continuous for the original Krull topologies. -/
theorem originalScalarStageRestriction_continuous
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a) :
    letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
    letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
    Continuous (AlgEquiv.restrictNormalHom L.val :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(L.val/ℚ)) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  let e : L.val →ₐ[ℚ] U := IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)
  letI : Algebra L.val U := e.toAlgebra
  letI : IsScalarTower ℚ L.val U := IsScalarTower.of_algHom e
  let π : Gal(U/ℚ) →* Gal(L.val/ℚ) := AlgEquiv.restrictNormalHom L.val
  have heq : π = embeddedNormalGaloisRestriction (F := ℚ) e :=
    embeddedNormalGaloisRestriction_unique e π (fun g x => g.restrictNormal_commutes L.val x)
  change Continuous π
  rw [heq]
  exact embeddedNormalGaloisRestriction_continuous e

end
end Dubon2026
