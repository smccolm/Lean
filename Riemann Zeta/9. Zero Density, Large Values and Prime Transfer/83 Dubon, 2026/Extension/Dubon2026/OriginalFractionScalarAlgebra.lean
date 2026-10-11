import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual scalar extension from the original fraction field -/

namespace Dubon2026
noncomputable section

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [FaithfulSMul R L]

/-- The genuine fraction-field embedding induced by the injective original
coefficient map, retaining the original base field rather than a renamed copy. -/
@[reducible]
def originalFractionScalarAlgebra : Algebra K L :=
  (IsFractionRing.lift (K := K) (g := algebraMap R L)
    (FaithfulSMul.algebraMap_injective R L)).toAlgebra

/-- The induced scalar structure extends the literal original coefficient map. -/
theorem originalFractionScalarAlgebra_tower :
    letI : Algebra K L := originalFractionScalarAlgebra R K L
    IsScalarTower R K L := by
  letI : Algebra K L := originalFractionScalarAlgebra R K L
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (IsFractionRing.lift_algebraMap (K := K)
    (g := algebraMap R L) (FaithfulSMul.algebraMap_injective R L) x).symm

end
end Dubon2026
