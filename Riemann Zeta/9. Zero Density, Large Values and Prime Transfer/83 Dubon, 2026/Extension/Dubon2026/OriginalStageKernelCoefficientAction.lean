import Dubon2026.OriginalGaloisKernelCoefficientTriviality
import Dubon2026.UnramifiedUnionFiniteFieldCriterion

/-! # The original finite-stage inclusions derive kernel-trivial coefficient action

Use the actual intermediate-field inclusions to construct all scalar
towers. Literal field restriction then shows that every coefficient
from the original lower stage is fixed by the middle-stage restriction
kernel. This supplies DUB-17's coefficient-action hypothesis from the
same stage containments already constructed by the norm-root theorem.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

/-- The actual inclusions of original finite Galois stages construct
all tower maps and make the middle-field kernel fix each inflated
lower-stage coefficient. No tower or action comparison is supplied. -/
theorem originalFiniteGaloisStages_kernel_coefficient_trivial
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (P E N : FiniteGaloisIntermediateField K Ω)
    (hPE : P.toIntermediateField ≤ E.toIntermediateField)
    (hEN : E.toIntermediateField ≤ N.toIntermediateField) :
    letI : Algebra P E := (IntermediateField.inclusion hPE).toRingHom.toAlgebra
    letI : Algebra E N := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
    letI : Algebra P N := (IntermediateField.inclusion (hPE.trans hEN)).toRingHom.toAlgebra
    letI : IsScalarTower K P E := IsScalarTower.of_algHom (IntermediateField.inclusion hPE)
    letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
    letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion (hPE.trans hEN))
    ∀ (B : Rep ℤ Gal(P/K))
      (g : (AlgEquiv.restrictNormalHom E : Gal(N/K) →* Gal(E/K)).ker)
      (b : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B),
      (Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B).ρ g.val b = b := by
  letI : Algebra P E := (IntermediateField.inclusion hPE).toRingHom.toAlgebra
  letI : Algebra E N := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
  letI : Algebra P N := (IntermediateField.inclusion (hPE.trans hEN)).toRingHom.toAlgebra
  letI : IsScalarTower K P E := IsScalarTower.of_algHom (IntermediateField.inclusion hPE)
  letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion (hPE.trans hEN))
  letI : IsScalarTower P E N := IsScalarTower.of_algebraMap_eq' rfl
  exact originalGaloisTowerKernel_coefficient_trivial K P E N

end
end Dubon2026
