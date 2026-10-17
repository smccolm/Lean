import Dubon2026.OriginalGaloisRestrictionTowerIso
import Dubon2026.OriginalRelationGroupChange

/-! # The actual relation presentation through an original field tower

The identity-on-values coefficient comparison gives a commuting diagram
for the original free relation sequence. This supplies the two tower edges
from DUB-17's enlarged scalar stage to its descended source relation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable (K E L U : Type) [Field K] [Field E] [Field L] [Field U]
  [Algebra K E] [Algebra K L] [Algebra K U]
  [Algebra E L] [Algebra E U] [Algebra L U]
  [IsScalarTower K E L] [IsScalarTower K E U] [IsScalarTower K L U]
  [IsScalarTower E L U] [Normal K E] [Normal K L]
  (A : Rep.{0} ℤ Gal(E/K))

/-- The actual free relation sequence compares along the field tower by
the proved identity-on-values Galois-restriction isomorphisms. -/
def originalGaloisRestrictionTowerDiagram :
    (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(U/K) →* Gal(L/K))).mapShortComplex.obj
      ((Rep.resFunctor (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))).mapShortComplex.obj
        (originalRelationShortComplex A)) ⟶
    (Rep.resFunctor (AlgEquiv.restrictNormalHom E : Gal(U/K) →* Gal(E/K))).mapShortComplex.obj
      (originalRelationShortComplex A) where
  τ₁ := (originalGaloisRestrictionTowerIso K E L U (originalRelationModule A)).hom
  τ₂ := (originalGaloisRestrictionTowerIso K E L U (Rep.free ℤ Gal(E/K) A)).hom
  τ₃ := (originalGaloisRestrictionTowerIso K E L U A).hom
  comm₁₂ := rfl
  comm₂₃ := rfl

/-- The canonical relation map followed by the literal tower comparison
maps the larger field's relation presentation to the original one. -/
def originalGaloisRelationTowerMap :
    (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(U/K) →* Gal(L/K))).mapShortComplex.obj
      (originalRelationShortComplex
        (Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) A)) ⟶
    (Rep.resFunctor (AlgEquiv.restrictNormalHom E : Gal(U/K) →* Gal(E/K))).mapShortComplex.obj
      (originalRelationShortComplex A) :=
  (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(U/K) →* Gal(L/K))).mapShortComplex.map
      (originalRelationGroupChangeSequenceMap (AlgEquiv.restrictNormalHom E) A) ≫
    originalGaloisRestrictionTowerDiagram K E L U A

end
end Dubon2026
