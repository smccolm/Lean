import Dubon2026.GaloisUnitBaseChangeComposition

/-! # The literal coefficient isomorphism for the scalar-stage field tower

The pinned restriction-composition theorem identifies successive and
direct actions. Its identity-on-values isomorphism is needed to include
the scalar stage's actual class coefficient into the arithmetic colimit.
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

/-- Successive and direct original Galois restrictions are isomorphic by
the identity on every coefficient element. -/
def originalGaloisRestrictionTowerIso :
    Rep.res (AlgEquiv.restrictNormalHom L : Gal(U/K) →* Gal(L/K))
      (Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) A) ≅
    Rep.res (AlgEquiv.restrictNormalHom E : Gal(U/K) →* Gal(E/K)) A where
  hom := Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun σ : Gal(E/K) => A.ρ σ x)
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E L g).symm }
  inv := Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun σ : Gal(E/K) => A.ρ σ x)
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E L g) }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The original tower isomorphism preserves the coefficient value. -/
theorem originalGaloisRestrictionTowerIso_hom_apply (x : A) :
    (originalGaloisRestrictionTowerIso K E L U A).hom.hom x = x := rfl

/-- Its inverse also preserves the same original coefficient value. -/
theorem originalGaloisRestrictionTowerIso_inv_apply (x : A) :
    (originalGaloisRestrictionTowerIso K E L U A).inv.hom x = x := rfl

end
end Dubon2026
