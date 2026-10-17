import Dubon2026.OriginalIdeleClassH2Restriction
import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Preserve actual class H2 under the fixed field's degree-one realization

The image of the actual Sylow fixed field has relative degree one over
that field. Every original automorphism therefore fixes the image base.
The existing group-change theorem makes its class H2 restriction an
isomorphism, preserving the obstruction in DUB-17's normalization route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

/-- Changing the fixed field through its actual degree-one algebra leaves
the original field automorphisms unchanged, with no surjectivity premise. -/
theorem galoisTowerBaseRestriction_bijective_of_degree_one
    (hd : Module.finrank K E = 1) :
    Function.Bijective (galoisTowerBaseRestriction K E L) := by
  have hs := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd).2
  constructor
  · intro σ τ h
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun g : Gal(L/K) => g x) h
  · intro σ
    let τ : Gal(L/E) := {
      __ := σ.toRingEquiv
      commutes' := by
        intro x
        obtain ⟨z, rfl⟩ := hs x
        rw [← IsScalarTower.algebraMap_apply K E L]
        exact σ.commutes z }
    exact ⟨τ, by ext x; rfl⟩

/-- Actual original class H2 is unchanged by the fixed field's degree-one
realization; its map is precisely the original base-restriction map. -/
theorem originalIdeleClassTowerH2Restriction_isIso_of_degree_one [NumberField L]
    (hd : Module.finrank K E = 1) :
    IsIso (originalIdeleClassTowerH2Restriction K E L) := by
  let e := MulEquiv.ofBijective (galoisTowerBaseRestriction K E L)
    (galoisTowerBaseRestriction_bijective_of_degree_one K E L hd)
  exact originalGroupChangeCohomology_isIso (originalIdeleClassRep K L)
    (originalIdeleClassRep E L) e (originalIdeleClassTowerRestrictionCoefficient K E L).hom 2

end
end Dubon2026
