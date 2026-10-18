import Dubon2026.OriginalRelationObstructionGroupChange
import Dubon2026.OriginalGroupChangeCohomologyIsomorphism

/-! Transfer the zero relation obstruction across the actual group
isomorphism between a constructed original arithmetic field and its image
in the unramified union. DUB-17 needs this between the rational Cartier
total criterion and the already proved original-field extension criterion.
Surjectivity on H1 is derived from the original cochain isomorphism. -/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A genuine group isomorphism carries a zero original relation
obstruction through the canonical relation map and any coefficient map.
No surjectivity hypothesis on cohomology is supplied. -/
theorem originalRelationExtensionObstruction_zero_of_groupEquiv
    {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (B C : Rep.{0} ℤ H) (D : Rep.{0} ℤ G)
    (φ : originalRelationModule B ⟶ C) (j : Rep.res e.toMonoidHom C ⟶ D)
    (hφ : originalRelationExtensionObstruction B C φ = 0) :
    originalRelationExtensionObstruction (Rep.res e.toMonoidHom B) D
      (originalRelationGroupChange e.toMonoidHom B ≫ (Rep.resFunctor e.toMonoidHom).map φ ≫ j) = 0 := by
  let f := groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom B)) 1
  haveI : IsIso f := originalGroupChangeCohomology_isIso B (Rep.res e.toMonoidHom B)
    e (𝟙 (Rep.res e.toMonoidHom B)) 1
  apply (cancel_epi f).mp
  change groupCohomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom B)) 1 ≫ _ = _
  rw [originalRelationExtensionObstruction_groupChange, hφ, Limits.zero_comp, Limits.comp_zero]

end
end Dubon2026
