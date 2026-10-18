import Dubon2026.OriginalRelationFreeGroupEquiv

/-! Descend an extension through the actual group isomorphism between
an original arithmetic stage and its image field. The canonical relation
kernel map is surjective because the already proved free-cover map is
bijective. This preserves the required relation equation on DUB-17's
Cartier-extension-to-S-unit-correction dependency chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G H : Type} [Group G] [Group H] (e : G ≃* H) (B : Rep.{0} ℤ H)

/-- The actual relation kernel map is bijective under the same group isomorphism. -/
theorem originalRelationGroupChange_bijective :
    Function.Bijective (originalRelationGroupChange e.toMonoidHom B).hom := by
  have hp := originalRelationFreeGroupChange_bijective e B
  constructor
  · intro x y h
    apply Subtype.ext
    exact hp.injective (congrArg Subtype.val h)
  · intro r
    obtain ⟨x, hx⟩ := hp.surjective r.val
    have hcover := congrArg (fun m => m.hom x) (originalRelationFreeGroupChange_cover e.toMonoidHom B)
    have hz : (originalRelationFreeCover (Rep.res e.toMonoidHom B)).hom x = 0 :=
      hcover.symm.trans ((congrArg (originalRelationFreeCover B).hom hx).trans r.property)
    exact ⟨⟨x, hz⟩, Subtype.ext hx⟩


end
end Dubon2026
