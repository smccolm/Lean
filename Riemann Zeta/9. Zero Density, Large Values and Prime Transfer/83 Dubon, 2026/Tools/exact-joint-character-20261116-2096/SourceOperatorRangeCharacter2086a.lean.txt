import Dubon2026.SourceFiniteOperatorCharacterDescent

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
joint geometric/boundary character. Name the literal operator-image
character condition so that its ring instances elaborate before inserting
the large actual Tate and boundary spaces. The native kernel descent
proves this condition; it is never assumed as an association theorem. -/
namespace Dubon2026
noncomputable section
variable {A B C : Type} [Ring A] [Ring B] [Ring C]

/-- A character on the actual image ring with its entire prescribed pullback. -/
def sourceOperatorRangeCharacterData (θ : A →+* B) (ψ : A →+* C) : Prop :=
  ∃ χ : θ.range →+* C, χ.comp θ.rangeRestrict = ψ

/-- Native image descent constructs the character from a proved kernel inclusion. -/
theorem sourceOperatorRangeCharacterData_of_kernel
    (θ : A →+* B) (ψ : A →+* C) (h : ∀ a, θ a = 0 → ψ a = 0) :
    sourceOperatorRangeCharacterData θ ψ := by
  have hker : RingHom.ker θ.rangeRestrict ≤ RingHom.ker ψ := by
    intro a ha
    exact RingHom.mem_ker.mpr (h a (congrArg Subtype.val (RingHom.mem_ker.mp ha)))
  exact ⟨sourceFiniteOperatorCharacterDescend θ.rangeRestrict
    θ.rangeRestrict_surjective ψ hker, sourceFiniteOperatorCharacterDescend_comp _ _ _ _⟩

end
end Dubon2026
