import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic

/-! # Genuine irreducibility of the actual restricted representation from its original invariant subspaces -/

namespace Dubon2026

/-- A nonzero original invariant subspace with no proper invariant subspaces gives an irreducible actual restricted representation in Mathlib's sense. -/
theorem representation_restriction_irreducible {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V) (hS : ∀ g x, x ∈ S → ρ g x ∈ S)
    (hne : S ≠ ⊥)
    (hirr : ∀ W : Submodule ℂ V, W ≤ S → (∀ g x, x ∈ W → ρ g x ∈ W) → W = ⊥ ∨ W = S) :
    (Representation.subrepresentation ρ S (fun g x hx => hS g x hx)).IsIrreducible := by
  let σ := Representation.subrepresentation ρ S (fun g x hx => hS g x hx)
  obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have htb : (⊤ : Subrepresentation σ) ≠ ⊥ := by
    intro he
    have hm : (⟨x, hx⟩ : S) ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
    rw [he] at hm
    have hz : (⟨x, hx⟩ : S) = 0 := hm
    exact hxn (congrArg Subtype.val hz)
  letI : Nontrivial (Subrepresentation σ) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro U
  let W := U.toSubmodule.map S.subtype
  have hle : W ≤ S := by
    rintro _ ⟨w, _, rfl⟩
    exact w.property
  have hi : ∀ g x, x ∈ W → ρ g x ∈ W := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, U.apply_mem_toSubmodule g hw, rfl⟩
  rcases hirr W hle hi with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective (f := S.subtype) Subtype.val_injective
    change W = (⊥ : Submodule ℂ S).map S.subtype
    simpa only [Submodule.map_bot] using hbot
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective (f := S.subtype) Subtype.val_injective
    change W = (⊤ : Submodule ℂ S).map S.subtype
    simpa only [Submodule.map_top, Submodule.range_subtype] using htop

end Dubon2026
