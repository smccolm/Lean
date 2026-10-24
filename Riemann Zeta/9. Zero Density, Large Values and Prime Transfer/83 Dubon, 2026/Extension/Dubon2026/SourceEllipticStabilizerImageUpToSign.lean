import Dubon2026.SourceEllipticNegationVariableChange

/-! A faithful inertia action reaches the whole actual elliptic
stabilizer when its cardinality is at least that of the stabilizer. In the
remaining size-at-most-two case every stabilizer element is identity or
the actual elliptic negation. These are precisely the two branches in the
source DUB-17/18 full inertia-image-up-to-sign argument. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] (W : WeierstrassCurve K)

theorem stabilizer_eq_one_or_negation_of_card_le_two
    [Finite (MulAction.stabilizer (VariableChange K) W)] (h2 : (2 : K) ≠ 0)
    (hcard : Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 2)
    (g : VariableChange K) (hg : g • W = W) : g = 1 ∨ g = negationChange W := by
  classical
  by_contra h
  push Not at h
  letI := Fintype.ofFinite (MulAction.stabilizer (VariableChange K) W)
  have h3 : 2 < Nat.card (MulAction.stabilizer (VariableChange K) W) := by
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    exact ⟨⟨1, one_mem _⟩,
      ⟨negationChange W, MulAction.mem_stabilizer_iff.mpr (negationChange_smul W)⟩,
      ⟨g, MulAction.mem_stabilizer_iff.mpr hg⟩,
      fun he => negationChange_ne_one W h2 (congrArg Subtype.val he).symm,
      fun he => h.1 (congrArg Subtype.val he).symm,
      fun he => h.2 (congrArg Subtype.val he).symm⟩
  omega

theorem stabilizer_image_surjective_of_card_le
    {I : Type*} [Group I] (ρ : I →* VariableChange K) (hinj : Function.Injective ρ)
    (hfix : ∀ σ, ρ σ • W = W)
    (hcard : Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ Nat.card I)
    [Finite (MulAction.stabilizer (VariableChange K) W)]
    (g : VariableChange K) (hg : g • W = W) : ∃ σ, ρ σ = g := by
  let f : I → MulAction.stabilizer (VariableChange K) W :=
    fun σ => ⟨ρ σ, MulAction.mem_stabilizer_iff.mpr (hfix σ)⟩
  have hf : Function.Injective f := fun _ _ h => hinj (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := (hf.bijective_of_nat_card_le hcard).surjective
    ⟨g, MulAction.mem_stabilizer_iff.mpr hg⟩
  exact ⟨σ, congrArg Subtype.val hσ⟩

theorem stabilizer_image_up_to_sign
    [Finite (MulAction.stabilizer (VariableChange K) W)] (h2 : (2 : K) ≠ 0)
    {I : Type*} [Group I] (ρ : I →* VariableChange K) (hinj : Function.Injective ρ)
    (hfix : ∀ σ, ρ σ • W = W)
    (hcard : Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ Nat.card I ∨
      Nat.card (MulAction.stabilizer (VariableChange K) W) ≤ 2)
    (g : VariableChange K) (hg : g • W = W) :
    (∃ σ, ρ σ = g) ∨ g = negationChange W := by
  rcases hcard with hlarge | hsmall
  · exact Or.inl (stabilizer_image_surjective_of_card_le W ρ hinj hfix hlarge g hg)
  · rcases stabilizer_eq_one_or_negation_of_card_le_two W h2 hsmall g hg with h | h
    · exact Or.inl ⟨1, by rw [map_one, h]⟩
    · exact Or.inr h

end
end Dubon2026.SourceEllipticStabilizer
