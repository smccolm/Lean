import Mathlib.GroupTheory.Coset.Basic

/-! # Genuine coset bijections induced by a surjective original group homomorphism -/

namespace Dubon2026

noncomputable section

variable {G H : Type*} [Group G] [Group H]

/-- A genuine homomorphism maps the actual cosets of a subgroup preimage into the original target cosets. -/
def subgroupComapCosetMap (f : G →* H) (K : Subgroup H) : G ⧸ K.comap f → H ⧸ K :=
  Quotient.map f (by
    intro a b hab
    apply (QuotientGroup.leftRel_apply).mpr
    have h := (QuotientGroup.leftRel_apply).mp hab
    change f (a⁻¹ * b) ∈ K at h
    simpa only [map_mul, map_inv] using h)

/-- The actual subgroup-preimage coset map is always injective. -/
theorem subgroupComapCosetMap_injective (f : G →* H) (K : Subgroup H) :
    Function.Injective (subgroupComapCosetMap f K) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro hab
      apply QuotientGroup.eq.mpr
      have h := QuotientGroup.eq.mp hab
      change f (a⁻¹ * b) ∈ K
      simpa only [map_mul, map_inv] using h

/-- Every original target coset has a source coset when the genuine group map is surjective. -/
theorem subgroupComapCosetMap_surjective (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Function.Surjective (subgroupComapCosetMap f K) := by
  intro b
  induction b using Quotient.inductionOn with
  | h b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩

/-- A surjective original group homomorphism gives a genuine equivalence of its subgroup-preimage cosets with the original target cosets. -/
def subgroupComapCosetEquiv (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    G ⧸ K.comap f ≃ H ⧸ K :=
  Equiv.ofBijective (subgroupComapCosetMap f K)
    ⟨subgroupComapCosetMap_injective f K, subgroupComapCosetMap_surjective f hf K⟩

/-- The genuine coset equivalence sends every original representative to its actual group image. -/
theorem subgroupComapCosetEquiv_mk (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) (g : G) :
    subgroupComapCosetEquiv f hf K (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

end
end Dubon2026
