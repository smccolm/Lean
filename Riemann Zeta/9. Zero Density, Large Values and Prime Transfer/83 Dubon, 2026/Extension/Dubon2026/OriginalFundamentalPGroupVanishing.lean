import Dubon2026.OriginalFundamentalTwoDegreeVanishing
import Dubon2026.OriginalPGroupInvariantNorms

/-! # Positive and degree-zero vanishing for the actual fundamental coefficient

The finite class-system data first proves H1/H2 vanishing on every
subgroup of the actual twisted extension. The proved p-group criterion
then gives positive cohomology vanishing and literal invariant norm
preimages. These discharge the fundamental-coefficient acyclicity input
of DUB-17's finite duality route; the lattice-Hom comparison remains.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Every invariant of the actual representation has a literal group-norm preimage. This proposition alone asserts no existence. -/
def OriginalInvariantNormSurjective {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) : Prop :=
  ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.ρ.norm y = x

/-- The actual fundamental splitting coefficient has vanishing positive cohomology and literal invariant norm preimages, derived from the original p-group class-system data. -/
theorem originalFundamentalPGroup_positive_and_norm
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hG : IsPGroup p G) (C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (h1 : ∀ S : Subgroup G, Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hcard : ∀ S : Subgroup G, Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Nat.card S)
    (hgen : ∀ S : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2) (groupCohomology.H2π C φ)} = ⊤) :
    (∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2)) ∧
    (∀ n : ℕ, Limits.IsZero (groupCohomology (originalFundamentalSplittingModule C φ) (n + 1))) ∧
    OriginalInvariantNormSurjective (originalFundamentalSplittingModule C φ) := by
  have hvan (S : Subgroup G) :
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI := Fintype.ofFinite S
    exact originalFundamentalSubgroup_first_second_zero C φ S (h1 S)
      ((hcard S).trans (Nat.card_eq_fintype_card)) (hgen S)
  exact ⟨hvan, originalPGroup_positive_zero_of_subgroup_first_second p hG _ hvan,
    originalPGroup_norm_preimages_of_subgroup_first_second p hG _ hvan⟩

end
end Dubon2026
