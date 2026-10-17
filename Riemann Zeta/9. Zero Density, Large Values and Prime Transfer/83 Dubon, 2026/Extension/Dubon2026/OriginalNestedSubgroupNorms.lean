import Dubon2026.OriginalPGroupInvariantNorms

/-! # Norm preimages on every actual subgroup

The actual fundamental coefficient's free-kernel presentation needs
invariant lifts on every subgroup, not only on the full group. Pinned
subgroup-image equivalence and the existing group-change comparison
transport H1/H2 vanishing without a nested-subgroup certificate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- The actual nested restriction has the cohomology vanishing of its literal image subgroup. -/
theorem originalNestedSubgroup_zero (S : Subgroup G) (T : Subgroup S) (n : ℕ)
    (h : Limits.IsZero (groupCohomology (Rep.res (T.map S.subtype).subtype A) n)) :
    Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) n) := by
  let e := T.equivMapOfInjective S.subtype S.subtype_injective
  let B := Rep.res T.subtype (Rep.res S.subtype A)
  let φ : Rep.res e.toMonoidHom (Rep.res (T.map S.subtype).subtype A) ⟶ B := 𝟙 B
  haveI : IsIso φ := by change IsIso (𝟙 B); infer_instance
  have hi := originalGroupChangeCohomology_isIso
    (Rep.res (T.map S.subtype).subtype A) B e φ n
  exact h.of_iso (@asIso _ _ _ _ _ hi).symm

/-- Subgroup H1/H2 vanishing gives actual invariant norm preimages on every subgroup of the original p-group. -/
theorem originalPGroup_subgroup_norm_preimages
    (p : ℕ) [Fact p.Prime] [Fintype G] (hG : IsPGroup p G)
    (h : ∀ H : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res H.subtype A) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype A) 2))
    (S : Subgroup G) [Fintype S] :
    ∀ x : A, x ∈ (Rep.res S.subtype A).ρ.invariants →
      ∃ y : A, (Rep.res S.subtype A).ρ.norm y = x := by
  have hS (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 2) :=
    ⟨originalNestedSubgroup_zero A S T 1 (h _).1,
      originalNestedSubgroup_zero A S T 2 (h _).2⟩
  exact originalPGroup_norm_preimages_of_subgroup_first_second p
    (hG.to_subgroup S) (Rep.res S.subtype A) hS

end
end Dubon2026
