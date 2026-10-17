import Dubon2026.OriginalPGroupInternalHomAcyclicity
import Dubon2026.FiniteFirstCohomologySylowDetection

/-! # The original lattice internal Hom has zero H1 for any finite group

DUB-17's constructed enlarged arithmetic stage need not have prime-power
degree. Its relation-extension criterion therefore needs the existing
converse norm argument for general finite groups. That argument uses only
H1 vanishing of the lattice internal Hom. Apply the proved p-group theorem
on each actual Sylow subgroup and the existing H1 detection theorem;
no all-degree finite-group generalization is needed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Subgroup H1/H2 vanishing of the actual target forces H1 vanishing
of its original lattice internal Hom, without a p-group premise. -/
theorem originalFinite_internalHom_first_zero
    {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
    [Module.Projective ℤ M]
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj B) 1) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  apply finiteFirstCohomology_sylow_zero ((Rep.ihom M).obj B) x
  intro p hp _
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  let S : Subgroup G := P
  letI : Fintype S := Fintype.ofFinite S
  letI : Module.Projective ℤ (Rep.res S.subtype M) := ‹Module.Projective ℤ M›
  have hS (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 2) :=
    ⟨originalNestedSubgroup_zero B S T 1 (h _).1,
      originalNestedSubgroup_zero B S T 2 (h _).2⟩
  have hz : Limits.IsZero
      (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) 1) :=
    originalPGroup_internalHom_positive_zero (Rep.res S.subtype M)
      (Rep.res S.subtype B) p P.isPGroup' hS 0
  haveI := ModuleCat.isZero_iff_subsingleton.mp hz
  exact ⟨P, Subsingleton.elim _ _⟩

end
end Dubon2026
