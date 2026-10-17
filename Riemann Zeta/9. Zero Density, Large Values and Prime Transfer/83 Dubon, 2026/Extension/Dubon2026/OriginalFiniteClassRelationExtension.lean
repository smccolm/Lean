import Dubon2026.OriginalRelationDevissage
import Dubon2026.OriginalInducedRelationComparison
import Dubon2026.OriginalInducedRelationExtension
import Dubon2026.OriginalFiniteRelationH2Surjectivity
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Relation extension from exactly the finite class data used

DUB-17's finite class/Ext step uses a full-order class and its subgroup
cohomology facts. Completion-normalization identities are unnecessary for
this step. The actual induced sequence, decomposition and correction are
constructed from these data; no extension or duality premise is supplied.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- Full-order finite class data and subgroup invariant norm roots give
the actual relation-extension criterion, allowing nontrivial group action. -/
theorem originalFiniteClass_relation_extension_iff
    {G : Type} [Group G] [Fintype G]
    (C : Rep.{0} ℤ G) (u : groupCohomology C 2) (hu : addOrderOf u = Nat.card G)
    (h1 : ∀ H : Subgroup G, Limits.IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hc : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (hg : ∀ H : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [Fintype N]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : N, C.ρ g d = d) ∧
      (∑ g : N, C.ρ g c) = p • d)
    (B : Rep.{0} ℤ G) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (χ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C χ = 0 ↔
      ∃ a : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ a = χ := by
  have hcard : Nat.card (groupCohomology C 2) = Nat.card G :=
    (Nat.card_congr (originalCohomologyReindex C Subgroup.topEquiv 2).toLinearEquiv.toEquiv).trans
      ((hc ⊤).trans (Nat.card_congr Subgroup.topEquiv.toEquiv))
  letI : Finite (groupCohomology C 2) := Nat.finite_of_card_ne_zero
    (hcard.trans_ne Nat.card_pos.ne')
  letI : IsAddCyclic (groupCohomology C 2) :=
    isAddCyclic_of_addOrderOf_eq_card u (hu.trans hcard.symm)
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  have hv (H : Subgroup G) :
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI : Fintype H := Fintype.ofFinite H
    exact originalFundamentalSubgroup_first_second_zero C φ H (h1 H)
      ((hc H).trans Nat.card_eq_fintype_card) (hg H)
  constructor
  · intro hz
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    letI : Finite SB.X₃ := originalSubgroupInducedQuotient_finite N B
    obtain ⟨ιR, ιP, ρR, ρP, hi₁, hi₂, hr₁, hr₂, hk⟩ :=
      originalInducedRelation_zero_obstruction_decomposition N B C φ
        (hu.trans Nat.card_eq_fintype_card) hv
    exact originalRelation_extension_of_devissage C p
      (originalSubgroupInducedSequence_shortExact N B)
      (originalSubgroupInducedQuotient_nsmul_zero N B p hB)
      TI.f TI.g TI.zero (originalInducedRelationSequence_shortExact N B)
      ιR ιP hi₁ hi₂ ρR ρP hr₁ hr₂ hk
      (fun ψ hψ => (originalInducedRelation_obstruction_zero_iff_extension
        C (groupCohomology.H2π C φ) hu h1 hc hg p N hnorm B hB hNB ψ).mp hψ)
      (originalFiniteFundamental_relation_obstruction_surjective SB.X₃ C φ
        (hu.trans Nat.card_eq_fintype_card) hv) χ hz
  · rintro ⟨a, ha⟩
    exact originalRelationExtensionObstruction_zero_of_extension B C χ a ha

end
end Dubon2026
