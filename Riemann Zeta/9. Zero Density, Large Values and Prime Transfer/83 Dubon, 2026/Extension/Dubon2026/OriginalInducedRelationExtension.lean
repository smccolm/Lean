import Dubon2026.OriginalInducedRelationH2Detection
import Dubon2026.OriginalRestrictedFundamentalData
import Dubon2026.OriginalFiniteFundamentalRelationCriterion

/-! # Actual extension of zero-obstruction induced relation morphisms

This is the middle-extension step of DUB-17's nontrivial-action reduction.
Existing class-trace injectivity detects the restricted obstruction;
the derived subgroup fundamental data and literal invariant norm roots
give an extension there. The actual adjunction transports that extension
to the induced free cover, without a new Shapiro/connecting comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- For the actual induced relation presentation, zero obstruction is
equivalent to literal extension through its free cover. Restricted
fundamental data and all cohomology comparisons are derived. -/
theorem originalInducedRelation_obstruction_zero_iff_extension
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
    (ψ : Rep.ind N.subtype (originalRelationModule (Rep.res N.subtype B)) ⟶ C) :
    groupCohomology.δ (originalInducedRelationSequence_shortExact N B) 1 2 rfl ≫
        (groupCohomology.functor ℤ G 2).map ψ = 0 ↔
      ∃ χ : Rep.ind N.subtype (Rep.free ℤ N (Rep.res N.subtype B)) ⟶ C,
        (Rep.indFunctor ℤ N.subtype).map (originalRelationInclusion (Rep.res N.subtype B)) ≫ χ = ψ := by
  constructor
  · intro hz
    have hr := originalInducedRelation_zero_obstruction_restricts C u hu N (hc N) (hg N) B ψ hz
    obtain ⟨φ, ho, hv⟩ := originalRestrictedFundamentalData_exists C u h1 hc hg N
    apply (originalInducedRelation_extension_iff N B C ψ).mpr
    exact (originalFiniteFundamental_relation_obstruction_zero_iff_extension
      (Rep.res N.subtype C) φ ho hv p hnorm (Rep.res N.subtype B) hB
      (fun g b => hNB g g.property b) _).mp hr
  · rintro ⟨χ, rfl⟩
    have hz := (groupCohomology.mapShortComplex₁
      (originalInducedRelationSequence_shortExact N B) (i := 1) (j := 2) rfl).zero
    erw [Functor.map_comp, ← Category.assoc, hz, Limits.zero_comp]

end
end Dubon2026
