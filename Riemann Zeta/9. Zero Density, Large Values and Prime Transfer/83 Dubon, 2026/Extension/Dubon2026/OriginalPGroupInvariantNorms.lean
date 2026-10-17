import Dubon2026.OriginalPGroupTwoDegreeVanishing
import Dubon2026.OriginalRepresentationNormTower

/-! # Invariant norm preimages from the actual two-degree criterion

The finite class/Ext converse needs degree-zero acyclicity as well as
positive vanishing. The original cyclic norm criterion, actual quotient
invariants and the literal norm tower produce these preimages by central
cyclic induction. The arithmetic fundamental-class splitting module and
the subsequent lattice-Hom comparison remain separate obligations.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- For a finite p-group, actual subgroup H1/H2 vanishing constructs a literal group-norm preimage of every invariant. -/
theorem originalPGroup_norm_preimages_of_subgroup_first_second
    {k : Type} [CommRing k] (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Fintype G] (hG : IsPGroup p G) (A : Rep.{0} k G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.ρ.norm y = x := by
  classical
  generalize hm : Nat.card G = m
  induction m using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hc : IsCyclic G
    · haveI := hc
      letI : CommGroup G := IsCyclic.commGroup
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
      have hsecond : Limits.IsZero (groupCohomology A 2) :=
        (h ⊤).2.of_iso (originalCohomologyReindex A Subgroup.topEquiv 2)
      exact originalCyclic_norm_preimages_of_second_zero A g hg hsecond
    · haveI : Nontrivial G := Nontrivial.of_not_isCyclic hc
      obtain ⟨S, hSn, hSc, _, hSi⟩ := pGroup_exists_central_cyclic_reduction hG
      haveI := hSn
      haveI := hSc
      letI : Fintype S := Fintype.ofFinite S
      letI : Fintype (G ⧸ S) := Fintype.ofFinite _
      have hS : ∀ j : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (j + 1)) := by
        letI : CommGroup S := IsCyclic.commGroup
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
        exact originalCyclic_positive_zero_of_first_second (Rep.res S.subtype A) g hg (h S).1 (h S).2
      have hQ : ∀ T : Subgroup (G ⧸ S),
          Limits.IsZero (groupCohomology (Rep.res T.subtype (A.quotientToInvariants S)) 1) ∧
            Limits.IsZero (groupCohomology (Rep.res T.subtype (A.quotientToInvariants S)) 2) := by
        intro T
        exact ⟨originalQuotientSubgroup_zero_of_preimage A S T hS 0 (h _).1,
          originalQuotientSubgroup_zero_of_preimage A S T hS 1 (h _).2⟩
      have hlt : Nat.card (G ⧸ S) < m := by rwa [← S.index_eq_card, ← hm]
      have hnQ := ih (Nat.card (G ⧸ S)) hlt (hG.to_quotient S) (A.quotientToInvariants S) hQ rfl
      have hnS : ∀ x : A, x ∈ (Rep.res S.subtype A).ρ.invariants →
          ∃ y : A, (Rep.res S.subtype A).ρ.norm y = x := by
        letI : CommGroup S := IsCyclic.commGroup
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
        exact originalCyclic_norm_preimages_of_second_zero (Rep.res S.subtype A) g hg (h S).2
      exact originalNorm_preimages_of_subgroup_quotient A S hnS hnQ

end
end Dubon2026
