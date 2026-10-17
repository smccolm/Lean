import Dubon2026.OriginalQuotientSubgroupVanishing
import Dubon2026.OriginalCyclicTwoDegreeVanishing
import Dubon2026.PGroupCentralCyclicReduction

/-! # Positive cohomological triviality from two subgroup degrees

For the finite class/Ext converse, the middle coefficient of the
fundamental-class extension must be acyclic. For a finite p-group, actual
H1/H2 vanishing on every subgroup suffices in all positive degrees. Use
the existing central cyclic reduction, the actual quotient-invariant
comparison and the pinned cyclic resolution. No Tate-cup construction or
cohomological-triviality certificate is assumed.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- For a finite p-group, vanishing H1 and H2 on all actual subgroups implies vanishing in every positive degree. -/
theorem originalPGroup_positive_zero_of_subgroup_first_second
    {k : Type} [CommRing k] (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Finite G] (hG : IsPGroup p G) (A : Rep.{0} k G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype A) 2)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) := by
  classical
  generalize hm : Nat.card G = m
  induction m using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hc : IsCyclic G
    · haveI := hc
      letI : CommGroup G := IsCyclic.commGroup
      letI : Fintype G := Fintype.ofFinite G
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
      have hfirst : Limits.IsZero (groupCohomology A 1) :=
        (h ⊤).1.of_iso (originalCohomologyReindex A Subgroup.topEquiv 1)
      have hsecond : Limits.IsZero (groupCohomology A 2) :=
        (h ⊤).2.of_iso (originalCohomologyReindex A Subgroup.topEquiv 2)
      exact originalCyclic_positive_zero_of_first_second A g hg hfirst hsecond n
    · haveI : Nontrivial G := Nontrivial.of_not_isCyclic hc
      obtain ⟨S, hSn, hSc, _, hSi⟩ := pGroup_exists_central_cyclic_reduction hG
      haveI := hSn
      haveI := hSc
      have hS : ∀ j : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (j + 1)) := by
        letI : CommGroup S := IsCyclic.commGroup
        letI : Fintype S := Fintype.ofFinite S
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
        exact originalCyclic_positive_zero_of_first_second (Rep.res S.subtype A) g hg (h S).1 (h S).2
      have hQ : ∀ T : Subgroup (G ⧸ S),
          Limits.IsZero (groupCohomology (Rep.res T.subtype (A.quotientToInvariants S)) 1) ∧
            Limits.IsZero (groupCohomology (Rep.res T.subtype (A.quotientToInvariants S)) 2) := by
        intro T
        exact ⟨originalQuotientSubgroup_zero_of_preimage A S T hS 0 (h _).1,
          originalQuotientSubgroup_zero_of_preimage A S T hS 1 (h _).2⟩
      have hlt : Nat.card (G ⧸ S) < m := by rwa [← S.index_eq_card, ← hm]
      have hz := ih (Nat.card (G ⧸ S)) hlt (hG.to_quotient S) (A.quotientToInvariants S) hQ rfl
      have hi := originalPositiveInflation_isIso_of_subgroup_zero A S hS n
      exact hz.of_iso (@asIso _ _ _ _ _ hi).symm

end
end Dubon2026
