import Dubon2026.OriginalIdeleClassFixedFieldCohomology
import Dubon2026.OriginalCyclicIdeleClassCohomology
import Dubon2026.PGroupCentralCyclicReduction

/-! # Original idele-class H1 and H2 for finite p-group extensions

Induction through actual central cyclic fixed fields uses the proved
cyclic norm index and the original inflation-restriction comparisons.
It removes any assumed cohomology vanishing or size bound for p-group
stages needed in DUB-17's global invariant and arithmetic duality chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Original p-group idele-class H1 vanishes, and H2 is finite of order dividing the actual degree. -/
theorem originalIdeleClass_pGroup_cohomology
    (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hG : IsPGroup p Gal(L/K)) :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
        Nat.card (groupCohomology (originalIdeleClassRep K L) 2) ∣ Nat.card Gal(L/K) := by
  classical
  generalize hn : Nat.card Gal(L/K) = n
  induction n using Nat.strong_induction_on generalizing K L with
  | h n ih =>
    by_cases hc : IsCyclic Gal(L/K)
    · haveI := hc
      refine ⟨original_ideleClass_first_zero K L, (original_ideleClass_herbrand K L).2.1, ?_⟩
      have he := original_ideleClass_second_card K L
      rw [← IsGalois.card_aut_eq_finrank K L, hn] at he
      exact dvd_of_eq he
    · haveI : Nontrivial Gal(L/K) := Nontrivial.of_not_isCyclic hc
      obtain ⟨S, hSn, hSc, _, hSi⟩ := pGroup_exists_central_cyclic_reduction hG
      haveI := hSn
      haveI := hSc
      let F := IntermediateField.fixedField S
      haveI : IsCyclic Gal(L/F) :=
        (IntermediateField.subgroupEquivAlgEquiv S).isCyclic.mp hSc
      haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
      have hQcard : Nat.card Gal(F/K) = S.index :=
        (Nat.card_congr (IsGalois.normalAutEquivQuotient S).toEquiv).symm
      have hQp : IsPGroup p Gal(F/K) :=
        (hG.to_quotient S).of_equiv (IsGalois.normalAutEquivQuotient S)
      obtain ⟨hQfirst, hQfinite, hQdvd⟩ := @ih (Nat.card Gal(F/K))
        (by rwa [hQcard, ← hn]) K F inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance (inferInstance : IsGalois K F) hQp rfl
      have hSfirst := original_ideleClass_first_zero F L
      haveI := hQfinite
      haveI := (original_ideleClass_herbrand F L).2.1
      obtain ⟨hf, hd⟩ := originalIdeleClass_second_fixedField_card_dvd S hSfirst
      refine ⟨originalIdeleClass_first_zero_of_fixedField S hQfirst hSfirst, hf, ?_⟩
      have hScard : Nat.card (groupCohomology (originalIdeleClassRep F L) 2) =
          Nat.card Gal(L/F) := by
        rw [original_ideleClass_second_card, IsGalois.card_aut_eq_finrank]
      have hSc : Nat.card Gal(L/F) = Nat.card S :=
        (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv).symm
      have hmul : Nat.card Gal(F/K) * Nat.card Gal(L/F) = Nat.card Gal(L/K) := by
        rw [hQcard, hSc, mul_comm, S.card_mul_index]
      have hd' := hd.trans (Nat.mul_dvd_mul hQdvd (dvd_of_eq hScard))
      rwa [hmul, hn] at hd'

end
end Dubon2026
