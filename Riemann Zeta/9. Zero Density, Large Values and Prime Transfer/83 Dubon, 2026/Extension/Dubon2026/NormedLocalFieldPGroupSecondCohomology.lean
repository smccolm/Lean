import Dubon2026.NormedLocalFieldCyclicCohomology
import Dubon2026.GaloisFixedFieldSecondCohomology
import Dubon2026.PGroupCentralCyclicReduction

/-! # Original local-field H2 order bound for actual p-group extensions -/

namespace Dubon2026
noncomputable section

/-- For the actual units of an original finite Galois local extension
whose Galois group is a p-group, H2 is finite and its order divides the
actual Galois group order. The proof inducts through literal fixed fields
of constructed central cyclic subgroups. -/
theorem normedLocalField_pGroup_second_cohomology_card_dvd
    (p : ℕ) [Fact p.Prime]
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K)) :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) := by
  classical
  generalize hn : Nat.card Gal(L/K) = n
  induction n using Nat.strong_induction_on generalizing K L with
  | h n ih =>
    by_cases hc : IsCyclic Gal(L/K)
    · haveI := hc
      obtain ⟨hf, he⟩ := normedLocalField_cyclic_second_cohomology_order K L
      exact ⟨hf, dvd_of_eq (he.trans hn)⟩
    · haveI : Nontrivial Gal(L/K) := Nontrivial.of_not_isCyclic hc
      obtain ⟨S, hSn, hSc, _, hSi⟩ := pGroup_exists_central_cyclic_reduction hG
      haveI := hSn
      haveI := hSc
      let F := IntermediateField.fixedField S
      letI : NormedAlgebra F L := {
        __ := (inferInstance : Algebra F L)
        norm_smul_le := fun r x => by
          change ‖(r : L) * x‖ ≤ ‖r‖ * ‖x‖
          exact (norm_mul _ _).le }
      haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      haveI : ProperSpace F := FiniteDimensional.proper K F
      haveI : IsCyclic Gal(L/F) :=
        (IntermediateField.subgroupEquivAlgEquiv S).isCyclic.mp hSc
      obtain ⟨hSfinite, hScard⟩ := normedLocalField_cyclic_second_cohomology_order F L
      have hQcard : Nat.card Gal(F/K) = S.index :=
        (Nat.card_congr (IsGalois.normalAutEquivQuotient S).toEquiv).symm
      have hQp : IsPGroup p Gal(F/K) :=
        (hG.to_quotient S).of_equiv (IsGalois.normalAutEquivQuotient S)
      haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
      obtain ⟨hQfinite, hQdvd⟩ := @ih (Nat.card Gal(F/K))
        (by rwa [hQcard, ← hn]) K F inferInstance inferInstance inferInstance inferInstance
        (inferInstance : NormedAlgebra K F) inferInstance inferInstance inferInstance
        (inferInstance : IsGalois K F) hQp rfl
      obtain ⟨hf, hd⟩ := @galoisUnit_second_cohomology_fixedField_card_dvd
        K L _ _ _ _ _ S hSn hQfinite hSfinite
      refine ⟨hf, ?_⟩
      have hSc : Nat.card Gal(L/F) = Nat.card S :=
        (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv).symm
      have hmul : Nat.card Gal(F/K) * Nat.card Gal(L/F) = Nat.card Gal(L/K) := by
        rw [hQcard, hSc, mul_comm, S.card_mul_index]
      have hd' := hd.trans (Nat.mul_dvd_mul hQdvd (dvd_of_eq hScard))
      rwa [hmul, hn] at hd'

end
end Dubon2026
