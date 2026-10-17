import Dubon2026.LocalFieldFiniteGaloisSecondCohomologyBound

/-! # Actual local unit H2 bounds on every subgroup

The existing fixed-field unit comparison and local H2 bound give the
subgroup input needed for the local fundamental extension. This serves
DUB-17's local/global norm comparison and prescribed-support norm field.
-/
namespace Dubon2026
noncomputable section

/-- Every subgroup of the actual local Galois group has finite unit H2
of order at most its own order, using its literal fixed field. -/
theorem localField_subgroup_second_cohomology_finite_card_le
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] (S : Subgroup Gal(L/K)) :
    Finite (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) ≤
        Nat.card S := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace L := FiniteDimensional.proper K L
  let F := IntermediateField.fixedField S
  letI : NormedAlgebra F L := {
    __ := (inferInstance : Algebra F L)
    norm_smul_le := fun r x => by
      change ‖(r : L) * x‖ ≤ ‖r‖ * ‖x‖
      exact (norm_mul _ _).le }
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace F := FiniteDimensional.proper K F
  obtain ⟨hf, hd⟩ := normedLocalField_second_cohomology_card_dvd F L
  haveI := hf
  let e := (galoisSubgroupUnitCohomologyIso S 2).toLinearEquiv.toEquiv
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e]
  exact (Nat.le_of_dvd (Nat.card_pos (α := Gal(L/F))) hd).trans_eq
    (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv).symm

end
end Dubon2026
