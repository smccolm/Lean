import Dubon2026.NormedLocalFieldPGroupSecondCohomology
import Dubon2026.SecondCohomologySylowCardinality

/-! # Actual H2 order bound for every original finite Galois normed local extension -/

namespace Dubon2026
noncomputable section

/-- The actual multiplicative-group H2 of every finite Galois normed
local extension is finite and its order divides the genuine Galois group
order. No norm index, H2 bound or local invariant is supplied as a premise. -/
theorem normedLocalField_second_cohomology_card_dvd
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) := by
  apply secondCohomology_card_dvd_of_sylows (Rep.ofAlgebraAutOnUnits K L)
  intro p hp P
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup Gal(L/K) := P
  let F := IntermediateField.fixedField S
  letI : NormedAlgebra F L := {
    __ := (inferInstance : Algebra F L)
    norm_smul_le := fun r x => by
      change ‖(r : L) * x‖ ≤ ‖r‖ * ‖x‖
      exact (norm_mul _ _).le }
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace F := FiniteDimensional.proper K F
  have hpG : IsPGroup p Gal(L/F) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv S)
  obtain ⟨hfinite, hdvd⟩ := normedLocalField_pGroup_second_cohomology_card_dvd p F L hpG
  let e := galoisSubgroupUnitCohomologyIso S 2
  haveI := hfinite
  refine ⟨Finite.of_equiv _ e.toLinearEquiv.toEquiv, ?_⟩
  have hc := Nat.card_congr e.toLinearEquiv.toEquiv
  have hG := Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv
  rw [← hc]
  exact hdvd.trans (dvd_of_eq hG.symm)

/-- The same actual H2 order bound is the divisibility by the original
extension degree, using the genuine Galois degree identity. -/
theorem normedLocalField_second_cohomology_card_dvd_finrank
    (K L : Type) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [LocallyCompactSpace K] [LocallyCompactSpace L]
    [FiniteDimensional K L] [IsGalois K L] :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Module.finrank K L := by
  have h := (normedLocalField_second_cohomology_card_dvd K L).2
  rwa [IsGalois.card_aut_eq_finrank K L] at h

end
end Dubon2026
