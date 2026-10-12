import Dubon2026.NormedLocalFieldSecondCohomologyBound
import Dubon2026.LocalFieldOriginalNorm

/-! # Original finite Galois unit H2 is finite of order dividing the actual degree -/

namespace Dubon2026
noncomputable section

/-- For every actual finite Galois extension of the original local
field, the original algebraic unit H2 is finite of order dividing its
Galois group order. The spectral norm is constructed on the same field;
the original field, units, algebra map and Galois action are preserved. -/
theorem localField_finite_galois_second_cohomology_card_dvd
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Nat.card Gal(L/K) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  haveI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace L := FiniteDimensional.proper K L
  exact normedLocalField_second_cohomology_card_dvd K L

/-- The actual degree formulation of the original local H2 bound,
without imposing a topology or valuation certificate on the extension. -/
theorem localField_finite_galois_second_cohomology_card_dvd_finrank
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L] :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣ Module.finrank K L := by
  have h := (localField_finite_galois_second_cohomology_card_dvd K L).2
  rwa [IsGalois.card_aut_eq_finrank K L] at h

end
end Dubon2026
