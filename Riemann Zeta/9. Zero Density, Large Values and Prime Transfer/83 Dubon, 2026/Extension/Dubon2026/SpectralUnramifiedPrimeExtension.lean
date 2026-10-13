import Dubon2026.SpectralUnramifiedDegreeContainment
import Dubon2026.UnramifiedCharacteristicInflation

/-! # Actual characteristic-degree enlargement of an original unramified stage

The larger original field is constructed by the existing unramified-stage
existence theorem. Containment follows from the proved degree criterion,
so the degree-q tower needed for DUB-17's unramified H2 vanishing is not assumed.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- Every original unramified finite Galois stage is contained in an actual
unramified stage whose relative degree is the specified prime. -/
theorem spectralUnramifiedStage_exists_prime_extension
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (q : ℕ) [Fact q.Prime] :
    ∃ E : FiniteGaloisIntermediateField K Ω, ∃ hFE : F ≤ E,
      SpectralStageUnramified K Ω E ∧
        letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
        Module.finrank F E = q := by
  have hn : 0 < Module.finrank K F := Module.finrank_pos
  letI : NeZero (Module.finrank K F * q) := ⟨Nat.mul_ne_zero (Nat.ne_of_gt hn)
    (Nat.Prime.ne_zero (Fact.out : q.Prime))⟩
  obtain ⟨E, hdeg, hE⟩ := localField_exists_spectral_original_unramified_stage
    K Ω (Module.finrank K F * q)
  have hFE : F ≤ E := spectralUnramifiedStage_le_of_finrank_dvd F E hF hE
    (hdeg ▸ dvd_mul_right (Module.finrank K F) q)
  refine ⟨E, hFE, hE, ?_⟩
  letI : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
  exact Nat.eq_of_mul_eq_mul_left hn ((Module.finrank_mul_finrank K F E).trans hdeg)

end
end Dubon2026
