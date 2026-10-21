import Dubon2026.SourceWeightTwoParabolicPeriods
import Dubon2026.SourceTrivialIntegralHecke

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization.
The proved injective original period pair and existing finite native H1
give the required lower dimension bound. The reverse inequality remains
a separate geometric obligation; no dimension equality is assumed here.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup SourceCuspBoundary groupCohomology
open scoped MatrixGroups

variable (N : ℕ) [NeZero N]

/-- Finite native trivial-coefficient H1 gives finiteness of the actual
additive-character space through the pinned canonical identification. -/
theorem sourceWeightTwoCharacter_finite :
    Module.Finite ℂ (Additive (Gamma0 N) →+ ℂ) := by
  letI := sourceTrivialH1_finite ℂ N
  let e := H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)
  apply Module.Finite.of_surjective e.hom.hom
  intro φ
  refine ⟨e.inv φ, ?_⟩
  exact CategoryTheory.Iso.inv_hom_id_apply e φ

/-- The actual parabolic character subspace is finite-dimensional. -/
theorem sourceWeightTwoParabolic_finite :
    Module.Finite ℂ (parabolicHoms N) := by
  letI := sourceWeightTwoCharacter_finite N
  infer_instance

/-- The constructed original period pair proves the lower dimension bound
needed for geometric realization, without any surjectivity hypothesis. -/
theorem sourceWeightTwoPeriod_dimension_lower :
    2 * Module.finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) ≤
      Module.finrank ℂ (parabolicHoms N) := by
  letI := sourceWeightTwoParabolic_finite N
  letI := Module.Finite.of_injective (sourceWeightTwoParabolicPeriodPair N)
    (sourceWeightTwoParabolicPeriodPair_injective N)
  letI := Module.Finite.of_injective
    (LinearMap.inl ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
      (CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)) LinearMap.inl_injective
  have h := LinearMap.finrank_le_finrank_of_injective
    (sourceWeightTwoParabolicPeriodPair_injective N)
  simpa only [Module.finrank_prod, two_mul] using h

end
end Dubon2026
