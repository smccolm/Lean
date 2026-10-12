import Dubon2026.SpectralContinuousH2InvariantEquiv

/-! # The full rational invariant for every original nonarchimedean local field -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original continuous local Galois unit H2 is linearly
equivalent to the actual rational circle. A compatible norm is constructed
on the same original base field, and arithmetic Frobenius periods on genuine
unramified subfields define the map. No norm or cohomology certificate is required. -/
def localFieldContinuousH2InvariantEquiv :
    GaloisUnitContinuousH2 (K := K) (Ω := Ω) ≃ₗ[ℤ] AddCircle (1 : ℚ) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  exact spectralContinuousH2InvariantEquiv K Ω

/-- The full original continuous local H2 has the genuine additive
group and integer-module structure of the rational circle. -/
theorem localField_continuousH2_equivalent_rationalCircle :
    Nonempty (GaloisUnitContinuousH2 (K := K) (Ω := Ω) ≃ₗ[ℤ] AddCircle (1 : ℚ)) :=
  ⟨localFieldContinuousH2InvariantEquiv K Ω⟩

/-- Every actual rational invariant value is attained by an original
continuous local Galois cohomology class. -/
theorem localFieldContinuousH2InvariantEquiv_surjective :
    Function.Surjective (localFieldContinuousH2InvariantEquiv K Ω) :=
  (localFieldContinuousH2InvariantEquiv K Ω).surjective

/-- Equality of genuine invariant values detects equality of the
original continuous local cohomology classes. -/
theorem localFieldContinuousH2InvariantEquiv_injective :
    Function.Injective (localFieldContinuousH2InvariantEquiv K Ω) :=
  (localFieldContinuousH2InvariantEquiv K Ω).injective

end
end Dubon2026
