import Dubon2026.ArithmeticOrbitFieldEmbedding
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension

/-! # Constructed local-field structures on the actual arithmetic orbit field

The existing spectral finite-extension and valuation-extension proofs
discharge the local-field premises required by the existing invariant
corestriction theorem. This serves the orbit-to-localization comparison
on DUB-17's global reciprocity dependency chain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- The actual finite orbit field has a constructed local topology and
valuation extending the original prime-completion valuation. -/
theorem rationalArithmeticOrbitLocalField_exists_structure
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    let E := rationalArithmeticOrbitLocalField a p hp F c
    ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E), IsNonarchimedeanLocalField E ∧
      (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E) := by
  let K := rationalPrimeLocalField p hp
  let E := rationalArithmeticOrbitLocalField a p hp F c
  letI : FiniteDimensional K E := rationalArithmeticOrbitLocalField_finiteDimensional a p hp F c
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let normK := localFieldOriginalNorm K
  letI : NontriviallyNormedField K := normK
  letI : NormedField K := normK.toNormedField
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  haveI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  exact ⟨inferInstance, inferInstance, spectralFiniteExtension_isNonarchimedeanLocalField K E,
    spectralValuation_hasExtension K E⟩

end
end Dubon2026
