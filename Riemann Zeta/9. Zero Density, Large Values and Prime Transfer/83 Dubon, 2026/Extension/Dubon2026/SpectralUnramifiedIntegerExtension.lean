import Dubon2026.LocalFieldIntegerAlgEquiv
import Dubon2026.SpectralValuationExtension

/-! # Actual unramified integer rings under the canonical spectral norm -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- The canonical spectral structure on the same original finite field
retains unramifiedness. Both integer rings are proved to be the actual integral
closure, so no unramifiedness or valuation-comparison certificate is assumed. -/
theorem spectralIntegerExtension_formallyUnramified
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
    [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]] :
    letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
    letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
      spectralValuation_hasExtension K L
    Algebra.FormallyUnramified 𝒪[K] 𝒪[L] := by
  let A := 𝒪[L]
  haveI : IsIntegralClosure A 𝒪[K] L := localField_integer_isIntegralClosure
  haveI : Algebra.FormallyUnramified 𝒪[K] A := inferInstance
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  letI : TopologicalSpace L := (spectralNorm.uniformSpace K L).toTopologicalSpace
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := ValuativeRel.ofValuation (NormedField.valuation (K := L))
  haveI : IsNonarchimedeanLocalField L := spectralFiniteExtension_isNonarchimedeanLocalField K L
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L) :=
    spectralValuation_hasExtension K L
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  exact Algebra.FormallyUnramified.of_equiv (IsIntegralClosure.equiv 𝒪[K] A L 𝒪[L])

end
end Dubon2026
