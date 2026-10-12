import Dubon2026.LocalFieldUnramifiedCompositum
import Dubon2026.SpectralOriginalUnramifiedStage
import Dubon2026.NormedLocalFieldCyclicCohomology
import Dubon2026.IntermediateFieldSupEmbeddings

/-! # Actual finite Galois composita preserve original spectral unramifiedness -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- The literal supremum of the original finite Galois stages is
unramified over E whenever F is unramified over K. All norms, valuations,
inclusions and valuation extension instances come from the actual spectral tower. -/
theorem spectralFiniteGalois_sup_unramified (E F : FiniteGaloisIntermediateField K Ω)
    (hF :
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F]) :
    let H := E ⊔ F
    letI : Algebra E H :=
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left)).toAlgebra
    letI : IsScalarTower K E H := IsScalarTower.of_algHom
      (IntermediateField.inclusion (show E.toIntermediateField ≤ H.toIntermediateField
        from le_sup_left))
    letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
    letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
    letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
    letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
    letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
      normedFieldValuation_hasExtension E H
    Algebra.FormallyUnramified 𝒪[E] 𝒪[H] := by
  let H := E ⊔ F
  let i := IntermediateField.inclusion
    (show E.toIntermediateField ≤ H.toIntermediateField from le_sup_left)
  let j := IntermediateField.inclusion
    (show F.toIntermediateField ≤ H.toIntermediateField from le_sup_right)
  letI : Algebra E H := i.toAlgebra
  letI : Algebra F H := j.toAlgebra
  haveI : IsScalarTower K E H := IsScalarTower.of_algHom i
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom j
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
  letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
  letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : IsNonarchimedeanLocalField H := spectralFiniteExtension_isNonarchimedeanLocalField K H
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension E H
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  exact localField_integer_unramified_of_compositum K E F H
    (intermediateField_sup_inclusion_ranges E.toIntermediateField F.toIntermediateField)

end
end Dubon2026
