import Dubon2026.SpectralFiniteGaloisUnramifiedSup
import Dubon2026.LocalFieldPeriodInvariantInflation
import Dubon2026.GaloisUnitH2FiniteColimitMap

/-! # Actual spectral unramified stages and their arithmetic period invariants -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- Unramifiedness of the literal integer extension of the original
finite Galois stage equipped with its canonical spectral norm over K. -/
def SpectralStageUnramified (F : FiniteGaloisIntermediateField K Ω) : Prop :=
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  Algebra.FormallyUnramified 𝒪[K] 𝒪[F]

/-- The actual arithmetic-Frobenius period invariant on an original
unramified finite stage with its spectral local structures. -/
def spectralUnramifiedStageInvariant (F : FiniteGaloisIntermediateField K Ω)
    (hF : SpectralStageUnramified K Ω F) :
    GaloisUnitH2FiniteStage K Ω F →ₗ[ℤ] AddCircle (1 : ℚ) := by
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact localFieldPeriodRationalInvariant K F

/-- The invariant of each actual spectral unramified stage is injective. -/
theorem spectralUnramifiedStageInvariant_injective (F : FiniteGaloisIntermediateField K Ω)
    (hF : SpectralStageUnramified K Ω F) :
    Function.Injective (spectralUnramifiedStageInvariant K Ω F hF) := by
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact localFieldPeriodRationalInvariant_injective K F

/-- The image is exactly the rational classes annihilated by the
actual original field degree. -/
theorem spectralUnramifiedStageInvariant_mem_range_iff (F : FiniteGaloisIntermediateField K Ω)
    (hF : SpectralStageUnramified K Ω F) (q : AddCircle (1 : ℚ)) :
    q ∈ (spectralUnramifiedStageInvariant K Ω F hF).range ↔ Module.finrank K F • q = 0 := by
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact localFieldPeriodRationalInvariant_mem_range_iff K F q

end
end Dubon2026
