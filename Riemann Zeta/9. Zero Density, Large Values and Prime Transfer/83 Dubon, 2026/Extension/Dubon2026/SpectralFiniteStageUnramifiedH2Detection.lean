import Dubon2026.SpectralFiniteGaloisUnramifiedSup
import Dubon2026.LocalFieldH2UnramifiedCompositumDetection
import Dubon2026.GaloisUnitFiniteStageTower

/-! # Original finite-stage classes come from genuine unramified spectral stages -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every genuine finite-stage class has the same original absolute
inflation as a class of an actual unramified stage of the same degree.
The proof constructs the literal compositum with compatible spectral structures. -/
theorem spectralFiniteStageH2_exists_unramified_representative
    (E : FiniteGaloisIntermediateField K Ω)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, Module.finrank K F = Module.finrank K E ∧
      letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
      letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
      letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
      letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
        spectralValuation_hasExtension K F
      Algebra.FormallyUnramified 𝒪[K] 𝒪[F] ∧
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
        ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := F),
          galoisUnitFiniteStageH2Inflation E x = galoisUnitFiniteStageH2Inflation F y := by
  haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨F, hdegree, hF⟩ :=
    localField_exists_spectral_original_unramified_stage K Ω (Module.finrank K E)
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
  letI : NormedAlgebra F H := spectralNorm.normedAlgebra' K F H
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
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation H) :=
    spectralValuation_hasExtension K H
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension E H
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension F H
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K H) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
  obtain ⟨y, hy⟩ := localFieldH2_exists_unramified_compositum_representative K E F H
    (intermediateField_sup_inclusion_ranges E.toIntermediateField F.toIntermediateField) hdegree x
  have heqE := galoisUnitFiniteStageH2Inflation_tower E H le_sup_left x
  have heqF := galoisUnitFiniteStageH2Inflation_tower F H le_sup_right y
  exact ⟨F, hdegree, hF, y,
    heqE.trans ((congrArg (galoisUnitFiniteStageH2Inflation H) hy).trans heqF.symm)⟩

end
end Dubon2026
