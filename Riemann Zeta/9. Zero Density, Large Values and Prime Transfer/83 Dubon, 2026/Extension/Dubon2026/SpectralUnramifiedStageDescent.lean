import Dubon2026.LocalFieldH2UnramifiedDescent
import Dubon2026.SpectralUnramifiedStageInvariant
import Dubon2026.SpectralFiniteGaloisUnramifiedSup
import Dubon2026.GaloisUnitFiniteStageTower

/-! # Actual unramified classes descend to every original finite Galois stage of the same degree -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every class of the original unramified stage F descends to a
class of the original E/K extension when the actual degrees agree.
The proof constructs the literal compositum and its local structures,
then applies the exact arithmetic-period descent criterion. -/
theorem spectralUnramifiedStageH2_descends_same_degree
    (E F : FiniteGaloisIntermediateField K Ω)
    (hdegree : Module.finrank K F = Module.finrank K E)
    (hF : SpectralStageUnramified K Ω F) (y : GaloisUnitH2FiniteStage K Ω F) :
    ∃ x : GaloisUnitH2FiniteStage K Ω E,
      galoisUnitH2FiniteStageMap K Ω E x = galoisUnitH2FiniteStageMap K Ω F y := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
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
  have hkill : Module.finrank K E • localFieldPeriodRationalInvariant K F y = 0 := by
    rw [← hdegree]
    exact (localFieldPeriodRationalInvariant_mem_range_iff K F _).mp ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := (localFieldH2_unramified_descends_iff K E F H
    (intermediateField_sup_inclusion_ranges E.toIntermediateField F.toIntermediateField) y).mpr hkill
  have heqE := galoisUnitFiniteStageH2Inflation_tower E H le_sup_left x
  have heqF := galoisUnitFiniteStageH2Inflation_tower F H le_sup_right y
  exact ⟨x, heqE.trans ((congrArg (galoisUnitFiniteStageH2Inflation H) hx).trans heqF.symm)⟩

end
end Dubon2026
