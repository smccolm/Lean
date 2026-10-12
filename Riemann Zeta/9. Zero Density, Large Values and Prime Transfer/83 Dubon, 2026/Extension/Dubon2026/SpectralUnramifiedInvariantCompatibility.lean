import Dubon2026.SpectralUnramifiedStageInvariant
import Dubon2026.ContinuousGaloisUnitFiniteStageInjection

/-! # Original unramified period invariants agree on actual common extensions -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- The actual supremum of two original spectral unramified fields
is again unramified over the original base. -/
theorem spectralStageUnramified_sup (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F) :
    SpectralStageUnramified K Ω (E ⊔ F) := by
  let H := E ⊔ F
  let i := IntermediateField.inclusion
    (show E.toIntermediateField ≤ H.toIntermediateField from le_sup_left)
  letI : Algebra E H := i.toAlgebra
  haveI : IsScalarTower K E H := IsScalarTower.of_algHom i
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
  letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
  letI : NormedAlgebra E H := spectralNorm.normedAlgebra' K E H
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation H) :=
    spectralValuation_hasExtension K H
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) :=
    normedFieldValuation_hasExtension E H
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[E] := hE
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[H] := spectralFiniteGalois_sup_unramified E F hF
  haveI : IsScalarTower 𝒪[K] 𝒪[E] 𝒪[H] := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply K E H (x : K))
  exact Algebra.FormallyUnramified.comp 𝒪[K] 𝒪[E] 𝒪[H]

/-- Literal field inclusion preserves the genuine arithmetic period
invariant of the original class. -/
theorem spectralUnramifiedStageInvariant_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (x : GaloisUnitH2FiniteStage K Ω E) :
    spectralUnramifiedStageInvariant K Ω F hF (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      spectralUnramifiedStageInvariant K Ω E hE x := by
  let i := IntermediateField.inclusion hEF
  letI : Algebra E F := i.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algHom i
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : NormedAlgebra E F := spectralNorm.normedAlgebra' K E F
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation F) :=
    normedFieldValuation_hasExtension E F
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[E] := hE
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[F] := hF
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  exact localFieldPeriodRationalInvariant_inflation K E F x

variable [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Two original unramified representatives of the same actual
continuous class have the same arithmetic period invariant. -/
theorem spectralUnramifiedStageInvariant_eq_of_inflation_eq
    (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (x : GaloisUnitH2FiniteStage K Ω E) (y : GaloisUnitH2FiniteStage K Ω F)
    (hxy : galoisUnitH2FiniteStageMap K Ω E x = galoisUnitH2FiniteStageMap K Ω F y) :
    spectralUnramifiedStageInvariant K Ω E hE x =
      spectralUnramifiedStageInvariant K Ω F hF y := by
  let H := E ⊔ F
  have hH : SpectralStageUnramified K Ω H := spectralStageUnramified_sup K Ω E F hE hF
  have hcommon : galoisUnitH2FiniteTransition K Ω E H le_sup_left x =
      galoisUnitH2FiniteTransition K Ω F H le_sup_right y := by
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K H) := ⟨rfl⟩
    apply galoisUnitFiniteStageH2Inflation_injective H
    exact (galoisUnitH2FiniteStageMap_transition K Ω E H le_sup_left x).trans
      (hxy.trans (galoisUnitH2FiniteStageMap_transition K Ω F H le_sup_right y).symm)
  exact (spectralUnramifiedStageInvariant_transition K Ω E H le_sup_left hE hH x).symm.trans
    ((congrArg (spectralUnramifiedStageInvariant K Ω H hH) hcommon).trans
      (spectralUnramifiedStageInvariant_transition K Ω F H le_sup_right hF hH y))

end
end Dubon2026
