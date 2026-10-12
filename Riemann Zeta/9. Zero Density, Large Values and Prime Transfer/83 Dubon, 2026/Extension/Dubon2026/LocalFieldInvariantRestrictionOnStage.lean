import Dubon2026.ContinuousGaloisRestrictionRebasedStage
import Dubon2026.LocalFieldContinuousInvariantNormalization
import Dubon2026.LocalFieldInvariantBaseChange

/-! # The original full invariant restriction formula on actual unramified representatives -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- For an actual unramified representative and an actual common
extension unramified over the new base, the full original invariant of its
restriction is multiplied by the actual base degree. The cohomology maps
are the original infinite restriction and literal finite-stage inflations. -/
theorem localFieldContinuousInvariant_restriction_on_stage
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [ValuativeRel E] [ValuativeRel F] [ValuativeRel H]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace H]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField H]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F)]
    [Algebra.FormallyUnramified 𝒪[K] 𝒪[F]]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)] :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ [_hextEH : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H)]
      [_hextFH : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H)]
      [_hunram : Algebra.FormallyUnramified 𝒪[E] 𝒪[H]] (y : GaloisUnitH2FiniteStage K Ω F),
      localFieldContinuousH2InvariantEquiv E Ω
        (continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F y)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (galoisUnitH2FiniteStageMap K Ω F y) := by
  letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  haveI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E H := FiniteDimensional.right K E H
  haveI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  intro hextEH hextFH hunram y
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation H) := hextEH
  letI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation H) := hextFH
  letI : Algebra.FormallyUnramified 𝒪[E] 𝒪[H] := hunram
  letI : ValuativeRel (finiteGaloisStageExtendScalars E H hEH) := inferInstanceAs (ValuativeRel H)
  letI : TopologicalSpace (finiteGaloisStageExtendScalars E H hEH) := inferInstanceAs (TopologicalSpace H)
  haveI : IsNonarchimedeanLocalField (finiteGaloisStageExtendScalars E H hEH) :=
    inferInstanceAs (IsNonarchimedeanLocalField H)
  haveI : (ValuativeRel.valuation E).HasExtension
      (ValuativeRel.valuation (finiteGaloisStageExtendScalars E H hEH)) := hextEH
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[finiteGaloisStageExtendScalars E H hEH] := hunram
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
  have hres := continuousGaloisUnitRestriction_rebased_stage E F H hEH hFH y
  have hE := localFieldContinuousH2InvariantEquiv_stage E Ω
    (finiteGaloisStageExtendScalars E H hEH) (finiteGaloisUnitBaseChangeH2 K E F H y)
  have hF := localFieldContinuousH2InvariantEquiv_stage K Ω F y
  have hbase := localFieldPeriodRationalInvariant_baseChange K E F H y
  exact (congrArg (localFieldContinuousH2InvariantEquiv E Ω) hres).trans
    (hE.trans (hbase.trans (congrArg (fun q : AddCircle (1 : ℚ) => Module.finrank K E • q) hF.symm)))

end
end Dubon2026
