import Dubon2026.FiniteGaloisStageRebasedCohomology

/-! # Actual full restriction is inflation from the original rebased finite stage -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Restricting an original inflated finite-stage class equals
inflation of its actual finite base change in any genuine common finite
extension. The upper stage is the same field with its fixed base extended. -/
private theorem continuousGaloisUnitRestriction_rebased_compositum
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 E E H Ω
        (finiteGaloisUnitBaseChangeH2 K E F H x) := by
  letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  haveI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
  haveI : IsScalarTower F H Ω := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E H := FiniteDimensional.right K E H
  haveI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
  have hleft : continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 K E F Ω x :=
    (congrArg (continuousGaloisUnitBaseChangeH2 K E Ω Ω)
      (continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F x).symm).trans
        (continuousGaloisUnitBaseChangeH2_comp K K E F Ω Ω x)
  have hright : continuousGaloisUnitBaseChangeH2 E E H Ω
      (finiteGaloisUnitBaseChangeH2 K E F H x) = continuousGaloisUnitBaseChangeH2 K E F Ω x :=
    continuousGaloisUnitBaseChangeH2_comp K E E F H Ω x
  exact hleft.trans hright.symm

/-- Restricting an original inflated finite-stage class equals
inflation of its actual finite base change in any genuine common finite
extension. The upper stage is the same field with its fixed base extended. -/
theorem continuousGaloisUnitRestriction_rebased_stage
    (E F H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : IsScalarTower K E H := .of_algebraMap_eq' rfl
    letI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
    letI : FiniteDimensional E H := FiniteDimensional.right K E H
    letI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω (finiteGaloisStageExtendScalars E H hEH)
        (finiteGaloisUnitBaseChangeH2 K E F H x) := by
  letI : Algebra E H := inferInstanceAs (Algebra E (finiteGaloisStageExtendScalars E H hEH))
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  haveI : IsScalarTower K E H := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  haveI : IsScalarTower E H Ω := .of_algebraMap_eq' rfl
  haveI : IsScalarTower F H Ω := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E H := FiniteDimensional.right K E H
  haveI : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E H) := ⟨rfl⟩
  exact (continuousGaloisUnitRestriction_rebased_compositum E F H hEH hFH x).trans
    (continuousGaloisUnitBaseChangeH2_eq_finiteStage E Ω
      (finiteGaloisStageExtendScalars E H hEH) (finiteGaloisUnitBaseChangeH2 K E F H x))

end
end Dubon2026
