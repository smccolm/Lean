import Dubon2026.ContinuousGaloisBaseChangeFiniteStage

/-! # Restriction to an arbitrary intermediate base on genuine finite stages -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K Ω)
  (G : FiniteGaloisIntermediateField E Ω)
  [Algebra F G] [IsScalarTower K F G] [IsScalarTower F G Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- On the original finite cocycle, changing the fixed base and then
inflating equals inflating first and restricting. No normality of the new
base over the original base is assumed. -/
private theorem continuousGaloisUnitRestriction_general_compositum
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 E E G Ω (finiteGaloisUnitBaseChangeH2 K E F G x) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
  have hleft : continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      continuousGaloisUnitBaseChangeH2 K E F Ω x :=
    (congrArg (continuousGaloisUnitBaseChangeH2 K E Ω Ω)
      (continuousGaloisUnitBaseChangeH2_eq_finiteStage K Ω F x).symm).trans
        (continuousGaloisUnitBaseChangeH2_comp K K E F Ω Ω x)
  have hright : continuousGaloisUnitBaseChangeH2 E E G Ω
      (finiteGaloisUnitBaseChangeH2 K E F G x) = continuousGaloisUnitBaseChangeH2 K E F Ω x :=
    continuousGaloisUnitBaseChangeH2_comp K E E F G Ω x
  exact hleft.trans hright.symm

/-- Actual restriction of an inflated class is the original finite
base change inflated from a genuine stage over the new intermediate base. -/
theorem continuousGaloisUnitRestriction_general_stage
    (x : GaloisUnitH2FiniteStage K Ω F) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K E Ω Ω (galoisUnitH2FiniteStageMap K Ω F x) =
      galoisUnitH2FiniteStageMap E Ω G (finiteGaloisUnitBaseChangeH2 K E F G x) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E G) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E G) := ⟨rfl⟩
  exact (continuousGaloisUnitRestriction_general_compositum E F G x).trans
    (continuousGaloisUnitBaseChangeH2_eq_finiteStage E Ω G (finiteGaloisUnitBaseChangeH2 K E F G x))

end
end Dubon2026
