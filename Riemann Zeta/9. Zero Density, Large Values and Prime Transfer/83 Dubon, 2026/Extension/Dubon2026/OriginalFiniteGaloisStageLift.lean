import Dubon2026.ContinuousGaloisBaseChangeFiniteStage

/-! # A finite stage inside the original intermediate field retains its ambient embedding

Pinned intermediate-field lifting identifies the actual nested finite
field with its literal ambient image. The scalar towers and original
continuous inflation comparison let DUB-17's arithmetic Kummer stage enter
the cyclic descent theorem without replacing its field or class.
-/
namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (U : IntermediateField K Ω) (F : FiniteGaloisIntermediateField K U)

/-- Lift the original finite stage to its literal image in the original ambient field. -/
def originalFiniteGaloisStageLift : FiniteGaloisIntermediateField K Ω := by
  let E := IntermediateField.lift F.toIntermediateField
  let e : F ≃ₐ[K] E := IntermediateField.liftAlgEquiv F.toIntermediateField
  letI : FiniteDimensional K E := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K E := IsGalois.of_algEquiv e
  exact ⟨E⟩

/-- The lifted finite stage lies inside the same original intermediate field. -/
theorem originalFiniteGaloisStageLift_le :
    (originalFiniteGaloisStageLift U F).toIntermediateField ≤ U :=
  IntermediateField.lift_le F.toIntermediateField

/-- The actual original finite field and its lifted image are equivalent over the original base. -/
def originalFiniteGaloisStageLiftEquiv : F ≃ₐ[K] originalFiniteGaloisStageLift U F :=
  IntermediateField.liftAlgEquiv F.toIntermediateField

/-- Retain the original finite-field embedding in its lifted image. -/
abbrev originalFiniteGaloisStageLiftAlgebra : Algebra F (originalFiniteGaloisStageLift U F) :=
  (originalFiniteGaloisStageLiftEquiv U F).toRingHom.toAlgebra

/-- Include the actual lifted image in the same original intermediate field. -/
abbrev originalFiniteGaloisStageLiftUpperAlgebra : Algebra (originalFiniteGaloisStageLift U F) U :=
  (IntermediateField.inclusion (originalFiniteGaloisStageLift_le U F)).toAlgebra

attribute [local instance] originalFiniteGaloisStageLiftAlgebra originalFiniteGaloisStageLiftUpperAlgebra

/-- The actual lifted image preserves the original base scalar tower. -/
theorem originalFiniteGaloisStageLift_baseTower :
    IsScalarTower K F (originalFiniteGaloisStageLift U F) :=
  IsScalarTower.of_algHom (originalFiniteGaloisStageLiftEquiv U F).toAlgHom

/-- Inclusion of the lifted image preserves the original intermediate-field scalar tower. -/
theorem originalFiniteGaloisStageLift_upperBaseTower :
    IsScalarTower K (originalFiniteGaloisStageLift U F) U :=
  IsScalarTower.of_algHom (IntermediateField.inclusion (originalFiniteGaloisStageLift_le U F))

/-- The actual finite-to-image-to-upper embedding is literally the original finite-stage inclusion. -/
theorem originalFiniteGaloisStageLift_upperTower :
    IsScalarTower F (originalFiniteGaloisStageLift U F) U :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [IsGalois K U]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K U)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K U)]

/-- Use the original finite-stage coefficient topology. -/
local instance originalStageLiftFiniteTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥

/-- The original finite-stage coefficients are discrete. -/
local instance originalStageLiftFiniteDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩

/-- Passing through the constructed literal ambient image preserves the original continuous finite-stage inflation. -/
theorem originalFiniteGaloisStageLift_inflation
    (x : GaloisUnitContinuousH2 (K := K) (Ω := F)) :
    let E := originalFiniteGaloisStageLift U F
    letI := originalFiniteGaloisStageLift_baseTower U F
    letI := originalFiniteGaloisStageLift_upperBaseTower U F
    letI := originalFiniteGaloisStageLift_upperTower U F
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
    continuousGaloisUnitBaseChangeH2 K K E U
      (finiteGaloisUnitBaseChangeH2 K K F E x) = galoisUnitFiniteStageH2Inflation F x := by
  let E := originalFiniteGaloisStageLift U F
  letI := originalFiniteGaloisStageLift_baseTower U F
  letI := originalFiniteGaloisStageLift_upperBaseTower U F
  letI := originalFiniteGaloisStageLift_upperTower U F
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact (continuousGaloisUnitBaseChangeH2_comp K K K F E U x).trans
    (continuousGaloisUnitBaseChangeH2_eq_finiteStage K U F x)

end
end Dubon2026
