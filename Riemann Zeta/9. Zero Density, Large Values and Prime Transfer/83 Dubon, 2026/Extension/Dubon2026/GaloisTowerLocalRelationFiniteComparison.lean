import Dubon2026.GaloisTowerLocalUnitRelationCup
import Dubon2026.ContinuousShortComplexObstructionSquare
import Dubon2026.ContinuousGaloisUnitBaseChange

/-! Finite-to-infinite comparison for the actual local relation obstruction.
The original continuous connecting square identifies the same local relation
class under genuine Galois base change. This is needed to match the finite
S-place obstruction with the normalized continuous local cup invariant. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] localRelationCupKernelTopology localRelationCupKernelDiscrete
  localRelationCupKernelContinuousSMul localRelationCupFreeTopology localRelationCupFreeDiscrete
  localRelationCupFreeContinuousSMul localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete
  localRelationCupCoefficientContinuousSMul localRelationCupUnitsTopology localRelationCupUnitsDiscrete
  localRelationCupUnitsContinuousSMul
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] [FiniteDimensional K L]
  (H : Type) [Group H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H)

/-- The original global relation presentation at the specified finite local group. -/
abbrev galoisTowerFiniteLocalRelationComplex : ShortComplex (Rep.{0} ℤ Gal(L/K)) :=
  { X₁ := Rep.res ι (originalRelationModule B)
    X₂ := Rep.res ι (Rep.free ℤ H B)
    X₃ := Rep.res ι B
    f := (Rep.resFunctor ι).map (originalRelationInclusion B)
    g := (Rep.resFunctor ι).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor ι)).zero }

/-- Retain the original discrete finite kernel coefficient topology. -/
local instance finiteLocalRelationKernelTopology : TopologicalSpace (Rep.res ι (originalRelationModule B)) := ⊥
/-- The finite kernel coefficient topology is discrete. -/
local instance finiteLocalRelationKernelDiscrete : DiscreteTopology (Rep.res ι (originalRelationModule B)) := ⟨rfl⟩
/-- Integer scalar multiplication is continuous on the original discrete coefficient. -/
local instance finiteLocalRelationKernelContinuousSMul :
    @ContinuousSMul ℤ (Rep.res ι (originalRelationModule B)) (Rep.res ι (originalRelationModule B)).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (Rep.res ι (originalRelationModule B)) (Rep.res ι (originalRelationModule B)).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Retain the original discrete finite free coefficient topology. -/
local instance finiteLocalRelationFreeTopology : TopologicalSpace (Rep.res ι (Rep.free ℤ H B)) := ⊥
/-- The finite free coefficient topology is discrete. -/
local instance finiteLocalRelationFreeDiscrete : DiscreteTopology (Rep.res ι (Rep.free ℤ H B)) := ⟨rfl⟩
/-- Integer scalar multiplication is continuous on the original discrete coefficient. -/
local instance finiteLocalRelationFreeContinuousSMul :
    @ContinuousSMul ℤ (Rep.res ι (Rep.free ℤ H B)) (Rep.res ι (Rep.free ℤ H B)).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (Rep.res ι (Rep.free ℤ H B)) (Rep.res ι (Rep.free ℤ H B)).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Retain the original discrete finite coefficient coefficient topology. -/
local instance finiteLocalRelationCoefficientTopology : TopologicalSpace (Rep.res ι B) := ⊥
/-- The finite coefficient coefficient topology is discrete. -/
local instance finiteLocalRelationCoefficientDiscrete : DiscreteTopology (Rep.res ι B) := ⟨rfl⟩
/-- Integer scalar multiplication is continuous on the original discrete coefficient. -/
local instance finiteLocalRelationCoefficientContinuousSMul :
    @ContinuousSMul ℤ (Rep.res ι B) (Rep.res ι B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (Rep.res ι B) (Rep.res ι B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Actual finite local H1, before original Galois restriction into the closure. -/
abbrev galoisTowerFiniteLocalCoefficientH1 :=
  ContinuousRepresentationH1 (Rep.res ι B) continuous_of_discreteTopology

/-- The original finite local H1 inflates through restriction, retaining its coefficient values. -/
def galoisTowerFiniteLocalH1Inflation
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B) :
    galoisTowerLocalCoefficientH1 K L Ω H ι B :=
  let π : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let hπ := galoisTowerNormalRestriction_continuous K L Ω
  continuousCoefficientH1Map (Rep.res π (Rep.res ι B)) (Rep.res (ι.comp π) B)
    LinearMap.id continuous_of_discreteTopology (fun _ _ => rfl)
    (restrictedCoefficientAction_continuous (Rep.res ι B) π hπ continuous_of_discreteTopology)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    (continuousRepresentationH1Restriction (Rep.res ι B) continuous_of_discreteTopology π hπ x)

/-- The actual same-field local unit relation applied to its finite connecting class. -/
def galoisTowerFiniteLocalRelationConnecting
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B) :
    GaloisUnitContinuousH2 (K := K) (Ω := L) :=
  continuousCoefficientH2Map (Rep.res ι (originalRelationModule B)) (Rep.ofAlgebraAutOnUnits K L)
    ψ.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply ψ)
    continuous_of_discreteTopology (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
    (continuousShortComplexConnectingMap (galoisTowerFiniteLocalRelationComplex K L H ι B)
      (originalRelationGroupChange_shortExact ι B)
      continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology x)

/-- The constructed local relation connecting class is the actual continuous
Galois base change of the same finite local connecting obstruction. -/
theorem galoisTowerLocalRelationConnecting_eq_finite_baseChange
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (x : galoisTowerFiniteLocalCoefficientH1 K L H ι B) :
    galoisTowerLocalUnitRelationConnecting K L Ω H ι B ψ
      (galoisTowerFiniteLocalH1Inflation K L Ω H ι B x) =
    continuousGaloisUnitBaseChangeH2 K K L Ω
      (galoisTowerFiniteLocalRelationConnecting K L H ι B ψ x) := by
  let π : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let hπ := galoisTowerNormalRestriction_continuous K L Ω
  let X := galoisTowerFiniteLocalRelationComplex K L H ι B
  let Y := galoisTowerLocalRelationComplex K L Ω H ι B
  let C := Rep.ofAlgebraAutOnUnits K L
  let D := Rep.ofAlgebraAutOnUnits K Ω
  letI : TopologicalSpace X.X₁ := ⊥
  letI : DiscreteTopology X.X₁ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₁ (X.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₁ (X.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₂ := ⊥
  letI : DiscreteTopology X.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₂ (X.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₂ (X.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace X.X₃ := ⊥
  letI : DiscreteTopology X.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ X.X₃ (X.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ X.X₃ (X.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace Y.X₁ := ⊥
  letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₁ (Y.X₁).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₁ (Y.X₁).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace Y.X₂ := ⊥
  letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₂ (Y.X₂).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₂ (Y.X₂).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace Y.X₃ := ⊥
  letI : DiscreteTopology Y.X₃ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₃ (Y.X₃).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₃ (Y.X₃).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  letI : @ContinuousSMul ℤ C (C).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ C (C).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  let d : (Rep.resFunctor π).mapShortComplex.obj X ⟶ Y :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  let j := finiteGaloisUnitTowerInclusion K L Ω
  let φ := (Rep.resFunctor π).map ψ ≫ j
  have hs : (Rep.resFunctor π).map ψ ≫ j = d.τ₁ ≫ φ := by
    exact (Category.id_comp φ).symm
  exact continuousShortComplex_obstruction_square π hπ X Y d
    (originalRelationGroupChange_shortExact ι B)
    (originalRelationGroupChange_shortExact (ι.comp π) B)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (originalRelationModule B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (Rep.free ℤ H B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    C D (discreteGaloisUnitAction_continuous (K := K) (Ω := L))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) ψ j φ hs x

end
end Dubon2026
