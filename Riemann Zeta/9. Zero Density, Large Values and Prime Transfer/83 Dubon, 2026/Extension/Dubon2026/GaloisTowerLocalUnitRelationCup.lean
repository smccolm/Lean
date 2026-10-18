import Dubon2026.GaloisTowerLocalRelationContinuity
import Dubon2026.OriginalRelationCupContinuous
import Dubon2026.OriginalRelationGroupChange

/-! The constructed local unit relation represents the original continuous
cup class. Continuity, short exactness and the free-cover lift are derived
from the original finite data and Hilbert 90. This is the local connecting
square required by DUB-17's normalized source total and reverse localization. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] [FiniteDimensional K L]
  (H : Type) [Group H] [Finite H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H) [Finite B]

/-- The original relation presentation restricted through the actual local group map. -/
abbrev galoisTowerLocalRelationComplex : ShortComplex (Rep.{0} ℤ Gal(Ω/K)) :=
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  { X₁ := Rep.res π (originalRelationModule B)
    X₂ := Rep.res π (Rep.free ℤ H B)
    X₃ := Rep.res π B
    f := (Rep.resFunctor π).map (originalRelationInclusion B)
    g := (Rep.resFunctor π).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor π)).zero }

/-- Use the original discrete kernel coefficient topology. -/
local instance localRelationCupKernelTopology : TopologicalSpace ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))) := ⊥
/-- The original kernel coefficient is discrete. -/
local instance localRelationCupKernelDiscrete : DiscreteTopology ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete kernel coefficient. -/
local instance localRelationCupKernelContinuousSMul :
    @ContinuousSMul ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete free coefficient topology. -/
local instance localRelationCupFreeTopology : TopologicalSpace ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))) := ⊥
/-- The original free coefficient is discrete. -/
local instance localRelationCupFreeDiscrete : DiscreteTopology ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete free coefficient. -/
local instance localRelationCupFreeContinuousSMul :
    @ContinuousSMul ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (Rep.free ℤ H B))).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete coefficient coefficient topology. -/
local instance localRelationCupCoefficientTopology : TopologicalSpace ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) := ⊥
/-- The original coefficient coefficient is discrete. -/
local instance localRelationCupCoefficientDiscrete : DiscreteTopology ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete coefficient coefficient. -/
local instance localRelationCupCoefficientContinuousSMul :
    @ContinuousSMul ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)) ((Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete units coefficient topology. -/
local instance localRelationCupUnitsTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
/-- The original units coefficient is discrete. -/
local instance localRelationCupUnitsDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete units coefficient. -/
local instance localRelationCupUnitsContinuousSMul :
    @ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete coefficienthom coefficient topology. -/
local instance localRelationCupCoefficientHomTopology : TopologicalSpace (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) := ⊥
/-- The original coefficienthom coefficient is discrete. -/
local instance localRelationCupCoefficientHomDiscrete : DiscreteTopology (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete coefficienthom coefficient. -/
local instance localRelationCupCoefficientHomContinuousSMul :
    @ContinuousSMul ℤ (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) (galoisTowerLocalCoefficientUnitHom K L Ω H ι B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) (galoisTowerLocalCoefficientUnitHom K L Ω H ι B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete freehom coefficient topology. -/
local instance localRelationCupFreeHomTopology : TopologicalSpace (galoisTowerPartialFreeUnitHom K L Ω H ι B) := ⊥
/-- The original freehom coefficient is discrete. -/
local instance localRelationCupFreeHomDiscrete : DiscreteTopology (galoisTowerPartialFreeUnitHom K L Ω H ι B) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete freehom coefficient. -/
local instance localRelationCupFreeHomContinuousSMul :
    @ContinuousSMul ℤ (galoisTowerPartialFreeUnitHom K L Ω H ι B) (galoisTowerPartialFreeUnitHom K L Ω H ι B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (galoisTowerPartialFreeUnitHom K L Ω H ι B) (galoisTowerPartialFreeUnitHom K L Ω H ι B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Use the original discrete kernelhom coefficient topology. -/
local instance localRelationCupKernelHomTopology : TopologicalSpace ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)) := ⊥
/-- The original kernelhom coefficient is discrete. -/
local instance localRelationCupKernelHomDiscrete : DiscreteTopology ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete kernelhom coefficient. -/
local instance localRelationCupKernelHomContinuousSMul :
    @ContinuousSMul ℤ ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)) ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)) ((Rep.ihom (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) (originalRelationModule B))).obj (Rep.ofAlgebraAutOnUnits K Ω)).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Continuous H1 of the original coefficient under the actual local restriction. -/
abbrev galoisTowerLocalCoefficientH1 :=
  ContinuousRepresentationH1 (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)

/-- The actual continuous local evaluation cup, before any invariant normalization. -/
def galoisTowerLocalUnitCup
    (c : continuousRepresentationCocyclesOne (galoisTowerLocalCoefficientUnitHom K L Ω H ι B))
    (x : galoisTowerLocalCoefficientH1 K L Ω H ι B) :
    ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) :=
  continuousH1Cup (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)
    (galoisTowerLocalCoefficientUnitHom K L Ω H ι B) (Rep.ofAlgebraAutOnUnits K Ω)
    (originalInternalHomEvaluation (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)
      (Rep.ofAlgebraAutOnUnits K Ω))
    (originalInternalHomEvaluation_equivariant (Rep.res (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) B)
      (Rep.ofAlgebraAutOnUnits K Ω))
    continuous_of_discreteTopology (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) x
    ((continuousRepresentationCoboundariesOne (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)
      (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)).mkQ c)

/-- The same original local relation map applied to the continuous connecting class. -/
def galoisTowerLocalUnitRelationConnecting
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (x : galoisTowerLocalCoefficientH1 K L Ω H ι B) :
    ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) := by
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  let X := galoisTowerLocalRelationComplex K L Ω H ι B
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
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₂).obj D) (((Rep.ihom X.X₂).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₂).obj D) (((Rep.ihom X.X₂).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₁).obj D) (((Rep.ihom X.X₁).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₁).obj D) (((Rep.ihom X.X₁).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  let φ : X.X₁ ⟶ D :=
    (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))).map ψ ≫
      finiteGaloisUnitTowerInclusion K L Ω
  exact continuousCoefficientH2Map X.X₁ D φ.hom.toLinearMap continuous_of_discreteTopology
    (Rep.hom_comm_apply φ)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (originalRelationModule B))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    (continuousShortComplexConnectingMap X (originalRelationGroupChange_shortExact π B)
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (originalRelationModule B))
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (Rep.free ℤ H B))
      (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B) x)

/-- One constructed original local relation morphism represents every cup
with the given local Hom cocycle in continuous H2 itself. The short exact
sequence, action continuity, free lift and same-field descent are derived. -/
theorem galoisTowerLocalUnitCocycle_exists_relation_cup
    (hι : Function.Injective ι)
    (c : continuousRepresentationCocyclesOne (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)) :
    ∃ ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L,
      ∀ x : galoisTowerLocalCoefficientH1 K L Ω H ι B,
        galoisTowerLocalUnitCup K L Ω H ι B c x =
          galoisTowerLocalUnitRelationConnecting K L Ω H ι B ψ x := by
  obtain ⟨u, ψ, he, hu⟩ := galoisTowerLocalUnitCocycle_exists_relation_representative
    K L Ω H ι B hι c
  refine ⟨ψ, ?_⟩
  intro x
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  let X := galoisTowerLocalRelationComplex K L Ω H ι B
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
  letI : TopologicalSpace D := ⊥
  letI : DiscreteTopology D := ⟨rfl⟩
  letI : @ContinuousSMul ℤ D (D).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ D (D).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₃).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₃).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₃).obj D) (((Rep.ihom X.X₃).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₂).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₂).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₂).obj D) (((Rep.ihom X.X₂).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₂).obj D) (((Rep.ihom X.X₂).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  letI : TopologicalSpace ((Rep.ihom X.X₁).obj D) := ⊥
  letI : DiscreteTopology ((Rep.ihom X.X₁).obj D) := ⟨rfl⟩
  letI : @ContinuousSMul ℤ ((Rep.ihom X.X₁).obj D) (((Rep.ihom X.X₁).obj D)).hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ ((Rep.ihom X.X₁).obj D) (((Rep.ihom X.X₁).obj D)).hV2.toSMul _ _ continuous_of_discreteTopology
  let φ : X.X₁ ⟶ D :=
    (Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))).map ψ ≫
      finiteGaloisUnitTowerInclusion K L Ω
  exact originalRelationCup_explicit_lift_continuous X D
    (originalRelationGroupChange_shortExact π B)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (originalRelationModule B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (Rep.free ℤ H B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
    (galoisTowerPartialFreeUnitHomAction_continuous K L Ω H ι B)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) x c u φ hu he

end
end Dubon2026
