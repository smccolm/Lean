import Dubon2026.GaloisUnitRelationDualSequence
import Dubon2026.GaloisTowerLocalUnitRelationCup
import Dubon2026.OriginalDualRelationCupAdjunction
import Mathlib.RepresentationTheory.Invariants

/-! The source-local finite relation defines a genuine dual connecting
H1 class, and its retained continuous relation cup is the cup with that
class. This supplies the local comparison for DUB-17's prescribed-class
recovery from the actual finite S-unit correction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance]
  localRelationCupKernelTopology localRelationCupKernelDiscrete localRelationCupKernelContinuousSMul
  localRelationCupFreeTopology localRelationCupFreeDiscrete localRelationCupFreeContinuousSMul
  localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete localRelationCupCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  localRelationCupCoefficientHomTopology localRelationCupCoefficientHomDiscrete localRelationCupCoefficientHomContinuousSMul
  localRelationCupFreeHomTopology localRelationCupFreeHomDiscrete localRelationCupFreeHomContinuousSMul
  localRelationCupKernelHomTopology localRelationCupKernelHomDiscrete localRelationCupKernelHomContinuousSMul

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [IsGalois K L] [IsGalois K Ω] [FiniteDimensional K L] [IsAlgClosed Ω]
  (H : Type) [Group H] [Finite H] (ι : Gal(L/K) →* H) (B : Rep.{0} ℤ H) [Finite B]
  (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)

/-- The actual local relation invariant in the original local unit dual. -/
def galoisTowerLocalUnitRelationInvariant
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L) :
    ((Rep.ihom (galoisTowerLocalRelationComplex K L Ω H ι B).X₁).obj
      (Rep.ofAlgebraAutOnUnits K Ω)).ρ.invariants :=
  (Representation.linHom.invariantsEquivRepHom _ _).symm
    ((Rep.resFunctor (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))).map ψ ≫
      finiteGaloisUnitTowerInclusion K L Ω)

/-- The source-local relation produces its original continuous dual H1
class, with dual exactness and both action-continuity inputs derived. -/
def galoisTowerLocalUnitDualConnectingClass
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L) :
    ContinuousRepresentationH1 (galoisTowerLocalCoefficientUnitHom K L Ω H ι B)
      (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B) :=
  continuousShortComplexInvariantConnectingMap
    (originalContravariantHomShortComplex (galoisTowerLocalRelationComplex K L Ω H ι B)
      (Rep.ofAlgebraAutOnUnits K Ω))
    (galoisUnitRelationDualSequence_shortExact K Ω H
      (ι.comp (AlgEquiv.restrictNormalHom L : Gal(Ω/K) →* Gal(L/K))) q B hCoeff)
    (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
    (galoisTowerPartialFreeUnitHomAction_continuous K L Ω H ι B)
    (galoisTowerLocalUnitRelationInvariant K L Ω H ι B ψ)

/-- The source's actual local relation cup equals the continuous cup
against its constructed dual connecting class. -/
theorem galoisTowerLocalUnitRelationConnecting_cup
    (ψ : Rep.res ι (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits K L)
    (x : galoisTowerLocalCoefficientH1 K L Ω H ι B) :
    let X := galoisTowerLocalRelationComplex K L Ω H ι B
    let D := Rep.ofAlgebraAutOnUnits K Ω
    galoisTowerLocalUnitRelationConnecting K L Ω H ι B ψ x =
      continuousH1Cup X.X₃ ((Rep.ihom X.X₃).obj D) D
        (originalInternalHomEvaluation X.X₃ D) (originalInternalHomEvaluation_equivariant X.X₃ D)
        continuous_of_discreteTopology (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
        (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) x
        (galoisTowerLocalUnitDualConnectingClass K L Ω H ι B q hCoeff ψ) := by
  let π : Gal(Ω/K) →* H := ι.comp (AlgEquiv.restrictNormalHom L)
  let X := galoisTowerLocalRelationComplex K L Ω H ι B
  let D := Rep.ofAlgebraAutOnUnits K Ω
  exact originalDualRelationCup_adjunction X D
    (originalRelationGroupChange_shortExact π B)
    (galoisUnitRelationDualSequence_shortExact K Ω H π q B hCoeff)
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (originalRelationModule B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι (Rep.free ℤ H B))
    (galoisTowerRestrictedCoefficientAction_continuous K L Ω H ι B)
    (galoisTowerLocalCoefficientUnitHomAction_continuous K L Ω H ι B)
    (galoisTowerPartialFreeUnitHomAction_continuous K L Ω H ι B)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) x
    (galoisTowerLocalUnitRelationInvariant K L Ω H ι B ψ)

end
end Dubon2026
