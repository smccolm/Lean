import Dubon2026.OriginalSPlaceRelationCompletionObstruction
import Dubon2026.OriginalAdicLocalFiniteRelationCup
import Dubon2026.GaloisTowerFiniteLocalConnectingAlgebraic
import Dubon2026.OriginalFullIdeleCompletionInvariant

/-! The original full-idele completion invariant of an S-place relation
obstruction is the invariant of its actual continuous local connecting
class. Only literal coefficient and H1 input identities are used. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois
  originalAdicLocalRelationCupFinite originalCompletionCarryValuation originalCompletionCarryLocalField
  finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (v : HeightOneSpectrum (𝓞 K)) (w : S) [w.val.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.val.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.val.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  (B : Rep.{0} ℤ Gal(L/K))

/-- The normalized completion invariant of the actual S-place obstruction
agrees with the same original local continuous connecting class. -/
theorem originalSPlaceRelation_completion_invariant
    (Φ : originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS)
    (ψ : Rep.res (originalAdicCompletionGaloisInclusion K L v w.val)
      (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L))
    (heval : ∀ z : originalRelationModule B, Φ.hom z (Sum.inr w) = ψ.hom z)
    (y : groupCohomology B 1)
    (x : galoisTowerFiniteLocalCoefficientH1 (v.adicCompletion K) (w.val.adicCompletion L)
      Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B)
    (hxy : continuousH1ToAlgebraic
      (Rep.res (originalAdicCompletionGaloisInclusion K L v w.val) B)
      continuous_of_discreteTopology x =
      groupCohomology.map (originalAdicCompletionGaloisInclusion K L v w.val)
        (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L v w.val) B)) 1 y) :
    originalFullIdeleCompletionInvariant K L v w.val Ω
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
        (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS) Φ y)) =
    localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
      (galoisTowerLocalUnitRelationConnecting (v.adicCompletion K) (w.val.adicCompletion L) Ω
        Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B ψ
        (galoisTowerFiniteLocalH1Inflation (v.adicCompletion K) (w.val.adicCompletion L) Ω
          Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B x)) := by
  let C := Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L)
  let hC := discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.val.adicCompletion L)
  let e := continuousDiscreteH2Equiv C hC
  let u := (groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
    (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS) Φ y)
  let z := galoisTowerFiniteLocalRelationConnecting (v.adicCompletion K) (w.val.adicCompletion L)
    Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B ψ x
  have hc := galoisTowerFiniteLocalRelationConnecting_toAlgebraic (v.adicCompletion K)
    (w.val.adicCompletion L) Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B ψ x
  rw [hxy] at hc
  have he : e.symm (originalFullIdeleCompletionH2 K L v w.val u) = z := by
    apply e.injective
    exact (e.apply_symm_apply _).trans
      ((originalSPlaceRelation_completion_obstruction K L S hS v w B Φ ψ heval y).trans hc.symm)
  let b := continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
    (w.val.adicCompletion L) Ω
  let inv := localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
  exact (congrArg (fun t => inv (b t)) he).trans
    (congrArg inv (galoisTowerLocalRelationConnecting_eq_finite_baseChange (v.adicCompletion K)
      (w.val.adicCompletion L) Ω Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w.val) B ψ x).symm)

end
end Dubon2026
