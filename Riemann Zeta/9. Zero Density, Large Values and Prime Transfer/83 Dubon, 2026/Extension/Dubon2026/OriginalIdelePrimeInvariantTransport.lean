import Dubon2026.OriginalIdelePrimeConjugation
import Dubon2026.OriginalFullIdeleInvariantClosureIndependence
import Dubon2026.FiniteGaloisH2InverseBaseChangeComparison
import Dubon2026.GaloisUnitBaseChangeComposition

/-! # Normalized original idele invariants under upper-prime transport

Use the proved original cohomology transport and the existing literal
composition law for inflation. Both prime coordinates are evaluated in
one common closure, with the source embedding explicitly transported.
This removes the local invariant comparison in DUB-17's upper-prime
independence step; arbitrary compatible closures are compared separately.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (u w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)
  (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- Transporting the source completion into the target's actual closure preserves the original normalized full-idele invariant. -/
theorem originalFullIdeleCompletionInvariant_prime_transport
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
    let j := (IsScalarTower.toAlgHom (v.adicCompletion K) (w.adicCompletion L) Ω).comp e.toAlgHom
    letI : Algebra (u.adicCompletion L) Ω := j.toRingHom.toAlgebra
    letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) Ω := IsScalarTower.of_algHom j
    originalFullIdeleCompletionInvariant K L v w Ω x =
      originalFullIdeleCompletionInvariant K L v u Ω x := by
  let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
  let j := (IsScalarTower.toAlgHom (v.adicCompletion K) (w.adicCompletion L) Ω).comp e.toAlgHom
  letI : Algebra (u.adicCompletion L) Ω := j.toRingHom.toAlgebra
  letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) Ω := IsScalarTower.of_algHom j
  letI : Algebra (u.adicCompletion L) (w.adicCompletion L) := e.toRingHom.toAlgebra
  letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L) :=
    IsScalarTower.of_algHom e.toAlgHom
  letI : IsScalarTower (u.adicCompletion L) (w.adicCompletion L) Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (u.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (u.adicCompletion L)) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  let eU := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (u.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := u.adicCompletion L))
  let eW := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  let y := eU.symm (originalFullIdeleCompletionH2 K L v u x)
  have hb := continuousDiscreteH2Equiv_symm_finiteGaloisBaseChange
    (v.adicCompletion K) (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L)
    (originalFullIdeleCompletionH2 K L v u x)
  have hc := (congrArg eW.symm
    (originalFullIdeleCompletionH2_prime_transport K L v u w σ hσ x)).symm.trans hb
  have hi := continuousGaloisUnitBaseChangeH2_comp
    (v.adicCompletion K) (v.adicCompletion K) (v.adicCompletion K)
    (u.adicCompletion L) (w.adicCompletion L) Ω y
  exact (congrArg (fun z => localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω z)) hc).trans
        (congrArg (localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω) hi)

end
end Dubon2026
