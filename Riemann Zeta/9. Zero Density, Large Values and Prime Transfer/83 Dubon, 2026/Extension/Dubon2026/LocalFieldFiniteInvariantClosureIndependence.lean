import Dubon2026.LocalFieldInvariantClosureTransport
import Mathlib.FieldTheory.IsSepClosed

/-! # Independence of the closure used for an actual finite local class

A separably closed lift over the actual finite coefficient field is
constructed. The proved closure transport and literal H2 composition
then identify the two normalized values. No comparison map is assumed;
this discharges the closure-choice input for DUB-17's canonical prime sum.
-/
namespace Dubon2026
noncomputable section

/-- The normalized invariant of the same actual finite local class is independent of the chosen separably closed Galois coefficient field and its compatible embedding. -/
theorem localFieldFiniteInvariant_closure_independent
    (K L Ω Ξ : Type) [Field K] [Field L] [Field Ω] [Field Ξ]
    [Algebra K L] [Algebra K Ω] [Algebra K Ξ] [Algebra L Ω] [Algebra L Ξ]
    [IsScalarTower K L Ω] [IsScalarTower K L Ξ]
    [IsGalois K L] [IsGalois K Ω] [IsGalois K Ξ] [IsSepClosed Ω] [IsSepClosed Ξ]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ξ)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ξ)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    localFieldContinuousH2InvariantEquiv K Ξ (continuousGaloisUnitBaseChangeH2 K K L Ξ x) =
      localFieldContinuousH2InvariantEquiv K Ω (continuousGaloisUnitBaseChangeH2 K K L Ω x) := by
  letI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  let φ : Ω →ₐ[L] Ξ := IsSepClosed.lift (K := L) (L := Ω) (M := Ξ)
  letI : Algebra Ω Ξ := φ.toRingHom.toAlgebra
  letI : IsScalarTower L Ω Ξ := IsScalarTower.of_algHom φ
  letI : IsScalarTower K Ω Ξ := IsScalarTower.of_algHom (φ.restrictScalars K)
  have hc := continuousGaloisUnitBaseChangeH2_comp K K K L Ω Ξ x
  have hi := localFieldContinuousInvariant_closure_transport K Ω Ξ
    (continuousGaloisUnitBaseChangeH2 K K L Ω x)
  exact (congrArg (localFieldContinuousH2InvariantEquiv K Ξ) hc).symm.trans hi

end
end Dubon2026
