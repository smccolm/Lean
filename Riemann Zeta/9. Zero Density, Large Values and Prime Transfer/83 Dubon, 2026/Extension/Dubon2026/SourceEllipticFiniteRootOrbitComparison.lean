import Dubon2026.SourceEllipticFixedCurvePointMap

/-! An equivariant exact finite-field root equivalence preserves and reflects
the original field-action orbits. The reverse implication uses the actual
image cyclic subgroup and injectivity of the proved equivalence. This is
applied to the actual inertia group in the DUB-17/18 exceptional-fiber route. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve WeierstrassCurve.Affine SourceFunctionField.IntegralJCoordinate
noncomputable section

theorem cyclicRootEquiv_galois_orbit_iff
    {B M : Type*} [Field B] [Field M] [Algebra B M] [DecidableEq M]
    (E : WeierstrassCurve B) (N : ℕ) (P : Polynomial M)
    (Θ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
      {y : M // P.IsRoot y})
    (hnat : ∀ (σ : M ≃ₐ[B] M) S T,
      T.val = S.val.map (Point.map (W' := E) σ.toAlgHom) → (Θ T).val = σ (Θ S).val)
    (I : Type*) (σGal : I → M ≃ₐ[B] M)
    (S T : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    (∃ σ : I, S.val.map (Point.map (W' := E) (σGal σ).toAlgHom) = T.val) ↔
      ∃ σ : I, (Θ T).val = σGal σ (Θ S).val := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hnat (σGal σ) S T hσ.symm⟩
  · rintro ⟨σ, hσ⟩
    let U := fixedCurveCyclicKernelMap (σGal σ).toRingHom (E.baseChange M)
      (E.map_baseChange (σGal σ).toAlgHom) N S
    have hU : U.val = S.val.map (Point.map (W' := E) (σGal σ).toAlgHom) := by
      rw [fixedCurveCyclicKernelMap_coe, fixedCurvePointMap_galois]
    have hv : (Θ T).val = (Θ U).val := hσ.trans (hnat (σGal σ) S U hU).symm
    have hTU := Θ.injective (Subtype.ext hv)
    exact ⟨σ, hU.symm.trans (congrArg Subtype.val hTU).symm⟩

end
end Dubon2026.SourceEllipticVelu
