import Dubon2026.SourceEllipticFullTorsionModularEmbeddings
import Dubon2026.SourceEllipticFixedCurvePointMap

/-! Reflect the actual field-action orbits through the modular embedding
equivalence. This uses the existing image cyclic subgroup and injectivity,
as in the proved root-orbit comparison, avoiding an intermediate root
presentation in the DUB-17/18 characteristic-three place census. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine SourceFunctionField
open SourceFunctionField.CoefficientPresentation SourceFunctionField.IntegralJCoordinate
open SourceEllipticVelu
noncomputable section

theorem modularEmbeddingEquiv_galois_orbit_iff
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M] [DecidableEq M]
    [DecidableEq (RatFunc K)]
    (N : ℕ)
    (Φ : {S : AddSubgroup ((ofJ (RatFunc.X : RatFunc K)).baseChange M).toAffine.Point //
        IsAddCyclic S ∧ Nat.card S = N} ≃
      {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
        ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X})
    (hnat : ∀ (σ : M ≃ₐ[RatFunc K] M) S T,
      T.val = S.val.map (Point.map (W' := ofJ (RatFunc.X : RatFunc K)) σ.toAlgHom) →
        (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val)
    (I : Type*) (σGal : I → M ≃ₐ[RatFunc K] M)
    (S T : {S : AddSubgroup ((ofJ (RatFunc.X : RatFunc K)).baseChange M).toAffine.Point //
      IsAddCyclic S ∧ Nat.card S = N}) :
    (∃ σ : I, S.val.map (Point.map (W' := ofJ (RatFunc.X : RatFunc K))
      (σGal σ).toAlgHom) = T.val) ↔
      ∃ σ : I, (Φ T).val = ((σGal σ).toAlgHom.restrictScalars K).comp (Φ S).val := by
  let E := ofJ (RatFunc.X : RatFunc K)
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hnat (σGal σ) S T hσ.symm⟩
  · rintro ⟨σ, hσ⟩
    let U := fixedCurveCyclicKernelMap (σGal σ).toRingHom (E.baseChange M)
      (E.map_baseChange (σGal σ).toAlgHom) N S
    have hU : U.val = S.val.map (Point.map (W' := E) (σGal σ).toAlgHom) := by
      rw [fixedCurveCyclicKernelMap_coe, fixedCurvePointMap_galois]
    have hv : (Φ T).val = (Φ U).val := hσ.trans (hnat (σGal σ) S U hU).symm
    have hTU := Φ.injective (Subtype.ext hv)
    exact ⟨σ, hU.symm.trans (congrArg Subtype.val hTU).symm⟩

end
end Dubon2026.SourceEllipticDivisionField
