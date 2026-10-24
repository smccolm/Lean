import Dubon2026.SourceEllipticFiniteFieldCyclicRoots
import Dubon2026.SourceEllipticDescendedCyclicGalois
import Dubon2026.SourceEllipticCyclicModularEmbeddings
import Dubon2026.SourceEllipticGenericCyclicRoots

/-! Assemble the already proved actual cyclic-root and modular-embedding
correspondences over a full-torsion field. No characteristic restriction
beyond invertibility of the level is introduced. The consumer serves the
DUB-17/18 wild inertia fixed-field construction. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_equivariant_modular_embeddings_of_full_torsion
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) (M : IntermediateField (RatFunc K) Ω)
    (hcard : Nat.card {P : ((ofJ (RatFunc.X : RatFunc K)).baseChange M).toAffine.Point //
      N • P = 0} = N ^ 2) :
    let E := ofJ (RatFunc.X : RatFunc K)
    ∃ Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
      {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
        ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X},
      ∀ (σ : M ≃ₐ[RatFunc K] M) S T,
        T.val = S.val.map (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) →
          (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val := by
  let E := ofJ (RatFunc.X : RatFunc K)
  letI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  letI : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) M x,
      ← IsScalarTower.algebraMap_apply (RatFunc K) M Ω,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) Ω]
  letI : Normal (RatFunc K) Ω := ⟨fun _ => IsAlgClosed.splits _⟩
  have hEt : (E.baseChange M).j = algebraMap (RatFunc K) M RatFunc.X := by
    change (E.map (algebraMap (RatFunc K) M)).j = _
    rw [map_j, ofJ_j]
  have hj : Transcendental K (E.baseChange M).j := by
    rw [hEt]
    exact SourceFunctionField.IntegralJCoordinate.transcendental_generic_j K M
  obtain ⟨Θ, hΘ⟩ := SourceEllipticVelu.exists_cyclicRootEquiv_of_full_torsion
    (L := Ω) N hNK (E.baseChange M) hj hcard
  let Ξ := SourceEllipticVelu.cyclicModularEmbeddingsEquiv N K E hNK hj Θ
  let Φ := Ξ.trans (Equiv.subtypeEquivRight fun ψ => by rw [hEt])
  refine ⟨Φ, ?_⟩
  intro σ S T hT
  have hσ : (σ.restrictScalars K) (E.baseChange M).j = (E.baseChange M).j := by
    change σ _ = _
    rw [hEt]
    exact σ.commutes RatFunc.X
  apply (SourceEllipticVelu.cyclicModularEmbeddingsEquiv_eq_postcomp_iff
    N K E hNK hj Θ (σ.restrictScalars K) hσ S T).mpr
  exact SourceEllipticVelu.descended_cyclic_value_galois (L := Ω) E N
    (by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K Ω)).mpr hNK)
    (fun S => (Θ S).val) hΘ σ S T hT

end
end Dubon2026.SourceEllipticDivisionField
