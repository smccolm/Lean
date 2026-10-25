import Dubon2026.SourceEllipticEmbeddingOrbitReflection
import Dubon2026.SourceEllipticCharTwoCyclicSpecialization
import Dubon2026.SourceEllipticCyclicSpecializationOrbits

/-! DUB-17/18 -> characteristic-two weighted exceptional census.
Reuse the existing actual cyclic specialization, embedding-orbit reflection
and rational-coordinate place/fiber theorems with the constructed full inertia
image. No generic point-map or place infrastructure is rebuilt.

 The actual characteristic-two specialization identifies the full
exceptional stabilizer relation with inertia orbits of actual modular
embeddings. All good-model, torsion, specialization and full-image inputs
are constructed upstream. This retains exactly the data consumed by the
DUB-17/18 modular place-fiber classifier. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceCurve SourceEllipticCharTwo SourceEllipticReduction
open SourceFunctionField SourceFunctionField.CoefficientPresentation
open SourceEllipticStabilizer
noncomputable section

theorem exists_char_two_modular_embedding_orbits
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) :
    let E := ofJ (RatFunc.X : RatFunc K)
    let E₀ := ofJ0 K
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      ∃ (v : Place K M)
        (Ψ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N})
        (Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X}),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) ∧
        ∀ S T, cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
            (Φ T).val = (σ.val.val.toAlgHom.restrictScalars K).comp (Φ S).val := by
  let E := ofJ (RatFunc.X : RatFunc K)
  let E₀ := ofJ0 K
  letI : Fact (IsUnit (3 : K)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
  obtain ⟨M, hfd, hgal, hcard, v, _decResidue, _e, _W, _κ, _hκ, _hW, _γ, _hγ,
    θ, ρ, Ψ, hv, hinj, _hθ, _hρinj, hfix, heq, _hIcard, hfull, hΨ, _hlift⟩ :=
    exists_char_two_exceptional_cyclic_specialization K Ω N hNK
  obtain ⟨Φ, hΦ⟩ := exists_equivariant_modular_embeddings_of_full_torsion K Ω N hNK M hcard
  have hv0 : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
    simpa only [ofJ0_j, map_zero, sub_zero] using hv
  refine ⟨M, hfd, hgal, v, Ψ, Φ, hv0, ?_⟩
  intro S T
  have horbit : cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
      ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
        S.val.map (WeierstrassCurve.Affine.Point.map (σ.val.val : M →ₐ[RatFunc K] M)) = T.val := by
    apply cyclic_specialization_orbit_iff E E₀ N (NeZero.ne N)
      (v.toValuationSubring.inertiaSubgroup (RatFunc K)) (fun σ => σ.val.val)
      θ hinj ρ hfix heq ?_ Ψ hΨ S T
    intro δ hδ
    obtain ⟨σ, hσ⟩ := hfull δ hδ
    exact ⟨σ, Or.inl (fun P => hσ ▸ heq σ P)⟩
  rw [horbit]
  exact modularEmbeddingEquiv_galois_orbit_iff N Φ hΦ
    (v.toValuationSubring.inertiaSubgroup (RatFunc K)) (fun σ => σ.val.val) S T

end
end Dubon2026.SourceEllipticDivisionField
