import Dubon2026.SourceEllipticPrescribedEquivariantRoots
import Dubon2026.SourceEllipticCyclicModularEmbeddings

/-! The actual finite Galois specialization identifies generic cyclic
subgroups with original modular coefficient-field embeddings at the literal
rational j-coordinate. Original j_N evaluation is the descended quotient
root. The equivalence respects every original field automorphism, and the
source relation on specialized elliptic cyclic subgroups is exactly the
actual inertia postcomposition orbit of these embeddings. This reuses the
existing exact embedding/root theorem; no new minimal-polynomial or field
presentation is constructed. Actual restricted place fibers and their
orders remain required for DUB-17/18, followed by the exceptional census,
reverse genus, good reduction and automorphy. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_prescribed_ofJ_embedding_orbits
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
    let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M) (_ : DecidableEq v.ResidueField) (e : v.ResidueField ≃ₐ[K] K)
        (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
        (hκ : κ • E.baseChange M = W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ)
        (γ : VariableChange K)
        (hγ : γ • (W.map (residue v.toValuationSubring)).map e.toRingHom = E₀)
        (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+ E₀.toAffine.Point)
        (ρ : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* VariableChange K)
        (Ψ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j) ∧
        Function.Injective θ ∧
        (∀ P, θ P = residueCurvePointEquiv e.toRingEquiv (W.map (residue v.toValuationSubring))
          E₀ γ hγ (reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
            (modelPointEquiv E W κ hκ P))) ∧
        Function.Injective ρ ∧
        (∀ σ, ρ σ • E₀ = E₀) ∧
        (∀ σ P, HEq (vcInvFun (ρ σ) E₀.toAffine (θ P))
          (θ (galoisTorsionMap E N σ.val.val P))) ∧
        (∀ S Q, Q ∈ (Ψ S).val ↔
          ∃ P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ),
            P.val ∈ S.val ∧ θ P = Q) ∧
        (Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤
          (v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j)).toNat ∨
          Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2) ∧
        Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) =
          (v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j)).toNat ∧
        (∀ δ : VariableChange K, δ • E₀ = E₀ →
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
            (∀ P, HEq (vcInvFun δ E₀.toAffine (θ P))
              (θ (galoisTorsionMap E N σ.val.val P))) ∨
            (∀ P, HEq (vcInvFun δ E₀.toAffine (θ P))
              (-(θ (galoisTorsionMap E N σ.val.val P))))) ∧
        (∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
            S.val.map (WeierstrassCurve.Affine.Point.map (σ.val.val : M →ₐ[RatFunc K] M)) = T.val) ∧
        (∃ Θ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {y : M // (SourceFunctionField.relationAtSeed
            (SourceFunctionField.IntegralJCoordinate.modularPolynomial N) (E.baseChange M).j).IsRoot y},
          (∀ S, algebraMap M Ω (Θ S).val =
            SourceEllipticVelu.cyclicQuotientJ ((E.baseChange M).baseChange Ω) N
              (by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K Ω)).mpr hNK)
              (SourceFunctionField.IntegralJCoordinate.primeCyclicKernelMap
                (algebraMap M Ω) (E.baseChange M) N S)) ∧
          (∀ (σ : M ≃ₐ[RatFunc K] M) S T,
            T.val = S.val.map (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) →
              (Θ T).val = σ (Θ S).val) ∧
          (∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
            ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
              (Θ T).val = σ.val.val (Θ S).val) ∧
          ∃ Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
            {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
              ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X},
            (∀ S, (Φ S).val (jN N K) = (Θ S).val) ∧
            (∀ (σ : M ≃ₐ[RatFunc K] M) S T,
              T.val = S.val.map (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) →
                (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val) ∧
            ∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
              ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
                (Φ T).val = (σ.val.val.toAlgHom.restrictScalars K).comp (Φ S).val) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit, hroots, hlift⟩ :=
    exists_prescribed_ofJ_equivariant_roots K Ω p hp N hNK E₀
  letI := decResidue
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  obtain ⟨Θ, hΘ, hnat, hrootOrbit⟩ := hroots
  have hEt : ((ofJ (RatFunc.X : RatFunc K)).baseChange M).j =
      algebraMap (RatFunc K) M RatFunc.X := by
    change ((ofJ (RatFunc.X : RatFunc K)).map (algebraMap (RatFunc K) M)).j = _
    rw [map_j, ofJ_j]
  have hj : Transcendental K ((ofJ (RatFunc.X : RatFunc K)).baseChange M).j := by
    rw [hEt]
    exact SourceFunctionField.IntegralJCoordinate.transcendental_generic_j K M
  let Ξ := SourceEllipticVelu.cyclicModularEmbeddingsEquiv N K
    (ofJ (RatFunc.X : RatFunc K)) hNK hj Θ
  let Φ := Ξ.trans (Equiv.subtypeEquivRight fun ψ => by rw [hEt])
  have hΦj (S) : (Φ S).val (jN N K) = (Θ S).val :=
    SourceEllipticVelu.cyclicModularEmbeddingsEquiv_jN N K
      (ofJ (RatFunc.X : RatFunc K)) hNK hj Θ S
  have hΦiff (σ : M ≃ₐ[RatFunc K] M) S T :
      (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val ↔
        (Θ T).val = σ (Θ S).val := by
    have hσ : (σ.restrictScalars K) ((ofJ (RatFunc.X : RatFunc K)).baseChange M).j =
        ((ofJ (RatFunc.X : RatFunc K)).baseChange M).j := by
      change σ _ = _
      rw [hEt]
      exact σ.commutes RatFunc.X
    exact SourceEllipticVelu.cyclicModularEmbeddingsEquiv_eq_postcomp_iff N K
      (ofJ (RatFunc.X : RatFunc K)) hNK hj Θ (σ.restrictScalars K) hσ S T
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit,
    ⟨Θ, hΘ, hnat, hrootOrbit, Φ, hΦj, ?_, ?_⟩, hlift⟩
  · intro σ S T hT
    exact (hΦiff σ S T).mpr (hnat σ S T hT)
  · intro S T
    rw [hrootOrbit S T]
    exact exists_congr fun σ => (hΦiff σ.val.val S T).symm

end
end Dubon2026.SourceEllipticDivisionField
