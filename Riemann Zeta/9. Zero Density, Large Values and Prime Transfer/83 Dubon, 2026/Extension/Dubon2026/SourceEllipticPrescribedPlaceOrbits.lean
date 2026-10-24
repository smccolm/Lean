import Dubon2026.SourceEllipticPrescribedEmbeddingOrbits
import Dubon2026.SourceRationalCoordinatePlaceOrbits

/-! DUB-17/18 -> reverse genus -> actual exceptional place fibers.
For the original finite Galois ofJ(X) specialization, the source relation
on specialized cyclic subgroups is exactly equality of the actual modular
coefficient-field places obtained by restriction. Every embedding's
finiteness is derived from its literal rational-coordinate equation.
The previous faithful model, quotient-root and inertia data are retained.
Fiber surjectivity and normalized fiber cardinalities remain required. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_prescribed_ofJ_place_orbits
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
            (∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
              ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K),
                (Φ T).val = (σ.val.val.toAlgHom.restrictScalars K).comp (Φ S).val) ∧
            ∃ hfinite : ∀ ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
                ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X},
                ψ.val.toRingHom.Finite,
              ∀ S T, SourceEllipticStabilizer.cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
                Place.restrictAlongFinite (Φ T).val (hfinite (Φ T)) v =
                  Place.restrictAlongFinite (Φ S).val (hfinite (Φ S)) v) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit, hroots, hlift⟩ :=
    exists_prescribed_ofJ_embedding_orbits K Ω p hp N hNK E₀
  letI := decResidue
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  haveI := hfd
  haveI := hgal
  obtain ⟨Θ, hΘ, hnat, hrootOrbit, Φ, hΦj, hΦnat, hΦorbit⟩ := hroots
  have hfinite (ψ : {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
      ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X}) :
      ψ.val.toRingHom.Finite :=
    (finite_galois_along_coordinate (jCoeff N K) (transcendental_jCoeff N K)
      ψ.val ψ.property).1
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit,
    ⟨Θ, hΘ, hnat, hrootOrbit, Φ, hΦj, hΦnat, hΦorbit, hfinite, ?_⟩, hlift⟩
  intro S T
  rw [hΦorbit S T]
  exact (Place.restrictAlongFinite_eq_iff_inertia (jCoeff N K)
    (transcendental_jCoeff N K) (Φ S).val (Φ T).val (Φ S).property (Φ T).property v).symm

end
end Dubon2026.SourceEllipticDivisionField
