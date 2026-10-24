import Dubon2026.SourceEllipticPrescribedCyclicOrbits
import Dubon2026.SourceEllipticFiniteFieldCyclicRoots
import Dubon2026.SourceEllipticGenericCyclicRoots

/-! The actual finite Galois ofJ(X) specialization has an exact cyclic
subgroup-to-modular-root equivalence over that same finite field. Each
root has the proved literal cyclic quotient value after the original
embedding into the algebraically closed ambient field. Full torsion,
transcendence, separability and root descent are derived. This removes
the finite-field root rationality obstacle in the DUB-17/18 place-fiber
route; equivariance of this descended equivalence and actual place fibers
remain required, followed by exceptional counts, genus and good reduction. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_prescribed_ofJ_finite_roots
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
          ∀ S, algebraMap M Ω (Θ S).val =
            SourceEllipticVelu.cyclicQuotientJ ((E.baseChange M).baseChange Ω) N
              (by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K Ω)).mpr hNK)
              (SourceFunctionField.IntegralJCoordinate.primeCyclicKernelMap
                (algebraMap M Ω) (E.baseChange M) N S)) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit, hlift⟩ :=
    exists_prescribed_ofJ_cyclic_orbits K Ω p hp N hNK E₀
  letI := decResidue
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  letI : IsAlgClosure M Ω := ⟨inferInstance, inferInstance⟩
  letI : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) M x,
      ← IsScalarTower.algebraMap_apply (RatFunc K) M Ω,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) Ω]
  have hj : Transcendental K ((ofJ (RatFunc.X : RatFunc K)).baseChange M).j := by
    change Transcendental K ((ofJ (RatFunc.X : RatFunc K)).map (algebraMap (RatFunc K) M)).j
    rw [map_j, ofJ_j]
    exact SourceFunctionField.IntegralJCoordinate.transcendental_generic_j K M
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hfull, horbit, ?_, hlift⟩
  exact SourceEllipticVelu.exists_cyclicRootEquiv_of_full_torsion (L := Ω) N hNK
    ((ofJ (RatFunc.X : RatFunc K)).baseChange M) hj hcard

end
end Dubon2026.SourceEllipticDivisionField
