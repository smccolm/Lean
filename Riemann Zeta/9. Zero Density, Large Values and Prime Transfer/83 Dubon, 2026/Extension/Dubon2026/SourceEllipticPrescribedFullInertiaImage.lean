import Dubon2026.SourceEllipticPrescribedInertiaCardinality
import Dubon2026.SourceEllipticStabilizerImageUpToSign

/-! Every actual coordinate-change stabilizer action on the prescribed
elliptic curve is realized by the derived inertia action up to actual
elliptic negation. The actual finite Galois specialization supplies all
cardinality, good-model, residue, torsion and action inputs. This closes
the full-image-up-to-sign obstacle in the source DUB-17/18 cyclic orbit
comparison. Cyclic orbit and place-fiber identification, numerical fiber
counts, reverse genus, good reduction and automorphy remain required. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_prescribed_ofJ_full_inertia_image
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
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
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, hlift⟩ :=
    exists_prescribed_ofJ_inertia_cardinality K Ω p hp N hNK E₀
  letI := decResidue
  haveI : Finite (MulAction.stabilizer (VariableChange K) E₀) :=
    (SourceEllipticStabilizer.stabilizer_bounds_of_five_le K p hp E₀).1
  have h2 : (2 : K) ≠ 0 := (isUnit_two_three_of_five_le K K p hp).1.ne_zero
  have hbound' : Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤
      Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) ∨
      Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 2 := by
    rwa [hIcard]
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hΨ, hbound, hIcard, ?_, hlift⟩
  intro δ hδ
  rcases SourceEllipticStabilizer.stabilizer_image_up_to_sign E₀ h2 ρ hρinj hfix
      hbound' δ hδ with ⟨σ, hσ⟩ | hn
  · refine ⟨σ, Or.inl ?_⟩
    intro P
    rw [← hσ]
    exact heq σ P
  · refine ⟨1, Or.inr ?_⟩
    intro P
    change HEq (vcInvFun δ E₀.toAffine (θ P))
      (-(θ (galoisTorsionMap (ofJ (RatFunc.X : RatFunc K)) N
        (1 : M ≃ₐ[RatFunc K] M) P)))
    have h1 : galoisTorsionMap (ofJ (RatFunc.X : RatFunc K)) N
        (1 : M ≃ₐ[RatFunc K] M) P = P := by
      apply Subtype.ext
      rcases P with ⟨P, hP⟩
      cases P <;> rfl
    rw [h1, hn]
    exact SourceEllipticStabilizer.vcInvFun_negationChange_heq E₀ (θ P)

end
end Dubon2026.SourceEllipticDivisionField
