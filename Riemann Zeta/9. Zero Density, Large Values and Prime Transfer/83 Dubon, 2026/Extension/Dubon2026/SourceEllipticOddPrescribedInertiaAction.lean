import Dubon2026.SourceEllipticOddFaithfulSpecializationHom
import Dubon2026.SourceEllipticResidueConjugateHom

/-! DUB-17/18 -> characteristic-three modular good reduction -> faithful
prescribed elliptic specialization. Reuse the existing actual field, torsion,
place and point maps, with the newly proved integral inertia cocycle valid
in every residue characteristic. The Legendre field requires only two nonzero.
Wild census and the remaining characteristic-two model branch remain open. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_prescribed_ofJ_inertia_action_of_two_ne_zero
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (h2K : (2 : K) ≠ 0)
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
        (ρ : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* VariableChange K),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j) ∧
        Function.Injective θ ∧
        (∀ P, θ P = residueCurvePointEquiv e.toRingEquiv (W.map (residue v.toValuationSubring))
          E₀ γ hγ (reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
            (modelPointEquiv E W κ hκ P))) ∧
        Function.Injective ρ ∧
        (∀ σ, ρ σ • E₀ = E₀) ∧
        (∀ σ P, HEq (vcInvFun (ρ σ) E₀.toAffine (θ P))
          (θ (galoisTorsionMap E N σ.val.val P))) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, θ,
    hv, hγ, hinj, hθ, ρ, hρinj, hfix, heq, hlift⟩ :=
    exists_faithful_ofJ_inertia_hom_of_two_ne_zero K Ω h2K N hNK E₀
  letI := decResidue
  have hγ' : γ • (W.map (residue v.toValuationSubring)).map e.toRingHom = E₀ := by
    rw [WeierstrassCurve.map_map]
    exact hγ
  let ε := residueCurvePointEquiv e.toRingEquiv (W.map (residue v.toValuationSubring)) E₀ γ hγ'
  let θ₀ := ε.toAddMonoidHom.comp θ
  let ρ₀ := (residueConjugateHom e.toRingEquiv γ).comp ρ
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ', θ₀, ρ₀,
    hv, ε.injective.comp hinj, ?_, (residueConjugateHom_injective e.toRingEquiv γ).comp hρinj,
    ?_, ?_, ?_⟩
  · intro P
    change ε (θ P) = ε (reducePoint _ (modelPointEquiv E W κ hκ P))
    rw [hθ P]
  · exact fun σ => residueConjugateHom_stabilizes e.toRingEquiv
      (W.map (residue v.toValuationSubring)) E₀ γ hγ' (ρ σ) (hfix σ)
  · exact fun σ P => residueCurvePointEquiv_equivariant e.toRingEquiv
      (W.map (residue v.toValuationSubring)) E₀ γ hγ' (ρ σ) (hfix σ)
      (θ P) (θ (galoisTorsionMap E N σ.val.val P)) (heq σ P)
  · intro σ
    obtain ⟨g, hg, hgr⟩ := hlift σ
    refine ⟨g, hg, ?_⟩
    change residueConjugateHom e.toRingEquiv γ (ρ σ) =
      residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring))
    rw [hgr]

end
end Dubon2026.SourceEllipticDivisionField
