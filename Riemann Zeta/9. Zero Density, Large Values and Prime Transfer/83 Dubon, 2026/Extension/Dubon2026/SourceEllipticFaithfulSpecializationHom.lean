import Dubon2026.SourceEllipticOfJSpecialization
import Dubon2026.SourceEllipticResidueInertiaHom

/-! The actual source ofJ(X) specialization has an injective inertia
homomorphism into the actual residue-curve stabilizer. The point action
is equivariant with the literal torsion reduction. The finite field,
place, good model and faithful action are derived by the preceding
consumer, so no faithfulness premise is assumed here. This advances the
DUB-17/18 exceptional-fiber census; full image realization and transport
to the prescribed residue curve still remain. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_faithful_ofJ_inertia_hom
    (K Ω : Type*) [Field K] [IsAlgClosed K] [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    [DecidableEq (RatFunc K)]
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M) (_ : DecidableEq v.ResidueField) (e : v.ResidueField ≃ₐ[K] K)
        (W : WeierstrassCurve v.toValuationSubring) (κ : VariableChange M)
        (hκ : κ • E.baseChange M = W.map v.toValuationSubring.subtype) (hW : IsUnit W.Δ)
        (γ : VariableChange K)
        (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+
          (W.map (residue v.toValuationSubring)).toAffine.Point),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M E₀.j) ∧
        γ • W.map (e.toRingHom.comp (residue v.toValuationSubring)) = E₀ ∧
        Function.Injective θ ∧
        (∀ P, θ P = reducePoint ((map_residue_Δ_ne_zero_iff W).mpr hW)
          (modelPointEquiv E W κ hκ P)) ∧
        ∃ ρ : v.toValuationSubring.inertiaSubgroup (RatFunc K) →*
            VariableChange v.ResidueField,
          Function.Injective ρ ∧
          (∀ σ, ρ σ • W.map (residue v.toValuationSubring) = W.map (residue v.toValuationSubring)) ∧
          (∀ σ P, HEq (vcInvFun (ρ σ) (W.map (residue v.toValuationSubring)).toAffine (θ P))
            (θ (galoisTorsionMap E N σ.val.val P))) ∧
          ∀ σ, ∃ g : VariableChange v.toValuationSubring,
            g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
            g.map (residue v.toValuationSubring) = ρ σ := by
  let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, θ,
    hv, hγ, hinj, hθ, heq⟩ := exists_faithful_ofJ_specialization K Ω p hp N hNK E₀
  letI := decResidue
  obtain ⟨h2, h3⟩ := isUnit_two_three_of_five_le K v.toValuationSubring p hp
  have hNA : IsUnit (N : v.toValuationSubring) := by
    simpa only [map_natCast] using hNK.isUnit.map (algebraMap K v.toValuationSubring)
  let ρ := residueInertiaHom h2 h3 E W κ hκ hW
  have hρinj : Function.Injective ρ := by
    apply (injective_iff_map_eq_one ρ).mpr
    intro σ hσ
    obtain ⟨g, hg, -, -, hfaith⟩ := heq σ.val.val σ.val.property
    have hgr : g.map (residue v.toValuationSubring) = 1 := by
      rw [← residueInertiaHom_eq_map h2 h3 E W κ hκ hW σ g hg]
      exact hσ
    exact Subtype.ext (Subtype.ext (hfaith hgr))
  have hθeq : θ = modelTorsionReduction E W κ hκ
      ((map_residue_Δ_ne_zero_iff W).mpr hW) hNA := by
    apply AddMonoidHom.ext
    exact hθ
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, θ,
    hv, hγ, hinj, hθ, ρ, hρinj, ?_, ?_, ?_⟩
  · exact residueInertiaHom_stabilizes h2 h3 E W κ hκ hW
  · intro σ P
    rw [hθeq]
    exact residueInertiaHom_torsion_equivariance h2 h3 E W κ hκ hW hNA σ P
  · intro σ
    exact ⟨integralInertiaCocycle h2 h3 E W κ hκ hW σ,
      integralInertiaCocycle_generic h2 h3 E W κ hκ hW σ, rfl⟩

end
end Dubon2026.SourceEllipticDivisionField
