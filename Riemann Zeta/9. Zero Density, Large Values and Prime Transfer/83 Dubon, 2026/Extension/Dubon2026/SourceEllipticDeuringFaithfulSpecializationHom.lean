import Dubon2026.SourceEllipticDeuringOfJSpecialization
import Dubon2026.SourceEllipticWildResidueInertiaHom

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> prescribed faithful inertia.
The existing specialization proofs use two nonzero only for their Legendre field.
The proved Deuring field replaces that input with three nonzero. Actual point,
residue, inertia and conjugation maps are retained, and their general local
proofs are reused. The exceptional modular-order and genus consumers follow. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_faithful_ofJ_inertia_hom_of_three_ne_zero
    (K Ω : Type*) [Field K] [IsAlgClosed K] [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω]
    (h3K : (3 : K) ≠ 0)
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
    hv, hγ, hinj, hθ, heq⟩ := exists_faithful_ofJ_specialization_of_three_ne_zero K Ω h3K N hNK E₀
  letI := decResidue
  have hNA : IsUnit (N : v.toValuationSubring) := by
    simpa only [map_natCast] using hNK.isUnit.map (algebraMap K v.toValuationSubring)
  let ρ := residueInertiaHomAll E W κ hκ hW
  have hρinj : Function.Injective ρ := by
    apply (injective_iff_map_eq_one ρ).mpr
    intro σ hσ
    obtain ⟨g, hg, -, -, hfaith⟩ := heq σ.val.val σ.val.property
    have hgr : g.map (residue v.toValuationSubring) = 1 := by
      rw [← residueInertiaHomAll_eq_map E W κ hκ hW σ g hg]
      exact hσ
    exact Subtype.ext (Subtype.ext (hfaith hgr))
  have hθeq : θ = modelTorsionReduction E W κ hκ
      ((map_residue_Δ_ne_zero_iff W).mpr hW) hNA := by
    apply AddMonoidHom.ext
    exact hθ
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, θ,
    hv, hγ, hinj, hθ, ρ, hρinj, ?_, ?_, ?_⟩
  · exact residueInertiaHomAll_stabilizes E W κ hκ hW
  · intro σ P
    rw [hθeq]
    exact residueInertiaHomAll_torsion_equivariance E W κ hκ hW hNA σ P
  · intro σ
    exact ⟨integralInertiaCocycleAll E W κ hκ hW σ,
      integralInertiaCocycleAll_generic E W κ hκ hW σ, rfl⟩

end
end Dubon2026.SourceEllipticDivisionField
