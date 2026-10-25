import Dubon2026.SourceEllipticFullTorsionDivisor
import Dubon2026.SourceEllipticDeuringPrescribedInertiaAction

/-! DUB-17/18 -> characteristic-two census -> full inertia image.
Restrict the already proved faithful specialization at level 3N to level N.
The actual field retains all nine three-torsion points, supplying the
eighth-power factorization without a new faithful-field construction. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_prescribed_ofJ_inertia_action_with_three_torsion
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    (h3K : (3 : K) ≠ 0)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // (3 : ℕ) • P = 0} = 9 ∧
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
  have h3NK : ((3 * N : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact mul_ne_zero h3K hNK
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, hθ, hρinj, hfix, heq, hlift⟩ :=
    exists_prescribed_ofJ_inertia_action_of_three_ne_zero K Ω h3K (3 * N) h3NK E₀
  letI := decResidue
  have h3NF : ((3 * N : ℕ) : RatFunc K) ≠ 0 := natCast_ne_zero_of_ne_zero h3NK
  have hcardN := card_torsion_of_dvd_full_torsion E h3NF (dvd_mul_left N 3) M hcard
  have hcard3 : Nat.card {P : (E.baseChange M).toAffine.Point // (3 : ℕ) • P = 0} = 9 :=
    card_torsion_of_dvd_full_torsion E h3NF (dvd_mul_right 3 N) M hcard
  have hle : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) ≤
      Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point ((3 * N : ℕ) : ℤ) := by
    apply Submodule.torsionBy_le_torsionBy_of_dvd
    exact_mod_cast dvd_mul_left N 3
  let ι := (Submodule.inclusion hle).toAddMonoidHom
  let θN := θ.comp ι
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  refine ⟨M, hfd, hgal, hcardN, hcard3, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θN, ρ,
    hv, hinj.comp hι, ?_, hρinj, hfix, ?_, hlift⟩
  · intro P
    exact hθ (ι P)
  · intro σ P
    have hc : galoisTorsionMap E (3 * N) σ.val.val (ι P) =
        ι (galoisTorsionMap E N σ.val.val P) := rfl
    have h := heq σ (ι P)
    rw [hc] at h
    exact h

end
end Dubon2026.SourceEllipticDivisionField
