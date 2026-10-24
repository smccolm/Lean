import Dubon2026.SourceEllipticDeuringFaithfulTorsionModel
import Dubon2026.SourceEllipticGoodModelResidueJ
import Dubon2026.SourceRatFuncFiniteValueSpecialization

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> prescribed faithful inertia.
The existing specialization proofs use two nonzero only for their Legendre field.
The proved Deuring field replaces that input with three nonzero. Actual point,
residue, inertia and conjugation maps are retained, and their general local
proofs are reused. The exceptional modular-order and genus consumers follow. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve
noncomputable section

theorem exists_faithful_specialization_field_place_of_three_ne_zero
    (K Ω : Type*) [Field K] [IsAlgClosed K] [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω]
    (h3K : (3 : K) ≠ 0)
    (E : WeierstrassCurve (RatFunc K)) [E.IsElliptic] (hj : E.j = RatFunc.X)
    (N : ℕ) (hNK : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
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
        ∀ (σ : M ≃ₐ[RatFunc K] M)
          (_hσ : σ ∈ v.toValuationSubring.decompositionSubgroup (RatFunc K)),
          ∃ g : VariableChange v.toValuationSubring,
            g.map v.toValuationSubring.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue v.toValuationSubring) • W.map (residue v.toValuationSubring) =
              W.map (residue v.toValuationSubring) ∧
            (∀ P, HEq (vcInvFun (g.map (residue v.toValuationSubring))
                (W.map (residue v.toValuationSubring)).toAffine (θ P))
              (θ (galoisTorsionMap E N σ P))) ∧
            (g.map (residue v.toValuationSubring) = 1 → σ = 1) := by
  obtain ⟨M, hfd, hgal, hcard, hM⟩ := exists_faithful_torsion_model_of_three_ne_zero K (Ω := Ω) h3K E N hNK
  haveI := hfd
  haveI := hgal
  obtain ⟨v, ht, hv, e, -, he, hI⟩ := exists_rational_specialization_place K (M := M) E₀.j
  letI : DecidableEq v.ResidueField := Classical.decEq _
  have hjA : algebraMap (RatFunc K) M E.j ∈ v.toValuationSubring := by
    rw [hj]
    exact ht
  obtain ⟨W, κ, hκ, hW, θ, hinj, hθ, heq⟩ := hM v.toValuationSubring hjA
  haveI : W.IsElliptic := ⟨hW⟩
  obtain ⟨γ, hγ⟩ := exists_prescribed_residue_model_change E W κ hκ
    (congrArg (algebraMap (RatFunc K) M) hj) ht
    (e.toRingHom.comp (residue v.toValuationSubring)) E₀ he
  refine ⟨M, hfd, hgal, hcard, v, inferInstance, e, W, κ, hκ, hW, γ, θ, hv, hγ, hinj, hθ, ?_⟩
  exact fun σ hσ => heq σ hσ (hI σ hσ)

end
end Dubon2026.SourceEllipticDivisionField
