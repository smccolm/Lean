import Dubon2026.SourceEllipticCharThreePrescribedInertia
import Dubon2026.SourceEllipticCharThreeStabilizerBound
import Dubon2026.SourceEllipticCharThreeGoodModelOrder
import Dubon2026.SourceRatFuncInertiaCardinality
import Dubon2026.SourceEllipticStabilizerImageUpToSign

/-! The actual characteristic-three exceptional specialization has full
elliptic stabilizer image and inertia order twelve. Its good model,
faithful action and torsion reduction are constructed by the existing
Legendre route. Native cardinality and the actual discriminant discharge
the remaining image assumptions. This serves the DUB-17/18 wild census;
the census and stronger differential bounds are still required. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceEllipticExceptional
noncomputable section

theorem exists_char_three_exceptional_full_inertia_image
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3]
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    let E₀ := SourceEllipticExceptional.EA (-1 : K)
    letI : E₀.IsElliptic := SourceEllipticExceptional.isElliptic_EA_neg_one_of_char_three
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
        Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) = 12 ∧
        (∀ δ : VariableChange K, δ • E₀ = E₀ →
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K), ρ σ = δ) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  let E₀ := EA (-1 : K)
  letI : E₀.IsElliptic := isElliptic_EA_neg_one_of_char_three
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, hθ, hρinj, hfix, heq, hlift⟩ :=
    exists_prescribed_ofJ_inertia_action_of_char_three K Ω N hNK E₀
  letI := decResidue
  letI := hfd
  letI := hgal
  have hj : E₀.j = 0 := EA_neg_one_j_of_char_three
  have hv0 : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
    simpa only [hj, map_zero, sub_zero] using hv
  have hIcard := Place.inertia_card_eq_rational_specialization_order K v E₀.j hv
  rw [hj, map_zero, sub_zero] at hIcard
  have hd := ofJ_good_model_order_divisibility_of_char_three v W κ hκ hW
  have hlo : (12 : ℤ) ≤ v.ord (algebraMap (RatFunc K) M RatFunc.X) :=
    Int.le_of_dvd hv0 hd
  obtain ⟨hfin, hbound⟩ := char_three_stabilizer_card_le_twelve (K := K)
  letI : Finite (MulAction.stabilizer (VariableChange K) E₀) := hfin
  let f : v.toValuationSubring.inertiaSubgroup (RatFunc K) →
      MulAction.stabilizer (VariableChange K) E₀ := fun σ =>
    ⟨ρ σ, MulAction.mem_stabilizer_iff.mpr (hfix σ)⟩
  have hf : Function.Injective f := fun _ _ h => hρinj (congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective f hf
  have h12 : Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) = 12 := by
    change Nat.card (MulAction.stabilizer (VariableChange K) E₀) ≤ 12 at hbound
    omega
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, hθ, hρinj, hfix, heq, h12, ?_, hlift⟩
  apply SourceEllipticStabilizer.stabilizer_image_surjective_of_card_le E₀ ρ hρinj hfix
  rw [h12]
  exact hbound

end
end Dubon2026.SourceEllipticDivisionField
