import Dubon2026.SourceEllipticDeuringThreeTorsionSpecialization
import Dubon2026.SourceEllipticCharTwoGoodModelOrder
import Dubon2026.SourceEllipticCharTwoStabilizerCard
import Dubon2026.SourceRatFuncInertiaCardinality
import Dubon2026.SourceEllipticStabilizerImageUpToSign

/-! DUB-17/18 -> characteristic-two genus/Picard -> weighted exceptional census.
The actual prescribed faithful specialization retains three-torsion. Its
eighth-power factorization and good-model discriminant force inertia order
at least twenty-four. The proved actual stabilizer cardinality then gives
equality and full image, without a full-image or ramification assumption.
The source argument is S_ModularCurve_exists_equivariant_torsion_reduction_ofJ,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceEllipticCharTwo
noncomputable section

theorem exists_char_two_exceptional_full_inertia_image
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2]
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    letI : Fact (IsUnit (3 : K)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
    let E₀ := ofJ0 K
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
        Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) = 24 ∧
        (∀ δ : VariableChange K, δ • E₀ = E₀ →
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K), ρ σ = δ) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  have h3 : (3 : K) ≠ 0 := by rw [three_eq_one]; exact one_ne_zero
  letI : Fact (IsUnit (3 : K)) := ⟨h3.isUnit⟩
  let E₀ := ofJ0 K
  obtain ⟨M, hfd, hgal, hcard, hcard3, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, hθ, hρinj, hfix, heq, hlift⟩ :=
    exists_prescribed_ofJ_inertia_action_with_three_torsion K Ω h3 N hNK E₀
  letI := decResidue
  letI := hfd
  letI := hgal
  have hj : E₀.j = 0 := ofJ0_j K
  have hv0 : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
    simpa only [hj, map_zero, sub_zero] using hv
  have hIcard := Place.inertia_card_eq_rational_specialization_order K v E₀.j hv
  rw [hj, map_zero, sub_zero] at hIcard
  have hd12 := ofJ_good_model_order_divisibility_of_char_two v W κ hκ hW
  have hd8 := ofJ_order_eight_dvd_of_full_three_torsion v hv0 hcard3
  have hd24 : (24 : ℤ) ∣ v.ord (algebraMap (RatFunc K) M RatFunc.X) := by omega
  have hlo : (24 : ℤ) ≤ v.ord (algebraMap (RatFunc K) M RatFunc.X) :=
    Int.le_of_dvd hv0 hd24
  have hbound : Nat.card (MulAction.stabilizer (VariableChange K) E₀) = 24 :=
    SourceEllipticCharTwo.char_two_stabilizer_card
  letI : Finite (MulAction.stabilizer (VariableChange K) E₀) :=
    Nat.finite_of_card_ne_zero (by rw [hbound]; norm_num)
  let f : v.toValuationSubring.inertiaSubgroup (RatFunc K) →
      MulAction.stabilizer (VariableChange K) E₀ := fun σ =>
    ⟨ρ σ, MulAction.mem_stabilizer_iff.mpr (hfix σ)⟩
  have hf : Function.Injective f := fun _ _ h => hρinj (congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective f hf
  have h24 : Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) = 24 := by omega
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ,
    hv, hinj, hθ, hρinj, hfix, heq, h24, ?_, hlift⟩
  apply SourceEllipticStabilizer.stabilizer_image_surjective_of_card_le E₀ ρ hρinj hfix
  rw [h24]
  exact hbound.le

end
end Dubon2026.SourceEllipticDivisionField
