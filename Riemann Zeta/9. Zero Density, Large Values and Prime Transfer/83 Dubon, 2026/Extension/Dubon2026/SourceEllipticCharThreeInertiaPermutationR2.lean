import Dubon2026.SourceEllipticCharThreeCyclicSpecialization
import Dubon2026.SourceEllipticCharThreePermutationKernelR2

/-! The constructed characteristic-three inertia action factors, modulo
identity or negation on all torsion points, through permutations of three
actual roots. The target permutation group has order six. This discharges
the kernel-action premise needed for the DUB-17/18 wild order bound;
the auxiliary Galois-field and place comparison remain to be assembled. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve IsLocalRing SourceEllipticReduction SourceEllipticVariableChange
open SourceCurve SourceEllipticExceptional SourceEllipticStabilizer
noncomputable section

theorem exists_char_three_exceptional_inertia_permutation
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
        (ρ : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* VariableChange K)
        (π : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* Equiv.Perm (charThreeRoots K))
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
        Nat.card (v.toValuationSubring.inertiaSubgroup (RatFunc K)) = 12 ∧
        (∀ δ : VariableChange K, δ • E₀ = E₀ →
          ∃ σ : v.toValuationSubring.inertiaSubgroup (RatFunc K), ρ σ = δ) ∧
        (∀ S Q, Q ∈ (Ψ S).val ↔
          ∃ P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ),
            P.val ∈ S.val ∧ θ P = Q) ∧
        Nat.card (Equiv.Perm (charThreeRoots K)) = 6 ∧
        (∀ σ, π σ = 1 →
          (∀ P, galoisTorsionMap E N σ.val.val P = P) ∨
          (∀ P, galoisTorsionMap E N σ.val.val P = -P)) ∧
        ∀ σ, ∃ g : VariableChange v.toValuationSubring,
          g.map v.toValuationSubring.subtype = κ * (κ.map (σ.val.val : M →+* M))⁻¹ ∧
          ρ σ = residueConjugateHom e.toRingEquiv γ (g.map (residue v.toValuationSubring)) := by
  let E₀ := EA (-1 : K)
  letI : E₀.IsElliptic := isElliptic_EA_neg_one_of_char_three
  let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hIcard, hfull, hΨ, hlift⟩ :=
    exists_char_three_exceptional_cyclic_specialization K Ω N hNK
  letI := decResidue
  let π := charThreeInertiaPermHom ρ hfix
  refine ⟨M, hfd, hgal, hcard, v, decResidue, e, W, κ, hκ, hW, γ, hγ, θ, ρ, π, Ψ,
    hv, hinj, hθ, hρinj, hfix, heq, hIcard, hfull, hΨ,
    charThreeRoots_perm_card K, ?_, hlift⟩
  intro σ hσ
  rcases charThreeInertiaPermHom_kernel ρ hfix σ hσ with h1 | hn
  · have hσ1 : σ = 1 := hρinj (h1.trans ρ.map_one.symm)
    subst σ
    left
    intro P
    apply Subtype.ext
    rcases P with ⟨P, hP⟩
    cases P <;> rfl
  · right
    intro P
    apply hinj
    rw [map_neg]
    have h := heq σ P
    rw [hn] at h
    exact eq_of_heq (h.symm.trans (vcInvFun_negationChange_heq E₀ (θ P)))

end
end Dubon2026.SourceEllipticDivisionField
