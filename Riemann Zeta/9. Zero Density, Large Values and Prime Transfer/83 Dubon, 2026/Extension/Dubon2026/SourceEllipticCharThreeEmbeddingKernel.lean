import Dubon2026.SourceEllipticCharThreeInertiaPermutationR2
import Dubon2026.SourceEllipticFullTorsionModularEmbeddings
import Dubon2026.SourceEllipticTorsionSignSubgroups

/-! The kernel of the constructed three-root inertia action fixes every
actual modular coefficient-field embedding. Existing literal modular
roots and quotient naturality construct the embedding correspondence.
This consumer retains exactly the field, place, action and embedding data
needed for the DUB-17/18 auxiliary normal field. The full good-model,
torsion and stabilizer witnesses remain in the upstream constructed theorem. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceEllipticReduction SourceCurve SourceEllipticExceptional
open SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section

theorem exists_char_three_exceptional_embedding_kernel
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3] (N : ℕ) (hNK : (N : K) ≠ 0) :
    let E := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M)
        (π : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* Equiv.Perm (charThreeRoots K)),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) ∧
        Nat.card (Equiv.Perm (charThreeRoots K)) = 6 ∧
        ∃ Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X},
          (∀ (σ : M ≃ₐ[RatFunc K] M) S T,
            T.val = S.val.map (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) →
              (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val) ∧
          ∀ σ, π σ = 1 → ∀ ψ : modularFunctionFieldCoeff N K →ₐ[K] M,
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X →
              (σ.val.val.toAlgHom.restrictScalars K).comp ψ = ψ := by
  let E₀ := EA (-1 : K)
  letI : E₀.IsElliptic := isElliptic_EA_neg_one_of_char_three
  let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, _, _, _, _, _, _, _, _, _, _, π, _,
    hv, _, _, _, _, _, _, _, _, hperm, hker, _⟩ :=
    exists_char_three_exceptional_inertia_permutation K Ω N hNK
  have hv0 : 0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) := by
    simpa only [EA_neg_one_j_of_char_three, map_zero, sub_zero] using hv
  letI : NeZero N := ⟨by rintro rfl; exact hNK Nat.cast_zero⟩
  obtain ⟨Φ, hΦ⟩ := exists_equivariant_modular_embeddings_of_full_torsion K Ω N hNK M hcard
  refine ⟨M, hfd, hgal, hcard, v, π, hv0, hperm, Φ, hΦ, ?_⟩
  intro σ hσ ψ hψ
  obtain ⟨S, hS⟩ := Φ.surjective ⟨ψ, hψ⟩
  have hf := subgroup_map_eq_of_torsion_sign E N σ.val.val (hker σ hσ) S.val S.property.2
  have hn := hΦ σ.val.val S S hf.symm
  rw [hS] at hn
  exact hn.symm

end
end Dubon2026.SourceEllipticDivisionField
