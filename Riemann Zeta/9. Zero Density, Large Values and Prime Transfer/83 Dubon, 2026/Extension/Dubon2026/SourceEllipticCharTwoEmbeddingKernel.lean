import Dubon2026.SourceEllipticCharTwoInertiaSign
import Dubon2026.SourceEllipticFullTorsionModularEmbeddings
import Dubon2026.SourceEllipticTorsionSignSubgroups

/-! DUB-17/18 -> characteristic-two genus/Picard -> wild different bound.
The actual order-twelve inertia sign quotient fixes original modular
embeddings. Existing coordinate fixing-field and normal-place order proofs
provide the finite Galois auxiliary field; full census data is not assumed. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve SourceEllipticReduction SourceCurve SourceEllipticCharTwo
open SourceFunctionField SourceFunctionField.CoefficientPresentation
noncomputable section
attribute [local instance] SourceEllipticCharTwo.charTwoSignSubgroup_normal

theorem exists_char_two_exceptional_embedding_kernel
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) (hNK : (N : K) ≠ 0) :
    let E := ofJ (RatFunc.X : RatFunc K)
    ∃ M : IntermediateField (RatFunc K) Ω,
      FiniteDimensional (RatFunc K) M ∧ IsGalois (RatFunc K) M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∃ (v : Place K M)
        (π : v.toValuationSubring.inertiaSubgroup (RatFunc K) →* ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)),
        0 < v.ord (algebraMap (RatFunc K) M RatFunc.X) ∧
        Nat.card (((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)) = 12 ∧
        ∃ Φ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
          {ψ : modularFunctionFieldCoeff N K →ₐ[K] M //
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X},
          (∀ (σ : M ≃ₐ[RatFunc K] M) S T,
            T.val = S.val.map (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) →
              (Φ T).val = (σ.toAlgHom.restrictScalars K).comp (Φ S).val) ∧
          ∀ σ, π σ = 1 → ∀ ψ : modularFunctionFieldCoeff N K →ₐ[K] M,
            ψ (jCoeff N K) = algebraMap (RatFunc K) M RatFunc.X →
              (σ.val.val.toAlgHom.restrictScalars K).comp ψ = ψ := by
  let E : WeierstrassCurve (RatFunc K) := ofJ (RatFunc.X : RatFunc K)
  obtain ⟨M, hfd, hgal, hcard, v, π, hv0, hperm, hker⟩ :=
    exists_char_two_exceptional_inertia_sign K Ω N hNK
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
