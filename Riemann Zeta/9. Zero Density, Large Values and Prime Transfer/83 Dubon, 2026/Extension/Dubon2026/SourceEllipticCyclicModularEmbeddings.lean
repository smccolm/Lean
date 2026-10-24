import Dubon2026.SourceModularEmbeddingRootActions
import Dubon2026.SourceEllipticFixedCurvePointMap

/-! Compose the proved cyclic-root equivalence with the existing exact
modular coefficient-field embedding/root equivalence. The original j_N
evaluation and automorphism action are retained. This is the direct bridge
to the actual place-restriction fibers required by DUB-17/18. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField SourceFunctionField.IntegralJCoordinate
open SourceFunctionField.CoefficientPresentation
noncomputable section
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
variable {B M : Type*} [Field B] [Field M] [Algebra B M] [Algebra K M] [DecidableEq M]
variable (E : WeierstrassCurve B) [E.IsElliptic] (hNK : (N : K) ≠ 0)
variable (hj : Transcendental K (E.baseChange M).j)
variable (Θ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
  {y : M // (relationAtSeed (modularPolynomial N) (E.baseChange M).j).IsRoot y})

/-- The actual cyclic subgroup determines the modular-field embedding through its original quotient root. -/
def cyclicModularEmbeddingsEquiv :
    {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
      {ψ : modularFunctionFieldCoeff N K →ₐ[K] M // ψ (jCoeff N K) = (E.baseChange M).j} :=
  Θ.trans (embeddingsEquivModularRoots N K hNK hj).symm

theorem cyclicModularEmbeddingsEquiv_jN
    (S : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    (cyclicModularEmbeddingsEquiv N K E hNK hj Θ S).val (jN N K) = (Θ S).val := by
  have h := congrArg Subtype.val ((embeddingsEquivModularRoots N K hNK hj).apply_symm_apply (Θ S))
  rw [embeddingsEquivModularRoots_apply] at h
  exact h

theorem cyclicModularEmbeddingsEquiv_eq_postcomp_iff
    (σ : M ≃ₐ[K] M) (hσ : σ (E.baseChange M).j = (E.baseChange M).j)
    (S T : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    (cyclicModularEmbeddingsEquiv N K E hNK hj Θ T).val =
      σ.toAlgHom.comp (cyclicModularEmbeddingsEquiv N K E hNK hj Θ S).val ↔
        (Θ T).val = σ (Θ S).val := by
  rw [embeddings_eq_postcomp_iff N K hNK hj σ hσ,
    embeddingsEquivModularRoots_apply, embeddingsEquivModularRoots_apply,
    cyclicModularEmbeddingsEquiv_jN, cyclicModularEmbeddingsEquiv_jN]

end
end Dubon2026.SourceEllipticVelu
