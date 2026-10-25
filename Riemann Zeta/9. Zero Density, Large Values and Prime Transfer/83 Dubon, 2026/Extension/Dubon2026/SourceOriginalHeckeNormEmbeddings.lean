import Dubon2026.SourceOriginalHeckePrimeDegree
import Dubon2026.SourcePrimeConjugateRoots
import Mathlib.FieldTheory.AlgebraicClosure

/-! DUB-17/18 -> actual degeneracy norm product -> explicit embeddings.
The literal original inclusion is the source algebra, while q-expansion
defines the target algebra. Twisting the Atkin map and the final expansion
give the p+1 candidates. The forward degeneracy equation is explicit here
and is discharged by the proved actual Atkin involution in the consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Kronecker norm solution. -/
namespace Dubon2026.SourceFunctionField.HeckeNorm
noncomputable section
open IntermediateField PrimeDegreeAux
variable (L : Type*) [Field L] [Algebra ℚ L]
variable (N p : ℕ) [Fact p.Prime]
local notation "FF" => modularFunctionFieldOver N L
local notation "GG" => modularFunctionFieldOver (N * p) L
local notation "EE" => AlgebraicClosure (LaurentSeries L)

/-- The actual first degeneracy map supplies the source extension algebra. -/
abbrev alphaAlgebra : Algebra FF GG := SourceCurve.algebraAlong (originalHeckeAlpha L N p)

/-- The actual second degeneracy map supplies the Laurent closure's lower-field algebra. -/
abbrev targetAlgebra : Algebra FF EE :=
  ((algebraMap (LaurentSeries L) EE).comp
    ((modularFunctionFieldOver (N * p) L).toSubfield.subtype.comp (originalHeckeBeta L N p).toRingHom)).toAlgebra

attribute [local instance] alphaAlgebra

/-- Twist the actual Atkin map to obtain an embedding over the original inclusion. -/
def twistEmbedding (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (c : Lˣ) (hc : c ^ p = 1) :
    letI := targetAlgebra L N p; GG →ₐ[FF] EE := by
  letI := targetAlgebra L N p
  exact {
    toRingHom := (algebraMap (LaurentSeries L) EE).comp
      ((qTwist c).comp ((modularFunctionFieldOver (N * p) L).toSubfield.subtype.comp w.toAlgHom.toRingHom))
    commutes' x := by
      change algebraMap (LaurentSeries L) EE (qTwist c (w (originalHeckeAlpha L N p x))) =
        algebraMap (LaurentSeries L) EE (originalHeckeBeta L N p x)
      rw [hforward x, originalHeckeBeta_coe, qTwist_qExpand_of_pow_eq_one p c hc] }

theorem lastEmbedding_commutes (x : FF) :
    ((algebraMap (LaurentSeries L) EE).comp
      ((qExpand L p).comp (modularFunctionFieldOver (N * p) L).toSubfield.subtype))
        (originalHeckeAlpha L N p x) =
      algebraMap (LaurentSeries L) EE (originalHeckeBeta L N p x) :=
  congrArg (algebraMap (LaurentSeries L) EE)
    ((congrArg (qExpand L p) (originalHeckeAlpha_coe L N p x)).trans
      (originalHeckeBeta_coe L N p x).symm)

/-- The remaining embedding is literal Laurent q-expansion. -/
def lastEmbedding : letI := targetAlgebra L N p; GG →ₐ[FF] EE := by
  letI := targetAlgebra L N p
  exact {
    toRingHom := (algebraMap (LaurentSeries L) EE).comp
      ((qExpand L p).comp (modularFunctionFieldOver (N * p) L).toSubfield.subtype)
    commutes' := lastEmbedding_commutes L N p }

/-- The p twists and one expansion, indexed by the existing prime-conjugate indexing set. -/
def embedding (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x) :
    Fin (p + 1) → (letI := targetAlgebra L N p; GG →ₐ[FF] EE) :=
  Fin.cases (lastEmbedding L N p) (fun b =>
    twistEmbedding L N p w hforward (ζ ^ (b : ℕ)) (by
      rw [← pow_mul, Nat.mul_comm (b : ℕ) p, pow_mul,
        units_pow_eq_one_of_isPrimitiveRoot hζ, one_pow]))

theorem embedding_zero_apply (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (v : GG) : embedding L N p ζ hζ w hforward 0 v =
      algebraMap (LaurentSeries L) EE (qExpand L p v) := rfl

theorem embedding_succ_apply (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (b : Fin p) (v : GG) : embedding L N p ζ hζ w hforward b.succ v =
      algebraMap (LaurentSeries L) EE (qTwist (ζ ^ (b : ℕ)) (w v)) := rfl

theorem embedding_jBeta (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (hback : ∀ x, w (originalHeckeBeta L N p x) = originalHeckeAlpha L N p x)
    (i : Fin (p + 1)) :
    embedding L N p ζ hζ w hforward i (originalHeckeBeta L N p (jOver N L)) =
      algebraMap (LaurentSeries L) EE (PhiGen.conj p ζ i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [embedding_zero_apply, originalHeckeBeta_coe, PhiGen.conj_zero, qExpand_qExpand]
    rfl
  · rw [embedding_succ_apply, hback, originalHeckeAlpha_coe, PhiGen.conj_succ]
    rfl

end
end Dubon2026.SourceFunctionField.HeckeNorm
