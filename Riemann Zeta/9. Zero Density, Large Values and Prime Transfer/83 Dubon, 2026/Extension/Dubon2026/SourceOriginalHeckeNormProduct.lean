import Dubon2026.SourceOriginalHeckeEmbeddingCensus
import Dubon2026.SourceOriginalAtkinCoefficientExtensionR2
import Mathlib.RingTheory.Norm.Transitivity

/-! DUB-17/18 -> Hecke reduction -> the actual expanded norm identity.
The complete original embedding census and the native norm product formula
give the literal Laurent product. The proved coefficient-field Atkin map
discharges its compatibility premises in the final original-field theorem.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Kronecker norm solution. -/
namespace Dubon2026.SourceFunctionField.HeckeNorm
noncomputable section
open IntermediateField
variable (L : Type*) [Field L] [Algebra ℚ L]
variable (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "FF" => modularFunctionFieldOver N L
local notation "GG" => modularFunctionFieldOver (N * p) L
local notation "EE" => AlgebraicClosure (LaurentSeries L)
attribute [local instance] alphaAlgebra

theorem qExpand_norm (hpN : ¬ p ∣ N) (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (hback : ∀ x, w (originalHeckeBeta L N p x) = originalHeckeAlpha L N p x)
    (v : GG) :
    qExpand L p (Algebra.norm FF v : LaurentSeries L) =
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) (w v : LaurentSeries L)) *
        qExpand L p (v : LaurentSeries L) := by
  classical
  letI := targetAlgebra L N p
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero FF :=
    charZero_of_injective_algebraMap (algebraMap L FF).injective
  haveI : FiniteDimensional FF GG := Module.finite_of_finrank_pos (by
    rw [originalHeckeAlpha_finrank L N p hpN]
    exact Nat.succ_pos p)
  apply (algebraMap (LaurentSeries L) EE).injective
  have hnorm := Algebra.norm_eq_prod_embeddings (K := FF) (L := GG) (E := EE) v
  have hmap : algebraMap FF EE (Algebra.norm FF v) =
      algebraMap (LaurentSeries L) EE (qExpand L p (Algebra.norm FF v : LaurentSeries L)) := by
    exact congrArg (algebraMap (LaurentSeries L) EE)
      (originalHeckeBeta_coe L N p (Algebra.norm FF v))
  rw [← hmap, hnorm,
    ← (embedding_bijective L N p hpN ζ hζ w hforward hback).prod_comp (fun σ => σ v),
    Fin.prod_univ_succ, map_mul, map_prod, Finset.prod_range]
  simp only [embedding_zero_apply, embedding_succ_apply]
  exact mul_comm _ _

theorem original_hecke_norm_expanded_product [Algebra.IsAlgebraic ℚ L]
    (hpN : ¬ p ∣ N) (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p) (f : FF) :
    qExpand L p (Algebra.norm FF (originalHeckeBeta L N p f) : LaurentSeries L) =
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) (f : LaurentSeries L)) *
        qExpand L p (qExpand L p (f : LaurentSeries L)) := by
  obtain ⟨w, _, hforward, hback⟩ := exists_original_atkin_over L N p hpN
  have h := qExpand_norm L N p hpN ζ hζ w hforward hback (originalHeckeBeta L N p f)
  simpa only [hback, originalHeckeAlpha_coe, originalHeckeBeta_coe] using h

end
end Dubon2026.SourceFunctionField.HeckeNorm
