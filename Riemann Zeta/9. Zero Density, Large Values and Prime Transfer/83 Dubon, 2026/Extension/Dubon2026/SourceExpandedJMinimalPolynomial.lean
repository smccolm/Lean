import Dubon2026.SourceOriginalJMinimalPolynomial
import Dubon2026.SourceConjugateSlotProduct

/-! DUB-17/18 -> numerical modular genus -> all-level degree -> the
explicit mapped minimal polynomial. This is the original minimal
polynomial after the actual coefficient embedding and q expansion.
Integrality, monicity, degree preservation and its distinguished root
follow from existing proofs, with no root-list identity assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
open scoped IntermediateField

/-- The original j-substitution minimal polynomial under literal expansion and coefficient embedding. -/
def expandedJMinpoly (K : Type*) [Field K] [Algebra ℚ K]
    (A N : ℕ) [NeZero A] [NeZero N] : Polynomial (LaurentSeries K) :=
  (minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).map
    (((coeffEmb K).comp (qExpand ℚ A)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))

theorem expandedJMinpoly_monic (K : Type*) [Field K] [Algebra ℚ K]
    (A N : ℕ) [NeZero A] [NeZero N] : (expandedJMinpoly K A N).Monic :=
  (minpoly.monic (original_j_substitution_isIntegral N)).map _

theorem expandedJMinpoly_natDegree (K : Type*) [Field K] [Algebra ℚ K]
    (A N : ℕ) [NeZero A] [NeZero N] :
    (expandedJMinpoly K A N).natDegree =
      Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮qExpand ℚ N jq⟯ := by
  rw [expandedJMinpoly, (minpoly.monic (original_j_substitution_isIntegral N)).natDegree_map]
  exact (original_j_simple_finrank_eq_minpoly N).symm

theorem expandedJMinpoly_distinguished_root (K : Type*) [Field K] [Algebra ℚ K]
    (A N : ℕ) [NeZero A] [NeZero N] :
    (expandedJMinpoly K A N).eval (TS K (A * N) 1) = 0 := by
  have he : coeffEmb K (qExpand ℚ A (qExpand ℚ N jq)) = TS K (A * N) 1 := by
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
  rw [← he, expandedJMinpoly, Polynomial.eval_map]
  have h := congrArg ((coeffEmb K).comp (qExpand ℚ A))
    (minpoly.aeval ℚ⟮jq⟯ (qExpand ℚ N jq))
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h
  exact h

end
end Dubon2026.SourceFunctionField
