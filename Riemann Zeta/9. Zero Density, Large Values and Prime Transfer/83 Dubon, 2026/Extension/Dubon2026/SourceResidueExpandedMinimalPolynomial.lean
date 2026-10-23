import Dubon2026.SourceResidueJMinimalPolynomial
import Dubon2026.SourceConjugateSlotProduct

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> actual lower-level conjugates.
Expand the native minimal polynomial over K(j), without a rational-field
algebra structure on K. Integrality proves monicity and the distinguished
root. Adapted from the existing SourceExpandedJMinimalPolynomial. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
open scoped IntermediateField

/-- The actual coefficient-field j minimal polynomial under literal expansion. -/
def residueExpandedJMinpoly (K : Type*) [Field K]
    (A N : ℕ) [NeZero A] [NeZero N] : Polynomial (LaurentSeries K) :=
  (minpoly K⟮jqModC K⟯ (qExpand K N (jqModC K))).map
    ((qExpand K A).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))

theorem residueExpandedJMinpoly_monic (K : Type*) [Field K]
    (A N : ℕ) [NeZero A] [NeZero N] : (residueExpandedJMinpoly K A N).Monic :=
  (minpoly.monic (residue_j_substitution_isIntegral K N)).map _

theorem residueExpandedJMinpoly_natDegree (K : Type*) [Field K]
    (A N : ℕ) [NeZero A] [NeZero N] :
    (residueExpandedJMinpoly K A N).natDegree =
      Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮qExpand K N (jqModC K)⟯ := by
  rw [residueExpandedJMinpoly, (minpoly.monic (residue_j_substitution_isIntegral K N)).natDegree_map]
  exact (residue_j_simple_finrank_eq_minpoly K N).symm

theorem residueExpandedJMinpoly_distinguished_root (K : Type*) [Field K]
    (A N : ℕ) [NeZero A] [NeZero N] :
    (residueExpandedJMinpoly K A N).eval (TS K (A * N) 1) = 0 := by
  have he : qExpand K A (qExpand K N (jqModC K)) = TS K (A * N) 1 := by
    rw [qExpand_qExpand, TS, qTwist_one_apply]
  rw [← he, residueExpandedJMinpoly, Polynomial.eval_map]
  have h := congrArg (qExpand K A) (minpoly.aeval K⟮jqModC K⟯ (qExpand K N (jqModC K)))
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h
  exact h

end
end Dubon2026.SourceFunctionField
