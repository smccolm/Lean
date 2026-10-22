import Dubon2026.SourceOriginalPairBaseChange

/-! DUB-17/18 -> numerical modular genus -> cusp classification -> actual
conjugate embeddings over the geometric coefficient field. The rational
minimal polynomial transports to the actual coefficient-extended minimal
polynomial: evaluation gives divisibility, and the proved exact degree
gives equality. This supplies the precise relation needed to construct
every conjugate embedding without a new irreducibility assumption.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem original_mapped_minpoly_root :
    Polynomial.aeval (coeffEmb L (qExpand ℚ N jq))
      ((minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).map (DegreeTransport.φ L)) = 0 := by
  have hcomp : (algebraMap (DegreeTransport.K L jq) (LaurentSeries L)).comp
      (DegreeTransport.φ L) =
      (coeffEmb L).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp,
    ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

theorem original_j_substitution_isIntegral_over :
    IsIntegral (DegreeTransport.K L jq) (coeffEmb L (qExpand ℚ N jq)) :=
  ⟨(minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).map (DegreeTransport.φ L),
    (minpoly.monic (original_j_substitution_isIntegral N)).map _, original_mapped_minpoly_root N L⟩

theorem original_minpoly_degree_over :
    (minpoly (DegreeTransport.K L jq) (coeffEmb L (qExpand ℚ N jq))).natDegree =
      SourceLevelProjective.dedekindPsi N := by
  let B := DegreeTransport.K L jq
  let S := IntermediateField.adjoin B ({coeffEmb L (qExpand ℚ N jq)} : Set (LaurentSeries L))
  have hle : B ≤ modularFunctionFieldOver N L := DegreeTransport.K_le L (jq_mem_full N)
  have hs : extendScalars hle = S := by
    apply restrictScalars_injective L
    exact (extendScalars_restrictScalars hle).trans (original_field_eq_simple_restrict_over N L)
  have h := finrank_original_over_j_eq_psi N L
  rw [original_coordinate_finrank_eq_relfinrank,
    relfinrank_eq_finrank_of_le hle, hs] at h
  exact (IntermediateField.adjoin.finrank (original_j_substitution_isIntegral_over N L)).symm.trans h

theorem original_minpoly_eq_map_over :
    minpoly (DegreeTransport.K L jq) (coeffEmb L (qExpand ℚ N jq)) =
      (minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).map (DegreeTransport.φ L) := by
  have hm := minpoly.monic (original_j_substitution_isIntegral N)
  have hdegree : ((minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).map (DegreeTransport.φ L)).natDegree =
      (minpoly (DegreeTransport.K L jq) (coeffEmb L (qExpand ℚ N jq))).natDegree := by
    rw [hm.natDegree_map, original_minpoly_degree_over,
      original_minpoly_degree_eq_full_relfinrank_of_generation N (original_full_eq_pair N),
      original_full_rational_relfinrank_eq_psi]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (original_j_substitution_isIntegral_over N L)) (hm.map _)
    (minpoly.dvd _ _ (original_mapped_minpoly_root N L)) hdegree.le).symm

end
end Dubon2026.SourceFunctionField
