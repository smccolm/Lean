import Dubon2026.SourceCoprimePrimeImage

/-! DUB-17/18 -> numerical modular genus -> composite degree ->
coprime prime nonmembership. Under the lower generation equality,
every actual field member has a polynomial expression in j_N of degree
below its minimal polynomial. Native algebraic adjoining and remainder
evaluation give the bounded expression. Its values transport through
the actual conjugate embeddings with the specified base action.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

theorem original_member_reduced_polynomial (N : ℕ) [NeZero N]
    (hgen : modularFunctionFieldFull N =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)))
    (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull N) :
    ∃ g : Polynomial ℚ⟮jq⟯,
      g.natDegree < (minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).natDegree ∧
      Polynomial.aeval (qExpand ℚ N jq) g = x := by
  let S := IntermediateField.adjoin ℚ⟮jq⟯ ({qExpand ℚ N jq} : Set (LaurentSeries ℚ))
  have hxS : x ∈ S := by
    have hle : (IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ))).toSubfield ≤ S.toSubfield := by
      rw [IntermediateField.adjoin_toSubfield]
      apply Subfield.closure_le.mpr
      rintro z (hz | hz)
      · obtain ⟨r, rfl⟩ := hz
        simp
      · rcases hz with rfl | hz
        · exact S.algebraMap_mem ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩
        · rw [Set.mem_singleton_iff] at hz
          exact hz ▸ IntermediateField.subset_adjoin ℚ⟮jq⟯ _ rfl
    exact hle (hgen ▸ hx)
  have hi := original_j_substitution_isIntegral N
  have hxA : x ∈ Algebra.adjoin ℚ⟮jq⟯ ({qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
    exact hxS
  obtain ⟨g, hg⟩ := Algebra.adjoin_mem_exists_aeval ℚ⟮jq⟯ (qExpand ℚ N jq) hxA
  refine ⟨g %ₘ minpoly ℚ⟮jq⟯ (qExpand ℚ N jq), ?_, ?_⟩
  · by_cases hz : g %ₘ minpoly ℚ⟮jq⟯ (qExpand ℚ N jq) = 0
    · rw [hz, Polynomial.natDegree_zero]
      exact minpoly.natDegree_pos hi
    · exact Polynomial.natDegree_lt_natDegree hz
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hi))
  · rw [Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hg

theorem original_polynomial_value_under_embedding {K : Type*} [Field K] [Algebra ℚ K]
    (N A : ℕ) [NeZero N] [NeZero A]
    (σ : modularFunctionFieldFull N →+* LaurentSeries K)
    (hbase : ∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull N),
      σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ A (z : LaurentSeries ℚ)))
    (g : Polynomial ℚ⟮jq⟯) (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull N)
    (hg : Polynomial.aeval (qExpand ℚ N jq) g = x) :
    g.eval₂ (((coeffEmb K).comp (qExpand ℚ A)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      (σ ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩) = σ ⟨x, hx⟩ := by
  let F := modularFunctionFieldFull N
  have hBF : ℚ⟮jq⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_full N))
  let ι : ℚ⟮jq⟯ →+* F := Subfield.inclusion
    (show (ℚ⟮jq⟯).toSubfield ≤ F.toSubfield from hBF)
  have hF : g.eval₂ ι (⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩ : F) = ⟨x, hx⟩ := by
    apply (algebraMap F (LaurentSeries ℚ)).injective
    rw [Polynomial.hom_eval₂]
    exact hg
  have h := congrArg σ hF
  rw [Polynomial.hom_eval₂] at h
  have hc : σ.comp ι =
      ((coeffEmb K).comp (qExpand ℚ A)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    refine RingHom.ext fun z => ?_
    exact hbase z (hBF z.2)
  rwa [hc] at h

end
end Dubon2026.SourceFunctionField
