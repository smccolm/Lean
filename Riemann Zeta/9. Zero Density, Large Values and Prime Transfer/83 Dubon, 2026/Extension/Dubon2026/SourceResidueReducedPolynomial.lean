import Dubon2026.SourceResidueCoprimePrimeImage

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> coprime prime nonmembership. Adapt local SourceOriginalReducedPolynomial
to actual coefficient-field j series and divisor fields. Lower generation and
conjugate products are explicit induction inputs. Expansion-range preservation
forces each image of j_p to the distinguished branch; bounded polynomial
descent contradicts the already proved prime nonmembership in K(j).
The level and prime must remain nonzero in the coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_member_reduced_polynomial (N : ℕ) [NeZero N]
    (hgen : modularFunctionFieldCoeff N K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)))
    (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldCoeff N K) :
    ∃ g : Polynomial K⟮(jqModC K)⟯,
      g.natDegree < (minpoly K⟮(jqModC K)⟯ (qExpand K N (jqModC K))).natDegree ∧
      Polynomial.aeval (qExpand K N (jqModC K)) g = x := by
  let S := IntermediateField.adjoin K⟮(jqModC K)⟯ ({qExpand K N (jqModC K)} : Set (LaurentSeries K))
  have hxS : x ∈ S := by
    have hle : (IntermediateField.adjoin K
        ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K))).toSubfield ≤ S.toSubfield := by
      rw [IntermediateField.adjoin_toSubfield]
      apply Subfield.closure_le.mpr
      rintro z (hz | hz)
      · obtain ⟨r, rfl⟩ := hz
        exact S.algebraMap_mem (algebraMap K K⟮jqModC K⟯ r)
      · rcases hz with rfl | hz
        · exact S.algebraMap_mem ⟨(jqModC K), IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩
        · rw [Set.mem_singleton_iff] at hz
          exact hz ▸ IntermediateField.subset_adjoin K⟮(jqModC K)⟯ _ rfl
    exact hle (hgen ▸ hx)
  have hi := residue_j_substitution_isIntegral K N
  have hxA : x ∈ Algebra.adjoin K⟮(jqModC K)⟯ ({qExpand K N (jqModC K)} : Set (LaurentSeries K)) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
    exact hxS
  obtain ⟨g, hg⟩ := Algebra.adjoin_mem_exists_aeval K⟮(jqModC K)⟯ (qExpand K N (jqModC K)) hxA
  refine ⟨g %ₘ minpoly K⟮(jqModC K)⟯ (qExpand K N (jqModC K)), ?_, ?_⟩
  · by_cases hz : g %ₘ minpoly K⟮(jqModC K)⟯ (qExpand K N (jqModC K)) = 0
    · rw [hz, Polynomial.natDegree_zero]
      exact minpoly.natDegree_pos hi
    · exact Polynomial.natDegree_lt_natDegree hz
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hi))
  · rw [Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hg

theorem residue_polynomial_value_under_embedding
    (N A : ℕ) [NeZero N] [NeZero A]
    (σ : modularFunctionFieldCoeff N K →+* LaurentSeries K)
    (hbase : ∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff N K),
      σ ⟨z, hz⟩ = (qExpand K A (z : LaurentSeries K)))
    (g : Polynomial K⟮(jqModC K)⟯) (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldCoeff N K)
    (hg : Polynomial.aeval (qExpand K N (jqModC K)) g = x) :
    g.eval₂ (((qExpand K A)).comp (algebraMap K⟮(jqModC K)⟯ (LaurentSeries K)))
      (σ ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩) = σ ⟨x, hx⟩ := by
  let F := modularFunctionFieldCoeff N K
  have hBF : K⟮(jqModC K)⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_coeff_field N K))
  let ι : K⟮(jqModC K)⟯ →+* F := Subfield.inclusion
    (show (K⟮(jqModC K)⟯).toSubfield ≤ F.toSubfield from hBF)
  have hF : g.eval₂ ι (⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩ : F) = ⟨x, hx⟩ := by
    apply (algebraMap F (LaurentSeries K)).injective
    rw [Polynomial.hom_eval₂]
    exact hg
  have h := congrArg σ hF
  rw [Polynomial.hom_eval₂] at h
  have hc : σ.comp ι =
      ((qExpand K A)).comp (algebraMap K⟮(jqModC K)⟯ (LaurentSeries K)) := by
    refine RingHom.ext fun z => ?_
    exact hbase z (hBF z.2)
  rwa [hc] at h

end
end Dubon2026.SourceFunctionField
