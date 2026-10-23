import Dubon2026.SourceResidueSimpleEmbedding

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> actual lower conjugate embeddings.
A lower-level expanded minimal-polynomial root gives an embedding of the
actual full divisor field under its explicit lower-level generation equality.
The actual j action and new generator image are proved. Adapted from local
SourceOriginalConjugateEmbedding using native coefficient-field simple extensions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_full_embedding_of_expanded_minpoly_root
    (A N : ℕ) [NeZero A] [NeZero N]
    (hgen : modularFunctionFieldCoeff N K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)))
    (y : LaurentSeries K) (hy : (residueExpandedJMinpoly K A N).eval y = 0) :
    ∃ σ : modularFunctionFieldCoeff N K →+* LaurentSeries K,
      σ ⟨(jqModC K), jq_mem_coeff_field N K⟩ = TS K A 1 ∧
      σ ⟨qExpand K N (jqModC K), jqd_mem_coeff_field N K dvd_rfl⟩ = y ∧
      ∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff N K),
        σ ⟨z, hz⟩ = qExpand K A (z : LaurentSeries K) := by
  let B := K⟮(jqModC K)⟯
  let φ : B →+* LaurentSeries K :=
    (qExpand K A).comp (algebraMap B (LaurentSeries K))
  have hrange : ∀ z : B, φ z ∈ (qExpand K 1).range := by
    intro z
    exact ⟨φ z, qExpand_one_apply _⟩
  have hyrange : y ∈ (qExpand K 1).range := ⟨y, qExpand_one_apply _⟩
  obtain ⟨τ, hbase, hnew, _⟩ := extend_coefficient_simple_embedding_in_expansion_range
    B φ (qExpand K N (jqModC K)) (residue_j_substitution_isIntegral K N) y hy 1 hrange hyrange
  let G := IntermediateField.adjoin K ((B : Set (LaurentSeries K)) ∪ {qExpand K N (jqModC K)})
  have he : modularFunctionFieldCoeff N K = G :=
    hgen.trans (residue_j_adjoin_union_eq_pair K N).symm
  let σ : modularFunctionFieldCoeff N K →+* LaurentSeries K :=
    τ.comp (Subfield.inclusion
      (show (modularFunctionFieldCoeff N K).toSubfield ≤ G.toSubfield from he.le))
  have hcompat : ∀ (z : B) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff N K),
      σ ⟨z, hz⟩ = φ z := by
    intro z hz
    have hzG : (z : LaurentSeries K) ∈ G := by rw [← he]; exact hz
    exact hbase z hzG
  refine ⟨σ, ?_, ?_, hcompat⟩
  · have h := hcompat ⟨(jqModC K), IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩ (jq_mem_coeff_field N K)
    exact h.trans (by rw [TS, qTwist_one_apply]; rfl)
  · have hxG : qExpand K N (jqModC K) ∈ G := by rw [← he]; exact jqd_mem_coeff_field N K dvd_rfl
    exact hnew hxG

end
end Dubon2026.SourceFunctionField
