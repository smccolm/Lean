import Dubon2026.SourceExpandedJConjugateComparison

/-! DUB-17/18 -> numerical modular genus -> composite degree and
generation -> constructing the actual indexed minimal-polynomial roots.
An already proved root at a lower level gives an embedding of that
original full field whenever its lower-level generation equality holds.
The existing simple-extension embedding theorem supplies the map; the
range requirement is trivial at expansion one. This avoids a second
native adjoin-homomorphism construction for the conjugate induction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem original_full_embedding_of_expanded_minpoly_root
    (A N : ℕ) [NeZero A] [NeZero N]
    (hgen : modularFunctionFieldFull N =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)))
    (y : LaurentSeries K) (hy : (expandedJMinpoly K A N).eval y = 0) :
    ∃ σ : modularFunctionFieldFull N →+* LaurentSeries K,
      σ ⟨jq, jq_mem_full N⟩ = TS K A 1 ∧
      σ ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩ = y ∧
      ∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull N),
        σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ A (z : LaurentSeries ℚ)) := by
  let B := ℚ⟮jq⟯
  let φ : B →+* LaurentSeries K :=
    ((coeffEmb K).comp (qExpand ℚ A)).comp (algebraMap B (LaurentSeries ℚ))
  have hrange : ∀ z : B, φ z ∈ (qExpand K 1).range := by
    intro z
    exact ⟨φ z, qExpand_one_apply _⟩
  have hyrange : y ∈ (qExpand K 1).range := ⟨y, qExpand_one_apply _⟩
  obtain ⟨τ, hbase, hnew, _⟩ := extend_simple_embedding_in_expansion_range
    B φ (qExpand ℚ N jq) (original_j_substitution_isIntegral N) y hy 1 hrange hyrange
  let G := IntermediateField.adjoin ℚ ((B : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ N jq})
  have he : modularFunctionFieldFull N = G :=
    hgen.trans (original_j_adjoin_union_eq_pair N).symm
  let σ : modularFunctionFieldFull N →+* LaurentSeries K :=
    τ.comp (Subfield.inclusion
      (show (modularFunctionFieldFull N).toSubfield ≤ G.toSubfield from he.le))
  have hcompat : ∀ (z : B) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull N),
      σ ⟨z, hz⟩ = φ z := by
    intro z hz
    have hzG : (z : LaurentSeries ℚ) ∈ G := by rw [← he]; exact hz
    exact hbase z hzG
  refine ⟨σ, ?_, ?_, hcompat⟩
  · have h := hcompat ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩ (jq_mem_full N)
    exact h.trans (coeffEmb_qExpand_jq_eq_TS A)
  · have hxG : qExpand ℚ N jq ∈ G := by rw [← he]; exact jqd_mem_full N dvd_rfl
    exact hnew hxG

end
end Dubon2026.SourceFunctionField
