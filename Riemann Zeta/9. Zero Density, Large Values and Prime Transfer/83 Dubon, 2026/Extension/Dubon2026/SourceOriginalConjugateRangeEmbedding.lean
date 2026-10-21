import Dubon2026.SourceConjugateConstantDescent

/-! DUB-17/18 -> numerical modular genus -> composite degree -> coprime
prime nonmembership. Every lower conjugate in the p-expansion range
constructs an embedding of the actual original lower field whose entire
image stays in that range. The existing simple-extension range theorem
supplies this fact directly, replacing a second field-induction proof.
Original lower-level generation is the explicit induction input.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem original_conjugate_embedding_in_prime_expansion_range
    (M p : ℕ) [NeZero M] [NeZero p]
    (hgen : modularFunctionFieldFull M =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ)))
    (y : LaurentSeries K) (hy : (expandedJMinpoly K (M * p) M).IsRoot y)
    (hyrange : y ∈ (qExpand K p).range) :
    ∃ σ : modularFunctionFieldFull M →+* LaurentSeries K,
      (∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull M),
        σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ (M * p) (z : LaurentSeries ℚ))) ∧
      σ ⟨qExpand ℚ M jq, jqd_mem_full M dvd_rfl⟩ = y ∧
      ∀ z : modularFunctionFieldFull M, σ z ∈ (qExpand K p).range := by
  let B := ℚ⟮jq⟯
  let φ : B →+* LaurentSeries K :=
    ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap B (LaurentSeries ℚ))
  have hrange : ∀ z : B, φ z ∈ (qExpand K p).range := by
    intro z
    refine ⟨coeffEmb K (qExpand ℚ M (z : LaurentSeries ℚ)), ?_⟩
    change qExpand K p (coeffMap (algebraMap ℚ K) (qExpand ℚ M (z : LaurentSeries ℚ))) = _
    rw [← coeffMap_qExpand, qExpand_qExpand,
      qExpand_congr (Nat.mul_comm p M) (z : LaurentSeries ℚ)]
    rfl
  obtain ⟨τ, hbase, hnew, hall⟩ := extend_simple_embedding_in_expansion_range
    B φ (qExpand ℚ M jq) (original_j_substitution_isIntegral M) y hy p hrange hyrange
  let G := IntermediateField.adjoin ℚ ((B : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ M jq})
  have he : modularFunctionFieldFull M = G :=
    hgen.trans (original_j_adjoin_union_eq_pair M).symm
  let σ : modularFunctionFieldFull M →+* LaurentSeries K := τ.comp
    (Subfield.inclusion (show (modularFunctionFieldFull M).toSubfield ≤ G.toSubfield from he.le))
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro z hz
    have hzG : (z : LaurentSeries ℚ) ∈ G := by rw [← he]; exact hz
    exact hbase z hzG
  · have hzG : qExpand ℚ M jq ∈ G := by rw [← he]; exact jqd_mem_full M dvd_rfl
    exact hnew hzG
  · intro z
    exact hall ⟨z, he.le z.2⟩

end
end Dubon2026.SourceFunctionField
