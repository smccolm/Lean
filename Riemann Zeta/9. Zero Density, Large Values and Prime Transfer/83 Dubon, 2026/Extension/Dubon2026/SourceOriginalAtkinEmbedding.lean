import Dubon2026.SourceOriginalAtkinPrimePolynomial
import Dubon2026.SourceOriginalConjugateEmbedding

/-! DUB-17/18 -> actual Hecke norm product -> Atkin-Lehner embedding.
The proved reverse root feeds the existing simple-extension constructor.
Actual mixed-level generation identifies its domain with level Np. This
avoids duplicating the external AdjoinRoot/carrier construction. The result
is an embedding with exact base and generator equations; preservation of
the full field and involution are still separate obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
variable (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "FF" => modularFunctionFieldFull N

theorem atkin_extension_generation (hpN : ¬ p ∣ N) :
    modularFunctionFieldFull (N * p) =
      IntermediateField.adjoin ℚ ((FF : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ p jq}) := by
  simpa only [zero_add, pow_one, pow_zero, mul_one] using
    original_full_mixed_prime_power_step_eq_adjoin N p 0 hpN

theorem exists_original_atkin_embedding (hpN : ¬ p ∣ N) :
    ∃ σ : modularFunctionFieldFull (N * p) →+* LaurentSeries ℚ,
      (∀ (z : FF) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull (N * p)),
        σ ⟨z, hz⟩ = qExpand ℚ p z.val) ∧
      σ ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ = jq := by
  have hroot : ((minpoly FF (qExpand ℚ p jq)).map (atkinBase N p)).eval jq = 0 := by
    rw [Polynomial.eval_map]
    exact atkinPrime_minpoly_reverse_root N p hpN
  have hrange : ∀ z : FF, atkinBase N p z ∈ (qExpand ℚ 1).range := by
    intro z
    exact ⟨atkinBase N p z, qExpand_one_apply _⟩
  obtain ⟨τ, hbase, hnew, _⟩ := extend_simple_embedding_in_expansion_range
    FF (atkinBase N p) (qExpand ℚ p jq) (original_j_substitution_isIntegral_over_full N p)
    jq hroot 1 hrange ⟨jq, qExpand_one_apply jq⟩
  let G := IntermediateField.adjoin ℚ ((FF : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ p jq})
  have he : modularFunctionFieldFull (N * p) = G := atkin_extension_generation N p hpN
  let σ : modularFunctionFieldFull (N * p) →+* LaurentSeries ℚ :=
    τ.comp (Subfield.inclusion
      (show (modularFunctionFieldFull (N * p)).toSubfield ≤ G.toSubfield from he.le))
  refine ⟨σ, ?_, ?_⟩
  · intro z hz
    have hzG : (z : LaurentSeries ℚ) ∈ G := he.le hz
    exact hbase z hzG
  · have hxG : qExpand ℚ p jq ∈ G := he.le (jqd_mem_full (N * p) (dvd_mul_left p N))
    exact hnew hxG

end
end Dubon2026.SourceFunctionField
