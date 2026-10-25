import Dubon2026.SourceOriginalAdjacentRootUniqueness
import Dubon2026.SourceOriginalAtkinEmbedding
import Dubon2026.SourcePrimePowerRelationTransport

/-! DUB-17/18 -> actual Hecke norm -> Atkin-Lehner involution.
The common-root theorem pins the second generator directly at level N.
The two-generator theorem makes a separate divisor induction unnecessary. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField IntegralJCoordinate PrimePowerNonmembership
variable (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "FF" => modularFunctionFieldFull (N * p)

theorem exists_original_atkin_generator_embedding (hpN : ¬ p ∣ N) :
    ∃ σ : FF →+* LaurentSeries ℚ,
      (∀ (z : modularFunctionFieldFull N) (hz : (z : LaurentSeries ℚ) ∈ FF),
        σ ⟨z, hz⟩ = qExpand ℚ p z.val) ∧
      σ ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ = jq ∧
      σ ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ = qExpand ℚ N jq := by
  obtain ⟨σ, hbase, hp⟩ := exists_original_atkin_embedding N p hpN
  refine ⟨σ, hbase, hp, ?_⟩
  have hjN : σ ⟨qExpand ℚ N jq, jqd_mem_full (N * p) (dvd_mul_right N p)⟩ =
      qExpand ℚ (N * p) jq := by
    rw [hbase ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩]
    rw [qExpand_qExpand]
    exact qExpand_congr (mul_comm p N) jq
  apply original_adjacent_common_root_unique N p
  · have hrel := relationAtSeed_substitution_eval (modularPolynomial N) (modularPolynomial_eval N) p
    rw [qExpand_congr (mul_comm p N)] at hrel
    have h := relationAtSeed_eval_subfield_map (modularPolynomial N) FF σ
      ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩
      ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ hrel
    rwa [hp] at h
  · have hrel := relationAtSeed_substitution_eval (modularPolynomial p) (modularPolynomial_eval p) N
    have h := relationAtSeed_eval_subfield_map (modularPolynomial p) FF σ
      ⟨qExpand ℚ N jq, jqd_mem_full (N * p) (dvd_mul_right N p)⟩
      ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ hrel
    rwa [hjN] at h

end
end Dubon2026.SourceFunctionField
