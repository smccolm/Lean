import Dubon2026.SourceGammaOneAdjacentJEmbedding
import Mathlib.Algebra.Algebra.Hom.Rat

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> coefficient extension
of the reverse embedding. The proved correspondence generators map into
the actual correspondence field: the lower field maps by beta and the
adjacent j-coordinate maps to j. Native field-adjoin induction therefore
proves preservation; it is not an extra Atkin hypothesis. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
local notation "FF" => x1FunctionField M
local notation "GG" => x1x0FunctionFieldC ℚ M (p * M)

theorem adjacentJ_embedding_preserves (hcop : Nat.Coprime M p)
    (σ : GG →+* LaurentSeries ℚ)
    (hbase : ∀ (z : FF) (hz : (z : LaurentSeries ℚ) ∈ GG), σ ⟨z, hz⟩ = qExpand ℚ p z.val)
    (hj : σ ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩ = jq) :
    ∀ x : GG, σ x ∈ GG := by
  let φ : GG →ₐ[ℚ] LaurentSeries ℚ := σ.toRatAlgHom
  let A : IntermediateField ℚ GG := (GG).comap φ
  let ι : GG →ₐ[ℚ] LaurentSeries ℚ := RingHom.toRatAlgHom (R := GG) (GG).toSubfield.subtype
  have hle : GG ≤ A.map ι := by
    apply le_trans (gammaOne_adjacentJ_generation M p hcop).le
    apply adjoin_le_iff.mpr
    rintro y (hy | hy)
    · have hyG := x1FunctionFieldC_le_x1x0 ℚ M (p * M) hy
      refine ⟨⟨y, hyG⟩, ?_, rfl⟩
      change σ ⟨y, hyG⟩ ∈ GG
      rw [hbase ⟨y, hy⟩ hyG]
      exact gamma1_degeneracy_map_le ℚ M p ⟨y, hy, rfl⟩
    · rcases hy with rfl
      refine ⟨⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩, ?_, rfl⟩
      change σ ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩ ∈ GG
      rw [hj]
      exact jq_mem_qExpFunctionField _
  intro x
  obtain ⟨y, hy, hyx⟩ := hle x.property
  have he : y = x := Subtype.ext hyx
  rw [← he]
  exact hy

theorem exists_gammaOne_adjacentJ_endomorphism (hcop : Nat.Coprime M p) :
    ∃ w : GG →+* GG,
      (∀ (z : FF) (hz : (z : LaurentSeries ℚ) ∈ GG),
        (w ⟨z, hz⟩ : LaurentSeries ℚ) = qExpand ℚ p z.val) ∧
      (w ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩ : LaurentSeries ℚ) = jq := by
  obtain ⟨σ, hbase, hj⟩ := exists_gammaOne_adjacentJ_embedding M p hcop
  exact ⟨σ.codRestrict GG (adjacentJ_embedding_preserves M p hcop σ hbase hj), hbase, hj⟩

end
end Dubon2026.SourceFunctionField.GammaOne
