import Dubon2026.SourceOriginalAtkinGeneratorImages
import Mathlib.Algebra.Algebra.Hom.Rat

/-! DUB-17/18 -> Hecke norm product -> the actual Atkin-Lehner involution.
The proved two-generator field description gives preservation and the
square identity. No additional generator induction or symmetry data is
assumed. The lower-field equation is retained for the degeneracy maps. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem original_full_internal_pair_adjoin_top (N : ℕ) [NeZero N] :
    IntermediateField.adjoin ℚ
      ({⟨jq, jq_mem_full N⟩, ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩} :
        Set (modularFunctionFieldFull N)) = ⊤ := by
  let v : modularFunctionFieldFull N →ₐ[ℚ] LaurentSeries ℚ :=
    RingHom.toRatAlgHom (R := modularFunctionFieldFull N) (modularFunctionFieldFull N).toSubfield.subtype
  have hv : v.fieldRange = modularFunctionFieldFull N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  apply IntermediateField.map_injective v
  rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton]
  change IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) = _
  exact (original_full_eq_pair N).symm.trans (hv.symm.trans (AlgHom.fieldRange_eq_map v))

variable (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "FF" => modularFunctionFieldFull (N * p)

theorem exists_original_atkin_involution (hpN : ¬ p ∣ N) :
    ∃ w : FF ≃+* FF,
      Function.Involutive w ∧
      (∀ (z : modularFunctionFieldFull N) (hz : (z : LaurentSeries ℚ) ∈ FF),
        (w ⟨z, hz⟩ : LaurentSeries ℚ) = qExpand ℚ p z.val) ∧
      (w ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ : LaurentSeries ℚ) = jq ∧
      (w ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ : LaurentSeries ℚ) =
        qExpand ℚ N jq := by
  obtain ⟨σ, hbase, hp, hNp⟩ := exists_original_atkin_generator_embedding N p hpN
  have hj : σ ⟨jq, jq_mem_full (N * p)⟩ = qExpand ℚ p jq :=
    hbase ⟨jq, jq_mem_full N⟩ _
  have hpres : ∀ x : FF, σ x ∈ FF := by
    intro x
    have hx : x ∈ IntermediateField.adjoin ℚ
        ({⟨jq, jq_mem_full (N * p)⟩,
          ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩} : Set FF) := by
      rw [original_full_internal_pair_adjoin_top]
      exact IntermediateField.mem_top
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · rw [hj]
        exact jqd_mem_full (N * p) (dvd_mul_left p N)
      · rcases hy with rfl
        rw [hNp]
        exact jqd_mem_full (N * p) (dvd_mul_right N p)
    | algebraMap r =>
      rw [RingHom.map_rat_algebraMap]
      exact IntermediateField.algebraMap_mem _ r
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let w : FF →+* FF := σ.codRestrict FF hpres
  have hwj : w ⟨jq, jq_mem_full (N * p)⟩ =
      ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ := Subtype.ext hj
  have hwp : w ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ =
      ⟨jq, jq_mem_full (N * p)⟩ := Subtype.ext hp
  have hwNp : w ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ =
      ⟨qExpand ℚ N jq, jqd_mem_full (N * p) (dvd_mul_right N p)⟩ := Subtype.ext hNp
  have hwN : w ⟨qExpand ℚ N jq, jqd_mem_full (N * p) (dvd_mul_right N p)⟩ =
      ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩ := by
    apply Subtype.ext
    change σ ⟨qExpand ℚ N jq, _⟩ = _
    rw [hbase ⟨qExpand ℚ N jq, jqd_mem_full N dvd_rfl⟩, qExpand_qExpand]
    exact qExpand_congr (mul_comm p N) jq
  have hi : Function.Involutive w := by
    intro x
    have hx : x ∈ IntermediateField.adjoin ℚ
        ({⟨jq, jq_mem_full (N * p)⟩,
          ⟨qExpand ℚ (N * p) jq, jqd_mem_full (N * p) dvd_rfl⟩} : Set FF) := by
      rw [original_full_internal_pair_adjoin_top]
      exact IntermediateField.mem_top
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · rw [hwj, hwp]
      · rcases hy with rfl
        rw [hwNp, hwN]
    | algebraMap r => rw [RingHom.map_rat_algebraMap, RingHom.map_rat_algebraMap]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | inv y _ hy => rw [map_inv₀, map_inv₀, hy]
    | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  let e : FF ≃+* FF := { w with invFun := w, left_inv := hi, right_inv := hi }
  exact ⟨e, hi, hbase, hp, hNp⟩

end
end Dubon2026.SourceFunctionField
