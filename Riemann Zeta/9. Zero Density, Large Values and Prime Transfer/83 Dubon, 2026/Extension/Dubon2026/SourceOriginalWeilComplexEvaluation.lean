import Dubon2026.SourceOriginalWeilEvaluation
import Dubon2026.SourceOriginalDivisorConorm

/-! DUB-17/18 -> original Tate nondegeneracy -> arithmetic finite detection.
The already proved constant-field place extension preserves literal residue
values, and its injective divisor conorm preserves their finite products.
This supplies the evaluation edge needed to descend complex Weil detection. -/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem originalPlaceEval_liftPlace (v : Place Qbar FQ) (f : FQ) :
    originalPlaceEval N ℂ (liftPlace N v) (fieldMap N f) =
      sigma (originalPlaceEval N Qbar v f) := by
  classical
  by_cases hf : f ∈ v.toValuationSubring
  · let c := originalPlaceEval N Qbar v f
    by_cases he : f - algebraMap Qbar FQ c = 0
    · have heq := sub_eq_zero.mp he
      rw [heq, fieldMap_constants, originalPlaceEval_algebraMap,
        originalPlaceEval_algebraMap]
    · have hz : originalPlaceEval N Qbar v (f - algebraMap Qbar FQ c) = 0 := by
        rw [originalPlaceEval_sub_algebraMap N Qbar v hf]
        exact sub_self _
      have ho := (originalPlaceEval_eq_zero_iff_ord_pos N Qbar v
        (sub_mem hf (v.algebraMap_mem' c)) he).mp hz
      apply originalPlaceEval_eq_of_ord_sub_pos N ℂ
      rw [← fieldMap_constants, ← map_sub, ord_liftPlace]
      exact ho
  · have ht : fieldMap N f ∉ (liftPlace N v).toValuationSubring :=
      fun h => hf ((mem_liftPlace_iff N v f).mp h)
    simp only [originalPlaceEval, dif_neg hf, dif_neg ht, map_zero]

theorem originalDivisorEval_conorm (f : FQ) (D : Divisor Qbar FQ) :
    originalDivisorEval N ℂ (fieldMap N f) (conorm N D) =
      sigma (originalDivisorEval N Qbar f D) := by
  classical
  change (Finsupp.mapDomain (liftPlace N) D).prod
      (fun v n => originalPlaceEval N ℂ v (fieldMap N f) ^ n) = _
  rw [Finsupp.prod_mapDomain_index_inj (liftPlace_injective N)]
  simp only [originalDivisorEval, Finsupp.prod, map_prod, map_zpow₀,
    originalPlaceEval_liftPlace]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
