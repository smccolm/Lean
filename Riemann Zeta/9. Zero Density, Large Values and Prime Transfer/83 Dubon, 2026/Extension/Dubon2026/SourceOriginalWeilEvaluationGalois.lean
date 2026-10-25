import Dubon2026.SourceOriginalWeilEvaluation
import Dubon2026.SourceOriginalArithmeticDivisors

/-! DUB-17/18 -> original Frobenius determinant -> arithmetic Weil
pairing -> semilinearity of its literal divisor evaluations. The actual
coefficient automorphism and original place permutation preserve evaluation
by the proved order criterion and residue identification. This proves the
arithmetic compatibility of the evaluation factors; it does not yet descend
their ratio to Picard torsion or establish nondegeneracy. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
local notation "FF" => modularFunctionFieldOver N L

theorem originalPlaceEval_arithmetic (σ : L ≃ₐ[ℚ] L) (v : Place L FF) (f : FF) :
    originalPlaceEval N L (originalArithmeticPlace N σ v) (originalArithmeticRingAut N σ f) =
      σ (originalPlaceEval N L v f) := by
  classical
  by_cases hf : f ∈ v.toValuationSubring
  · let c := originalPlaceEval N L v f
    by_cases he : f - algebraMap L FF c = 0
    · have heq := sub_eq_zero.mp he
      rw [heq, originalArithmeticRingAut_constants, originalPlaceEval_algebraMap,
        originalPlaceEval_algebraMap]
    · have hz : originalPlaceEval N L v (f - algebraMap L FF c) = 0 := by
        rw [originalPlaceEval_sub_algebraMap N L v hf]
        exact sub_self _
      have ho := (originalPlaceEval_eq_zero_iff_ord_pos N L v
        (sub_mem hf (v.algebraMap_mem' c)) he).mp hz
      apply originalPlaceEval_eq_of_ord_sub_pos N L
      rw [← originalArithmeticRingAut_constants, ← map_sub, originalArithmeticPlace_ord_action]
      exact ho
  · have ht : originalArithmeticRingAut N σ f ∉ (originalArithmeticPlace N σ v).toValuationSubring := by
      rw [Place.mem_iff_ord_nonneg, originalArithmeticPlace_ord_action]
      exact fun h => hf (v.mem_of_ord_nonneg h)
    simp only [originalPlaceEval, dif_neg hf, dif_neg ht, map_zero]

theorem originalDivisorEval_arithmetic (σ : L ≃ₐ[ℚ] L) (f : FF) (D : Divisor L FF) :
    originalDivisorEval N L (originalArithmeticRingAut N σ f) (originalArithmeticDivisorEquiv N σ D) =
      σ (originalDivisorEval N L f D) := by
  classical
  change (Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N σ) D).prod
      (fun v n => originalPlaceEval N L v (originalArithmeticRingAut N σ f) ^ n) = _
  rw [Finsupp.prod_equivMapDomain]
  change D.prod (fun v n => originalPlaceEval N L (originalArithmeticPlace N σ v)
    (originalArithmeticRingAut N σ f) ^ n) = σ (D.prod (fun v n => originalPlaceEval N L v f ^ n))
  simp only [Finsupp.prod, map_prod, map_zpow₀, originalPlaceEval_arithmetic]

end
end Dubon2026.SourceFunctionField
