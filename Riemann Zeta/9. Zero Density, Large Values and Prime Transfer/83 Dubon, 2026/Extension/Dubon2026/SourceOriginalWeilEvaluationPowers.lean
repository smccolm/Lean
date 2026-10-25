import Dubon2026.SourceOriginalWeilEvaluation

/-! DUB-17/18 -> Frobenius determinant -> original Weil pairing descent.
Evaluation commutes with the natural power used when changing a principal
representative. The local statement uses the actual residue ring map. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped BigOperators
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalPlaceEval_pow_of_mem (v : Place L (modularFunctionFieldOver N L))
    {f : modularFunctionFieldOver N L} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    originalPlaceEval N L v (f ^ n) = originalPlaceEval N L v f ^ n := by
  rw [originalPlaceEval_of_mem N L v (pow_mem hf n), originalPlaceEval_of_mem N L v hf]
  exact (originalPlaceRegularEval N L v).map_pow ⟨f, hf⟩ n

theorem originalDivisorEval_pow (f : modularFunctionFieldOver N L)
    (D : Divisor L (modularFunctionFieldOver N L))
    (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (n : ℕ) :
    originalDivisorEval N L (f ^ n) D = originalDivisorEval N L f D ^ n := by
  classical
  simp only [originalDivisorEval, Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro v hv
  rw [originalPlaceEval_pow_of_mem N L v (hf v hv)]
  simpa only [zpow_natCast] using zpow_comm (originalPlaceEval N L v f) (n : ℤ) (D v)

end
end Dubon2026.SourceFunctionField
