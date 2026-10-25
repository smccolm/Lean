import Dubon2026.SourceTateScalarFaithfulness
import Dubon2026.SourceFractionTensorInjective

/-! DUB-17/18 -> rational original Weil nondegeneracy. The existing faithful
p-adic scalar action makes the literal Tate module inject into its rational
tensor. This applies in particular to the actual roots-of-unity Tate target. -/
namespace Dubon2026.TateModule
noncomputable section
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M]

theorem rational_one_tmul_injective :
    Function.Injective (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1) := by
  let j := TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p M) 1
  letI : IsLocalizedModule (nonZeroDivisors ℤ_[p]) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[p]) ℚ_[p] j).mpr
      (TensorProduct.isBaseChange ℤ_[p] (TateModule p M) ℚ_[p])
  apply (IsLocalizedModule.injective_iff_isRegular (S := nonZeroDivisors ℤ_[p])
    (f := j)).mpr
  intro c x y h
  apply sub_eq_zero.mp
  apply eq_zero_of_nonzero_scalar_smul_eq_zero p c.val (nonZeroDivisors.ne_zero c.property)
  exact (smul_sub c.val x y).trans (sub_eq_zero.mpr h)

end
end Dubon2026.TateModule
