import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_zsmul

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) (D : Divisor K F) (n : ℤ) : Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  rw [show evalFun f (n • D) = ∏ v ∈ D.support, v.evalAt f ^ ((n • D) v) from
      Finsupp.prod_of_support_subset _ Finsupp.support_smul _ fun v _ => zpow_zero _,
    evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm n (D v), zpow_mul]
