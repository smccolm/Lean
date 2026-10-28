import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, Place.evalAt v f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [AlgebraicCurve.Divisor.evalFun_add f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂), evalFun_single, evalFun_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]
