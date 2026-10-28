import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import P2M.Util
namespace P2MW.S_ModularCurve_cuspZeroBar_ne_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) :
    cuspZeroBar N ≠ cuspInftyBar N := by
  intro e
  have h0 := ModularCurve.ord_cuspZeroBar_coeffEmb_jq N h
  rw [e, ModularCurve.ord_cuspInftyBar_coeffEmb_jq] at h0
  have : (N : ℤ) = 1 := by linarith
  exact absurd (Nat.cast_eq_one.mp this) hN.ne'
