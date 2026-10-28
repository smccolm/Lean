import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ = -a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_qExpand.solution
