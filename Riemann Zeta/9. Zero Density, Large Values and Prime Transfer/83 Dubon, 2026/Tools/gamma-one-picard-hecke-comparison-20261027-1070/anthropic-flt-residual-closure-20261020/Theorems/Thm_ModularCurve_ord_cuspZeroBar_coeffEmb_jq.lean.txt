import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_jq (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspZeroBar_coeffEmb_jq.solution
