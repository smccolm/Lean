import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve

theorem ModularCurve.frickeInvolutionBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (a b : ℕ) (hab : a * b = N) [NeZero a] [NeZero b] : frickeInvolutionBar N ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro_left a hab))⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand.solution
