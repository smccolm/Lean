import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩ = -d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand.solution
