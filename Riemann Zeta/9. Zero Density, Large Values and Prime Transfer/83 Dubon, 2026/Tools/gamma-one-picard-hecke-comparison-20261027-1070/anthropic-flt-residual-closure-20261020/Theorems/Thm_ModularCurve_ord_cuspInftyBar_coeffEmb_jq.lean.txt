import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_jq (N : ℕ) [NeZero N] : (cuspInftyBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_cuspInftyBar_coeffEmb_jq.solution
