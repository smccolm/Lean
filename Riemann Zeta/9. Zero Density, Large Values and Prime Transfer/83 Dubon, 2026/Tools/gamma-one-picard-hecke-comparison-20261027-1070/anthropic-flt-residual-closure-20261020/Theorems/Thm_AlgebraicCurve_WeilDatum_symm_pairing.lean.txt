import Mathlib
import Definitions.Def_AlgebraicCurve_WeilDatum
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_WeilDatum_symm_pairing

open AlgebraicCurve
theorem AlgebraicCurve.WeilDatum.symm_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_WeilDatum_symm_pairing.solution
