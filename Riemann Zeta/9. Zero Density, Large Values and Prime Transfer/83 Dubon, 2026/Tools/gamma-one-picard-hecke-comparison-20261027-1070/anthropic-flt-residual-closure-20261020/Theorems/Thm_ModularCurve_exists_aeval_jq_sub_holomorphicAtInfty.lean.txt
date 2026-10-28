import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty (n : ℕ) : ∀ f : LaurentSeries ℚ, PoleOrderLE f n → ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.solution
