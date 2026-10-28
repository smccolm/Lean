import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

theorem PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.solution
