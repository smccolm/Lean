import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_heckeULin

theorem ModularCurve.periodMap_heckeULin {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeULin 2 hqN f)
      = HeckeEis.heckeOperatorHom N q ℂ (ModularCurve.periodMap N f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_heckeULin.solution
