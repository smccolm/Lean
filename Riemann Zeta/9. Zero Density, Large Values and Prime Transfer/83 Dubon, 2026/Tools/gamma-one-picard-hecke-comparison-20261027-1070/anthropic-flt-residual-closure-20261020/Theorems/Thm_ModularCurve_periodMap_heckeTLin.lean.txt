import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_heckeTLin

theorem ModularCurve.periodMap_heckeTLin {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_heckeTLin.solution
