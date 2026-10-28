import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_qExpansion_heckeTLin

theorem CuspForm.qExpansion_heckeTLin {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(CuspForm.heckeTLin 2 hp hpN f)
      = PowerSeries.heckeT p 2 (UpperHalfPlane.qExpansion 1 ⇑f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qExpansion_heckeTLin.solution
