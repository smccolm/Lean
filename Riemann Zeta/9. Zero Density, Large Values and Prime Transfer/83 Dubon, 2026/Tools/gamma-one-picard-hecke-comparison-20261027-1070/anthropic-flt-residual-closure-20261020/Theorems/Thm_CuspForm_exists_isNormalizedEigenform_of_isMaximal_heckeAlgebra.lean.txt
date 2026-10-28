import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem CuspForm.exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra (N : ℕ) [NeZero N]
    (S : Set ℕ) (𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔐 : Ideal (integralClosure ℤ ℂ)),
      g.IsNormalizedEigenform ∧ 𝔐.IsMaximal ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S, ∃ a : integralClosure ℤ ℂ,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) g = (a : ℂ) • g ∧
        (t ∈ 𝔪 → a ∈ 𝔐) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra.solution
