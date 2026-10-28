import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime

theorem CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime {N : ℕ} [NeZero N]
    (S : Set ℕ) (𝔭 : Ideal (CuspForm.heckeAlgebra N 2 S)) (h𝔭 : 𝔭.IsPrime) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = 0 → t ∈ 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.solution
