import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.exists_sub_eq_const {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n f G) :
    ∃ v : ↥(HeckeEis.BinaryForm ℂ n), ∀ τ : UpperHalfPlane, F τ - G τ = v := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.solution
