import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {c : ℂ}
    (hc : ∀ τ : UpperHalfPlane,
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = c) :
    g = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const.solution
