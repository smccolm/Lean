import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_isEichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_isEichlerIntegral (n : ℕ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEichlerIntegral.solution
