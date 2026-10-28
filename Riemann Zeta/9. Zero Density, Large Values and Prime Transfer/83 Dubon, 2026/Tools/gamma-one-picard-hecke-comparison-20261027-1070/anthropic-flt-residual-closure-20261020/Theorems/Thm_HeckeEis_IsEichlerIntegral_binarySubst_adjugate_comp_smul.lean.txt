import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hF : HeckeEis.IsEichlerIntegral n f F)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] β)
      (fun τ => ((HeckeEis.binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => HeckeEis.binarySubst_mem ℂ M.adjugate h)) (F (β • τ))) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul.solution
