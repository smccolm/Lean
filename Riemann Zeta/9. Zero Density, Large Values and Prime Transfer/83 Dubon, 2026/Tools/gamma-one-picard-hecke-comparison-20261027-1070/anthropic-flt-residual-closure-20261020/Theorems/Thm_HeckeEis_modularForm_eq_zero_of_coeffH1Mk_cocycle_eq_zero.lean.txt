import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero (N : ℕ) [NeZero N] (n : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (h0 : HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩ = 0) :
    f = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero.solution
