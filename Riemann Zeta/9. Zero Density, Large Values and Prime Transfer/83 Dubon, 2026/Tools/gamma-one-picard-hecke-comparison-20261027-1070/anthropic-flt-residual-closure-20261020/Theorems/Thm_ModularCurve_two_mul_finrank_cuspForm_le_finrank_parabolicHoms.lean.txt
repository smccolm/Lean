import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false
theorem ModularCurve.two_mul_finrank_cuspForm_le_finrank_parabolicHoms (N : ℕ) [NeZero N] :
    2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)
      ≤ Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_two_mul_finrank_cuspForm_le_finrank_parabolicHoms.solution
