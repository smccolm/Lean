import Mathlib
import Definitions.Def_CuspForm_EigenformCoefficientRing
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

open scoped CongruenceSubgroup
theorem CuspForm.IsNormalizedEigenform.primeCoeffsIntegral_of_neZero {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform) : g.PrimeCoeffsIntegral := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero.solution
