import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine
theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j.solution
