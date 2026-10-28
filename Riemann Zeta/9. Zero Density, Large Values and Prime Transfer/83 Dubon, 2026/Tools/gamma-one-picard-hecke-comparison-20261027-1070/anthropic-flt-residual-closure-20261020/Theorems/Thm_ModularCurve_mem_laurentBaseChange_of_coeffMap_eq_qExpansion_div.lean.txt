import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

open UpperHalfPlane

theorem ModularCurve.mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div (N : ℕ) [NeZero N]
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (σ : AlgebraicClosure ℚ →+* ℂ) (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : ModularCurve.coeffMap σ x =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    x ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldFull N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div.solution
