import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk

open ModularCurve

theorem ModularCurve.exists_coeffMap_diffQExpBar_eq_qExpansion (N : ℕ) [NeZero N]
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ ι₀.range) :
    ∃ ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExpBar N ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion.solution
