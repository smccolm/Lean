import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeRoof_adjoin_range_union_eq_top
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.heckeRoof_adjoin_range_union_eq_top (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ') (hgenQ : FunctionFieldGeneration M) (data' : ModularPolynomialData ℓ') : Algebra.adjoin L (Set.range (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) ∪ Set.range (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeRoof_adjoin_range_union_eq_top.solution
