import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.solution
