import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeAlphaBar
    {N : ℕ} [NeZero N] (ℓ : ℕ) [NeZero ℓ] (D : ModularCurve.ComplexPlaceDictionary N)
    (D' : ModularCurve.ComplexPlaceDictionary (N * ℓ))
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong (ModularCurve.heckeAlphaBar ℂ N ℓ) hα = D.pt τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar.solution
