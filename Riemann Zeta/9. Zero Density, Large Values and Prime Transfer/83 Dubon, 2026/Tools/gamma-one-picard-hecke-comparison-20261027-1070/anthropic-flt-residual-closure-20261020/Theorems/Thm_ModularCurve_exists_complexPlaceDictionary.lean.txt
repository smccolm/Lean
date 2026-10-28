import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_complexPlaceDictionary
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.exists_complexPlaceDictionary (N : ℕ) [NeZero N] :
    Nonempty (ModularCurve.ComplexPlaceDictionary N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_complexPlaceDictionary.solution
