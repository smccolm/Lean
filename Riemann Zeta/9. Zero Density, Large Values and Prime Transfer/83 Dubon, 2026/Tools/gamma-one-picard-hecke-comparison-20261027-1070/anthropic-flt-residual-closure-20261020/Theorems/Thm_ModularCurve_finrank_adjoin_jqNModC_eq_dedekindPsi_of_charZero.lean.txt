import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero {K : Type*} [Field K] [CharZero K] (d : ℕ) [NeZero d] : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero.solution
