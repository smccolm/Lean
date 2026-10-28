import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import P2M.Util
namespace P2MW.S_ModularCurve_isIntegral_jqNModC_all
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  isIntegral_jqNModC_all_of_modularPolynomialFamily K modularPolynomialFamily N

#print axioms solution
