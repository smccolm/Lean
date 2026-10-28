import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import P2M.Util
namespace P2MW.S_ModularCurve_finiteAlong_heckeBetaBar_of_prime
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] : AlgebraicCurve.FiniteAlong L (ModularCurve.heckeBetaBar L N ℓ) := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact finiteAlong_heckeBetaBar_of_modularPolynomialData L data hsymm Fact.out N
