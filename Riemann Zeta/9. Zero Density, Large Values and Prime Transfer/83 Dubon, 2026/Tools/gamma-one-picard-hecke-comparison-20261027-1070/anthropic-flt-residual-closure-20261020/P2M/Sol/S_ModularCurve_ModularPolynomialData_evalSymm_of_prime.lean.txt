import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_of_prime
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import P2M.Util
namespace P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_prime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  rw [ModularCurve.ModularPolynomialData.eq_of_prime p data d]
  exact hd
