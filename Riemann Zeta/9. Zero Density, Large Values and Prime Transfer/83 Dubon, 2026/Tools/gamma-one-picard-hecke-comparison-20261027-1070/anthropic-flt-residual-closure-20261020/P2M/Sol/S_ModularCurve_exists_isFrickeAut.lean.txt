import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import P2M.Util
namespace P2MW.S_ModularCurve_exists_isFrickeAut
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm ℓ
  exact ModularCurve.exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

end
