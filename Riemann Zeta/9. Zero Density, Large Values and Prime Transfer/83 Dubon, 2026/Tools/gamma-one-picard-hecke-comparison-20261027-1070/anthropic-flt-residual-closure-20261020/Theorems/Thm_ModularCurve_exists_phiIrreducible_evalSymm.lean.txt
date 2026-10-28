import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_phiIrreducible_evalSymm
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_phiIrreducible_evalSymm.solution
