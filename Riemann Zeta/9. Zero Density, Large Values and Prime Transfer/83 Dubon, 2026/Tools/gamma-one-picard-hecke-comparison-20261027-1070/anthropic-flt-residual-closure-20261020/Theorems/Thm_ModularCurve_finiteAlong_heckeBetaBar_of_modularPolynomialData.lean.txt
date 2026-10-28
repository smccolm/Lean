import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData
attribute [-simp] ModularCurve.jqNModC_one

theorem ModularCurve.finiteAlong_heckeBetaBar_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L] {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hsymm : ModularCurve.EvalSymm data.Φ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : AlgebraicCurve.FiniteAlong L (ModularCurve.heckeBetaBar L N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteAlong_heckeBetaBar_of_modularPolynomialData.solution
