import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAut_of_modularPolynomialData {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.solution
