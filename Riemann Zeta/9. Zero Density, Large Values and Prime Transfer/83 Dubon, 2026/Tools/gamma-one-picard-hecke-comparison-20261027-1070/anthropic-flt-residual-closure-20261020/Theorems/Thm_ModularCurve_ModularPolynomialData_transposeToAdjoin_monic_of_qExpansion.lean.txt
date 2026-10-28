import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(dedekindPsi N : ℤ)) = 1) (h0le : ∀ m : ℕ, dedekindPsi N < m → (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0) (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi N ≤ m → (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) : ((swapBivar data.Φ).map evalAtJGen).Monic ∧ ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.solution
