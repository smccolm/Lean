import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (hint : ∀ k, IntCoeffs (c k)) (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) : ∃ data : ModularPolynomialData ℓ, ∀ k, evalAtJ (data.Φ.coeff k) = c k := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.solution
