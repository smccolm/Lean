import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.solution
