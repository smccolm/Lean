import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.PhiGenDescends.c_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) {k : ℕ} (hk : ℓ + 1 < k) : c k = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_c_eq_zero.solution
