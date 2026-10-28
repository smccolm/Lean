import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.PhiGenDescends.intCoeffs {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.solution
