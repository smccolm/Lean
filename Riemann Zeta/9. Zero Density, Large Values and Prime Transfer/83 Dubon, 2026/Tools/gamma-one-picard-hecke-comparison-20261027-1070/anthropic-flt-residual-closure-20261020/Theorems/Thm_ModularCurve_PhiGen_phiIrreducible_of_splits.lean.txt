import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_phiIrreducible_of_splits

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.phiIrreducible_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (data : ModularPolynomialData ℓ) (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_phiIrreducible_of_splits.solution
