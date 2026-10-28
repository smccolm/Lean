import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_evalSymm_of_splits

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.evalSymm_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (data : ModularPolynomialData ℓ) (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ)) (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic) (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ) : EvalSymm data.Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_evalSymm_of_splits.solution
