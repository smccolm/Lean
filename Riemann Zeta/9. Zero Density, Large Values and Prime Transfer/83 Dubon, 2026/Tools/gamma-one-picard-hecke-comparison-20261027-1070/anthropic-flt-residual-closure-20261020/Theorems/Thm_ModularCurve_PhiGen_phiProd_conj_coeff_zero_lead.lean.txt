import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ((phiProd ℓ (conj ℓ ζ)).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.solution
