import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_press

open ModularCurve
theorem ModularCurve.StarBank.press {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_press.solution
