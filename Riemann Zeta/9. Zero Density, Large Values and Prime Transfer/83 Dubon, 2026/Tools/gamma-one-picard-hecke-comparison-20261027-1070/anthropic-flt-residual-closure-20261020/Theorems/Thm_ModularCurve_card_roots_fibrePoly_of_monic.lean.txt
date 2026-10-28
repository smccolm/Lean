import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
import P2M.Sol.S_ModularCurve_card_roots_fibrePoly_of_monic

open Polynomial
namespace ModularCurve
theorem card_roots_fibrePoly_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_card_roots_fibrePoly_of_monic.solution
end ModularCurve
