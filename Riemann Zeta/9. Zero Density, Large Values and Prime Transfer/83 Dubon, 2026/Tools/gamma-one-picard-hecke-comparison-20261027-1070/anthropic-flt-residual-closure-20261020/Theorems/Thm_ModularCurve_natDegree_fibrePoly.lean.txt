import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
import P2M.Sol.S_ModularCurve_natDegree_fibrePoly

open Polynomial
namespace ModularCurve
theorem natDegree_fibrePoly {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)}
    (hΦ : Φ.Monic) (a : K) : (fibrePoly Φ a).natDegree = Φ.natDegree := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natDegree_fibrePoly.solution
end ModularCurve
