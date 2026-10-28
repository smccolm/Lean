import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot

theorem ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    (P : Polynomial (LaurentSeries K)) (hP : P.Monic) (hdeg : P.natDegree = (ModularCurve.primCosetReps N).card)
    (hroot : ∀ t ∈ ModularCurve.primCosetReps N, P.IsRoot (ModularCurve.cosetConj ζ J t)) :
    P = ModularCurve.cosetTwoVarPoly ζ N J := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot.solution
