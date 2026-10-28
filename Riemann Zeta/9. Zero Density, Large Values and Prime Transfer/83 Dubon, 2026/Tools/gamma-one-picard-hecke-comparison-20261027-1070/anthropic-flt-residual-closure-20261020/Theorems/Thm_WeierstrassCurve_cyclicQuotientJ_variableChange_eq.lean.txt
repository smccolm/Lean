import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.cyclicQuotientJ_variableChange_eq
    {L : Type u} [Field L] [DecidableEq L] (C : VariableChange L) (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) (H' : AddSubgroup (C • E).toAffine.Point)
    (hH' : ∀ P, P ∈ H' ↔ WeierstrassCurve.Affine.Point.vcFun C E P ∈ H)
    (N : ℕ) (hN : (N : L) ≠ 0) :
    (C • E).cyclicQuotientJ H' N = E.cyclicQuotientJ H N := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.solution
