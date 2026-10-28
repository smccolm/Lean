import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
attribute [-simp] WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty

open WeierstrassCurve

universe u v w in

theorem WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
    {R : Type u} [CommRing R] (E : WeierstrassCurve R)
    {A : Type v} {B : Type w} [Field A] [DecidableEq A] [IsAlgClosed A] [Field B] [DecidableEq B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (H : AddSubgroup (E.baseChange A).toAffine.Point) (N : ℕ) :
    (E.baseChange B).cyclicQuotientJ (H.map (WeierstrassCurve.Affine.Point.map f)) N =
      f ((E.baseChange A).cyclicQuotientJ H N) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.solution
