import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
import Definitions.Def_EllipticCurve_FunctionFieldPullback

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] : ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.solution
#p2m_type_eq_warn P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal
