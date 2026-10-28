import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal
import Definitions.Def_EllipticCurve_FunctionFieldPullback

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal {K : Type*} [Field K] {W : Affine K} {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal.solution
#p2m_type_eq_warn P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal
