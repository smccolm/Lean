import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

theorem solution {K : Type*} [Field K] {W : Affine K} {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField K) (quotientXYIdealEquiv (W' := W) h).toMulEquiv
