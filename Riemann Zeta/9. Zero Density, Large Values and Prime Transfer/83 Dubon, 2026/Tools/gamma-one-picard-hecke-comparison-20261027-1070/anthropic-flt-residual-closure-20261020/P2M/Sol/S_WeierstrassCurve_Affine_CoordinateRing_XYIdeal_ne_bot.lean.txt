import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

theorem solution {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) : XYIdeal W x y ≠ ⊥ := fun h0 =>
  XClass_ne_zero (W' := W) x <| by
    have : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (by simp)
    rwa [h0, Ideal.mem_bot] at this
