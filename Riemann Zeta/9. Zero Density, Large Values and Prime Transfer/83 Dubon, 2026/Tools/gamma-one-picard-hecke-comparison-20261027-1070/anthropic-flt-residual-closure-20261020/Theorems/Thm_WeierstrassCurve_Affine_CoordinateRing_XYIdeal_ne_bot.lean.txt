import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) : XYIdeal W x y ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot.solution
