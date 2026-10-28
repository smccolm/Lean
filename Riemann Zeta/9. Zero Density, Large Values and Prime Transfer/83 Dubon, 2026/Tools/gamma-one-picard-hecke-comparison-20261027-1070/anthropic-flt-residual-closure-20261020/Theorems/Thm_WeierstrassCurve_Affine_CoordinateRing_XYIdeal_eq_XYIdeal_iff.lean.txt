import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_XYIdeal_iff {F : Type*} [Field F] {W : Affine F} {x₁ y₁ : F} (h : W.Equation x₁ y₁) (x₂ y₂ : F) : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_eq_XYIdeal_iff.solution
