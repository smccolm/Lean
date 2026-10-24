import Dubon2026.SourceEllipticCubicModel

/-! DUB-17/18 -> reverse genus -> exceptional j=0 census.
The actual cubic coordinate automorphism and the native addition law
discharge its quadratic action identity. Reuse the existing stabilizer
point equivalence and optional-coordinate identities.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the corresponding cubic
variable-change, addition and exceptional fixed-subgroup source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer Polynomial
noncomputable section
variable {L : Type*} [Field L]

theorem cubic_some_add_some
    {k : Type*} [Field k] [DecidableEq k] (B w : k) (hw : w ^ 3 = 1) (hw1 : w ≠ 1) {x y : k}
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular x y)
    (hwx : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w * x) y)
    (hw2x : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular (w ^ 2 * x) y) (hx : x ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some (w * x) y hwx
      = -(WeierstrassCurve.Affine.Point.some (w ^ 2 * x) y hw2x) := by
  have hsum : 1 + w + w ^ 2 = 0 := by
    have h0 : (w - 1) * (1 + w + w ^ 2) = 0 := by linear_combination hw
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hw1
    · exact h1
  have hxne : x ≠ w * x := by
    intro heq
    have h0 : (1 - w) * x = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hw1 (by linear_combination -h1)
    · exact hx h1
  rw [Point.add_of_X_ne hxne, Point.neg_some]
  apply xy_injective
  simp only [xy, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addX]
    linear_combination -x * hsum
  · rw [slope_of_X_ne hxne, sub_self, zero_div]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring

theorem cubic_some_zero_add_self
    {k : Type*} [Field k] [DecidableEq k] (B : k) (h2 : (2 : k) ≠ 0) {y : k} (hy0 : y ≠ 0)
    (h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Nonsingular 0 y) :
    (WeierstrassCurve.Affine.Point.some 0 y h : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k).toAffine.Point)
      + WeierstrassCurve.Affine.Point.some 0 y h
      = -(WeierstrassCurve.Affine.Point.some 0 y h) := by
  have hyne : y ≠ Affine.negY (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve k) 0 y := by
    simp only [Affine.negY]
    intro heq
    have : (2 : k) * y = 0 := by linear_combination heq
    rcases mul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hy0 h'
  rw [Point.add_of_Y_ne hyne, Point.neg_some]
  apply xy_injective
  simp only [xy, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addX, Affine.negY]
    ring
  · rw [slope_of_Y_ne rfl hyne]
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX]
    ring

end
end Dubon2026.SourceEllipticExceptional
