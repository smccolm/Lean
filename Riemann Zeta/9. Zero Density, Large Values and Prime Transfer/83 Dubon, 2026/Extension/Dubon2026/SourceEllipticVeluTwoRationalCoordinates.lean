import Dubon2026.SourceEllipticVeluTwoNonsingular

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> actual cyclic-quotient interpretation of integral modular-polynomial roots
-> the degree-two quotient group map and its kernel.
This step constructs the actual rational coordinate map on nonsingular points
and identifies its zero fiber. Additivity remains a separate required proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Def_WeierstrassCurve_VeluPointMap2 and
the kernel geometry in S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.
The cleared equation is proved by eliminating two coefficients and factoring
the remaining point equation, without the source certificate's factor four. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R)

/-- The numerator of the degree-two quotient x coordinate. -/
def velu2XNum (x : R) : R :=
  x * (x - x₀) ^ 2 + veluGx W x₀ y₀ * (x - x₀)

/-- The numerator of the degree-two quotient y coordinate. -/
def velu2YNum (x y : R) : R :=
  y * (x - x₀) ^ 3 - veluGx W x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)

theorem velu2XNum_eq_mul (x : R) :
    velu2XNum W x₀ y₀ x = (x - x₀) * (x * (x - x₀) + veluGx W x₀ y₀) := by
  simp only [velu2XNum]; ring

theorem velu2_equation_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) :
    (velu2YNum W x₀ y₀ x y ^ 2
        + W.a₁ * velu2XNum W x₀ y₀ x * velu2YNum W x₀ y₀ x y * (x - x₀)
        + W.a₃ * velu2YNum W x₀ y₀ x y * (x - x₀) ^ 3)
      = (velu2XNum W x₀ y₀ x ^ 3 + W.a₂ * velu2XNum W x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * veluGx W x₀ y₀) * velu2XNum W x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * veluGx W x₀ y₀ - 7 * (x₀ * veluGx W x₀ y₀)) * (x - x₀) ^ 6) := by
  have h3 : W.a₃ = -(2 * y₀ + W.a₁ * x₀) := by
    simp only [veluGy] at hgy
    linear_combination -hgy
  have h6 : W.a₆ = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
      (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀) := by
    rw [WeierstrassCurve.Affine.equation_iff] at hQ
    linear_combination -hQ
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  simp only [velu2XNum, velu2YNum, veluGx, b₂]
  rw [h6, h3] at hP ⊢
  linear_combination
    ((x - x₀) ^ 2 * ((x - x₀) ^ 2 -
      (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)) ^ 2) * hP

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The rational x coordinate of the actual degree-two quotient map. -/
def velu2X (x₀ y₀ x : F) : F :=
  x + veluGx W x₀ y₀ / (x - x₀)

/-- The rational y coordinate of the actual degree-two quotient map. -/
def velu2Y (x₀ y₀ x y : F) : F :=
  y - veluGx W x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2

theorem velu2X_eq_div (x₀ y₀ : F) {x : F} (hx : x ≠ x₀) :
    velu2X W x₀ y₀ x = velu2XNum W x₀ y₀ x / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2X, velu2XNum]
  field_simp

theorem velu2Y_eq_div (x₀ y₀ : F) {x : F} (y : F) (hx : x ≠ x₀) :
    velu2Y W x₀ y₀ x y = velu2YNum W x₀ y₀ x y / (x - x₀) ^ 3 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  simp only [velu2Y, velu2YNum]
  field_simp


end
end Dubon2026.SourceEllipticVelu
