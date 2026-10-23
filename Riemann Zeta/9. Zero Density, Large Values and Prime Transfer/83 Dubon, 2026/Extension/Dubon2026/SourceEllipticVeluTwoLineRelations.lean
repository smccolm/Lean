import Dubon2026.SourceEllipticVeluTwoNonsingular

/-! Cubic root relations used to prove the degree-two Velu secant and tangent
identities. This is a direct dependency of the actual quotient homomorphism,
then the cyclic-quotient root interpretation, elliptic inertia census and
good reduction required by DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
These small polynomial identities replace the expanded certificates in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the two negAddY cleared identities.
No additivity or cubic-factorization conclusion is assumed. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve

theorem shifted_equation_at_two_torsion {R : Type*} [CommRing R]
    {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (y - y₀) ^ 2 + W.a₁ * (x - x₀) * (y - y₀) =
      (x - x₀) ^ 3 + (3 * x₀ + W.a₂) * (x - x₀) ^ 2 + veluGx W x₀ y₀ * (x - x₀) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  simp only [veluGx]
  linear_combination hP - hQ - (y - y₀) * hord

theorem line_y_identity {R : Type*} [CommRing R] {x₁ x₂ x₃ m b a B : R}
    (hB : B = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + (2 * m + a) * b)
    (hprod : x₁ * x₂ * x₃ = b ^ 2) :
    x₂ * x₃ * (x₂ - x₃) * (m * x₁ + b)
      - x₁ * ((a * x₂ + (m * x₂ + b)) * x₃ ^ 2 -
        (a * x₃ + (m * x₃ + b)) * x₂ ^ 2)
      + B * (x₃ * (m * x₂ + b) - x₂ * (m * x₃ + b)) = 0 := by
  calc
    _ = (x₂ - x₃) * (a + 2 * m) * (x₁ * x₂ * x₃ - b ^ 2) := by rw [hB]; ring
    _ = 0 := by rw [hprod, sub_self, mul_zero]

theorem secant_pair_product {F : Type*} [Field F] {x₁ x₂ x₃ m b a A B : F}
    (hx : x₁ ≠ x₂) (hsum : x₃ = m ^ 2 + a * m - A - x₁ - x₂)
    (h₁ : (m * x₁ + b) ^ 2 + a * x₁ * (m * x₁ + b) = x₁ ^ 3 + A * x₁ ^ 2 + B * x₁)
    (h₂ : (m * x₂ + b) ^ 2 + a * x₂ * (m * x₂ + b) = x₂ ^ 3 + A * x₂ ^ 2 + B * x₂) :
    B = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + (2 * m + a) * b ∧
      x₁ * x₂ * x₃ = b ^ 2 := by
  have hp : B = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ + (2 * m + a) * b := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hx)
    rw [hsum]
    linear_combination -h₁ + h₂
  refine ⟨hp, ?_⟩
  rw [hsum] at hp ⊢
  linear_combination -h₁ - x₁ * hp

theorem tangent_pair_product {R : Type*} [CommRing R] {x x₃ m b a A B : R}
    (hsum : x₃ = m ^ 2 + a * m - A - 2 * x)
    (hP : (m * x + b) ^ 2 + a * x * (m * x + b) = x ^ 3 + A * x ^ 2 + B * x)
    (hD : m * (2 * (m * x + b) + a * x) =
      3 * x ^ 2 + 2 * A * x + B - a * (m * x + b)) :
    B = x * x + x * x₃ + x * x₃ + (2 * m + a) * b ∧ x * x * x₃ = b ^ 2 := by
  have hp : B = x * x + x * x₃ + x * x₃ + (2 * m + a) * b := by
    rw [hsum]
    linear_combination -hD
  refine ⟨hp, ?_⟩
  rw [hsum] at hp ⊢
  linear_combination -hP - x * hp

end Dubon2026.SourceEllipticVelu
