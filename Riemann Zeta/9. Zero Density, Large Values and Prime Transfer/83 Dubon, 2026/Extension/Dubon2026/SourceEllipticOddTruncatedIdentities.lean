import Dubon2026.SourceEllipticOddQuotientPolynomials

/-! Polynomial coefficient comparison on the odd cyclic quotient
discriminant chain. The exact rational numerator and denominator are reflected
and compared modulo X^4 to recover the quotient cubic coefficients. These
calculations serve odd quotient ellipticity -> prime quotient maps/products
-> cyclic-subgroup root interpretation -> inertia census -> reverse genus
and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial reflection,
degree bounds, quotient rings and finite products are reused. The full
curve discriminant identity is not asserted by these conditional identities. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
section Trunc

variable {A : Type*} [CommRing A] {ε : A}

theorem trunc_unit (hε : ε ^ 4 = 0) (a : A) :
    (1 - a * ε) * (1 + a * ε + a ^ 2 * ε ^ 2 + a ^ 3 * ε ^ 3) = 1 := by
  linear_combination (-a ^ 4) * hε

theorem trunc_pow8 (hε : ε ^ 4 = 0) (a : A) :
    (1 - a * ε) ^ 8 = 1 - 8 * a * ε + 28 * a ^ 2 * ε ^ 2 - 56 * a ^ 3 * ε ^ 3 := by
  linear_combination (70 * a ^ 4 - 56 * a ^ 5 * ε + 28 * a ^ 6 * ε ^ 2
    - 8 * a ^ 7 * ε ^ 3 + a ^ 8 * ε ^ 4) * hε

theorem trunc_perq (hε : ε ^ 4 = 0) (a b₂ b₄ b₆ : A) :
    (1 - 4 * a * ε - (b₄ + b₂ * a) * ε ^ 2 - (2 * b₆ + 2 * b₄ * a) * ε ^ 3) ^ 2
      = (1 - a * ε) ^ 8 * (1 + ε ^ 2 * (-2 * (6 * a ^ 2 + b₂ * a + b₄)
          - 4 * (10 * a ^ 3 + 2 * b₂ * a ^ 2 + 3 * b₄ * a + b₆) * ε)) := by
  rw [trunc_pow8 hε]
  linear_combination (b₄ ^ 2 + 4 * ε * b₄ * b₆ + 4 * ε ^ 2 * b₆ ^ 2
    - 16 * a * b₆ + 2 * a * b₂ * b₄ + 4 * a * ε * b₄ ^ 2
    + 4 * a * ε * b₂ * b₆ + 8 * a * ε ^ 2 * b₄ * b₆ - 24 * a ^ 2 * b₄
    + a ^ 2 * b₂ ^ 2 + 112 * a ^ 2 * ε * b₆ + 4 * a ^ 2 * ε * b₂ * b₄
    + 4 * a ^ 2 * ε ^ 2 * b₄ ^ 2 - 8 * a ^ 3 * b₂ + 224 * a ^ 3 * ε * b₄
    - 224 * a ^ 3 * ε ^ 2 * b₆ + 16 * a ^ 4 + 112 * a ^ 4 * ε * b₂
    - 672 * a ^ 4 * ε ^ 2 * b₄ + 448 * a ^ 5 * ε - 448 * a ^ 5 * ε ^ 2 * b₂
    - 2240 * a ^ 6 * ε ^ 2) * hε

theorem trunc_lhs (hε : ε ^ 4 = 0) (η T W c₂ c₁ c₀ : A) :
    4 * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) ^ 3
      + c₂ * ε * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) ^ 2 * η ^ 2
      + c₁ * ε ^ 2 * (η ^ 2 * (1 + T * ε ^ 2 + W * ε ^ 3)) * η ^ 4 + c₀ * ε ^ 3 * η ^ 6
      = η ^ 6 * (4 + c₂ * ε + (12 * T + c₁) * ε ^ 2
          + (12 * W + 2 * c₂ * T + c₀) * ε ^ 3) := by
  linear_combination (η ^ 6 * (2 * W * c₂ + T * c₁ + 12 * T ^ 2
    + ε * W * c₁ + 24 * ε * T * W + ε * T ^ 2 * c₂ + 12 * ε ^ 2 * W ^ 2
    + 2 * ε ^ 2 * T * W * c₂ + 4 * ε ^ 2 * T ^ 3 + ε ^ 3 * W ^ 2 * c₂
    + 12 * ε ^ 3 * T ^ 2 * W + 12 * ε ^ 4 * T * W ^ 2 + 4 * ε ^ 5 * W ^ 3)) * hε

theorem trunc_alpha_summand (hε : ε ^ 4 = 0) (P a t u : A) :
    (t * (1 - a * ε) + u * ε) * P * ε ^ 2
      = P * (1 - a * ε) ^ 2 * (t * ε ^ 2 + (u + a * t) * ε ^ 3) := by
  linear_combination (P * (2 * a * (u + a * t) - a ^ 2 * t - a ^ 2 * (u + a * t) * ε)) * hε

theorem trunc_phi (hε : ε ^ 4 = 0) (b₂ b₄ b₆ T W : A) :
    (4 + b₂ * ε + 2 * b₄ * ε ^ 2 + b₆ * ε ^ 3) * (1 + ε ^ 2 * (-2 * T - 4 * W * ε))
      = 4 + b₂ * ε + (2 * b₄ - 8 * T) * ε ^ 2 + (b₆ - 2 * b₂ * T - 16 * W) * ε ^ 3 := by
  linear_combination (-4 * b₄ * T - 4 * b₂ * W - 2 * ε * b₆ * T - 8 * ε * b₄ * W
    - 4 * ε ^ 2 * b₆ * W) * hε

theorem trunc_num (hε : ε ^ 4 = 0) (a b₂ b₄ b₆ b₈ : A) :
    (1 * ε ^ 0 - b₄ * ε ^ 2 - 2 * b₆ * ε ^ 3 - b₈ * ε ^ 4)
      - a * (4 * ε ^ 1 + b₂ * ε ^ 2 + 2 * b₄ * ε ^ 3 + b₆ * ε ^ 4)
      = 1 - 4 * a * ε - (b₄ + b₂ * a) * ε ^ 2 - (2 * b₆ + 2 * b₄ * a) * ε ^ 3 := by
  linear_combination (-b₈ - a * b₆) * hε

end Trunc

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
