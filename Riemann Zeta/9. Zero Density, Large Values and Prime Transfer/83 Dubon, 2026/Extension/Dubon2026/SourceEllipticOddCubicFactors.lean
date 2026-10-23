import Dubon2026.SourceEllipticOddQuotientPolynomials

/-! Finite polynomial factorization for the explicit odd cyclic
quotient. Translated roots determine the cleared numerator; the three
two-torsion fibers then identify the quotient cubic and its discriminant.
This is the necessary algebraic step before actual-curve assembly in the
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain through quotient products,
cyclic-subgroup roots, inertia census, reverse genus and good reduction.
Adapted from the selected odd-order quotient discriminant proof,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native monic polynomial root
comparison is reused. The actual-curve hypotheses are not asserted here. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K]
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)
theorem fiber_to_diamond (ξ₁ ξ₂ ξ₃ : ι → K) (e₁ e₂ e₃ X₁ X₂ X₃ b₂ b₄ b₆ : K)
    (hF₁ : AP S x t u - C X₁ * hP S x ^ 2 = (X - C e₁) * (∏ q ∈ S, (X - C (ξ₁ q))) ^ 2)
    (hF₂ : AP S x t u - C X₂ * hP S x ^ 2 = (X - C e₂) * (∏ q ∈ S, (X - C (ξ₂ q))) ^ 2)
    (hF₃ : AP S x t u - C X₃ * hP S x ^ 2 = (X - C e₃) * (∏ q ∈ S, (X - C (ξ₃ q))) ^ 2)
    (hf : fP b₂ b₄ b₆ = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃))) :
    C 4 * AP S x t u ^ 3 + C (-4 * (X₁ + X₂ + X₃)) * AP S x t u ^ 2 * hP S x ^ 2
        + C (4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃)) * AP S x t u * hP S x ^ 4
        + C (-4 * (X₁ * X₂ * X₃)) * hP S x ^ 6
      = fP b₂ b₄ b₆ * ∏ q ∈ S, ((X - C (ξ₁ q)) * (X - C (ξ₂ q)) * (X - C (ξ₃ q))) ^ 2 := by
  have e : C 4 * AP S x t u ^ 3 + C (-4 * (X₁ + X₂ + X₃)) * AP S x t u ^ 2 * hP S x ^ 2
        + C (4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃)) * AP S x t u * hP S x ^ 4
        + C (-4 * (X₁ * X₂ * X₃)) * hP S x ^ 6
      = C 4 * ((AP S x t u - C X₁ * hP S x ^ 2) * (AP S x t u - C X₂ * hP S x ^ 2)
          * (AP S x t u - C X₃ * hP S x ^ 2)) := by
    simp only [map_mul, map_neg, map_add]
    ring
  rw [e, hF₁, hF₂, hF₃, hf, prod_pow, prod_mul_distrib, prod_mul_distrib]
  ring

theorem cubic_eq_of_coeffs (X₁ X₂ X₃ b₂' b₄' b₆' : K) (h₂ : -4 * (X₁ + X₂ + X₃) = b₂')
    (h₁ : 4 * (X₁ * X₂ + X₁ * X₃ + X₂ * X₃) = 2 * b₄') (h₀ : -4 * (X₁ * X₂ * X₃) = b₆') :
    C 4 * ((X - C X₁) * (X - C X₂) * (X - C X₃))
      = C 4 * X ^ 3 + C b₂' * X ^ 2 + C (2 * b₄') * X + C b₆' := by
  rw [← h₂, ← h₁, ← h₀]
  simp only [map_mul, map_neg, map_add]
  ring

omit [DecidableEq ι] in

theorem roots_cubic (X₁ X₂ X₃ : K) (h4 : (4 : K) ≠ 0) :
    (C 4 * ((X - C X₁) * (X - C X₂) * (X - C X₃))).roots = {X₁, X₂, X₃} := by
  rw [roots_C_mul _ h4, roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)), roots_mul (mul_ne_zero (X_sub_C_ne_zero _)
    (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
