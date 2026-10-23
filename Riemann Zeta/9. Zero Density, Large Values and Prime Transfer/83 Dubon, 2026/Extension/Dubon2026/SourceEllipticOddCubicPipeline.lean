import Dubon2026.SourceEllipticOddNormFibers
import Dubon2026.SourceEllipticOddCubicFactors
import Dubon2026.SourceEllipticOddPolynomialExpansion

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
theorem pipeline {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (ξ₁ ξ₂ ξ₃ : ι → K) (a₂ a₄ a₆ e₁ e₂ e₃ : K)
    (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u)
    (he₁ : ∀ q ∈ S, e₁ ≠ x q) (he₂ : ∀ q ∈ S, e₂ ≠ x q) (he₃ : ∀ q ∈ S, e₃ ≠ x q)
    (hfac₁ : ∀ q ∈ S, C ((e₁ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₁) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₁) = C ((e₁ - x q) ^ 2) * (X - C (ξ₁ q)) ^ 2)
    (hfac₂ : ∀ q ∈ S, C ((e₂ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₂) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₂) = C ((e₂ - x q) ^ 2) * (X - C (ξ₂ q)) ^ 2)
    (hfac₃ : ∀ q ∈ S, C ((e₃ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e₃) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e₃) = C ((e₃ - x q) ^ 2) * (X - C (ξ₃ q)) ^ 2)
    (hvieta : fP (4 * a₂) (2 * a₄) (4 * a₆) = C 4 * ((X - C e₁) * (X - C e₂) * (X - C e₃)))
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + 4 * a₂ * x q + 2 * a₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + 4 * a₂ * x q ^ 2 + 2 * (2 * a₄) * x q + 4 * a₆)
    (hperm : S.val.map d = S.val.map x)
    (hpack : ∀ q ∈ S, (X - C (ξ₁ q)) * (X - C (ξ₂ q)) * (X - C (ξ₃ q)) * (X - C (x q))
        = φP (2 * a₄) (4 * a₆) (4 * a₂ * a₆ - a₄ ^ 2) - C (d q) * fP (4 * a₂) (2 * a₄) (4 * a₆)) :
    C 4 * ((X - C (Xv S x t u e₁)) * (X - C (Xv S x t u e₂)) * (X - C (Xv S x t u e₃)))
      = C 4 * X ^ 3 + C (4 * a₂) * X ^ 2 + C (2 * (2 * a₄ - 10 * ∑ q ∈ S, t q)) * X
        + C (4 * a₆ - 4 * (4 * a₂) * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q)) := by

  have F := fiber S x t u a₂ a₄ a₆ hMP
  have D := fiber_to_diamond S x t u ξ₁ ξ₂ ξ₃ e₁ e₂ e₃ (Xv S x t u e₁) (Xv S x t u e₂)
    (Xv S x t u e₃) (4 * a₂) (2 * a₄) (4 * a₆) (F e₁ ξ₁ he₁ hfac₁) (F e₂ ξ₂ he₂ hfac₂)
    (F e₃ ξ₃ he₃ hfac₃) hvieta
  obtain ⟨k₂, k₁, k₀⟩ := expansion S x d t u (fun q => (X - C (ξ₁ q)) * (X - C (ξ₂ q))
    * (X - C (ξ₃ q))) (4 * a₂) (2 * a₄) (4 * a₆) (4 * a₂ * a₆ - a₄ ^ 2) _ _ _ ht hu hperm hpack D
  exact cubic_eq_of_coeffs _ _ _ _ _ _ k₂ (by rw [k₁]; ring) k₀


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
