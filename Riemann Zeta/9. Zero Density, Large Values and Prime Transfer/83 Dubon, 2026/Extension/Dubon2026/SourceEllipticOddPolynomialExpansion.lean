import Dubon2026.SourceEllipticOddTruncatedExpansion
import Dubon2026.SourceEllipticOddReflectedIdentity

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
theorem expansion {ι : Type*} [DecidableEq ι] (S : Finset ι) (x d t u : ι → K)
    (m : ι → K[X]) (b₂ b₄ b₆ b₈ c₂ c₁ c₀ : K)
    (ht : ∀ q ∈ S, t q = 6 * x q ^ 2 + b₂ * x q + b₄)
    (hu : ∀ q ∈ S, u q = 4 * x q ^ 3 + b₂ * x q ^ 2 + 2 * b₄ * x q + b₆)
    (hperm : S.val.map d = S.val.map x)
    (hm : ∀ q ∈ S, m q * (X - C (x q)) = φP b₄ b₆ b₈ - C (d q) * fP b₂ b₄ b₆)
    (hdiamond : C 4 * AP S x t u ^ 3 + C c₂ * AP S x t u ^ 2 * hP S x ^ 2
        + C c₁ * AP S x t u * hP S x ^ 4 + C c₀ * hP S x ^ 6
        = fP b₂ b₄ b₆ * ∏ q ∈ S, m q ^ 2) :
    c₂ = b₂ ∧ c₁ = 2 * b₄ - 20 * ∑ q ∈ S, t q
      ∧ c₀ = b₆ - 4 * b₂ * (∑ q ∈ S, t q) - 28 * ∑ q ∈ S, (u q + x q * t q) := by
  exact expansion_core S x d t u b₂ b₄ b₆ b₈ c₂ c₁ c₀ ht hu hperm _ _ _ _
    (reflect_hP S x) (reflect_AP S x t u) (reflect_fP b₂ b₄ b₆) (reflect_m S x d m b₂ b₄ b₆ b₈ hm)
    (reflect_diamond S x d t u m b₂ b₄ b₆ b₈ c₂ c₁ c₀ hm hdiamond)


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
