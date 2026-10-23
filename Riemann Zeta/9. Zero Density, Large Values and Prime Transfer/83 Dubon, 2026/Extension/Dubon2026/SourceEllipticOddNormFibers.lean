import Dubon2026.SourceEllipticOddNormIdentity

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
theorem spec_MM_eq_spec_PP_at (a₂ a₄ a₆ x₀ c : K) (τp τm : ι → K)
    (hx : ∀ q ∈ S, x₀ ≠ x q)
    (hsum : ∀ q ∈ S, τp q + τm q = 2 * x q + t q / (x₀ - x q) + u q / (x₀ - x q) ^ 2)
    (hprod : ∀ q ∈ S, τp q * τm q
      = ((x₀ * x q - a₄) ^ 2 - 4 * a₆ * (x₀ + x q + a₂)) / (x₀ - x q) ^ 2)
    (hnorm : (X - C x₀) * ∏ q ∈ S, ((X - C (τp q)) * (X - C (τm q)))
      = AP S x t u - C c * hP S x ^ 2)
    (hc : c * (hP S x).eval x₀ ^ 2 = (AP S x t u).eval x₀) :
    spec x₀ (MM S x t u a₂ a₄ a₆) = spec x₀ (PP S x t u) := by
  rw [spec_MM, spec_PP]
  have e1 : ∀ q ∈ S, C ((x₀ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval x₀) * X
      + C ((PqP x a₂ a₄ a₆ q).eval x₀) = C ((x₀ - x q) ^ 2) * ((X - C (τp q)) * (X - C (τm q))) := by
    intro q hq
    rw [eval_SqP, eval_PqP, chord_factor (x₀) (x q) (t q) (u q) a₂ a₄ a₆ (τp q) (τm q) (hx q hq)
      (hsum q hq) (hprod q hq), mul_assoc]
  rw [prod_congr rfl e1, prod_mul_distrib, ← map_prod,
    show ∏ q ∈ S, (x₀ - x q) ^ 2 = (hP S x).eval x₀ ^ 2 by rw [hP_eval, prod_pow],
    mul_left_comm, hnorm, ← hc, map_mul]
  ring

theorem fiber {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K) (a₂ a₄ a₆ : K)
    (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u) (e : K) (ξ : ι → K) (he : ∀ q ∈ S, e ≠ x q)
    (hfac : ∀ q ∈ S, C ((e - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e) = C ((e - x q) ^ 2) * (X - C (ξ q)) ^ 2) :
    AP S x t u - C (Xv S x t u e) * hP S x ^ 2 = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 := by
  have hh := hP_eval_ne_zero S x e he
  have key := fiber_of_MM_eq_PP S x t u a₂ a₄ a₆ hMP e ξ hfac hh
  rwa [AP_eval S x t u e he, mul_div_cancel_left₀ _ (pow_ne_zero 2 hh)] at key


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
