import Dubon2026.SourceEllipticOddNormPolynomials

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
theorem MM_eq_PP_of_infinite (a₂ a₄ a₆ : K)
    (hinf : Set.Infinite {x₀ : K | spec x₀ (MM S x t u a₂ a₄ a₆) = spec x₀ (PP S x t u)}) :
    MM S x t u a₂ a₄ a₆ = PP S x t u := by
  rw [← sub_eq_zero]
  refine Polynomial.ext fun i => ?_
  rw [coeff_zero]
  refine eq_zero_of_infinite_isRoot _ (hinf.mono fun x₀ hx₀ => ?_)
  simp only [Set.mem_setOf_eq] at hx₀ ⊢
  have e := congrArg (fun p : K[X] => p.coeff i) hx₀
  simp only [spec, coe_mapRingHom, coeff_map, coe_evalRingHom] at e
  rw [IsRoot.def, coeff_sub, eval_sub, e, sub_self]

theorem fiber_of_MM_eq_PP (a₂ a₄ a₆ : K) (hMP : MM S x t u a₂ a₄ a₆ = PP S x t u) (e : K)
    (ξ : ι → K) (hfac : ∀ q ∈ S, C ((e - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval e) * X
        + C ((PqP x a₂ a₄ a₆ q).eval e) = C ((e - x q) ^ 2) * (X - C (ξ q)) ^ 2)
    (he : (hP S x).eval e ≠ 0) :
    AP S x t u - C ((AP S x t u).eval e / (hP S x).eval e ^ 2) * hP S x ^ 2
      = (X - C e) * (∏ q ∈ S, (X - C (ξ q))) ^ 2 := by
  have key := congrArg (spec e) hMP
  rw [spec_MM, spec_PP, prod_congr rfl hfac, prod_mul_distrib, prod_pow, ← map_prod,
    show ∏ q ∈ S, (e - x q) ^ 2 = (hP S x).eval e ^ 2 by
      rw [hP, eval_prod, ← prod_pow]; simp [eval_sub, eval_X, eval_C]] at key
  have he2 : C ((hP S x).eval e ^ 2) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact pow_ne_zero 2 he
  refine mul_left_cancel₀ he2 ?_
  rw [mul_sub, ← mul_assoc, ← map_mul, show (hP S x).eval e ^ 2 * ((AP S x t u).eval e
      / (hP S x).eval e ^ 2) = (AP S x t u).eval e by field_simp, ← key]
  ring

omit [DecidableEq ι] in

theorem chord_factor (x₁ x₂ tq uq a₂ a₄ a₆ τp τm : K) (hx : x₁ ≠ x₂)
    (hsum : τp + τm = 2 * x₂ + tq / (x₁ - x₂) + uq / (x₁ - x₂) ^ 2)
    (hprod : τp * τm = ((x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂)) / (x₁ - x₂) ^ 2) :
    C ((x₁ - x₂) ^ 2) * X ^ 2 - C (2 * x₂ * (x₁ - x₂) ^ 2 + tq * (x₁ - x₂) + uq) * X
        + C ((x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂))
      = C ((x₁ - x₂) ^ 2) * (X - C τp) * (X - C τm) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hs : 2 * x₂ * (x₁ - x₂) ^ 2 + tq * (x₁ - x₂) + uq = (x₁ - x₂) ^ 2 * (τp + τm) := by
    rw [hsum]; field_simp
  have hp : (x₁ * x₂ - a₄) ^ 2 - 4 * a₆ * (x₁ + x₂ + a₂) = (x₁ - x₂) ^ 2 * (τp * τm) := by
    rw [hprod]; field_simp
  rw [hs, hp]
  simp only [map_mul, map_add, map_pow, map_sub]
  ring

omit [DecidableEq ι] in

theorem eval_SqP (x t u : ι → K) (q : ι) (x₀ : K) :
    (SqP x t u q).eval x₀ = 2 * x q * (x₀ - x q) ^ 2 + t q * (x₀ - x q) + u q := by
  simp [SqP]

omit [DecidableEq ι] in
theorem eval_PqP (x : ι → K) (a₂ a₄ a₆ : K) (q : ι) (x₀ : K) :
    (PqP x a₂ a₄ a₆ q).eval x₀ = (x₀ * x q - a₄) ^ 2 - 4 * a₆ * (x₀ + x q + a₂) := by
  simp only [PqP, eval_sub, eval_pow, eval_mul, eval_add, eval_X, eval_C]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
