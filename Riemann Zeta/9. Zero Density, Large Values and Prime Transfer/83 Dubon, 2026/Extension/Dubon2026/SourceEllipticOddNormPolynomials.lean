import Dubon2026.SourceEllipticOddPolynomialDegrees

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
/-- Cleared sum of the two translated x-coordinates. -/
noncomputable def SqP (x t u : ι → K) (q : ι) : K[X] :=
  C (2 * x q) * (X - C (x q)) ^ 2 + C (t q) * (X - C (x q)) + C (u q)

/-- Cleared product of the two translated x-coordinates. -/
noncomputable def PqP (x : ι → K) (a₂ a₄ a₆ : K) (q : ι) : K[X] :=
  (X * C (x q) - C a₄) ^ 2 - C (4 * a₆) * (X + C (x q) + C a₂)

/-- Bivariate product recording the original point and paired translates. -/
noncomputable def MM (a₂ a₄ a₆ : K) : K[X][X] :=
  (X - C X) * ∏ q ∈ S, ((C : K[X] →+* K[X][X]) ((X - C (x q)) ^ 2) * X ^ 2
    - (C : K[X] →+* K[X][X]) (SqP x t u q) * X + (C : K[X] →+* K[X][X]) (PqP x a₂ a₄ a₆ q))

/-- Bivariate cross product of the quotient numerator and denominator. -/
noncomputable def PP : K[X][X] :=
  (C : K[X] →+* K[X][X]) (hP S x ^ 2) * (AP S x t u).map C
    - (C : K[X] →+* K[X][X]) (AP S x t u) * ((hP S x).map C) ^ 2

omit [DecidableEq ι] in
theorem hP_monic : (hP S x).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [DecidableEq ι] in
theorem natDegree_hP : (hP S x).natDegree = S.card := by
  rw [hP, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

theorem natDegree_AP_sum_le :
    (∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2
      : K[X]).natDegree ≤ 2 * S.card - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
  refine (natDegree_mul_le).trans ?_
  have h1 := natDegree_lin_le x t u q
  have h2 := natDegree_Pq_le S x q
  have h3 : (S.erase q).card + 1 = S.card := card_erase_add_one hq
  omega

theorem degree_AP_sum_lt :
    (∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2
      : K[X]).degree < (X * hP S x ^ 2).degree := by
  refine lt_of_le_of_lt (degree_le_of_natDegree_le (natDegree_AP_sum_le S x t u)) ?_
  rw [degree_eq_natDegree (monic_X.mul ((hP_monic S x).pow 2)).ne_zero,
    natDegree_X_mul ((hP_monic S x).pow 2).ne_zero, (hP_monic S x).natDegree_pow, natDegree_hP]
  exact_mod_cast (show 2 * S.card - 1 < 2 * S.card + 1 by omega)

theorem AP_monic : (AP S x t u).Monic := by
  rw [AP]
  exact Monic.add_of_left (monic_X.mul ((hP_monic S x).pow 2)) (degree_AP_sum_lt S x t u)

theorem natDegree_AP : (AP S x t u).natDegree = 2 * S.card + 1 := by
  rw [AP, natDegree_add_eq_left_of_degree_lt (degree_AP_sum_lt S x t u),
    natDegree_X_mul ((hP_monic S x).pow 2).ne_zero, (hP_monic S x).natDegree_pow, natDegree_hP]

/-- Specialization of the coefficient variable in a bivariate polynomial. -/
noncomputable abbrev spec (x₀ : K) : K[X][X] →+* K[X] := mapRingHom (evalRingHom x₀)

omit [DecidableEq ι] in
theorem spec_C (x₀ : K) (p : K[X]) : spec x₀ ((C : K[X] →+* K[X][X]) p) = C (p.eval x₀) := by
  simp [spec]

omit [DecidableEq ι] in
theorem spec_map_C (x₀ : K) (p : K[X]) : spec x₀ (p.map C) = p := by
  rw [spec, coe_mapRingHom, Polynomial.map_map]
  have : (evalRingHom x₀).comp C = RingHom.id K := RingHom.ext fun a => eval_C
  rw [this, Polynomial.map_id]

omit [DecidableEq ι] in
theorem spec_X (x₀ : K) : spec x₀ (X : K[X][X]) = X := by
  simp [spec]

theorem spec_PP (x₀ : K) : spec x₀ (PP S x t u)
    = C ((hP S x).eval x₀ ^ 2) * AP S x t u - C ((AP S x t u).eval x₀) * hP S x ^ 2 := by
  simp only [PP, map_sub, map_mul, map_pow, spec_C, spec_map_C]

omit [DecidableEq ι] in
theorem spec_MM (x₀ a₂ a₄ a₆ : K) : spec x₀ (MM S x t u a₂ a₄ a₆)
    = (X - C x₀) * ∏ q ∈ S, (C ((x₀ - x q) ^ 2) * X ^ 2 - C ((SqP x t u q).eval x₀) * X
        + C ((PqP x a₂ a₄ a₆ q).eval x₀)) := by
  simp only [MM, map_mul, map_sub, map_add, map_prod, map_pow, spec_X, spec_C, eval_X, eval_C]


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
