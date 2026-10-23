import Dubon2026.SourceEllipticOddPolynomialReflection

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
section Defs
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (x t u : ι → K)

/-- Product of the linear factors at the kernel x-coordinates. -/
noncomputable def hP : K[X] := ∏ q ∈ S, (X - C (x q))

/-- Cleared numerator of the odd Velu x-coordinate sum. -/
noncomputable def AP : K[X] :=
  X * hP S x ^ 2 +
    ∑ q ∈ S, (C (t q) * (X - C (x q)) + C (u q)) * ∏ q' ∈ S.erase q, (X - C (x q')) ^ 2

end Defs

/-- Cubic square of the second division polynomial. -/
noncomputable def fP (b₂ b₄ b₆ : K) : K[X] :=
  C 4 * X ^ 3 + C b₂ * X ^ 2 + C (2 * b₄) * X + C b₆

/-- Quartic numerator of the doubling x-coordinate. -/
noncomputable def φP (b₄ b₆ b₈ : K) : K[X] :=
  X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈

/-- Polynomial ring truncated after its cubic coefficient. -/
abbrev R4 (K : Type*) [Field K] := K[X] ⧸ Ideal.span {(X : K[X]) ^ 4}

/-- Canonical map to the polynomial ring modulo X^4. -/
noncomputable abbrev π : K[X] →+* R4 K := Ideal.Quotient.mk _

theorem π_X_pow_four : (π (X : K[X])) ^ 4 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem eq_of_π_eq {p q : K[X]} (hp : p.natDegree ≤ 3) (hq : q.natDegree ≤ 3)
    (h : π p = π q) : p = q := by
  have hmem : (X : K[X]) ^ 4 ∣ p - q := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq.mp h
  have hzero : p - q = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hmem ?_
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt (natDegree_sub_le_of_le' hp hq) (by norm_num)
  exact sub_eq_zero.mp hzero

theorem prod_eq_of_map_eq {ι β : Type*} {M : Type*} [CommMonoid M] (S : Finset ι)
    {d x : ι → β} (hperm : S.val.map d = S.val.map x) (g : β → M) :
    ∏ q ∈ S, g (d q) = ∏ q ∈ S, g (x q) := by
  have h1 : ∏ q ∈ S, g (d q) = ((S.val.map d).map g).prod := by
    rw [Multiset.map_map]; rfl
  have h2 : ∏ q ∈ S, g (x q) = ((S.val.map x).map g).prod := by
    rw [Multiset.map_map]; rfl
  rw [h1, h2, hperm]

theorem prod_one_add_sq_mul {ι : Type*} {A : Type*} [CommRing A] (S : Finset ι) (ε : A)
    (hε : ε ^ 4 = 0) (y : ι → A) :
    ∏ q ∈ S, (1 + ε ^ 2 * y q) = 1 + ε ^ 2 * ∑ q ∈ S, y q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, ih]
    linear_combination (y a * ∑ q ∈ s, y q) * hε

/-- Nilpotent image of X in the truncated polynomial ring. -/
noncomputable def eps (K : Type*) [Field K] : R4 K := π (X : K[X])

theorem eps_pow_four : (eps K) ^ 4 = 0 := π_X_pow_four

theorem π_X : π (X : K[X]) = eps K := rfl

/-- Scalar map to the truncated polynomial ring. -/
noncomputable def sc {K : Type*} [Field K] : K →+* R4 K := (π : K[X] →+* R4 K).comp C

theorem π_C (a : K) : π (C a) = sc a := rfl


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra
