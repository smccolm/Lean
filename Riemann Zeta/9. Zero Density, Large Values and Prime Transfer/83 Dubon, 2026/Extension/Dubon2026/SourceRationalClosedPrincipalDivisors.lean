import Dubon2026.SourceRationalPolynomialPrincipalDegree

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
rational-function base of Galois descent. Numerator and denominator
factorization prove degree zero for every rational function over closed
constants, in arbitrary characteristic. No principal-divisor interface is
assumed in this construction. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped Polynomial

theorem degree_rationalPrincipalDivisor (K : Type*) [Field K] [IsAlgClosed K]
    (f : RatFunc K) : Divisor.degree (rationalPrincipalDivisor K f) = 0 := by
  by_cases hf : f = 0
  · subst f
    have h := rationalPrincipalDivisor_const K 0
    rw [map_zero] at h
    rw [h, map_zero]
  have hn : algebraMap K[X] (RatFunc K) f.num ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hf)
  have hd : algebraMap K[X] (RatFunc K) f.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr f.denom_ne_zero
  conv in rationalPrincipalDivisor K f => rw [← RatFunc.num_div_denom f, div_eq_mul_inv]
  rw [rationalPrincipalDivisor_mul K hn (inv_ne_zero hd), map_add,
    rationalPrincipalDivisor_inv, map_neg,
    degree_rationalPrincipalDivisor_polynomial, degree_rationalPrincipalDivisor_polynomial,
    neg_zero, add_zero]

theorem hasPrincipalDivisors_rational_closed (K : Type*) [Field K] [IsAlgClosed K] :
    HasPrincipalDivisors K (RatFunc K) := by
  refine ⟨fun f _ => ⟨rationalPrincipalDivisor K f, ?_, degree_rationalPrincipalDivisor K f⟩⟩
  exact rationalPrincipalDivisor_apply K f

end
end Dubon2026.SourceCurve
