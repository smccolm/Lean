import Dubon2026.SourceIntegralPrimeConjugateProduct

/-! Identify the prime-two conjugate product of the actual integral minimal
polynomial over the rational Laurent-series field. This uses coefficient
embedding injectivity and the already proved cyclotomic product. It is the
input to the explicit cubic coefficient comparison required for the actual
cyclic-quotient interpretation of the modular-polynomial roots, DUB-17/18. -/
namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
noncomputable section
open Polynomial

theorem modularPolynomial_two_rational_product :
    (modularPolynomial 2).map ((qExpand ℚ 2).comp evalAtJ) =
      PhiGen.phiProd 2 (PhiGen.conj 2 (-1 : ℚˣ)) := by
  let K := CyclotomicField 2 ℚ
  have hζ : IsPrimitiveRoot ((-1 : Kˣ) : K) 2 := by
    simpa using IsPrimitiveRoot.neg_one (R := K) 0 (by norm_num)
  have h := modularPolynomial_prime_conjugate_product 2 (-1) hζ
  apply Polynomial.map_injective (coeffEmb K) (coeffEmb K).injective
  rw [Polynomial.map_map]
  change (modularPolynomial 2).map
    (((coeffEmb K).comp (qExpand ℚ 2)).comp evalAtJ) = _
  rw [h]
  have he := coeffMap_prime_product (Algebra.ofId ℚ K) 2 (-1 : ℚˣ)
  have hu : Units.map (Algebra.ofId ℚ K).toRingHom.toMonoidHom (-1 : ℚˣ) = -1 := by
    apply Units.ext
    simp
  simpa only [hu] using he.symm

theorem modularPolynomial_two_cubic_product :
    (modularPolynomial 2).map ((qExpand ℚ 2).comp evalAtJ) =
      (X - C (qExpand ℚ 4 jq)) *
        ((X - C jq) * (X - C (qTwist (-1 : ℚˣ) jq))) := by
  rw [modularPolynomial_two_rational_product, PhiGen.phiProd,
    Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hc (f : LaurentSeries ℚ) : coeffEmb ℚ f = f := by
    ext m
    rfl
  simp only [PhiGen.conj_zero, PhiGen.conj_succ, Fin.val_zero, Fin.val_succ,
    pow_zero, zero_add, pow_one, qTwist_one_apply, Fin.prod_univ_zero, mul_one, hc]

theorem modularPolynomial_two_coefficient_identities :
    qExpand ℚ 2 (evalAtJ ((modularPolynomial 2).coeff 2)) =
      -(qExpand ℚ 4 jq + jq + qTwist (-1 : ℚˣ) jq) ∧
    qExpand ℚ 2 (evalAtJ ((modularPolynomial 2).coeff 1)) =
      qExpand ℚ 4 jq * jq + qExpand ℚ 4 jq * qTwist (-1 : ℚˣ) jq +
        jq * qTwist (-1 : ℚˣ) jq ∧
    qExpand ℚ 2 (evalAtJ ((modularPolynomial 2).coeff 0)) =
      -(qExpand ℚ 4 jq * jq * qTwist (-1 : ℚˣ) jq) := by
  have h := modularPolynomial_two_cubic_product
  have hexpand (a b c : LaurentSeries ℚ) :
      (X - C a) * ((X - C b) * (X - C c)) =
        X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + a * c + b * c) * X -
          C (a * b * c) := by
    simp only [map_add, map_mul]
    ring
  rw [hexpand] at h
  have hc (k : ℕ) := congrArg (fun P : Polynomial (LaurentSeries ℚ) => P.coeff k) h
  refine ⟨?_, ?_, ?_⟩
  · have h₂ := hc 2
    norm_num only [coeff_map, RingHom.comp_apply, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h₂
    simpa only [ite_true, ite_false, zero_sub, add_zero, sub_zero] using h₂
  · have h₁ := hc 1
    norm_num only [coeff_map, RingHom.comp_apply, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h₁
    simpa only [ite_true, ite_false, sub_zero, zero_add] using h₁
  · have h₀ := hc 0
    norm_num only [coeff_map, RingHom.comp_apply, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h₀
    simpa only [ite_true, ite_false, sub_zero, zero_add, zero_sub] using h₀

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
