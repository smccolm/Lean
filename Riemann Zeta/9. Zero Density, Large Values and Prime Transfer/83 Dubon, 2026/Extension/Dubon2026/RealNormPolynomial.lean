import Dubon2026.AnalyticZeroPolynomial

/-! # A real polynomial detecting the real zeros of a complex polynomial -/

namespace Dubon2026

open Polynomial Complex
open scoped ComplexConjugate

noncomputable section

/-- Take the real part of each coefficient, without claiming it is a ring homomorphism. -/
def realPartPolynomial (P : ℂ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.mapRange Complex.re Complex.zero_re)

theorem realPartPolynomial_coeff (P : ℂ[X]) (k : ℕ) :
    (realPartPolynomial P).coeff k = (P.coeff k).re := rfl

/-- The real coefficient polynomial obtained from the product with the coefficient conjugate. -/
def realNormPolynomial (P : ℂ[X]) : ℝ[X] :=
  realPartPolynomial (P * P.map (starRingEnd ℂ))

theorem conjugate_product_fixed (P : ℂ[X]) :
    (P * P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P * P.map (starRingEnd ℂ) := by
  rw [Polynomial.map_mul, Polynomial.map_map]
  have he : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext z; simp
  rw [he, Polynomial.map_id, mul_comm]

theorem map_realNormPolynomial (P : ℂ[X]) :
    (realNormPolynomial P).map (algebraMap ℝ ℂ) = P * P.map (starRingEnd ℂ) := by
  ext k
  have hh := congrArg (fun Q : ℂ[X] => Q.coeff k) (conjugate_product_fixed P)
  simp only [Polynomial.coeff_map] at hh
  have him : ((P * P.map (starRingEnd ℂ)).coeff k).im = 0 :=
    Complex.conj_eq_iff_im.mp hh
  simp only [Polynomial.coeff_map, realNormPolynomial, realPartPolynomial_coeff]
  apply Complex.ext
  · rfl
  · exact him.symm

theorem realNormPolynomial_ne_zero {P : ℂ[X]} (hP : P ≠ 0) : realNormPolynomial P ≠ 0 := by
  intro h
  have hh := map_realNormPolynomial P
  rw [h, Polynomial.map_zero] at hh
  exact mul_ne_zero hP ((Polynomial.map_ne_zero_iff (starRingEnd ℂ).injective).mpr hP) hh.symm

theorem realNormPolynomial_eval (P : ℂ[X]) (t : ℝ) :
    (↑((realNormPolynomial P).eval t) : ℂ) = P.eval (t : ℂ) * conj (P.eval (t : ℂ)) := by
  have he := congrArg (fun Q : ℂ[X] => Q.eval (t : ℂ)) (map_realNormPolynomial P)
  have hc : (P.map (starRingEnd ℂ)).eval (t : ℂ) = conj (P.eval (t : ℂ)) := by
    simpa using (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (t : ℂ))
  change ((realNormPolynomial P).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) t) = _ at he
  dsimp only at he
  rw [Polynomial.eval_map_apply, Polynomial.eval_mul, hc] at he
  exact he

theorem realNormPolynomial_eval_eq_zero_iff (P : ℂ[X]) (t : ℝ) :
    (realNormPolynomial P).eval t = 0 ↔ P.eval (t : ℂ) = 0 := by
  rw [← Complex.ofReal_eq_zero, realNormPolynomial_eval, mul_eq_zero]
  simp

theorem realNormPolynomial_rootMultiplicity {P : ℂ[X]} (hP : P ≠ 0) (t : ℝ) :
    (realNormPolynomial P).rootMultiplicity t = 2 * P.rootMultiplicity (t : ℂ) := by
  rw [Polynomial.eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective t, map_realNormPolynomial]
  have hn := mul_ne_zero hP ((Polynomial.map_ne_zero_iff (starRingEnd ℂ).injective).mpr hP)
  rw [Polynomial.rootMultiplicity_mul hn]
  have hc := Polynomial.eq_rootMultiplicity_map (p := P) (starRingEnd ℂ).injective (t : ℂ)
  change P.rootMultiplicity (t : ℂ) =
    (P.map (starRingEnd ℂ)).rootMultiplicity (conj (t : ℂ)) at hc
  rw [Complex.conj_ofReal] at hc
  change P.rootMultiplicity (t : ℂ) + (P.map (starRingEnd ℂ)).rootMultiplicity (t : ℂ) = _
  rw [← hc, two_mul]

end

end Dubon2026
