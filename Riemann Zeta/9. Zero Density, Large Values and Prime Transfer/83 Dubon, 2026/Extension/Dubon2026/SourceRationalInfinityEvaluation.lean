import Dubon2026.SourceRationalPlaceEvaluation
import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate case.
The actual infinity residue of an equal-degree quotient is the quotient
of leading coefficients. Leading-term cancellation is adapted from
S_AlgebraicCurve_RationalFunctionField_weilReciprocity, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical
variable (K : Type*) [Field K] [IsAlgClosed K]

theorem placeEval_infinity_eq {f : RatFunc K} {c : K}
    (h : f - algebraMap K (RatFunc K) c = 0 ∨
      (f - algebraMap K (RatFunc K) c).intDegree < 0) :
    placeEval K (infinityPlace K) f = c := by
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h, placeEval_algebraMap]
  · apply Place.rationalEval_eq_of_ord_sub_pos
    have hn : f - algebraMap K (RatFunc K) c ≠ 0 := by
      intro hz
      rw [hz, RatFunc.intDegree_zero] at h
      exact (lt_irrefl 0) h
    rw [infinityPlace_ord K hn]
    omega

theorem placeEval_infinity_div_polynomial {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    placeEval K (infinityPlace K)
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      p.leadingCoeff / q.leadingCoeff := by
  let c := p.leadingCoeff / q.leadingCoeff
  have hc0 : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  apply placeEval_infinity_eq K
  have he : algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q -
      algebraMap K (RatFunc K) c =
      algebraMap K[X] (RatFunc K) (p - C c * q) / algebraMap K[X] (RatFunc K) q := by
    rw [map_sub, map_mul, sub_div, mul_div_assoc,
      div_self (RatFunc.algebraMap_ne_zero hq), mul_one,
      IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  change _ = 0 ∨ _ < 0
  rw [he]
  rcases eq_or_ne (p - C c * q) 0 with hz | hn
  · exact Or.inl (by rw [hz, map_zero, zero_div])
  right
  rw [RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hn) (RatFunc.algebraMap_ne_zero hq),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (C c * q).degree = q.degree := by
    rw [degree_mul, degree_C hc0, zero_add]
  have heq : p.degree = (C c * q).degree := by
    rw [hCdeg, degree_eq_natDegree hp, degree_eq_natDegree hq, hdeg]
  have hlc : p.leadingCoeff = (C c * q).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C, div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hq)]
  have hlt := degree_sub_lt heq hp hlc
  rw [heq, hCdeg] at hlt
  exact_mod_cast natDegree_lt_natDegree hn hlt

end
end Dubon2026.SourceCurve.RationalFunction
