import Dubon2026.SourceRationalCoordinateReciprocity

/-! DUB-17/18 -> original Weil reciprocity -> finite norm transfer using
the second function as rational coordinate. Coprime numerator and denominator
discharge the presentation conditions, leaving exactly nonzero functions
whose divisors avoid the zero and pole of X. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical
variable (K : Type*) [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem num_denom_eval_ne_zero_of_point_ord_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (a : K) (ho : (pointPlace K a).ord f = 0) : f.num.eval a ≠ 0 ∧ f.denom.eval a ≠ 0 := by
  have hp := RatFunc.num_ne_zero hf
  have hq := f.denom_ne_zero
  have he : (pointPlace K a).ord (algebraMap K[X] (RatFunc K) f.num) =
      (pointPlace K a).ord (algebraMap K[X] (RatFunc K) f.denom) := by
    rw [← f.num_div_denom, div_eq_mul_inv,
      Place.ord_mul _ (RatFunc.algebraMap_ne_zero hp) (inv_ne_zero (RatFunc.algebraMap_ne_zero hq)),
      Place.ord_inv, ← sub_eq_add_neg, sub_eq_zero] at ho
    exact ho
  have hc := (f.isCoprime_num_denom.map (Polynomial.evalRingHom a)).ne_zero_or_ne_zero
  change f.num.eval a ≠ 0 ∨ f.denom.eval a ≠ 0 at hc
  rcases hc with h | h
  · exact ⟨h, (pointPlace_ord_polynomial_eq_zero_iff K a hq).mp
      (he.symm.trans ((pointPlace_ord_polynomial_eq_zero_iff K a hp).mpr h))⟩
  · exact ⟨(pointPlace_ord_polynomial_eq_zero_iff K a hp).mp
      (he.trans ((pointPlace_ord_polynomial_eq_zero_iff K a hq).mpr h)), h⟩

theorem coordinate_weil_reciprocity {f : RatFunc K} (hf : f ≠ 0)
    (h0 : (pointPlace K 0).ord f = 0) (hinf : (infinityPlace K).ord f = 0) :
    divisorEval K f (rationalExtensionPrincipalDivisor K (RatFunc K) RatFunc.X) =
      divisorEval K RatFunc.X (rationalExtensionPrincipalDivisor K (RatFunc K) f) := by
  obtain ⟨hp0, hq0⟩ := num_denom_eval_ne_zero_of_point_ord_eq_zero K hf 0 h0
  have hd : f.num.natDegree = f.denom.natDegree := by
    rw [infinityPlace_ord K hf, neg_eq_zero, RatFunc.intDegree, sub_eq_zero] at hinf
    exact_mod_cast hinf
  have h := coordinate_reciprocity_polynomial_quotient K
    (RatFunc.num_ne_zero hf) f.denom_ne_zero hp0 hq0 hd
  rwa [f.num_div_denom] at h

end
end Dubon2026.SourceCurve.RationalFunction
