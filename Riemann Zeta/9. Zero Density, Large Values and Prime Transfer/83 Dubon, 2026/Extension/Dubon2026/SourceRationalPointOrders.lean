import Dubon2026.SourceRationalPointPlaces

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate
reciprocity. Actual point orders of polynomials are their root multiplicities.
The pinned maximal-root-factorization theorem and the native center criterion
discharge this directly after normalization of X-a. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial IsDedekindDomain
open scoped Classical
variable (K : Type*) [Field K]

theorem pointPlace_ord_polynomial_eq_zero_iff (a : K) {q : K[X]} (hq : q ≠ 0) :
    (pointPlace K a).ord (algebraMap K[X] (RatFunc K) q) = 0 ↔ q.eval a ≠ 0 := by
  have hpos := Place.mem_center_iff_ord_pos
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) (pointPrime K a))
    (Place.algebraMap_mem_ofHeightOneSpectrum (pointPrime K a)) hq
  rw [Place.center_ofHeightOneSpectrum] at hpos
  change q ∈ Ideal.span {X - C a} ↔ 0 < (pointPlace K a).ord
    (algebraMap K[X] (RatFunc K) q) at hpos
  rw [Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot.def] at hpos
  have hn := (pointPlace K a).ord_nonneg_of_mem
    (Place.algebraMap_mem_ofHeightOneSpectrum (pointPrime K a) q)
  rw [ne_eq, hpos]
  omega

theorem pointPlace_ord_polynomial (a : K) {q : K[X]} (hq : q ≠ 0) :
    (pointPlace K a).ord (algebraMap K[X] (RatFunc K) q) = q.rootMultiplicity a := by
  obtain ⟨r, hr, hndvd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq a
  have hr0 : r ≠ 0 := by
    intro hz
    apply hq
    rw [hr, hz, mul_zero]
  have he : r.eval a ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot.def] using hndvd
  have ho := (pointPlace_ord_polynomial_eq_zero_iff K a hr0).mpr he
  conv_lhs => rw [hr, map_mul, map_pow]
  rw [Place.ord_mul, ← zpow_natCast, Place.ord_zpow, pointPlace_ord_parameter, ho]
  · simp
  · exact pow_ne_zero _ (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
  · exact RatFunc.algebraMap_ne_zero hr0

end
end Dubon2026.SourceCurve.RationalFunction
