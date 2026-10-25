import Dubon2026.SourceRationalDivisorEvaluation
import Dubon2026.SourceRationalInfinityEvaluation

/-! DUB-17/18 -> original Weil reciprocity -> finite norm transfer using
the second function as coordinate. Only reciprocity with X is needed on
the rational curve. Equal degrees cancel the signs in the pinned root-product
identity; actual endpoint residues give the other side. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical BigOperators
variable (K : Type*) [Field K] [IsAlgClosed K]

theorem principalDivisor_X :
    rationalExtensionPrincipalDivisor K (RatFunc K) RatFunc.X =
      Finsupp.single (pointPlace K 0) 1 - Finsupp.single (infinityPlace K) 1 := by
  have hr : rootDivisor K (X : K[X]) = Finsupp.single (pointPlace K 0) 1 := by
    simp [rootDivisor, ← count_roots]
  simpa only [RatFunc.algebraMap_X, hr, natDegree_X, Nat.cast_one] using
    principalDivisor_polynomial K (X_ne_zero (R := K))

theorem placeEval_point_div_polynomial (a : K) {p q : K[X]} (hq : q ≠ 0) (hqa : q.eval a ≠ 0) :
    placeEval K (pointPlace K a)
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) = p.eval a / q.eval a := by
  have he := (pointPlace K a).rationalEval_div_of_ord_eq_zero
    (rational_extension_place_residue_bijective K (RatFunc K) (pointPlace K a))
    (Place.algebraMap_mem_ofHeightOneSpectrum (pointPrime K a) p)
    (RatFunc.algebraMap_ne_zero hq) ((pointPlace_ord_polynomial_eq_zero_iff K a hq).mpr hqa)
  change placeEval K (pointPlace K a) _ = placeEval K (pointPlace K a) _ /
    placeEval K (pointPlace K a) _ at he
  simpa only [placeEval_polynomial] using he

theorem root_products_ratio {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    p.roots.prod / q.roots.prod = (p.eval 0 / q.eval 0) / (p.leadingCoeff / q.leadingCoeff) := by
  rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero,
    (IsAlgClosed.splits p).coeff_zero_eq_leadingCoeff_mul_prod_roots,
    (IsAlgClosed.splits q).coeff_zero_eq_leadingCoeff_mul_prod_roots, hdeg]
  have hs : (-1 : K) ^ q.natDegree ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hlp := leadingCoeff_ne_zero.mpr hp
  have hlq := leadingCoeff_ne_zero.mpr hq
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

theorem coordinate_reciprocity_polynomial_quotient {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hp0 : p.eval 0 ≠ 0) (hq0 : q.eval 0 ≠ 0) (hdeg : p.natDegree = q.natDegree) :
    divisorEval K (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)
      (rationalExtensionPrincipalDivisor K (RatFunc K) RatFunc.X) =
    divisorEval K RatFunc.X (rationalExtensionPrincipalDivisor K (RatFunc K)
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)) := by
  let f := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have hpoint : placeEval K (pointPlace K 0) f ≠ 0 := by
    rw [placeEval_point_div_polynomial K 0 hq hq0]
    exact div_ne_zero hp0 hq0
  have hinf : placeEval K (infinityPlace K) f ≠ 0 := by
    rw [placeEval_infinity_div_polynomial K hp hq hdeg]
    exact div_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  have heval : ∀ v ∈ (Finsupp.single (pointPlace K 0) (1 : ℤ)).support ∪
      (Finsupp.single (infinityPlace K) (1 : ℤ)).support, placeEval K v f ≠ 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
      simpa only [he] using hpoint
    · have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hv)
      simpa only [he] using hinf
  rw [principalDivisor_X, principalDivisor_div_polynomial K hp hq hdeg,
    divisorEval_sub K _ _ _ heval, divisorEval_single, divisorEval_single, zpow_one, zpow_one,
    placeEval_point_div_polynomial K 0 hq hq0, placeEval_infinity_div_polynomial K hp hq hdeg]
  have hr : ∀ v ∈ (rootDivisor K p).support ∪ (rootDivisor K q).support,
      placeEval K v RatFunc.X ≠ 0 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact placeEval_X_ne_zero_on_rootDivisor K hp hp0 v hv
    · exact placeEval_X_ne_zero_on_rootDivisor K hq hq0 v hv
  rw [divisorEval_sub K _ _ _ hr, divisorEval_X_rootDivisor, divisorEval_X_rootDivisor]
  exact (root_products_ratio K hp hq hdeg).symm

end
end Dubon2026.SourceCurve.RationalFunction
