import Dubon2026.SourceRationalPlaceEvaluation
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate case.
The finite root divisor records actual point orders, with multiplicity;
the actual principal divisor adds the infinity term of negative degree. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical BigOperators
variable (K : Type*) [Field K] [IsAlgClosed K]

/-- The finite zeros of a polynomial with their actual root multiplicities. -/
def rootDivisor (q : K[X]) : Divisor K (RatFunc K) :=
  ∑ a ∈ q.roots.toFinset, Finsupp.single (pointPlace K a) (q.rootMultiplicity a : ℤ)

theorem rootDivisor_point (q : K[X]) (a : K) :
    rootDivisor K q (pointPlace K a) = q.rootMultiplicity a := by
  simp only [rootDivisor, Finsupp.finsetSum_apply, Finsupp.single_apply,
    (pointPlace_injective K).eq_iff, Finset.sum_ite_eq']
  split_ifs with ha
  · rfl
  · rw [← count_roots, Multiset.count_eq_zero_of_notMem (by simpa using ha)]
    rfl

omit [IsAlgClosed K] in
theorem rootDivisor_infinity (q : K[X]) : rootDivisor K q (infinityPlace K) = 0 := by
  have hn (a : K) : pointPlace K a ≠ infinityPlace K :=
    (infinityPlace_ne_prime K (pointPrime K a)).symm
  simp only [rootDivisor, Finsupp.finsetSum_apply, Finsupp.single_apply, hn, if_false,
    Finset.sum_const_zero]

theorem principalDivisor_polynomial {q : K[X]} (hq : q ≠ 0) :
    rationalExtensionPrincipalDivisor K (RatFunc K) (algebraMap K[X] (RatFunc K) q) =
      rootDivisor K q - Finsupp.single (infinityPlace K) (q.natDegree : ℤ) := by
  ext v
  rcases eq_point_or_infinity K v with ⟨a, rfl⟩ | rfl
  · have hn : pointPlace K a ≠ infinityPlace K :=
      (infinityPlace_ne_prime K (pointPrime K a)).symm
    rw [rationalExtensionPrincipalDivisor_apply, pointPlace_ord_polynomial K a hq,
      Finsupp.sub_apply, rootDivisor_point, Finsupp.single_eq_of_ne hn, sub_zero]
  · rw [rationalExtensionPrincipalDivisor_apply,
      infinityPlace_ord K (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial,
      Finsupp.sub_apply, rootDivisor_infinity, Finsupp.single_eq_same, zero_sub]

theorem principalDivisor_div_polynomial {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    rationalExtensionPrincipalDivisor K (RatFunc K)
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      rootDivisor K p - rootDivisor K q := by
  have he : rationalExtensionPrincipalDivisor K (RatFunc K)
      (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      rationalExtensionPrincipalDivisor K (RatFunc K) (algebraMap K[X] (RatFunc K) p) -
      rationalExtensionPrincipalDivisor K (RatFunc K) (algebraMap K[X] (RatFunc K) q) := by
    ext v
    change v.ord (_ / _) = v.ord (algebraMap K[X] (RatFunc K) p) -
      v.ord (algebraMap K[X] (RatFunc K) q)
    rw [div_eq_mul_inv,
      v.ord_mul (RatFunc.algebraMap_ne_zero hp) (inv_ne_zero (RatFunc.algebraMap_ne_zero hq)),
      v.ord_inv, sub_eq_add_neg]
  rw [he, principalDivisor_polynomial K hp, principalDivisor_polynomial K hq, hdeg]
  abel

end
end Dubon2026.SourceCurve.RationalFunction
