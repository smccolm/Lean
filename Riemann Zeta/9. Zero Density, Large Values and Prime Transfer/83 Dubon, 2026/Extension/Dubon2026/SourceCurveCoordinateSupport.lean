import Dubon2026.SourceCurvePlaceCenters
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! DUB-17/18 -> regular differential dimension -> principal divisors ->
finite support. On the actual integral-closure chart of the coordinate X,
positive orders have finite support by pinned Dedekind prime factorization.
This selects the needed finite-support argument without ramification fibers.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial

theorem polynomial_mem_of_coordinate_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra K[X] F] [IsScalarTower K K[X] F]
    (v : Place K F) (hX : algebraMap K[X] F X ∈ v.toValuationSubring)
    (p : K[X]) : algebraMap K[X] F p ∈ v.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      refine mul_mem ?_ (pow_mem hX n)
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] F]
      exact v.algebraMap_mem' a

theorem integralClosure_mem_of_base_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {R : Type*} [CommRing R] [Algebra R F] (v : Place K F)
    (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)
    (c : integralClosure R F) : (c : F) ∈ v.toValuationSubring := by
  letI : Algebra R v.toValuationSubring :=
    ((algebraMap R F).codRestrict v.toValuationSubring.toSubring hR).toAlgebra
  letI : IsScalarTower R v.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hi : IsIntegral v.toValuationSubring (c : F) := c.2.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hy ▸ y.2

theorem finite_places_positive_X
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] :
    {v : Place K F | 0 < v.ord (algebraMap (RatFunc K) F RatFunc.X)}.Finite := by
  letI : Algebra K[X] F := ((algebraMap (RatFunc K) F).comp
    (algebraMap K[X] (RatFunc K))).toAlgebra
  letI : IsScalarTower K[X] (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F a = algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) (C a))
    rw [← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K),
      ← IsScalarTower.algebraMap_apply K (RatFunc K) F]
  let R := integralClosure K[X] F
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain K[X] (RatFunc K) F
  haveI : IsFractionRing R F := integralClosure.isFractionRing_of_finite_extension (RatFunc K) F
  let r : R := algebraMap K[X] R X
  have hr : r ≠ 0 := by
    intro h
    have h0 := congrArg (algebraMap R F) h
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) = 0 at h0
    rw [RatFunc.algebraMap_X, map_eq_zero] at h0
    exact RatFunc.X_ne_zero h0
  have he : algebraMap R F r = algebraMap (RatFunc K) F RatFunc.X := by
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) = _
    rw [RatFunc.algebraMap_X]
  refine (Place.finite_setOf_forall_mem_and_ord_pos (K := K) (F := F) hr).subset ?_
  intro v hv
  refine ⟨fun c => integralClosure_mem_of_base_mem v ?_ c, ?_⟩
  · apply polynomial_mem_of_coordinate_mem v
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
    rw [RatFunc.algebraMap_X]
    exact v.mem_of_ord_nonneg hv.le
  · rwa [he]

end
end Dubon2026.SourceCurve
