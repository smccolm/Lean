import Dubon2026.SourceCurveCoordinateDegree
import Dubon2026.SourceCurveCoordinateSupport

/-! DUB-17/18 -> principal-divisor degree zero. For an actual finite
separable rational-function extension, the integral-closure chart discharges
all containment, finite-module and normalization inputs to the positive-order
degree formula. No ramification or divisor formula is assumed.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial

theorem sum_positive_orders_X_eq_finrank
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] :
    (∑ᶠ v : {v : Place K F // 0 < v.ord (algebraMap (RatFunc K) F RatFunc.X)},
      v.1.ord (algebraMap (RatFunc K) F RatFunc.X) *
        (Module.finrank K v.1.ResidueField : ℤ)) = (Module.finrank (RatFunc K) F : ℤ) := by
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
  haveI : Module.Finite K[X] R := IsIntegralClosure.finite K[X] (RatFunc K) F R
  haveI : Module.IsTorsionFree K[X] F :=
    .trans_faithfulSMul K[X] (RatFunc K) F
  haveI : Module.IsTorsionFree K[X] R := IsIntegralClosure.isTorsionFree K[X] F
  have he : algebraMap R F (algebraMap K[X] R X) = algebraMap (RatFunc K) F RatFunc.X := by
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) = _
    rw [RatFunc.algebraMap_X]
  have hx : algebraMap K[X] R X ≠ 0 := by
    intro h
    have h0 := congrArg (algebraMap R F) h
    rw [he, map_zero, map_eq_zero] at h0
    exact RatFunc.X_ne_zero h0
  have hchart : ∀ v : Place K F,
      0 < v.ord (algebraMap R F (algebraMap K[X] R X)) →
        ∀ r : R, algebraMap R F r ∈ v.toValuationSubring := by
    intro v hv c
    apply integralClosure_mem_of_base_mem v _ c
    apply polynomial_mem_of_coordinate_mem v
    change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
    rw [RatFunc.algebraMap_X]
    rw [he] at hv
    exact v.mem_of_ord_nonneg hv.le
  simpa only [he] using sum_positive_orders_eq_finrank_of_chart hx hchart

end
end Dubon2026.SourceCurve
