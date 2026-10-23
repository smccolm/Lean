import Dubon2026.SourceCurveFiniteChartFunctionSupport
import Dubon2026.SourceCurveCoordinateSupport

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisor finite support. For the fixed finite separating coordinate, the
actual integral closure chart contains every place where the coordinate
is integral. Clearing denominators bounds the support there. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial

theorem finite_function_support_where_coordinate_integral
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    (f : F) : {v : Place K F | algebraMap (RatFunc K) F RatFunc.X ∈ v.toValuationSubring ∧
      v.ord f ≠ 0}.Finite := by
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
  refine (finite_chart_function_support (R := R) f).subset ?_
  rintro v ⟨hv, hf⟩
  refine ⟨fun c => integralClosure_mem_of_base_mem v ?_ c, hf⟩
  apply polynomial_mem_of_coordinate_mem v
  change algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) X) ∈ v.toValuationSubring
  rwa [RatFunc.algebraMap_X]

end
end Dubon2026.SourceCurve
