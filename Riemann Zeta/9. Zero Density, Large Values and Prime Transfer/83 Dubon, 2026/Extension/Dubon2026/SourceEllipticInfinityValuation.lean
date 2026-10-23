import Dubon2026.SourceEllipticNormUltrametric
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-! The actual infinity valuation, constructed from the native field norm.
Adapted from TauCeti InfinityPlace/Basic.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba, with its AINTLIB provenance.
Only the valuation and actual generic-coordinate values are constructed here.
They serve the explicit odd quotient coefficient comparison on DUB-17/18. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate RatFunc Classical

namespace Dubon2026.SourceEllipticFunctionField

attribute [local instance] faithfulSMul_polynomial finiteDimensional_functionField
  finite_polynomial_coordinateRing faithful_polynomial_coordinateRing

variable {F : Type*} [Field F] (W : Affine F)

/-- The native norm followed by rational infinity valuation satisfies the addition inequality. -/
theorem infinityValuation_add_le_max (x y : W.FunctionField) :
    RatFunc.inftyValuation F (Algebra.norm (RatFunc F) (x + y)) ≤
      max (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) x))
        (RatFunc.inftyValuation F (Algebra.norm (RatFunc F) y)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · simp [hxy]
  have hN {f : W.FunctionField} (hf : f ≠ 0) : Algebra.norm (RatFunc F) f ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := RatFunc F)).mpr hf
  simp only [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F (hN hx),
    RatFunc.inftyValuation_of_nonzero F (hN hy), RatFunc.inftyValuation_of_nonzero F (hN hxy)]
  exact le_max_iff.2 ((le_max_iff.1 (intDegree_norm_add_le W hx hy hxy)).imp
    WithZero.exp_le_exp.2 WithZero.exp_le_exp.2)

/-- The actual elliptic infinity valuation is the native norm followed by rational infinity. -/
noncomputable def infinityValuation : Valuation W.FunctionField (WithZero (Multiplicative ℤ)) where
  toFun f := RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f)
  map_zero' := by rw [Algebra.norm_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' := infinityValuation_add_le_max W

/-- Evaluation of the actual infinity valuation uses the actual native field norm. -/
theorem infinityValuation_apply (f : W.FunctionField) :
    infinityValuation W f = RatFunc.inftyValuation F (Algebra.norm (RatFunc F) f) := rfl

/-- The actual generic x-coordinate has a double pole at infinity. -/
theorem infinityValuation_genericX : infinityValuation W (genericX W) = WithZero.exp 2 := by
  rw [genericX_eq_algebraMap, infinityValuation_apply, norm_polynomial_coordinate,
    map_pow, RatFunc.algebraMap_X, RatFunc.inftyValuation.X, ← WithZero.exp_nsmul]
  norm_num

/-- The polynomial norm of the actual generic y-coordinate has degree three. -/
theorem natDegree_norm_coordinateY :
    (Algebra.norm F[X] (CoordinateRing.mk W Y)).natDegree = 3 := by
  have hY : CoordinateRing.mk W Y = (0 : F[X]) • 1 + (1 : F[X]) • CoordinateRing.mk W Y := by simp
  rw [hY, CoordinateRing.norm_smul_basis]
  compute_degree
  all_goals norm_num

/-- The actual generic y-coordinate has a triple pole at infinity. -/
theorem infinityValuation_genericY : infinityValuation W (genericY W) = WithZero.exp 3 := by
  rw [genericY_def, infinityValuation_apply, RatFunc.inftyValuation_apply,
    Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing),
    RatFunc.inftyValuation.polynomial F (ne_zero_of_natDegree_gt (show
      0 < (Algebra.norm F[X] (CoordinateRing.mk W Y)).natDegree by
      rw [natDegree_norm_coordinateY]; norm_num)), natDegree_norm_coordinateY]
  norm_num

/-- Restriction to the actual rational coordinate field squares its infinity valuation. -/
theorem infinityValuation_ratFunc (r : RatFunc F) :
    infinityValuation W (algebraMap (RatFunc F) W.FunctionField r) =
      RatFunc.inftyValuation F r ^ 2 := by
  rw [infinityValuation_apply, Algebra.norm_algebraMap, finrank_functionField, map_pow]

/-- The actual infinity valuation is trivial on the original base field. -/
theorem infinityValuation_trivial : (infinityValuation W).IsTrivialOn F where
  eq_one c hc := by
    rw [IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField,
      infinityValuation_ratFunc, RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C F hc, one_pow]

end Dubon2026.SourceEllipticFunctionField
