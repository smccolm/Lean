import Dubon2026.SourceOriginalRationalPrincipalDivisors
import Dubon2026.SourceRationalCoordinateWeilReciprocity

/-! DUB-17/18 -> original Weil pairing -> original reciprocity.
Transfer the proved coordinate identity through the actual finite norm.
Disjoint original principal divisors discharge every fiber regularity and
norm endpoint condition; no reciprocity or norm compatibility is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] (N : ℕ) [NeZero N]

theorem original_weil_reciprocity_coordinate
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L) (f : modularFunctionFieldOver N L) (hf : f ≠ 0)
    (hdisj : ∀ w : Place L (modularFunctionFieldOver N L), w.ord f ≠ 0 → w.ord (φ RatFunc.X) = 0) :
    originalDivisorEval N L f (originalPrincipalDivisor N L (φ RatFunc.X)) =
      originalDivisorEval N L (φ RatFunc.X) (originalPrincipalDivisor N L f) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  have hzero (v : Place L (RatFunc L)) (hv : v.ord RatFunc.X ≠ 0)
      (w : Place L (modularFunctionFieldOver N L))
      (hw : w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v) : w.ord f = 0 :=
    original_ord_zero_above_coordinate_support L N φ f hdisj v hv w hw
  have h0 : (RationalFunction.pointPlace L 0).ord (RatFunc.X : RatFunc L) = 1 := by
    simpa using RationalFunction.pointPlace_ord_parameter L 0
  have hn0 := original_norm_ord_zero_of_fiber L N φ f hf _
    (hzero (RationalFunction.pointPlace L 0) (by rw [h0]; exact one_ne_zero))
  have hni := original_norm_ord_zero_of_fiber L N φ f hf _
    (hzero (RationalFunction.infinityPlace L) (by
      rw [RationalFunction.infinityPlace_ord_X]; norm_num))
  calc
    _ = RationalFunction.divisorEval L (Algebra.norm (RatFunc L) f)
        (rationalExtensionPrincipalDivisor L (RatFunc L) RatFunc.X) := by
      rw [← originalPrincipalDivisor_ratfunc_pullback L N φ RatFunc.X]
      apply originalDivisorEval_ratfunc_finitePullback L N φ
      intro v hv w hw
      exact (hzero v (Finsupp.mem_support_iff.mp hv) w hw).ge
    _ = RationalFunction.divisorEval L RatFunc.X
        (rationalExtensionPrincipalDivisor L (RatFunc L) (Algebra.norm (RatFunc L) f)) :=
      RationalFunction.coordinate_weil_reciprocity L (Algebra.norm_ne_zero_iff.mpr hf) hn0 hni
    _ = _ := by
      rw [← originalPrincipalDivisor_ratfunc_pushforward L N φ f hf]
      apply rationalDivisorEval_original_geometricPushforward L N φ _ _ RatFunc.X_ne_zero
      intro w hw
      exact hdisj w (Finsupp.mem_support_iff.mp hw)

end
end Dubon2026.SourceFunctionField
