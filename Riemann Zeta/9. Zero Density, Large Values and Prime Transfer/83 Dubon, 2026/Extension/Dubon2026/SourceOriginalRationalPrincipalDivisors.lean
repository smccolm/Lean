import Dubon2026.SourceOriginalRationalDivisorEvaluation
import Dubon2026.SourceOriginalPrincipalDivisors
import Dubon2026.SourceCurveCorrespondenceRamification

/-! DUB-17/18 -> original Weil reciprocity -> rational norm transfer.
The existing order formulas identify the actual pulled-back and norm
principal divisors. Disjointness gives zero orders on precisely the fibers
needed for applying the norm evaluation and coordinate reciprocity theorems. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] (N : ℕ) [NeZero N]

omit [IsAlgClosed L] in
theorem originalPrincipalDivisor_ratfunc_pullback
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L) (g : RatFunc L) :
    Divisor.finitePullbackAlong φ (original_ratfunc_hom_finite L N φ)
      (rationalExtensionPrincipalDivisor L (RatFunc L) g) = originalPrincipalDivisor N L (φ g) := by
  ext w
  rw [Divisor.finitePullbackAlong_apply, rationalExtensionPrincipalDivisor_apply,
    originalPrincipalDivisor_apply, Place.ord_restrictAlong]

theorem originalPrincipalDivisor_ratfunc_pushforward
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L) (f : modularFunctionFieldOver N L) (hf : f ≠ 0) :
    letI := algebraAlong φ
    Divisor.geometricPushforwardAlong φ (original_ratfunc_hom_finite L N φ)
      (originalPrincipalDivisor N L f) =
        rationalExtensionPrincipalDivisor L (RatFunc L) (Algebra.norm (RatFunc L) f) := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  ext v
  change Divisor.geometricPushforward (RatFunc L) (originalPrincipalDivisor N L f) v = _
  rw [Divisor.geometricPushforward_apply, rationalExtensionPrincipalDivisor_apply,
    v.ord_norm_eq_sum_fiber (rational_extension_place_residue_bijective L (RatFunc L) v)
      (original_place_residue_algebraMap_bijective N L) hf]
  rfl

omit [IsAlgClosed L] in
theorem original_ord_zero_above_coordinate_support
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L) (f : modularFunctionFieldOver N L)
    (hdisj : ∀ w : Place L (modularFunctionFieldOver N L), w.ord f ≠ 0 → w.ord (φ RatFunc.X) = 0)
    (v : Place L (RatFunc L)) (hv : v.ord RatFunc.X ≠ 0)
    (w : Place L (modularFunctionFieldOver N L))
    (hw : w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v) : w.ord f = 0 := by
  by_contra hf
  have hg := hdisj w hf
  rw [Place.ord_restrictAlong φ (original_ratfunc_hom_finite L N φ) w, hw] at hg
  exact (mul_ne_zero hv (ne_of_gt (Place.ramificationAlong_pos φ
    (original_ratfunc_hom_finite L N φ) w))) hg

theorem original_norm_ord_zero_of_fiber
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L)
    (f : modularFunctionFieldOver N L) (hf : f ≠ 0) (v : Place L (RatFunc L))
    (hord : ∀ w : Place L (modularFunctionFieldOver N L),
      w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v → w.ord f = 0) :
    letI := algebraAlong φ
    v.ord (Algebra.norm (RatFunc L) f) = 0 := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  rw [v.ord_norm_eq_sum_fiber (rational_extension_place_residue_bijective L (RatFunc L) v)
    (original_place_residue_algebraMap_bijective N L) hf]
  exact finsum_eq_zero_of_forall_eq_zero fun w => hord w.val w.property

end
end Dubon2026.SourceFunctionField
