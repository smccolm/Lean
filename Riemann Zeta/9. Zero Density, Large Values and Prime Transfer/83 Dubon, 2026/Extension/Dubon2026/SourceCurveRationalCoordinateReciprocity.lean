import Dubon2026.SourceCurveRationalDivisorNorm
import Dubon2026.SourceRationalCoordinateWeilReciprocity
import Dubon2026.SourceCurveCorrespondenceRamification

/-! DUB-17/18 -> finite Weil nondegeneracy -> Kummer-cover reciprocity.
The existing rational-coordinate reciprocity theorem transfers through the
already proved norm and divisor adjunctions. No cover reciprocity is assumed. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable (K E : Type*) [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
variable [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E]

omit [IsAlgClosed K] in
theorem rationalExtensionPrincipalDivisor_pullback (g : RatFunc K) :
    Divisor.finitePullback E (rationalExtensionPrincipalDivisor K (RatFunc K) g) =
      rationalExtensionPrincipalDivisor K E (algebraMap (RatFunc K) E g) := by
  ext w
  simp only [Divisor.finitePullback_apply, rationalExtensionPrincipalDivisor_apply]
  exact (w.ord_algebraMap_restrict g).symm

variable [CharZero K]

theorem rationalExtensionPrincipalDivisor_pushforward (f : E) (hf : f ≠ 0) :
    Divisor.geometricPushforward (RatFunc K) (rationalExtensionPrincipalDivisor K E f) =
      rationalExtensionPrincipalDivisor K (RatFunc K) (Algebra.norm (RatFunc K) f) := by
  ext v
  rw [Divisor.geometricPushforward_apply, rationalExtensionPrincipalDivisor_apply,
    v.ord_norm_eq_sum_fiber (rational_extension_place_residue_bijective K (RatFunc K) v)
      (rational_extension_place_residue_bijective K E) hf]
  rfl

theorem rationalExtension_norm_ord_zero_of_fiber (f : E) (hf : f ≠ 0)
    (v : Place K (RatFunc K))
    (hord : ∀ w : Place K E, w.restrict (RatFunc K) = v → w.ord f = 0) :
    v.ord (Algebra.norm (RatFunc K) f) = 0 := by
  rw [v.ord_norm_eq_sum_fiber (rational_extension_place_residue_bijective K (RatFunc K) v)
    (rational_extension_place_residue_bijective K E) hf]
  exact finsum_eq_zero_of_forall_eq_zero fun w => hord w.val w.property

theorem rationalExtension_coordinate_weil_reciprocity (f : E) (hf : f ≠ 0)
    (hdisj : ∀ w : Place K E, w.ord f ≠ 0 →
      w.ord (algebraMap (RatFunc K) E RatFunc.X) = 0) :
    rationalDivisorEval (rational_extension_place_residue_bijective K E) f
      (rationalExtensionPrincipalDivisor K E (algebraMap (RatFunc K) E RatFunc.X)) =
    rationalDivisorEval (rational_extension_place_residue_bijective K E)
      (algebraMap (RatFunc K) E RatFunc.X) (rationalExtensionPrincipalDivisor K E f) := by
  have hzero (v : Place K (RatFunc K)) (hv : v.ord RatFunc.X ≠ 0)
      (w : Place K E) (hw : w.restrict (RatFunc K) = v) : w.ord f = 0 := by
    by_contra h
    have hg := hdisj w h
    rw [Place.ord_algebraMap_restrict] at hg
    have hpos := w.ord_restricted_uniformizer_pos (F := RatFunc K)
    rw [hw] at hg
    exact (mul_ne_zero hv (ne_of_gt (by simpa only [hw] using hpos))) hg
  have h0 : (RationalFunction.pointPlace K 0).ord (RatFunc.X : RatFunc K) = 1 := by
    simpa using RationalFunction.pointPlace_ord_parameter K 0
  have hn0 := rationalExtension_norm_ord_zero_of_fiber K E f hf _
    (hzero (RationalFunction.pointPlace K 0) (by rw [h0]; exact one_ne_zero))
  have hni := rationalExtension_norm_ord_zero_of_fiber K E f hf _
    (hzero (RationalFunction.infinityPlace K) (by
      rw [RationalFunction.infinityPlace_ord_X]; norm_num))
  calc
    _ = RationalFunction.divisorEval K (Algebra.norm (RatFunc K) f)
        (rationalExtensionPrincipalDivisor K (RatFunc K) RatFunc.X) := by
      rw [← rationalExtensionPrincipalDivisor_pullback]
      apply rationalDivisorEval_finitePullback
      intro v hv w hw
      exact (hzero v (Finsupp.mem_support_iff.mp hv) w hw).ge
    _ = RationalFunction.divisorEval K RatFunc.X
        (rationalExtensionPrincipalDivisor K (RatFunc K) (Algebra.norm (RatFunc K) f)) :=
      RationalFunction.coordinate_weil_reciprocity K (Algebra.norm_ne_zero_iff.mpr hf) hn0 hni
    _ = _ := by
      rw [← rationalExtensionPrincipalDivisor_pushforward K E f hf]
      apply rationalDivisorEval_geometricPushforward _ _ _ _ RatFunc.X_ne_zero
      intro w hw
      exact hdisj w (Finsupp.mem_support_iff.mp hw)

end
end Dubon2026.SourceCurve
