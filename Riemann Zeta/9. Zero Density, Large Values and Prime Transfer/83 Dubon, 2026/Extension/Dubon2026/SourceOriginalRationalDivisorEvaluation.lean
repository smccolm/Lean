import Dubon2026.SourceOriginalRationalNormEvaluation
import Dubon2026.SourceCurvePullbackEvaluationProduct
import Dubon2026.SourceFiniteDivisorEvaluationPushforward
import Dubon2026.SourceOriginalWeilEvaluation
import Dubon2026.SourceRationalDivisorEvaluation

/-! DUB-17/18 -> original Weil reciprocity -> finite norm transfer of
coordinate reciprocity. Actual original divisor evaluations commute with
pullback/norm and pushforward/pulled-back functions for a rational base. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] (N : ℕ) [NeZero N]

theorem originalDivisorEval_ratfunc_finitePullback
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L)
    (D : Divisor L (RatFunc L)) (f : modularFunctionFieldOver N L)
    (hord : ∀ v ∈ D.support, ∀ w : Place L (modularFunctionFieldOver N L),
      w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v → 0 ≤ w.ord f) :
    letI := algebraAlong φ
    originalDivisorEval N L f (Divisor.finitePullbackAlong φ (original_ratfunc_hom_finite L N φ) D) =
      RationalFunction.divisorEval L (Algebra.norm (RatFunc L) f) D := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  change (Divisor.finitePullback (modularFunctionFieldOver N L) D).prod
    (fun w n => originalPlaceEval N L w f ^ n) = _
  rw [Divisor.finitePullback_prod_zpow]
  apply Finset.prod_congr rfl
  intro v hv
  exact congrArg (fun a : L => a ^ D v)
    (rationalPlaceEval_original_norm_eq_finprod_fiber L N φ v f (hord v hv)).symm

theorem rationalDivisorEval_original_geometricPushforward
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L)
    (D : Divisor L (modularFunctionFieldOver N L)) (f : RatFunc L) (hf : f ≠ 0)
    (hord : ∀ w ∈ D.support, w.ord (φ f) = 0) :
    RationalFunction.divisorEval L f
      (Divisor.geometricPushforwardAlong φ (original_ratfunc_hom_finite L N φ) D) =
        originalDivisorEval N L (φ f) D := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  have hn (w : Place L (modularFunctionFieldOver N L)) (hw : w ∈ D.support) :
      RationalFunction.placeEval L (w.restrictAlong φ (original_ratfunc_hom_finite L N φ)) f ≠ 0 := by
    rw [← originalPlaceEval_ratfunc_map_restrict L N φ w f]
    exact originalPlaceEval_ne_zero_of_ord_eq_zero N L w ((map_ne_zero φ).mpr hf) (hord w hw)
  change (D.mapDomain (fun w => w.restrictAlong φ (original_ratfunc_hom_finite L N φ))).prod
    (fun v n => RationalFunction.placeEval L v f ^ n) = _
  rw [finsupp_prod_zpow_mapDomain _ _ _ hn]
  apply Finsupp.prod_congr
  intro w _
  rw [originalPlaceEval_ratfunc_map_restrict L N φ w f]

end
end Dubon2026.SourceFunctionField
