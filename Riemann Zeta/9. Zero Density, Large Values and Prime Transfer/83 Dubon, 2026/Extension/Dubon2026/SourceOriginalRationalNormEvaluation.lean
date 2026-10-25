import Dubon2026.SourceOriginalRationalCoordinate
import Dubon2026.SourceOriginalNormEvaluation
import Dubon2026.SourceRationalPlaceEvaluation
import Dubon2026.SourceCurveEvaluationRestriction

/-! DUB-17/18 -> original Weil reciprocity -> transfer of reciprocity
with the rational coordinate. These are the actual RatFunc-to-original
consumers of the previously proved norm and residue restriction formulas.
They discharge finiteness and residue identifications for that exact map. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L] (N : ℕ) [NeZero N]

theorem rationalPlaceEval_original_norm_eq_finprod_fiber
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L)
    (v : Place L (RatFunc L)) (f : modularFunctionFieldOver N L)
    (hord : ∀ w : Place L (modularFunctionFieldOver N L),
      w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v → 0 ≤ w.ord f) :
    letI := algebraAlong φ
    RationalFunction.placeEval L v (Algebra.norm (RatFunc L) f) =
      ∏ᶠ w : {w : Place L (modularFunctionFieldOver N L) //
        w.restrictAlong φ (original_ratfunc_hom_finite L N φ) = v},
        originalPlaceEval N L w.val f ^ (w.val.ord (φ v.uniformizer)).toNat := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  haveI : Algebra.IsSeparable (RatFunc L) (modularFunctionFieldOver N L) :=
    Algebra.IsSeparable.of_integral _ _
  exact Place.rationalEval_norm_eq_finprod_fiber v
    (rational_extension_place_residue_bijective L (RatFunc L) v)
    (original_place_residue_algebraMap_bijective N L) hord

theorem originalPlaceEval_ratfunc_map_restrict
    (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L)
    (w : Place L (modularFunctionFieldOver N L)) (f : RatFunc L) :
    originalPlaceEval N L w (φ f) = RationalFunction.placeEval L
      (w.restrictAlong φ (original_ratfunc_hom_finite L N φ)) f := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (RatFunc L) (modularFunctionFieldOver N L) := original_ratfunc_hom_finite L N φ
  exact Place.rationalEval_algebraMap_restrict w
    (rational_extension_place_residue_bijective L (RatFunc L) (w.restrict (RatFunc L)))
    (original_place_residue_algebraMap_bijective N L w) f

end
end Dubon2026.SourceFunctionField
