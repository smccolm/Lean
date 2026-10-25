import Dubon2026.SourceCurveEvaluationRestriction
import Dubon2026.SourceOriginalNormEvaluation

/-! DUB-17/18 -> original Weil reciprocity and Hecke adjointness ->
evaluation on pushed-forward divisors. The native original field-map and
residue theorems discharge the premises of residue restriction compatibility. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
attribute [local instance] originalNormCharZero
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M]

theorem originalPlaceEval_map_restrictAlong
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (w : Place L (modularFunctionFieldOver M L)) (f : modularFunctionFieldOver N L) :
    originalPlaceEval M L w (φ f) =
      originalPlaceEval N L (w.restrictAlong φ (original_field_hom_finite L N M φ)) f := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  exact Place.rationalEval_algebraMap_restrict w
    (original_place_residue_algebraMap_bijective N L (w.restrict _))
    (original_place_residue_algebraMap_bijective M L w) f

end
end Dubon2026.SourceFunctionField
