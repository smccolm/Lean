import Dubon2026.SourceCurveFieldNormEvaluation
import Dubon2026.SourceOriginalPlaceEvaluation
import Dubon2026.SourceOriginalHeckeFinite
import Dubon2026.SourceCurveCorrespondencePlaces

/-! DUB-17/18 -> original Frobenius determinant -> original Weil
reciprocity and Hecke adjointness -> norm evaluation on original curves.
The existing original field-map finiteness and residue-field bijections
discharge every geometric premise of the fiber norm formula. Its only
function condition is regularity on the actual fiber. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L]

/-- The original coefficient field has characteristic zero from its rational algebra. -/
local instance originalNormCharZero : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

variable [IsAlgClosed L]
variable (N M : ℕ) [NeZero N] [NeZero M]

omit [NeZero M] in
theorem originalPlaceEval_eq_rationalEval (v : Place L (modularFunctionFieldOver N L))
    (f : modularFunctionFieldOver N L) :
    originalPlaceEval N L v f =
      v.rationalEval (original_place_residue_algebraMap_bijective N L v) f := rfl

theorem originalPlaceEval_normAlong_eq_finprod_fiber
    (φ : modularFunctionFieldOver N L →ₐ[L] modularFunctionFieldOver M L)
    (v : Place L (modularFunctionFieldOver N L)) (f : modularFunctionFieldOver M L)
    (hord : ∀ w : Place L (modularFunctionFieldOver M L),
      w.restrictAlong φ (original_field_hom_finite L N M φ) = v → 0 ≤ w.ord f) :
    letI := algebraAlong φ
    originalPlaceEval N L v (Algebra.norm (modularFunctionFieldOver N L) f) =
      ∏ᶠ w : {w : Place L (modularFunctionFieldOver M L) //
        w.restrictAlong φ (original_field_hom_finite L N M φ) = v},
        originalPlaceEval M L w.val f ^ (w.val.ord (φ v.uniformizer)).toNat := by
  letI := algebraAlong φ
  haveI := scalarTower_along φ
  haveI : Module.Finite (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    original_field_hom_finite L N M φ
  haveI : Algebra.IsSeparable (modularFunctionFieldOver N L) (modularFunctionFieldOver M L) :=
    Algebra.IsSeparable.of_integral _ _
  exact Place.rationalEval_norm_eq_finprod_fiber v
    (original_place_residue_algebraMap_bijective N L v)
    (original_place_residue_algebraMap_bijective M L) hord

end
end Dubon2026.SourceFunctionField
