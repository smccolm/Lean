import Dubon2026.SourceEllipticPointCoordinates
import Dubon2026.SourceEllipticPointIntegral
import Mathlib.FieldTheory.AlgebraicClosure

/-! The translate of the actual generic point has transcendental x-coordinate.
Adapted from TauCeti Translation/Basic.lean, Apache-2.0,
bfcff79b60964ba7bdb78b952828313686c327ba. The relative algebraic closure and
native group law avoid a separate pole calculation. This supplies injectivity
for the translation pullback required by the odd quotient equation (DUB-17/18). -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- The actual generic point translated by the base change of a rational point. -/
noncomputable def translatedGenericPoint (P : (W⁄F).toAffine.Point) :
    (W⁄W.FunctionField).toAffine.Point :=
  genericPoint W + Point.baseChange (W' := W) F W.FunctionField P

/-- Translation by zero leaves the generic point unchanged. -/
theorem translatedGenericPoint_zero : translatedGenericPoint W 0 = genericPoint W := by
  rw [translatedGenericPoint, map_zero, add_zero]

/-- A constant translate of the generic point never equals the point at infinity. -/
theorem translatedGenericPoint_ne_zero (P : (W⁄F).toAffine.Point) :
    translatedGenericPoint W P ≠ 0 := by
  intro h
  have hneg : genericPoint W = -Point.baseChange (W' := W) F W.FunctionField P :=
    eq_neg_of_add_eq_zero_left h
  have he := congrArg (fun R => (coordsOrZero R).1) hneg
  dsimp only at he
  rw [coordsOrZero_genericPoint, coordsOrZero_neg_fst, coordsOrZero_point_map] at he
  have hx : genericX W = algebraMap F W.FunctionField (coordsOrZero P).1 := he
  apply transcendental_genericX W
  rw [hx]
  exact isAlgebraic_algebraMap _

/-- The translated x-coordinate is transcendental, with no extra nonconstancy hypothesis. -/
theorem transcendental_translatedGenericX (P : (W⁄F).toAffine.Point) :
    Transcendental F (coordsOrZero (translatedGenericPoint W P)).1 := by
  classical
  let E := algebraicClosure F W.FunctionField
  intro halg
  let Q := translatedGenericPoint W P
  have hQ : Q ≠ 0 := translatedGenericPoint_ne_zero W P
  let u := (coordsOrZero Q).1
  let v := (coordsOrZero Q).2
  have hns : (W⁄W.FunctionField).toAffine.Nonsingular u v := nonsingular_coordsOrZero hQ
  have hu : u ∈ E := halg.isIntegral
  have hv : v ∈ E := isIntegral_y_of_equation W hns.left hu
  have hnsE : (W⁄E).toAffine.Nonsingular (⟨u, hu⟩ : E) ⟨v, hv⟩ :=
    (WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
      (f := E.val) E.val.injective _ _).1 hns
  have hQmap : Point.map E.val (Point.some (⟨u, hu⟩ : E) ⟨v, hv⟩ hnsE) = Q := by
    rw [Point.map_some]
    exact some_coordsOrZero hQ
  have hg : genericPoint W = Point.map E.val
      (Point.some (⟨u, hu⟩ : E) ⟨v, hv⟩ hnsE - Point.baseChange (W' := W) F E P) := by
    rw [map_sub, hQmap, Point.map_baseChange]
    exact (add_sub_cancel_right (genericPoint W) _).symm
  have hx : IsIntegral F (genericX W) := by
    have he := congrArg (fun R => (coordsOrZero R).1) hg
    dsimp only at he
    rw [coordsOrZero_genericPoint, coordsOrZero_point_map] at he
    rw [show genericX W = _ from he]
    exact (Algebra.IsIntegral.isIntegral (R := F) _).map E.val
  exact transcendental_genericX W hx.isAlgebraic

end Dubon2026.SourceEllipticFunctionField
