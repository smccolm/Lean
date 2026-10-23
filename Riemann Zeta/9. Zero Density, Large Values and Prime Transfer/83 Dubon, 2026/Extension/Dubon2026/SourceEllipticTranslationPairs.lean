import Dubon2026.SourceEllipticTranslationCoordinates
import Dubon2026.SourceEllipticOddChordY

/-! Pairing actual field translations by an affine point and its negative.
The existing x-chord identity and the proved y-chord identity connect the
faithful field action to the rational summands of the explicit odd quotient.
This is an actual-coordinate bridge for its equation on the DUB-17/18 chain. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- Paired actual field translations have the explicit two-term x-correction. -/
theorem translation_x_pair {x y : F} (h : (W⁄F).toAffine.Nonsingular x y) :
    translation W (.some x y h) (genericX W) +
      translation W (-Point.some x y h) (genericX W) =
    2 * algebraMap F W.FunctionField x +
      veluT (W⁄W.FunctionField) (algebraMap F W.FunctionField x)
        (algebraMap F W.FunctionField y) / (genericX W - algebraMap F W.FunctionField x) +
      veluU (W⁄W.FunctionField) (algebraMap F W.FunctionField x)
        (algebraMap F W.FunctionField y) / (genericX W - algebraMap F W.FunctionField x) ^ 2 := by
  have hn := W.baseChange_negY (Algebra.ofId F W.FunctionField) x y
  have hp := (W.baseChange_equation (Algebra.ofId F W.FunctionField).injective x y).2 h.1
  simp only [Algebra.ofId_apply] at hn hp
  rw [Point.neg_some, translation_genericX_some, translation_genericX_some]
  rw [← hn]
  exact chord_sum' (W⁄W.FunctionField) (equation_genericX_genericY W) hp (genericX_ne_constant W x)

/-- Paired actual field translations have the explicit three-term y-correction. -/
theorem translation_y_pair {x y : F} (h : (W⁄F).toAffine.Nonsingular x y) :
    translation W (.some x y h) (genericY W) +
      translation W (-Point.some x y h) (genericY W) =
    -(W⁄W.FunctionField).a₁ * algebraMap F W.FunctionField x - (W⁄W.FunctionField).a₃ -
      (veluU (W⁄W.FunctionField) (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y) *
          (2 * genericY W + (W⁄W.FunctionField).a₁ * genericX W + (W⁄W.FunctionField).a₃) /
          (genericX W - algebraMap F W.FunctionField x) ^ 3 +
       veluT (W⁄W.FunctionField) (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y) *
          ((W⁄W.FunctionField).a₁ * (genericX W - algebraMap F W.FunctionField x) + genericY W -
            algebraMap F W.FunctionField y) / (genericX W - algebraMap F W.FunctionField x) ^ 2 +
       ((W⁄W.FunctionField).a₁ *
          veluU (W⁄W.FunctionField) (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y) -
        veluGx (W⁄W.FunctionField) (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y) *
        veluGy (W⁄W.FunctionField) (algebraMap F W.FunctionField x) (algebraMap F W.FunctionField y)) /
          (genericX W - algebraMap F W.FunctionField x) ^ 2) := by
  have hn := W.baseChange_negY (Algebra.ofId F W.FunctionField) x y
  have hp := (W.baseChange_equation (Algebra.ofId F W.FunctionField).injective x y).2 h.1
  simp only [Algebra.ofId_apply] at hn hp
  rw [Point.neg_some, translation_genericY_some, translation_genericY_some]
  rw [← hn]
  exact chord_y_sum (W⁄W.FunctionField) (equation_genericX_genericY W) hp (genericX_ne_constant W x)

end Dubon2026.SourceEllipticFunctionField
