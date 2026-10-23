import Dubon2026.SourceEllipticTranslationAction

/-! The translation action has the actual chord-formula coordinates. This is
the bridge between the native point-group action and the explicit finite Velu
coordinate sums in the odd quotient equation. Adapted from TauCeti
Translation/Basic.lean, Apache-2.0, bfcff79b60964ba7bdb78b952828313686c327ba. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : Affine F)

/-- The actual generic x-coordinate differs from every base-field constant. -/
theorem genericX_ne_constant (x : F) : genericX W ≠ algebraMap F W.FunctionField x := by
  intro h
  apply transcendental_genericX W
  rw [h]
  exact isAlgebraic_algebraMap _

variable [DecidableEq F] [W.IsElliptic]

/-- The translation of x by an affine point is the actual native chord x-formula. -/
theorem translation_genericX_some {x y : F} (h : (W⁄F).toAffine.Nonsingular x y) :
    translation W (.some x y h) (genericX W) =
      (W⁄W.FunctionField).toAffine.addX (genericX W) (algebraMap F W.FunctionField x)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x)
          (genericY W) (algebraMap F W.FunctionField y)) := by
  rw [translation_apply, translationPullback_genericX, translatedGenericPoint,
    Point.map_some, genericPoint_eq_some]
  simp only [Algebra.ofId_apply]
  rw [Point.add_some (fun hc => genericX_ne_constant W x hc.1)]
  rfl

/-- The translation of y by an affine point is the actual native chord y-formula. -/
theorem translation_genericY_some {x y : F} (h : (W⁄F).toAffine.Nonsingular x y) :
    translation W (.some x y h) (genericY W) =
      (W⁄W.FunctionField).toAffine.addY (genericX W) (algebraMap F W.FunctionField x)
        (genericY W)
        ((W⁄W.FunctionField).toAffine.slope (genericX W) (algebraMap F W.FunctionField x)
          (genericY W) (algebraMap F W.FunctionField y)) := by
  rw [translation_apply, translationPullback_genericY, translatedGenericPoint,
    Point.map_some, genericPoint_eq_some]
  simp only [Algebra.ofId_apply]
  rw [Point.add_some (fun hc => genericX_ne_constant W x hc.1)]
  rfl

end Dubon2026.SourceEllipticFunctionField
