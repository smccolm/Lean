import Dubon2026.SourceEllipticTranslatedGenericPoint
import Dubon2026.SourceEllipticFunctionLift

/-! Translation pullback on the actual elliptic function field. The existing
field lift consumes the proved equation and transcendence of a translated
generic point. Native point associativity gives composition. Adapted from
TauCeti Translation/Basic.lean, Apache-2.0,
bfcff79b60964ba7bdb78b952828313686c327ba. This is used to derive invariance
of the odd quotient coordinates, a prerequisite for their equation (DUB-17/18). -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- Actual field pullback obtained by evaluating at the translated generic point. -/
noncomputable def translationPullback (P : (W⁄F).toAffine.Point) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  functionFieldLift (nonsingular_coordsOrZero (translatedGenericPoint_ne_zero W P)).left
    (transcendental_translatedGenericX W P)

/-- The translation pullback takes x to the actual translated x-coordinate. -/
theorem translationPullback_genericX (P : (W⁄F).toAffine.Point) :
    translationPullback W P (genericX W) = (coordsOrZero (translatedGenericPoint W P)).1 :=
  functionFieldLift_genericX _ _

/-- The translation pullback takes y to the actual translated y-coordinate. -/
theorem translationPullback_genericY (P : (W⁄F).toAffine.Point) :
    translationPullback W P (genericY W) = (coordsOrZero (translatedGenericPoint W P)).2 :=
  functionFieldLift_genericY _ _

/-- Point base change by the pullback takes the generic point to its actual translate. -/
theorem map_translationPullback_genericPoint (P : (W⁄F).toAffine.Point) :
    Point.map (translationPullback W P) (genericPoint W) = translatedGenericPoint W P := by
  rw [genericPoint_eq_some, Point.map_some]
  simp only [translationPullback_genericX, translationPullback_genericY]
  exact some_coordsOrZero (translatedGenericPoint_ne_zero W P)

/-- A second translation acts on a translated generic point by actual point addition. -/
theorem map_translationPullback_translatedGenericPoint (P Q : (W⁄F).toAffine.Point) :
    Point.map (translationPullback W Q) (translatedGenericPoint W P) =
      translatedGenericPoint W (P + Q) := by
  rw [translatedGenericPoint, map_add, Point.map_baseChange, map_translationPullback_genericPoint,
    translatedGenericPoint, translatedGenericPoint, map_add, add_right_comm]
  exact add_assoc _ _ _

/-- Composition of actual pullbacks agrees with addition of the rational translation points. -/
theorem translationPullback_comp (P Q : (W⁄F).toAffine.Point) :
    (translationPullback W Q).comp (translationPullback W P) =
      translationPullback W (P + Q) := by
  have he := congrArg coordsOrZero (map_translationPullback_translatedGenericPoint W P Q)
  rw [coordsOrZero_point_map] at he
  apply functionFieldAlgHom_ext
  · simpa only [AlgHom.comp_apply, translationPullback_genericX] using congrArg Prod.fst he
  · simpa only [AlgHom.comp_apply, translationPullback_genericY] using congrArg Prod.snd he

/-- Translation by zero induces the identity of the actual function field. -/
theorem translationPullback_zero : translationPullback W 0 = AlgHom.id F W.FunctionField := by
  apply functionFieldAlgHom_ext
  · rw [translationPullback_genericX, translatedGenericPoint_zero, coordsOrZero_genericPoint]
    rfl
  · rw [translationPullback_genericY, translatedGenericPoint_zero, coordsOrZero_genericPoint]
    rfl

end Dubon2026.SourceEllipticFunctionField
