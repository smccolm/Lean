import Dubon2026.SourceEllipticTranslationCoordinates

/-! Actual finite translation sums and their invariance. Adapted from the
normalized coordinate sums in TauCeti Isogeny/Velu/Coordinates.lean,
Apache-2.0, bfcff79b60964ba7bdb78b952828313686c327ba. These actual function-field
elements will be identified with the explicit odd Velu formulas before proving
the quotient equation on the DUB-17/18 dependency chain. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
variable (H : AddSubgroup (W⁄F).toAffine.Point) [Finite H]

attribute [local instance] Fintype.ofFinite

/-- A finite sum over actual subgroup translations is fixed by each subgroup translation. -/
theorem translation_sum (P : H) (z : W.FunctionField) :
    translation W P (∑ Q : H, translation W Q z) = ∑ Q : H, translation W Q z := by
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.addRight P)
  intro Q
  exact (congrArg (fun e : W.FunctionField ≃ₐ[F] W.FunctionField => e z)
    (translation_add W Q P)).symm

/-- The actual normalized x-coordinate sum over a finite rational-point subgroup. -/
noncomputable def translationTraceX : W.FunctionField :=
  ∑ Q : H, (translation W Q (genericX W) -
    algebraMap F W.FunctionField (coordsOrZero (Q : (W⁄F).toAffine.Point)).1)

/-- The actual normalized y-coordinate sum over a finite rational-point subgroup. -/
noncomputable def translationTraceY : W.FunctionField :=
  ∑ Q : H, (translation W Q (genericY W) -
    algebraMap F W.FunctionField (coordsOrZero (Q : (W⁄F).toAffine.Point)).2)

/-- The normalized x-sum is the translation sum minus its actual constant correction. -/
theorem translationTraceX_eq_sum : translationTraceX W H =
    (∑ Q : H, translation W Q (genericX W)) -
      algebraMap F W.FunctionField (∑ Q : H, (coordsOrZero (Q : (W⁄F).toAffine.Point)).1) := by
  simp only [translationTraceX, Finset.sum_sub_distrib, map_sum]

/-- The normalized y-sum is the translation sum minus its actual constant correction. -/
theorem translationTraceY_eq_sum : translationTraceY W H =
    (∑ Q : H, translation W Q (genericY W)) -
      algebraMap F W.FunctionField (∑ Q : H, (coordsOrZero (Q : (W⁄F).toAffine.Point)).2) := by
  simp only [translationTraceY, Finset.sum_sub_distrib, map_sum]

/-- Every actual subgroup translation fixes its normalized x-coordinate sum. -/
theorem translation_translationTraceX (P : H) :
    translation W P (translationTraceX W H) = translationTraceX W H := by
  rw [translationTraceX_eq_sum, map_sub, translation_sum, AlgEquiv.commutes]

/-- Every actual subgroup translation fixes its normalized y-coordinate sum. -/
theorem translation_translationTraceY (P : H) :
    translation W P (translationTraceY W H) = translationTraceY W H := by
  rw [translationTraceY_eq_sum, map_sub, translation_sum, AlgEquiv.commutes]

end Dubon2026.SourceEllipticFunctionField
