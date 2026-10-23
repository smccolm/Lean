import Dubon2026.SourceEllipticTranslationPullback

/-! Faithful rational-point translation on the actual function field. The inverse
is the pullback by the negative point. Adapted from TauCeti Translation/Basic.lean,
Apache-2.0, bfcff79b60964ba7bdb78b952828313686c327ba. This action supplies the
finite kernel translations used for the odd quotient's invariant field and equation. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- Translation by a rational point as an actual function-field automorphism. -/
noncomputable def translation (P : (W⁄F).toAffine.Point) : W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (translationPullback W P) (translationPullback W (-P))
    (by rw [translationPullback_comp, neg_add_cancel, translationPullback_zero])
    (by rw [translationPullback_comp, add_neg_cancel, translationPullback_zero])

/-- The automorphism evaluates by the actual translation pullback. -/
theorem translation_apply (P : (W⁄F).toAffine.Point) (z : W.FunctionField) :
    translation W P z = translationPullback W P z := rfl

/-- Translation carries the generic point to its actual translate. -/
theorem map_translation_genericPoint (P : (W⁄F).toAffine.Point) :
    Point.map (translation W P).toAlgHom (genericPoint W) = translatedGenericPoint W P :=
  map_translationPullback_genericPoint W P

/-- Translation by zero is the identity automorphism. -/
theorem translation_zero : translation W 0 = 1 :=
  AlgEquiv.ext fun z => AlgHom.congr_fun (translationPullback_zero W) z

/-- Translation automorphisms compose by addition of the rational points. -/
theorem translation_add (P Q : (W⁄F).toAffine.Point) :
    translation W (P + Q) = (translation W P).trans (translation W Q) :=
  AlgEquiv.ext fun z => (AlgHom.congr_fun (translationPullback_comp W P Q) z).symm

/-- The actual translation action of the rational-point group. -/
noncomputable def translationHom :
    Multiplicative (W⁄F).toAffine.Point →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun P := translation W (Multiplicative.toAdd P)
  map_one' := translation_zero W
  map_mul' P Q :=
    (congrArg (translation W) (add_comm (Multiplicative.toAdd P) (Multiplicative.toAdd Q))).trans
      (translation_add W (Multiplicative.toAdd Q) (Multiplicative.toAdd P))

/-- The action homomorphism evaluates to the actual translation. -/
theorem translationHom_apply (P : Multiplicative (W⁄F).toAffine.Point) :
    translationHom W P = translation W (Multiplicative.toAdd P) := rfl

/-- Negating the rational point inverts its translation automorphism. -/
theorem translation_neg (P : (W⁄F).toAffine.Point) :
    translation W (-P) = (translation W P)⁻¹ :=
  map_inv (translationHom W) (Multiplicative.ofAdd P)

/-- Only the zero point induces the identity automorphism. -/
theorem translation_eq_one_iff {P : (W⁄F).toAffine.Point} :
    translation W P = 1 ↔ P = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ translation_zero W⟩
  have he : translationPullback W P = AlgHom.id F W.FunctionField := by
    change (translation W P).toAlgHom = _
    rw [h]
    rfl
  have hm := map_translationPullback_genericPoint W P
  rw [he] at hm
  have hid : Point.map (AlgHom.id F W.FunctionField) (genericPoint W) = genericPoint W := by
    rw [genericPoint_eq_some, Point.map_some]
    rfl
  rw [hid] at hm
  have hb : Point.baseChange (W' := W) F W.FunctionField P = 0 :=
    (add_eq_left.mp hm.symm)
  exact Point.map_injective (W' := W) _
    (hb.trans (map_zero (Point.baseChange (W' := W) F W.FunctionField)).symm)

/-- Distinct rational points induce distinct function-field translations. -/
theorem translation_injective : Function.Injective (translation W) := by
  intro P Q h
  have he : translation W (P - Q) = 1 := by
    rw [sub_eq_add_neg, translation_add, h, ← translation_add, add_neg_cancel, translation_zero]
  exact sub_eq_zero.mp ((translation_eq_one_iff W).mp he)

/-- The rational-point translation action is faithful. -/
theorem translationHom_injective : Function.Injective (translationHom W) := by
  intro P Q h
  apply Multiplicative.toAdd.injective
  exact translation_injective W h

end Dubon2026.SourceEllipticFunctionField
