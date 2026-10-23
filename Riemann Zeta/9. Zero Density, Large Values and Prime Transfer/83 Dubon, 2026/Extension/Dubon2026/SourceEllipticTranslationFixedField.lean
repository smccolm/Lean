import Dubon2026.SourceEllipticTranslationSubgroup
import Mathlib.FieldTheory.Galois.Basic

/-! The actual translation fixed field is a finite Galois subfield of the
original elliptic function field, of degree the subgroup cardinality.
Native Artin fixed-field theory and the actual faithful translation action
replace a separate quotient-degree argument. The equation of the explicit
odd quotient still requires identification of its coordinate field. -/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
variable (H : AddSubgroup (W⁄F).toAffine.Point)

/-- The actual subfield fixed by the point-subgroup translations. -/
noncomputable def translationFixedField : IntermediateField F W.FunctionField :=
  IntermediateField.fixedField (translationSubgroup W H)

/-- Fixed-field membership means invariance under the actual point translations. -/
theorem mem_translationFixedField_iff (z : W.FunctionField) :
    z ∈ translationFixedField W H ↔ ∀ P ∈ H, translation W P z = z := by
  rw [translationFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h P hP
    exact h (translation W P) ((mem_translationSubgroup_iff W H _).mpr ⟨P, hP, rfl⟩)
  · intro h σ hσ
    obtain ⟨P, hP, rfl⟩ := (mem_translationSubgroup_iff W H σ).mp hσ
    exact h P hP

/-- The actual elliptic function field is finite over the finite-translation fixed field. -/
theorem finiteDimensional_translationFixedField [Finite H] :
    FiniteDimensional (translationFixedField W H) W.FunctionField := by
  letI : Finite (translationSubgroup W H) := finite_translationSubgroup W H
  change FiniteDimensional (FixedPoints.subfield (translationSubgroup W H) W.FunctionField)
    W.FunctionField
  infer_instance

/-- The actual translation fixed-field degree equals the actual subgroup cardinality. -/
theorem finrank_translationFixedField [Finite H] :
    Module.finrank (translationFixedField W H) W.FunctionField = Nat.card H := by
  letI : Finite (translationSubgroup W H) := finite_translationSubgroup W H
  letI := Fintype.ofFinite (translationSubgroup W H)
  change Module.finrank (FixedPoints.subfield (translationSubgroup W H) W.FunctionField)
    W.FunctionField = _
  rw [FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, card_translationSubgroup]

/-- The actual extension over the translation fixed field is Galois, in every characteristic. -/
theorem isGalois_translationFixedField [Finite H] :
    IsGalois (translationFixedField W H) W.FunctionField := by
  letI : Finite (translationSubgroup W H) := finite_translationSubgroup W H
  change IsGalois (FixedPoints.subfield (translationSubgroup W H) W.FunctionField) W.FunctionField
  infer_instance

end Dubon2026.SourceEllipticFunctionField
