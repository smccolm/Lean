import Dubon2026.SourceEllipticTranslationAction
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.TypeTags.Finite

/-! The actual subgroup of translation automorphisms. Native subgroup ranges
and the already proved faithfulness identify its cardinality with the actual
point subgroup. This is the finite group needed by the native fixed-field
theorem, preceding the explicit odd quotient equation on DUB-17/18. -/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
variable (H : AddSubgroup (W⁄F).toAffine.Point)

/-- Restrict the actual translation action to the given point subgroup. -/
noncomputable def subgroupTranslationHom :
    Multiplicative H →* (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  (translationHom W).comp (AddMonoidHom.toMultiplicative H.subtype)

/-- The restricted translation action is faithful. -/
theorem subgroupTranslationHom_injective : Function.Injective (subgroupTranslationHom W H) := by
  intro P Q h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact translation_injective W h

/-- The actual subgroup of function-field automorphisms arising from translations in H. -/
noncomputable def translationSubgroup : Subgroup (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  (subgroupTranslationHom W H).range

/-- Membership identifies an actual point and its actual translation automorphism. -/
theorem mem_translationSubgroup_iff (σ : W.FunctionField ≃ₐ[F] W.FunctionField) :
    σ ∈ translationSubgroup W H ↔ ∃ P ∈ H, translation W P = σ := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.toAdd, P.toAdd.property, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨Multiplicative.ofAdd (⟨P, hP⟩ : H), rfl⟩

/-- A finite actual point subgroup gives a finite translation subgroup. -/
theorem finite_translationSubgroup [Finite H] : Finite (translationSubgroup W H) := by
  change Finite (Set.range (subgroupTranslationHom W H))
  infer_instance

/-- Faithfulness makes the actual translation subgroup have exactly the original cardinality. -/
theorem card_translationSubgroup [Finite H] : Nat.card (translationSubgroup W H) = Nat.card H := by
  classical
  letI := Fintype.ofFinite H
  change Nat.card (subgroupTranslationHom W H).range = Nat.card H
  rw [Nat.card_eq_fintype_card,
    Fintype.card_coeSort_range (subgroupTranslationHom_injective W H),
    Fintype.card_multiplicative, Nat.card_eq_fintype_card]

end Dubon2026.SourceEllipticFunctionField
