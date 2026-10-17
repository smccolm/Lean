import Mathlib.Algebra.Module.CharacterModule

/-! # A prescribed character on a finite-order element

DUB-17's full-order arithmetic class requires the missing two-primary
splitting step. The character defining its totally complex cyclic
cyclotomic subfield must detect minus one and retain the order of five.
Pinned character-module injectivity already extends the character of a
single element; only its exact value is needed here.
-/
namespace Dubon2026
noncomputable section

/-- A finite-order element has an actual rational-circle character with
value the reciprocal of its order. -/
theorem originalRationalCircle_exists_prescribed_character
    {A : Type*} [AddCommGroup A] (a : A) (ha : addOrderOf a ≠ 0) :
    ∃ χ : A →+ AddCircle (1 : ℚ),
      χ a = ((1 / addOrderOf a : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨χ, hχ⟩ := CharacterModule.dual_surjective_of_injective _
    (Submodule.injective_subtype (ℤ ∙ a)) (CharacterModule.ofSpanSingleton a)
  refine ⟨χ, ?_⟩
  have h := congrArg (fun f : CharacterModule (ℤ ∙ a) =>
    f ⟨a, Submodule.mem_span_singleton_self a⟩) hχ
  change χ a = _ at h
  refine h.trans ?_
  change CharacterModule.ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = _
  erw [CharacterModule.ofSpanSingleton, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, CharacterModule.intSpanEquivQuotAddOrderOf_apply_self,
    Submodule.liftQSpanSingleton_apply, AddMonoidHom.coe_toIntLinearMap,
    CharacterModule.int.divByNat, LinearMap.toSpanSingleton_apply_one]
  simp only [if_neg ha, one_div]

end
end Dubon2026
