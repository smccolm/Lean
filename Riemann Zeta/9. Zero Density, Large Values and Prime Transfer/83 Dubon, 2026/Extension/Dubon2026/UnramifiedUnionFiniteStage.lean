import Dubon2026.UnramifiedGaloisStageNonempty
import Dubon2026.FiniteSubextensionDirectedDescent

/-! # Actual finite subextensions of the constructed union embed in original stages -/

namespace Dubon2026

noncomputable section
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every actual finite subextension of the constructed original union embeds into an original arithmetic stage through its exact original ambient-field inclusion. -/
theorem originalUnramifiedUnion_finite_subextension_embeds_stage
    (a : 𝓞 K) (ha : a ≠ 0)
    (E : IntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [FiniteDimensional K E] :
    ∃ (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : E →ₐ[K] F.val),
      ∀ x : E, (i x : Ω) = (x.val : Ω) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let A := E.map U.val
  let e : E ≃ₐ[K] A := E.equivMap U.val
  letI : FiniteDimensional K A := Module.Finite.of_surjective e.toLinearMap e.surjective
  have hA : A ≤ U := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  letI : Nonempty (OriginalUnramifiedGaloisStage (Ω := Ω) a) :=
    originalUnramifiedGaloisStage_nonempty a
  obtain ⟨F, hF⟩ := finiteIntermediateField_le_directed_stage
    (fun F : OriginalUnramifiedGaloisStage (Ω := Ω) a => F.val.toIntermediateField)
    (originalUnramifiedGaloisStages_directed a ha) A hA
  let i : E →ₐ[K] F.val := (U.val.comp E.val).codRestrict
    F.val.toIntermediateField.toSubalgebra (fun x => hF ⟨x.val, x.property, rfl⟩)
  exact ⟨F, i, fun x => rfl⟩

end
end Dubon2026
