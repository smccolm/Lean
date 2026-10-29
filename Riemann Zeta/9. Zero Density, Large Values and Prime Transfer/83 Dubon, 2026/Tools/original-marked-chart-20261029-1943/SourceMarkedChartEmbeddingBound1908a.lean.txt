import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original-field
marked-point stabilizer. Embeddings with a prescribed j value form a finite
set bounded by the original degree over j. Native adjoin extensionality and
card_algHom_le_finrank replace an additional equalizer field and cardinal
arithmetic framework. The finite degree is an explicit upstream input that
the actual residue-coordinate degree theorem supplies in the consumer. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open IntermediateField

theorem normalized_embeddings_finite_and_card_le {K F Ω : Type*}
    [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
    (x : F) (c : Ω) [FiniteDimensional (adjoin K ({x} : Set F)) F] :
    Finite {ψ : F →ₐ[K] Ω // ψ x = c} ∧
      Nat.card {ψ : F →ₐ[K] Ω // ψ x = c} ≤
        Module.finrank (adjoin K ({x} : Set F)) F := by
  classical
  by_cases hn : Nonempty {ψ : F →ₐ[K] Ω // ψ x = c}
  · obtain ⟨ψ₀, hψ₀⟩ := hn
    let B := adjoin K ({x} : Set F)
    letI : Algebra B Ω := (ψ₀.toRingHom.comp (algebraMap B F)).toAlgebra
    let g : {ψ : F →ₐ[K] Ω // ψ x = c} → (F →ₐ[B] Ω) := fun ψ =>
      { ψ.val.toRingHom with
        commutes' := fun r => by
          change ψ.val (r : F) = ψ₀ (r : F)
          have he : ψ.val.comp B.val = ψ₀.comp B.val := by
            apply adjoin_algHom_ext
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst y
            exact ψ.property.trans hψ₀.symm
          exact AlgHom.congr_fun he r }
    have hg : Function.Injective g := by
      intro ψ ψ' h
      apply Subtype.ext
      exact AlgHom.ext fun y => AlgHom.congr_fun h y
    letI : Finite {ψ : F →ₐ[K] Ω // ψ x = c} := Finite.of_injective g hg
    exact ⟨inferInstance, (Nat.card_le_card_of_injective g hg).trans
      (card_algHom_le_finrank B F Ω)⟩
  · rw [not_nonempty_iff] at hn
    exact ⟨Finite.of_subsingleton, by simp⟩

end
end Dubon2026.SourceFunctionField.MarkedChart
