import Dubon2026.ArithmeticFiniteLocalStage

/-! # The actual arithmetic completion preserves subfield containment

Both local stages use the same original arithmetic embedding. Their literal
adjoin constructions therefore preserve inclusion. This is the containment
needed to apply the conductor-two cyclic-subfield character to DUB-17's
constructed global cyclic subfield without supplying a new local certificate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- Original finite-stage containment gives containment of the actual
local stages under the unchanged arithmetic embedding. -/
theorem rationalArithmeticFiniteLocalStage_mono
    (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) (p : ℕ) (hp : p.Prime) :
    (rationalArithmeticFiniteLocalStage a E p hp).toIntermediateField ≤
      (rationalArithmeticFiniteLocalStage a F p hp).toIntermediateField := by
  change IntermediateField.adjoin (rationalPrimeLocalField p hp)
      (Set.range (rationalArithmeticFiniteLocalEmbedding a E p hp)) ≤
    IntermediateField.adjoin (rationalPrimeLocalField p hp)
      (Set.range (rationalArithmeticFiniteLocalEmbedding a F p hp))
  apply IntermediateField.adjoin.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨IntermediateField.inclusion hEF x, rfl⟩

end
end Dubon2026
