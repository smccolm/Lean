import Dubon2026.RationalTwoArithmeticCyclotomicContainingStage

/-! # The original global containing field inside the canonical local stage

Restrict the codomain of the original arithmetic embedding using the proved
equality of local containing stages. The ambient value remains unchanged.
This is the actual embedding needed to compare conductor-two restriction
through the global containing field in DUB-17's principal product.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]

/-- The original global containing-field embedding has image in the same
canonical local cyclotomic field used by the conductor-two character. -/
def rationalTwoArithmeticContainingEmbedding :
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
    letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
    F →ₐ[ℚ] C := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
    (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
  let i := rationalArithmeticFiniteLocalEmbedding a F 2 Nat.prime_two
  have hstage : rationalArithmeticFiniteLocalStage a F 2 Nat.prime_two = C :=
    rationalTwoArithmeticFiniteLocalStage_eq_cyclotomicClosure
      a F n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  apply i.codRestrict (C.toIntermediateField.restrictScalars ℚ).toSubalgebra
  intro x
  change i x ∈ C.toIntermediateField
  rw [← hstage]
  exact IntermediateField.subset_adjoin K (Set.range i) ⟨x, rfl⟩

/-- Codomain restriction preserves the literal original arithmetic value. -/
theorem rationalTwoArithmeticContainingEmbedding_coe (x : F) :
    (rationalTwoArithmeticContainingEmbedding a F n x : rationalPrimeLocalClosure 2 Nat.prime_two) =
      rationalArithmeticLocalEmbedding a (x : rationalUnramifiedExtension a) := rfl

end
end Dubon2026
