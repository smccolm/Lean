import Dubon2026.RationalTwoArithmeticContainingEmbedding
import Dubon2026.RationalTwoArithmeticSubfieldRestriction

/-! # Restriction through the original global cyclotomic containing field

The original containing-field embedding and the actual local-stage embedding
agree on the global cyclic subfield. Restriction through either route gives
the same original automorphism. This is the conductor-two comparison needed
before DUB-17's global principal automorphism product can be assembled.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

/-- Use the module induced by the same rational algebra on the original
completion, avoiding competing completion scalar inference. -/
local instance twoPrimaryContainingRestrictionPrimeModule :
    Module ℚ (rationalPrimeLocalField 2 Nat.prime_two) := Algebra.toModule

variable (a : 𝓞 ℚ)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]

/-- Restrict the same local cyclotomic automorphism to the actual global
containing field through its original arithmetic embedding. -/
def rationalTwoArithmeticContainingRestriction :
    Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one /
      rationalPrimeLocalField 2 Nat.prime_two) →* Gal(F/ℚ) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
    (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  letI : Algebra K C := C.toIntermediateField.algebra'
  letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
  exact embeddedNormalGaloisRestriction (F := K) (rationalTwoArithmeticContainingEmbedding a F n)

/-- The containing-field and local-subfield embeddings give the same
element of the canonical local cyclotomic field on every original element. -/
theorem rationalTwoArithmeticContainingEmbedding_subfield
    (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) (x : E) :
    let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
    let hM : M.toIntermediateField ≤ C.toIntermediateField :=
      rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
        a E F hEF n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
    rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF x) =
      IntermediateField.inclusion hM (rationalArithmeticFiniteLocalStageInclusion a E 2 Nat.prime_two x) := by
  apply Subtype.ext
  rfl

variable
    (E : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (σ : Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
      (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one /
      rationalPrimeLocalField 2 Nat.prime_two))

/-- Restriction through the containing field commutes with the same
original embedded subfield element. -/
private theorem twoPrimaryContaining_path_commutes (x : E) :
    rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF
      (embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
        (rationalTwoArithmeticContainingRestriction a F n σ) x)) =
      σ (rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF x)) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
    (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  letI : Algebra K C := C.toIntermediateField.algebra'
  letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
  let i : E →ₐ[ℚ] F := IntermediateField.inclusion hEF
  let j : F →ₐ[ℚ] C := rationalTwoArithmeticContainingEmbedding a F n
  have hleft₁ := embeddedNormalGaloisRestriction_commutes i
    (rationalTwoArithmeticContainingRestriction a F n σ) x
  have hleft₂ := embeddedNormalGaloisRestriction_commutes j σ (i x)
  exact (congrArg j hleft₁).trans hleft₂

/-- The original local-subfield restriction commutes through that same
containing-field embedding, by the proved equality of embedded values. -/
private theorem twoPrimarySubfield_path_commutes (x : E) :
    rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF
      (rationalTwoArithmeticSubfieldRestriction a E F hEF n σ x)) =
      σ (rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF x)) := by
  have h := rationalTwoArithmeticSubfieldRestriction_commutes a E F hEF n σ x
  change rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF
    (rationalTwoArithmeticSubfieldRestriction a E F hEF n σ x)) =
    σ (rationalTwoArithmeticContainingEmbedding a F n (IntermediateField.inclusion hEF x)) at h
  exact h

/-- Restricting through the actual global containing field is identical to
the already constructed original arithmetic subfield restriction. -/
theorem rationalTwoArithmeticContainingRestriction_subfield :
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
        (rationalTwoArithmeticContainingRestriction a F n σ) =
      rationalTwoArithmeticSubfieldRestriction a E F hEF n σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1
    (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  letI : Algebra K C := C.toIntermediateField.algebra'
  letI : Algebra ℚ C := (C.toIntermediateField.restrictScalars ℚ).algebra'
  let i : E →ₐ[ℚ] F := IntermediateField.inclusion hEF
  let j : F →ₐ[ℚ] C := rationalTwoArithmeticContainingEmbedding a F n
  apply AlgEquiv.ext
  intro x
  apply i.injective
  apply j.injective
  exact (twoPrimaryContaining_path_commutes a F n E hEF σ x).trans
    (twoPrimarySubfield_path_commutes a F n E hEF σ x).symm

end
end Dubon2026
