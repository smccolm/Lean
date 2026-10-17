import Dubon2026.RationalTwoArithmeticCyclotomicContainingStage

/-! # The literal conductor-two restriction to the original arithmetic subfield

The two proved inclusions define the actual restriction from the canonical
local cyclotomic field through the arithmetic completion to the original
global subfield. Its commutation law uses the original embedding on every
field element, preparing DUB-17's global principal-product comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)
    (n : ℕ) [IsCyclotomicExtension {2 ^ (n + 1)} ℚ F]

/-- The actual local cyclotomic restriction, using the reference natural unit
one and the proved containment of the original arithmetic completion. -/
def rationalTwoArithmeticSubfieldRestriction :
    Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
      Nat.prime_two.not_dvd_one / rationalPrimeLocalField 2 Nat.prime_two) →* Gal(E/ℚ) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
    Nat.prime_two.not_dvd_one
  let hM : M.toIntermediateField ≤ C.toIntermediateField :=
    rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
      a E F hEF n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  let i : M →ₐ[K] C := IntermediateField.inclusion hM
  exact (rationalArithmeticFiniteLocalRestriction a E 2 Nat.prime_two).comp
    (embeddedNormalGaloisRestriction (F := K) i)

/-- On each original field element, the composed restriction agrees with
the same local cyclotomic automorphism through the unchanged embedding. -/
theorem rationalTwoArithmeticSubfieldRestriction_commutes
    (σ : Gal(rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
      Nat.prime_two.not_dvd_one / rationalPrimeLocalField 2 Nat.prime_two)) (x : E) :
    let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
    let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
      Nat.prime_two.not_dvd_one
    let hM : M.toIntermediateField ≤ C.toIntermediateField :=
      rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
        a E F hEF n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
    let i := IntermediateField.inclusion hM
    i (rationalArithmeticFiniteLocalStageInclusion a E 2 Nat.prime_two
        (rationalTwoArithmeticSubfieldRestriction a E F hEF n σ x)) =
      σ (i (rationalArithmeticFiniteLocalStageInclusion a E 2 Nat.prime_two x)) := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let M := rationalArithmeticFiniteLocalStage a E 2 Nat.prime_two
  let C := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n 1 1 (by simp only [Units.val_one, Nat.cast_one])
    Nat.prime_two.not_dvd_one
  let hM : M.toIntermediateField ≤ C.toIntermediateField :=
    rationalTwoArithmeticFiniteLocalStage_le_cyclotomicClosure
      a E F hEF n 1 1 (by simp only [Units.val_one, Nat.cast_one]) Nat.prime_two.not_dvd_one
  let i : M →ₐ[K] C := IntermediateField.inclusion hM
  let j := rationalArithmeticFiniteLocalStageInclusion a E 2 Nat.prime_two
  let τ := embeddedNormalGaloisRestriction (F := K) i σ
  have hj := embeddedNormalGaloisRestriction_commutes j τ x
  exact (congrArg i hj).trans (embeddedNormalGaloisRestriction_commutes i σ (j x))

end
end Dubon2026
