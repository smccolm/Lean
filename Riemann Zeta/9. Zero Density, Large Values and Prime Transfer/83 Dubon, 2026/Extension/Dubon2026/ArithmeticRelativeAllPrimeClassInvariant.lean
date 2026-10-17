import Dubon2026.ArithmeticRelativeAllPrimeFullOrderClass
import Dubon2026.OriginalClassInvariantOnInfiniteKernel

/-! # Actual all-prime class invariants on the zero-infinite part

Apply the original exact-kernel invariant theorem to the constructed
arithmetic witness and the fully proved arithmetic principal kernel.
The resulting invariant identifies finite total with class projection on
the exact zero-infinite part needed by DUB-17's auxiliary tower transfer.
No arbitrary-real-coordinate total formula is claimed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual cyclic prime-power stage has a constructed injective class
invariant with exact image and the finite-total formula on original ideles
with zero infinite localization, for every allowed prime including two. -/
theorem rationalArithmeticRelativeStage_exists_prime_power_invariant_on_infinite_kernel
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ invG : groupCohomology (originalIdeleClassRep F H) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ q ^ (r + 1) • t = 0) ∧
      ∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
        (∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) →
        invG ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  exact originalIdeleClass_exists_invariant_on_infinite_kernel F H (q ^ (r + 1)) hdegree
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativeStageIdeleTotalInvariant_principal_of_infinite a F H hFH q r hq hqa hdegree)
    (rationalArithmeticRelativeStage_exists_normalized_idele_total_infinite_zero
      a F H hFH q r hq hcyclic hdegree)

/-- On the original zero-infinite part, zero finite total detects exactly
zero actual class projection for all allowed primes. -/
theorem rationalArithmeticRelativeStage_class_zero_iff_total_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      (∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) →
      ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x = 0 ↔
        rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  obtain ⟨invG, hInj, _, hTotal⟩ := rationalArithmeticRelativeStage_exists_prime_power_invariant_on_infinite_kernel
    a F H hFH q r hq hqa hcyclic hdegree
  intro x hi
  rw [← hTotal x hi]
  exact (map_eq_zero_iff invG hInj).symm

end
end Dubon2026
