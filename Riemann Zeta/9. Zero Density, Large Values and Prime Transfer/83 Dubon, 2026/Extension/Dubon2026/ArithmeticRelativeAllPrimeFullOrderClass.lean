import Dubon2026.ArithmeticRelativePrimePowerPrincipalKernel
import Dubon2026.ArithmeticRelativeNormalizedTotalInfiniteKernel
import Dubon2026.OriginalClassFullOrderFromInfiniteKernel

/-! # A full-order original cyclic class for every allowed prime

The same normalized finite-idele witness has zero original infinite
localizations. The proved all-prime principal kernel therefore detects
its exact class order using the original class-card bound. No generator,
principal-kernel certificate or real comparison is supplied. This removes
the prime-two obstruction at DUB-17's actual relative cyclic stage; transfer
to an arbitrary original enlarged stage remains a separate obligation.
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

/-- The actual cyclic prime-power stage has a constructed normalized
original idele witness whose class image has full degree order, including
the prime two, with its original infinite vanishing retained. -/
theorem rationalArithmeticRelativeStage_exists_prime_power_full_order_idele
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
        (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      (∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) ∧
      addOrderOf ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
        q ^ (r + 1) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  obtain ⟨x, hx, hi⟩ := rationalArithmeticRelativeStage_exists_normalized_idele_total_infinite_zero
    a F H hFH q r hq hcyclic hdegree
  refine ⟨x, hx, hi, ?_⟩
  have hn : rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
      (↑((1 : ℚ) / Module.finrank F H) : AddCircle (1 : ℚ)) := by
    simpa only [hdegree] using hx
  exact (originalIdeleClass_full_order_of_infinite_kernel F H
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativeStageIdeleTotalInvariant_principal_of_infinite a F H hFH q r hq hqa hdegree)
    x hn hi).trans hdegree

end
end Dubon2026
