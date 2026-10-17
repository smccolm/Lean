import Dubon2026.ArithmeticRelativeAllPrimeClassInvariant

/-! # Full order of the actual class with normalized total

Use the proved injective original class invariant to compute the order
of a specified class. This preserves DUB-17's chosen auxiliary witness
while passing from its normalized total to its generator property.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The original class of the same normalized full-idele witness has exactly the original cyclic extension degree as its additive order. -/
theorem rationalArithmeticRelativeStage_class_order_of_normalized_total_infinite_zero
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (hx : rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
      (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)))
    (hInf : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      ∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    addOrderOf ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
      q ^ (r + 1) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  obtain ⟨invG, hi, _, ht⟩ := rationalArithmeticRelativeStage_exists_prime_power_invariant_on_infinite_kernel
    a F H hFH q r hq hqa hcyclic hdegree
  calc
    _ = addOrderOf (invG ((groupCohomology.functor ℤ Gal(H/F) 2).map
        (originalFullClassRepHom F H) x)) := (addOrderOf_injective invG hi _).symm
    _ = q ^ (r + 1) := by
      rw [ht x hInf, hx]
      letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
      exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (pow_pos hq.pos (r + 1))

end
end Dubon2026
