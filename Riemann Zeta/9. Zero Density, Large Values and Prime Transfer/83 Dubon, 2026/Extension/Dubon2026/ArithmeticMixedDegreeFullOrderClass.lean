import Dubon2026.ArithmeticMixedDegreePrimaryClass
import Dubon2026.FiniteFullOrderFromPrimePowers

/-! # Construct a full-order class at a mixed-degree arithmetic stage

Each required primary order is constructed by the existing prime-power
auxiliary fields. The finite abelian exponent theorem combines them without
postulating compatibility or a generator. This discharges the mixed-degree
class hypothesis for DUB-17 once the actual stage is placed in the unrestricted
union; field-realization comparison remains explicit in the downstream step.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- A finite Galois stage has an original full-order class when all prime
divisors of its degree are allowed in the ambient arithmetic union. -/
theorem rationalArithmeticRelativeStage_exists_mixed_degree_full_order_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (hallowed : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      ∀ q : ℕ, q.Prime → q ∣ Module.finrank K E → (q : 𝓞 ℚ) ∣ a) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ x : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf x = Module.finrank K E := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  obtain ⟨hf, hc⟩ := originalIdeleClass_finiteGalois_second_card_dvd K E
  letI := hf
  apply finiteAddCommGroup_exists_full_order_of_prime_powers _ _ hc
  intro q t hq hd
  by_cases ht : t = 0
  · exact ⟨0, by simp [ht]⟩
  · exact rationalArithmeticRelativeStage_exists_prime_power_order_class
      a K E hKE q t hq (hallowed q hq ((dvd_pow_self q ht).trans hd)) hd

/-- Every finite Galois relative stage in the unrestricted arithmetic union
has a constructed original class of its full extension-degree order. -/
theorem rationalArithmeticUnrestricted_exists_full_order_class
    (K E : IntermediateField ℚ (rationalUnramifiedExtension 0))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E] :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ x : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf x = Module.finrank K E :=
  rationalArithmeticRelativeStage_exists_mixed_degree_full_order_class
    0 K E hKE (fun _ _ _ => dvd_zero _)

end
end Dubon2026
