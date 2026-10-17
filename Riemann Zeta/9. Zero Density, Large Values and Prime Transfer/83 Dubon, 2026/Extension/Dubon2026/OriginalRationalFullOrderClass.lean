import Dubon2026.ArithmeticUnrestrictedRationalFullOrder
import Dubon2026.OriginalDegreeOneClassInflation
import Dubon2026.OriginalUnrestrictedNumberFieldRealization

/-! # A constructed original full-order class for every rational Galois field

Realize the actual number field in the unrestricted union, construct its
mixed-degree class there, and descend through the actual degree-one field
realization. This discharges the full-order class assumption at DUB-17's
constructed enlarged stage without changing that stage or its ramification.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The actual original class H2 of every finite Galois number field over
the rationals has a constructed element of full field-degree order. -/
theorem originalRationalNumberField_exists_full_order_class
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ u : groupCohomology (originalIdeleClassRep ℚ K) 2,
      addOrderOf u = Module.finrank ℚ K := by
  obtain ⟨H, hH, ⟨e⟩⟩ := originalNumberField_exists_unrestricted_arithmetic_realization K
  letI : FiniteDimensional ℚ H := hH
  letI : IsGalois ℚ H := IsGalois.of_algEquiv e
  letI : Algebra K H := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K H := IsScalarTower.of_algHom e.toAlgHom
  let ek : K ≃ₐ[K] H := { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : FiniteDimensional K H := Module.Finite.of_surjective ek.toLinearMap ek.surjective
  have hd : Module.finrank K H = 1 := Module.finrank_of_bijective_algebraMap ek.bijective
  obtain ⟨u, hu⟩ := rationalArithmeticUnrestricted_rational_exists_full_order_class H
  exact originalIdeleClass_full_order_descends_degree_one ℚ K H hd u hu

/-- The same full-order construction respects the displayed rational
algebra of the original finite Galois stage. -/
theorem originalRationalNumberField_exists_full_order_class_of_algebra
    (K : Type) [Field K] [NumberField K] [hAlg : Algebra ℚ K] [IsGalois ℚ K] :
    ∃ u : groupCohomology (originalIdeleClassRep ℚ K) 2,
      addOrderOf u = Module.finrank ℚ K := by
  have h : hAlg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  cases h
  exact originalRationalNumberField_exists_full_order_class K

end
end Dubon2026
