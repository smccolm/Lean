import Dubon2026.OriginalClassesModOutsideH2Inflation
import Dubon2026.ArithmeticClassesModOutsideH2Comparison

/-! # Actual arithmetic quotient H2 inflation is injective

The original finite arithmetic stages are unramified outside their fixed
exceptional support. Their proved quotient H2 isomorphisms and full-class
inflation injection therefore reflect zero from the common-stage source
cup comparison to the original scalar obstruction required by DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original rational inclusion of the arithmetic union. -/
local instance classH2InflationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the original rational inclusions of the finite arithmetic fields. -/
local instance classH2InflationStageAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Retain the identical rational inclusion on the underlying intermediate field. -/
local instance classH2InflationIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : IntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Original arithmetic quotient H2 inflation is injective at every finite
Galois enlargement, with all outside-unramified conditions discharged. -/
theorem rationalArithmeticClassesModOutsideH2Inflation_injective
    (E F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    letI : Module E F := Algebra.toModule
    letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
    letI : IsScalarTower ℚ E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
    Function.Injective (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/ℚ) →* Gal(E/ℚ))
      (arithmeticClassesModOutsideFiniteTransition ℚ Ω a ha E F hEF) 2) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower ℚ E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  exact originalClassesModOutsideH2Inflation_injective ℚ E F
    (arithmeticSUnitFiniteStageSupport ℚ Ω a ha E) (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (originalExceptionalIntegerSupport_galoisStable E ℚ a ha)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (arithmeticSPlaceFiniteStage_support ℚ Ω a ha E F hEF)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha E)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

end
end Dubon2026
