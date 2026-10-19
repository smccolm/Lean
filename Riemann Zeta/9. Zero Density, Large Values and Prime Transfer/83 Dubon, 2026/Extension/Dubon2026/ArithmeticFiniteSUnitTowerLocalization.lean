import Dubon2026.ArithmeticFiniteSUnitLocalH1Map
import Dubon2026.ArithmeticFiniteSUnitHomTowerH1
import Dubon2026.ArithmeticPrimeUnitHomTowerH1

/-! Global and prime-local tower identifications commute with the actual
arithmetic S-unit localization. This sends DUB-17's direct finite-correction
class to the same local connecting class before applying correction removal. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois arithmeticUnitMapAlgebra
variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ)) [Finite B] (p : ℕ) (hp : p.Prime)

/-- The exact actual global/local tower localization square. -/
abbrev ArithmeticFiniteSUnitTowerLocalizationCompatibility : Prop :=
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let BL := Rep.res τ B
    letI : Finite BL := inferInstanceAs (Finite B)
    ∀ x : ArithmeticFiniteSUnitHomH1 a ha L BL,
    arithmeticFiniteSUnitLocalH1Map a ha M B p hp
      (arithmeticFiniteSUnitHomTowerH1Equiv a ha M L hML B x) =
    arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p hp
      (arithmeticFiniteSUnitLocalH1Map a ha L BL p hp x)

/-- The original arithmetic localization preserves the literal tower H1 identification. -/
theorem arithmeticFiniteSUnitTowerH1_localization :
    ArithmeticFiniteSUnitTowerLocalizationCompatibility a ha M L hML B p hp := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let BL := Rep.res τ B
  letI : Finite BL := inferInstanceAs (Finite B)
  change ∀ x : ArithmeticFiniteSUnitHomH1 a ha L BL,
    arithmeticFiniteSUnitLocalH1Map a ha M B p hp
      (arithmeticFiniteSUnitHomTowerH1Equiv a ha M L hML B x) =
    arithmeticPrimeUnitHomTowerH1Equiv a M L hML B p hp
      (arithmeticFiniteSUnitLocalH1Map a ha L BL p hp x)
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro b
    rfl

end
end Dubon2026
