import Dubon2026.OriginalGaloisRestrictionTowerIso
import Dubon2026.RationalTraceFiniteTowerAction

/-! The actual field-tower identity gives the literal unit-Hom
coefficient comparison, both globally and after original-prime restriction.
This is the fixed-carrier coefficient step used to construct and localize
DUB-17's global class directly from the returned finite correction. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  rationalTraceCompletionArithmeticGalois rationalArithmeticOriginalFiniteGalois
variable (a : 𝓞 ℚ)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)
  (B : Rep.{0} ℤ Gal(M/ℚ))
  {P : Type} [Group P] (j : P →* rationalArithmeticGaloisGroup a) (D : Rep.{0} ℤ P)

/-- The tower coefficient comparison preserves every literal linear map. -/
def arithmeticUnitHomTowerCoefficientEquiv :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let πM : rationalArithmeticGaloisGroup a →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let πL : rationalArithmeticGaloisGroup a →* Gal(L/ℚ) := AlgEquiv.restrictNormalHom L
    let UL := (Rep.ihom (Rep.res (πL.comp j) (Rep.res τ B))).obj D
    let UM := (Rep.ihom (Rep.res (πM.comp j) B)).obj D
    UL ≃+ UM := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let πM : rationalArithmeticGaloisGroup a →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let πL : rationalArithmeticGaloisGroup a →* Gal(L/ℚ) := AlgEquiv.restrictNormalHom L
  let UL := (Rep.ihom (Rep.res (πL.comp j) (Rep.res τ B))).obj D
  let UM := (Rep.ihom (Rep.res (πM.comp j) B)).obj D
  exact AddEquiv.refl _

/-- The proved original Galois restriction-composition identity makes
the same coefficient map equivariant for either actual restriction. -/
theorem arithmeticUnitHomTowerCoefficientEquiv_equivariant :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
    letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
    let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let πM : rationalArithmeticGaloisGroup a →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
    let πL : rationalArithmeticGaloisGroup a →* Gal(L/ℚ) := AlgEquiv.restrictNormalHom L
    let UL := (Rep.ihom (Rep.res (πL.comp j) (Rep.res τ B))).obj D
    let UM := (Rep.ihom (Rep.res (πM.comp j) B)).obj D
    ∀ (g : P) (f : UL),
    arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D (UL.ρ g f) =
      UM.ρ g (arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D f) := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
  letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
  let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let πM : rationalArithmeticGaloisGroup a →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  let πL : rationalArithmeticGaloisGroup a →* Gal(L/ℚ) := AlgEquiv.restrictNormalHom L
  let UL := (Rep.ihom (Rep.res (πL.comp j) (Rep.res τ B))).obj D
  let UM := (Rep.ihom (Rep.res (πM.comp j) B)).obj D
  letI : IsScalarTower ℚ M L := IsScalarTower.of_algHom (IntermediateField.inclusion hML)
  letI : IsScalarTower M L (rationalUnramifiedExtension a) := IsScalarTower.of_algebraMap_eq' rfl
  change ∀ (g : P) (f : UL),
    arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D (UL.ρ g f) =
      UM.ρ g (arithmeticUnitHomTowerCoefficientEquiv a M L hML B j D f)
  intro g f
  let f' : B →ₗ[ℤ] D := f
  apply LinearMap.ext
  intro x
  change D.ρ g (f' (B.ρ (τ (πL (j g⁻¹))) x)) = D.ρ g (f' (B.ρ (πM (j g⁻¹)) x))
  exact congrArg (fun v : Gal(M/ℚ) => D.ρ g (f' (B.ρ v x)))
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply M L (j g⁻¹)).symm

end
end Dubon2026
