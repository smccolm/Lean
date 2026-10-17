import Dubon2026.ArithmeticClassesModOutsideColimit
import Dubon2026.OriginalRelationGroupChange

/-! # Literal arithmetic coefficient comparison through a finite tower

Successive finite Galois restrictions have the same underlying action as
the direct restriction. The identity on coefficient elements gives the
actual comparison of relation presentations required to connect DUB-17's
descended finite obstruction to its original source-class cup.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K)
  (P N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (hPN : P ≤ N)

/-- The direct and successive restriction representations compare by the
literal identity on coefficient elements, with equivariance derived. -/
def arithmeticFiniteRestrictionTowerComparison (A : Rep.{0} ℤ Gal(P/K)) :
    letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
    letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
    letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
    letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
    letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    Rep.res (AlgEquiv.restrictNormalHom N :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(N/K))
      (Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) A) ⟶
    Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) A := by
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
  letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun σ : Gal(P/K) => A.ρ σ x)
        (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P N g).symm }

omit [NumberField K] in
/-- The arithmetic tower comparison preserves the original coefficient value. -/
theorem arithmeticFiniteRestrictionTowerComparison_apply
    (A : Rep.{0} ℤ Gal(P/K)) (x : A) :
    letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
    letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
    letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
    letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
    letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    (arithmeticFiniteRestrictionTowerComparison K Ω a P N hPN A).hom x = x := rfl

/-- The actual identity-on-elements maps give the commuting diagram of
the composed and direct restricted original relation presentations. -/
def arithmeticFiniteRelationTowerDiagram (B : Rep.{0} ℤ Gal(P/K)) :
    letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
    letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
    letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
    letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
    letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
      IsScalarTower.of_algebraMap_eq' rfl
    (originalRelationShortComplex B).map
      (Rep.resFunctor ((AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)).comp
        (AlgEquiv.restrictNormalHom N :
          Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(N/K)))) ⟶
    (originalRelationShortComplex B).map (Rep.resFunctor
      (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K))) := by
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : Module P N := (IntermediateField.inclusion hPN).toAlgebra.toModule
  letI : SMul P N := (IntermediateField.inclusion hPN).toAlgebra.toSMul
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact {
    τ₁ := arithmeticFiniteRestrictionTowerComparison K Ω a P N hPN (originalRelationModule B)
    τ₂ := arithmeticFiniteRestrictionTowerComparison K Ω a P N hPN (Rep.free ℤ Gal(P/K) B)
    τ₃ := arithmeticFiniteRestrictionTowerComparison K Ω a P N hPN B
    comm₁₂ := rfl
    comm₂₃ := rfl }

end
end Dubon2026
