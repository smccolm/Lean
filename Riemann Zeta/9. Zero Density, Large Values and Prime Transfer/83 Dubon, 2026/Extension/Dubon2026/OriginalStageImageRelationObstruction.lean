import Dubon2026.OriginalRelationObstructionGroupEquiv
import Dubon2026.ArithmeticOriginalRelationClassTransport
import Dubon2026.ArithmeticOriginalStageClassColimit

/-! Carry the zero relation obstruction from the actual finite image in
the unramified union to the same original ambient field. This joins
DUB-17's rational Cartier total criterion to its constructed original
relation-extension criterion without transporting a new class-field theory. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] relationTransportUnionAlgebra relationTransportStageAlgebra

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)
  (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)

/-- The literal image equivalence carries an obstruction-free relation
to the original constructed arithmetic field through the native class
transition. The actual Galois map is proved bijective. -/
theorem arithmeticOriginalStageImage_relation_obstruction_zero
    (B : Rep.{0} ℤ Gal(originalUnramifiedStageInUnion a N / ℚ))
    (φ : originalRelationModule B ⟶
      arithmeticClassesModOutsideStageRep ℚ Ω a ha (originalUnramifiedStageInUnion a N))
    (hφ : originalRelationExtensionObstruction B
      (arithmeticClassesModOutsideStageRep ℚ Ω a ha (originalUnramifiedStageInUnion a N)) φ = 0) :
    let e := originalUnramifiedStageInUnionEquiv a N
    let BN := arithmeticOriginalStageRestrictedCoefficient Ω a
      (originalUnramifiedStageInUnion a N) N e.symm.toAlgHom B
    originalRelationExtensionObstruction BN (arithmeticOriginalStageClassRep Ω a ha N)
      (arithmeticOriginalStageRelationClassTransport Ω a ha
        (originalUnramifiedStageInUnion a N) N e.symm.toAlgHom B φ) = 0 := by
  let M := originalUnramifiedStageInUnion a N
  let e := originalUnramifiedStageInUnionEquiv a N
  letI : Algebra M N.val := e.symm.toAlgHom.toAlgebra
  letI : Module M N.val := e.symm.toAlgHom.toAlgebra.toModule
  letI : SMul M N.val := e.symm.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ M N.val := IsScalarTower.of_algHom e.symm.toAlgHom
  let π : Gal(N.val/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  have hπ : (π : Gal(N.val/ℚ) → Gal(M/ℚ)) = e.autCongr := by
    funext σ
    apply AlgEquiv.ext
    intro x
    apply e.symm.injective
    change e.symm (π σ x) = e.symm (e (σ (e.symm x)))
    rw [e.symm_apply_apply]
    exact σ.restrictNormal_commutes M x
  let g := MulEquiv.ofBijective π (hπ ▸ e.autCongr.bijective)
  let C := arithmeticClassesModOutsideStageRep ℚ Ω a ha M
  let D := arithmeticOriginalStageClassRep Ω a ha N
  let j : Rep.res π C ⟶ D := originalRationalExceptionalClassTransition M N.val a ha
  exact originalRelationExtensionObstruction_zero_of_groupEquiv g B C D φ j hφ

end
end Dubon2026
