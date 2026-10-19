import Dubon2026.ArithmeticFiniteSUnitLocalH1Map
import Dubon2026.ArithmeticFiniteSUnitPrincipalInvariant
import Dubon2026.ArithmeticPrimeUnitDualConnecting

/-! Localizing the actual finite S-unit connecting class gives the
connecting class of its principal S-place image. This joins the direct
global construction to the existing free-correction removal in DUB-17. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalExceptionalIndexedPrimeLiesOver

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : rationalArithmeticExceptionalPrimes a ha)

variable (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B]

attribute [local instance] arithmeticLocalConnectingAlgebraicClosure
variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (hCoeff : ∀ b : B, q • b = 0)
  (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)

/-- The exact localization-to-principal connecting identity. -/
abbrev ArithmeticFiniteSUnitPrincipalConnectingCompatibility : Prop :=
    let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp j
    let φ := (Rep.resFunctor π).map
      (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫
        rationalArithmeticSPlaceLocalMorphism a ha F p
    arithmeticFiniteSUnitLocalH1Map a ha F B p.val.val p.val.property
      (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa F B hCoeff η) =
      arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff
        ((Representation.linHom.invariantsEquivRepHom _ _).symm φ)

/-- The actual finite global connecting class localizes to the principal
S-place relation, using native connecting naturality and exact principal values. -/
theorem arithmeticFiniteSUnitLocalH1Map_connecting_principal :
    ArithmeticFiniteSUnitPrincipalConnectingCompatibility a ha F p B q hqa hCoeff η := by
  let j := (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp j
  let φ := (Rep.resFunctor π).map
    (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫
      rationalArithmeticSPlaceLocalMorphism a ha F p
  let d := arithmeticFiniteSUnitLocalDualDiagram a ha F B p.val.val p.val.property
  let Y := arithmeticPrimeLocalUnitDualSequence a F B p.val.val p.val.property
  let w := arithmeticFiniteSUnitRelationInvariant ℚ (AlgebraicClosure ℚ) a ha F B η
  let wZ : Y.X₃.ρ.invariants := ⟨d.τ₃.hom w.val, fun g =>
    (Rep.hom_comm_apply d.τ₃ g w.val).symm.trans (congrArg d.τ₃.hom (w.property (j g)))⟩
  have hw : wZ = (Representation.linHom.invariantsEquivRepHom _ _).symm φ :=
    Subtype.ext (arithmeticFiniteSUnitRelationInvariant_local_principal a ha F p B η)
  have h : arithmeticFiniteSUnitLocalH1Map a ha F B p.val.val p.val.property
      (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa F B hCoeff η) =
      arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff wZ :=
    arithmeticFiniteSUnitDualConnectingClass_local a ha q hqa F B hCoeff p.val.val p.val.property η
  exact h.trans (congrArg
    (arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff) hw)

end
end Dubon2026
