import Dubon2026.ArithmeticFiniteSUnitLocalCorrection

/-! Remove the actual finite free correction in the original local
connecting H1. This is the correction-removal consumer required for
DUB-17's prescribed local recovery; all dual exactness and continuity
inputs are derived from the original finite coefficient and local units. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B]
  (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0)
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- Exact removal of the actual finite correction at the original prime. -/
abbrev ArithmeticFiniteSUnitLocalCorrectionCompatibility : Prop :=
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom;
    let J := rationalArithmeticSPlaceLocalMorphism a ha F p;
    ∀ (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
      (l : Rep.free ℤ Gal(F/ℚ) B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
      (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F),
      η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F =
        φ - originalRelationInclusion B ≫ l →
    let φp := (Rep.resFunctor π).map φ ≫ J
    let ηp := (Rep.resFunctor π).map
      (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫ J
    arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff
      ((Representation.linHom.invariantsEquivRepHom _ _).symm ηp) =
    arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff
      ((Representation.linHom.invariantsEquivRepHom _ _).symm φp)

/-- The localized finite free correction does not change the actual
original local dual connecting H1 class. -/
theorem arithmeticFiniteSUnitCorrection_local_connecting :
    ArithmeticFiniteSUnitLocalCorrectionCompatibility a ha F B q hCoeff p := by
  let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
    (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
  let X := arithmeticPrimeLocalRelationPresentation a F B p.val.val p.val.property
  let D := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p.val.val p.val.property)
    (rationalPrimeLocalClosure p.val.val p.val.property)
  let Y := arithmeticPrimeLocalUnitDualSequence a F B p.val.val p.val.property
  let J := rationalArithmeticSPlaceLocalMorphism a ha F p
  letI : Module.Finite ℤ B := Module.Finite.of_finite
  letI : Module.Finite ℤ (Rep.free ℤ Gal(F/ℚ) B) := by
    change Module.Finite ℤ (B →₀ Gal(F/ℚ) →₀ ℤ)
    infer_instance
  letI : TopologicalSpace Y.X₁ := ⊥
  letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
  letI : TopologicalSpace Y.X₂ := ⊥
  letI : DiscreteTopology Y.X₂ := ⟨rfl⟩
  letI : @ContinuousSMul ℤ Y.X₁ Y.X₁.hV2.toSMul inferInstance inferInstance :=
    @ContinuousSMul.mk ℤ Y.X₁ Y.X₁.hV2.toSMul _ _ continuous_of_discreteTopology
  let hU := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p.val.val p.val.property
  let hV := arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p.val.val p.val.property
  let hY := arithmeticPrimeLocalUnitDualSequence_shortExact a F B p.val.val p.val.property q hCoeff
  change ∀ φ l η, _
  intro φ l η hη
  exact originalDualConnecting_eq_of_free_correction X D hY hU hV
    ((Rep.resFunctor π).map
      (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫ J)
    ((Rep.resFunctor π).map φ ≫ J) ((Rep.resFunctor π).map l ≫ J)
    (arithmeticFiniteSUnitCorrection_local_relation a ha F B p φ l η hη)

end
end Dubon2026
