import Dubon2026.ArithmeticPrimeRestrictedUnitHomContinuity
import Dubon2026.ContinuousShortComplexInvariantConnecting

/-! The actual local unit connecting class of the finite arithmetic relation
presentation. This packages the stage used on both sides of the existing
field-tower map in DUB-17's recovery of prescribed local classes. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (B : Rep.{0} ℤ Gal(F/ℚ)) (p : ℕ) (hp : p.Prime)

/-- The original finite relation presentation restricted to the actual prime. -/
abbrev arithmeticPrimeLocalRelationPresentation :
    ShortComplex (Rep ℤ Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :=
  let π : rationalArithmeticGaloisGroup a →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  { X₁ := Rep.res (π.comp j) (originalRelationModule B)
    X₂ := Rep.res (π.comp j) (Rep.free ℤ Gal(F/ℚ) B)
    X₃ := Rep.res (π.comp j) B
    f := (Rep.resFunctor (π.comp j)).map (originalRelationInclusion B)
    g := (Rep.resFunctor (π.comp j)).map (originalRelationFreeCover B)
    zero := ((originalRelationShortComplex B).map (Rep.resFunctor (π.comp j))).zero }

/-- Dualize the actual prime presentation with its original local units. -/
abbrev arithmeticPrimeLocalUnitDualSequence :=
  originalContravariantHomShortComplex (arithmeticPrimeLocalRelationPresentation a F B p hp)
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))

/-- The actual prime dual presentation is exact by local unit divisibility. -/
theorem arithmeticPrimeLocalUnitDualSequence_shortExact
    (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0) :
    (arithmeticPrimeLocalUnitDualSequence a F B p hp).ShortExact :=
  galoisUnitRelationDualSequence_shortExact
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) Gal(F/ℚ)
    ((AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) q B hCoeff

/-- The local connecting class of the original relation invariant;
continuity and dual exactness are proved for this arithmetic stage. -/
def arithmeticPrimeLocalUnitDualConnecting [Finite B]
    (q : ℕ) [Fact q.Prime] (hCoeff : ∀ b : B, q • b = 0) :
    let Y := arithmeticPrimeLocalUnitDualSequence a F B p hp
    letI : Module.Finite ℤ B := Module.Finite.of_finite
    letI : TopologicalSpace Y.X₁ := ⊥
    letI : DiscreteTopology Y.X₁ := ⟨rfl⟩
    letI : @ContinuousSMul ℤ Y.X₁ Y.X₁.hV2.toSMul inferInstance inferInstance :=
      @ContinuousSMul.mk ℤ Y.X₁ Y.X₁.hV2.toSMul _ _ continuous_of_discreteTopology
    Y.X₃.ρ.invariants →ₗ[ℤ] ContinuousRepresentationH1 Y.X₁
      (arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp) := by
  let Y := arithmeticPrimeLocalUnitDualSequence a F B p hp
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
  exact continuousShortComplexInvariantConnectingMap Y
    (arithmeticPrimeLocalUnitDualSequence_shortExact a F B p hp q hCoeff)
    (arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp)
    (arithmeticPrimeRestrictedUnitHomAction_continuous a F (Rep.free ℤ Gal(F/ℚ) B) p hp)

end
end Dubon2026
