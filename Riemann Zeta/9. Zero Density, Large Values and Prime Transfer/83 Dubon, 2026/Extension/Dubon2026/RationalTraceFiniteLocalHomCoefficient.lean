import Dubon2026.ArithmeticPrimeUnitDualConnecting
import Dubon2026.RationalTraceFiniteSUnitDualClass
import Dubon2026.RationalPrimeTraceUnitCohomology

/-! Identify the actual finite-stage local Hom coefficient with the
original prime-local trace Hom. This is the coefficient edge connecting
the global finite S-unit class to prescribed local trace classes in DUB-17. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois


variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)


/-- The actual restricted finite trace coefficient with its prime-local units. -/
abbrev rationalTraceFiniteLocalHomRep :=
  arithmeticPrimeRestrictedUnitHom a F (rationalTraceOriginalFiniteRep a q σ F hker) p hp

/-- The identification preserves every original linear function value. -/
def rationalTraceFiniteLocalHomCoefficientEquiv :
    rationalTraceFiniteLocalHomRep a q σ F hker p hp ≃+
      rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)) :=
  AddEquiv.refl _

/-- The actual finite restriction and original prime-local trace actions
agree under the literal coefficient identification. -/
theorem rationalTraceFiniteLocalHomCoefficientEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (f : rationalTraceFiniteLocalHomRep a q σ F hker p hp) :
    rationalTraceFiniteLocalHomCoefficientEquiv a q σ F hker p hp
      ((rationalTraceFiniteLocalHomRep a q σ F hker p hp).ρ g f) =
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ g
        (rationalTraceFiniteLocalHomCoefficientEquiv a q σ F hker p hp f) := by
  apply LinearMap.ext
  intro x
  let D := Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
  let f' : rationalArithmeticTraceZeroIntegerRep a q σ →ₗ[ℤ] D := f
  let j := rationalPrimeArithmeticRestriction a p hp
  change D.ρ g (f' (finiteStageCoefficientRepresentation
    (rationalArithmeticTraceZeroIntegerRep a q σ) F hker
      (AlgEquiv.restrictNormalHom F (j g⁻¹)) x)) =
    D.ρ g (f' ((rationalPrimeTraceZeroIntegerRep p hp q (σ.comp j)).ρ g⁻¹ x))
  exact congrArg (fun z => D.ρ g (f' z))
    (finiteStageCoefficientRepresentation_apply
      (rationalArithmeticTraceZeroIntegerRep a q σ) F hker (j g⁻¹) x |>.trans
      (DFunLike.congr_fun
        (DFunLike.congr_fun (matrixTraceZeroAdjointRepresentation_comp σ j.toMonoidHom) g⁻¹) x))

end
end Dubon2026
