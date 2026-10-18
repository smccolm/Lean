import Dubon2026.RationalArithmeticOriginalCompletionRestriction
import Dubon2026.RationalTraceIntegerActionContinuity
import Dubon2026.RationalPrimeTraceUnitCartierDuality
import Dubon2026.ContinuousFiniteCoefficientSplitting
import Dubon2026.FiniteCoefficientGaloisDescent

/-! Descend the original arithmetic trace-zero action to a genuine finite
Galois field and identify its literal local completion action. This is
the coefficient edge of DUB-17's local Cartier cup-total comparison;
neither a splitting field nor a local-action comparison is postulated. -/
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
  rationalOriginalCompletionClosureTower rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- The original arithmetic unramified union is Galois over the rationals. -/
local instance rationalTraceCompletionArithmeticGalois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a

/-- The finite trace coefficient retains its original matrix finiteness. -/
local instance rationalTraceCompletionCoefficientFinite :
    Finite (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))

/-- Retain the topology used by the original continuous matrix action. -/
local instance rationalTraceCompletionCoefficientTopology :
    TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficientTopology a q σ

/-- That original finite coefficient topology is discrete. -/
local instance rationalTraceCompletionCoefficientDiscrete :
    DiscreteTopology (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficient_discrete a q σ

/-- The descended coefficient action at the actual finite completion is
literally the original prime-local integer trace action. -/
theorem rationalTraceFiniteCompletion_action
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hker : ∀ u : rationalArithmeticGaloisGroup a,
      AlgEquiv.restrictNormalHom F u = 1 →
      ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
        (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
    (p : ℕ) (hp : p.Prime)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (x : rationalArithmeticTraceZeroIntegerRep a q σ) :
    finiteStageCoefficientRepresentation (rationalArithmeticTraceZeroIntegerRep a q σ) F hker
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)
        (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
          (rationalPrimeLocalField p hp)
          ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
          (rationalPrimeLocalClosure p hp) g)) x =
      (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ g x := by
  rw [rationalArithmeticOriginalCompletion_galois_restriction]
  exact (finiteStageCoefficientRepresentation_apply
    (rationalArithmeticTraceZeroIntegerRep a q σ) F hker
    (rationalPrimeArithmeticRestriction a p hp g) x).trans
    (DFunLike.congr_fun
      (DFunLike.congr_fun (matrixTraceZeroAdjointRepresentation_comp σ
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom) g) x)

/-- Continuity of the original arithmetic matrix action constructs one
finite Galois coefficient field whose local completion actions agree at
every rational prime with the specified original prime-local trace action. -/
theorem rationalTrace_exists_finiteCompletion_action (hσ : Continuous σ) :
    ∃ F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
    ∃ hker : ∀ u : rationalArithmeticGaloisGroup a,
      AlgEquiv.restrictNormalHom F u = 1 →
      ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
        (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x,
    ∀ (p : ℕ) (hp : p.Prime)
      (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
      (x : rationalArithmeticTraceZeroIntegerRep a q σ),
      finiteStageCoefficientRepresentation (rationalArithmeticTraceZeroIntegerRep a q σ) F hker
        (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)
          (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
            (rationalPrimeLocalField p hp)
            ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F)
            (rationalPrimeLocalClosure p hp) g)) x =
        (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ g x := by
  obtain ⟨F, hF⟩ := continuousFiniteCoefficient_exists_splittingField
    (rationalArithmeticTraceZeroIntegerRep a q σ) (rationalTraceIntegerAction_continuous a q σ hσ)
  have hker (u : rationalArithmeticGaloisGroup a) (hu : AlgEquiv.restrictNormalHom F u = 1)
      (x : rationalArithmeticTraceZeroIntegerRep a q σ) :
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x := by
    apply hF u _ x
    rw [← F.toIntermediateField.restrictNormalHom_ker]
    exact hu
  exact ⟨F, hker, rationalTraceFiniteCompletion_action a q σ F hker⟩

end
end Dubon2026
