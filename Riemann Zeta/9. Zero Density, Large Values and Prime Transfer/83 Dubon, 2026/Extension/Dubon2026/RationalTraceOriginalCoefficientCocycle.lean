import Dubon2026.RationalTraceOriginalLocalAction
import Dubon2026.RationalPrimeTraceIntegerCohomology
import Dubon2026.GaloisTowerLocalUnitRelationCup
import Dubon2026.ContinuousEquivariantCoefficientMap
import Dubon2026.ContinuousRepresentationRestriction
import Dubon2026.ContinuousCohomologyCoefficientCongr
import Dubon2026.ContinuousCocycleOneRestrictionCongr

/-! Transport the original integer trace cocycle to the actual descended
completion coefficient. This is the coefficient input needed to normalize
the DUB-17 Cartier relation cup, retaining its literal matrix values. -/
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

attribute [local instance] localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete
  localRelationCupCoefficientContinuousSMul primeTraceIntegerContinuousSMul

/-- The actual finite coefficient restricted to the original completion group. -/
abbrev rationalTraceOriginalLocalCoefficientRep :=
  Rep.res ((originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
    (rationalArithmeticOriginalPrime a p hp F)).comp
      (AlgEquiv.restrictNormalHom ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) :
        Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ) →*
          Gal((rationalArithmeticOriginalPrime a p hp F).adicCompletion F /
            (rationalOriginalPrimePlace p hp).adicCompletion ℚ)))
    (rationalTraceOriginalFiniteRep a q σ F hker)

/-- Retain the native discrete topology on the restricted finite coefficient. -/
local instance traceOriginalCoefficientTopology :
    TopologicalSpace (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp) := ⊥

/-- The actual restricted finite coefficient topology is discrete. -/
local instance traceOriginalCoefficientDiscrete :
    DiscreteTopology (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp) := ⟨rfl⟩

/-- The original integer scalar action is continuous in this discrete topology. -/
local instance traceOriginalCoefficientContinuousSMul :
    @ContinuousSMul ℤ (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
      (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp).hV2.toSMul
      inferInstance inferInstance := ⟨continuous_of_discreteTopology⟩

/-- The proved pointwise finite action identifies the same original matrix representation. -/
theorem rationalTraceOriginalLocalCoefficientRepresentation_eq :
    (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ.comp
      (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom =
    (show Representation ℤ
      Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))) from
      (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp).ρ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  exact (rationalTraceOriginalCompletion_action a q σ F hker p hp g x).symm

/-- The original prime-local integer cocycle becomes a continuous cocycle
for the actual descended coefficient, with the native discrete target topology. -/
def rationalTraceOriginalCoefficientCocycle
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))) :
    continuousRepresentationCocyclesOne (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp) := by
  let d := continuousCocycleOneRestrictionCongr
    (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp)
    (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp).ρ
    (rationalTraceOriginalLocalCoefficientRepresentation_eq a q σ F hker p hp) c
  refine ⟨⟨fun g => c.val ((rationalOriginalCompletionGaloisEquiv p hp).symm g), ?_⟩, ?_⟩
  · exact d.val.property
  · exact (continuous_of_discreteTopology : @Continuous
      (rationalPrimeTraceZeroIntegerRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
      (rationalPrimeTraceIntegerTopology p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (traceOriginalCoefficientTopology a q σ F hker p hp)
      (fun z : rationalPrimeTraceZeroIntegerRep p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp)) =>
          (z : rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp))).comp
      (c.property.comp (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp))

/-- No matrix value changes under the actual completion-group comparison. -/
theorem rationalTraceOriginalCoefficientCocycle_apply
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))))
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) :
    (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c).val g =
      c.val ((rationalOriginalCompletionGaloisEquiv p hp).symm g) := rfl

end
end Dubon2026

