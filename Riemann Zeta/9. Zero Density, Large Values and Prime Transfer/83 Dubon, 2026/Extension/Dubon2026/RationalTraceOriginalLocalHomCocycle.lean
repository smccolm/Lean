import Dubon2026.RationalTraceOriginalLocalAction
import Dubon2026.ContinuousEquivariantCoefficientMap
import Dubon2026.ContinuousRepresentationRestriction
import Dubon2026.ContinuousCohomologyCoefficientCongr
import Dubon2026.ContinuousCocycleOneRestrictionCongr

/-! Transport the actual prime-local Cartier Hom cocycle through the
proved continuous completion-group equivalence into the original finite
relation coefficient. Literal values are retained for DUB-17's cup sum. -/
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

/-- The descended coefficient has the same finite matrix carrier. -/
local instance traceOriginalFiniteRepFinite : Finite (rationalTraceOriginalFiniteRep a q σ F hker) :=
  inferInstanceAs (Finite (matrixTraceZeroSubmodule ι (ZMod q)))


/-- The actual local Hom coefficient consumed by the original finite relation. -/
abbrev rationalTraceOriginalLocalHomRep :
    Rep.{0} ℤ Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ) :=
  originalAdicLocalCoefficientUnitHom ℚ F (rationalOriginalPrimePlace p hp)
    (rationalArithmeticOriginalPrime a p hp F) (rationalPrimeLocalClosure p hp)
    (rationalTraceOriginalFiniteRep a q σ F hker)

variable [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
  (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
  (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]

/-- Integer multiplication is continuous on the original discrete Cartier Hom. -/
local instance traceOriginalSourceHomContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Retain the original discrete topology on the finite-relation Hom. -/
local instance traceOriginalTargetHomTopology :
    TopologicalSpace (rationalTraceOriginalLocalHomRep a q σ F hker p hp) :=
  inferInstanceAs (TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))))

/-- The original Hom coefficient is discrete. -/
local instance traceOriginalTargetHomDiscrete :
    DiscreteTopology (rationalTraceOriginalLocalHomRep a q σ F hker p hp) :=
  inferInstanceAs (DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))))

/-- Integer multiplication is continuous on the original target Hom. -/
local instance traceOriginalTargetHomContinuousSMul :
    @ContinuousSMul ℤ (rationalTraceOriginalLocalHomRep a q σ F hker p hp)
      (rationalTraceOriginalLocalHomRep a q σ F hker p hp).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

omit [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
  (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
  (σ.comp (rationalPrimeArithmeticRestriction a p hp)))] in
/-- The coefficient action equality retains the same original unit Hom
carrier, so native continuous cohomology congruence applies directly. -/
theorem rationalTraceOriginalLocalHomRepresentation_eq :
    (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))).ρ.comp
      (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom =
    (show Representation ℤ
      Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp))) from
      (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  exact (rationalTraceOriginalCompletionHom_action a q σ F hker p hp g f).symm

/-- The original prime-local Hom cocycle gives an actual continuous
original-completion Hom cocycle by the proved group and coefficient maps. -/
def rationalTraceOriginalLocalHomCocycleMap :
    continuousRepresentationCocyclesOne (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))) →ₗ[ℤ]
    continuousRepresentationCocyclesOne (rationalTraceOriginalLocalHomRep a q σ F hker p hp) :=
  continuousCocycleOneRestrictionCongr
    (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp)
    (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ
    (rationalTraceOriginalLocalHomRepresentation_eq a q σ F hker p hp)

/-- The transported cocycle retains exactly the original Hom value at
the corresponding original prime-local automorphism. -/
theorem rationalTraceOriginalLocalHomCocycleMap_apply
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))))
    (g : Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) :
    (rationalTraceOriginalLocalHomCocycleMap a q σ F hker p hp c).val g =
      c.val ((rationalOriginalCompletionGaloisEquiv p hp).symm g) := by
  exact continuousCocycleOneRestrictionCongr_apply
    (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp)
    (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ
    (rationalTraceOriginalLocalHomRepresentation_eq a q σ F hker p hp) c g

end
end Dubon2026
