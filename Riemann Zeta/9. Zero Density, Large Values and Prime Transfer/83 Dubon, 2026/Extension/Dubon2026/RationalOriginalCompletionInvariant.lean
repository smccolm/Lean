import Dubon2026.RationalOriginalPrimeCompletion
import Dubon2026.LocalFieldSurjectiveBaseInvariant

/-! The actual rational number-field completion comparison preserves the
normalized continuous local invariant. Its algebra, valuation and closure
towers are constructed, providing the original prime-local normalization
needed by DUB-17's arithmetic Cartier cup-total specialization. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul AlgebraicClosure.instSMulOfIsScalarTower
variable (p : ℕ) (hp : p.Prime)

/-- Use the actual completion isomorphism as the local base inclusion. -/
local instance rationalOriginalCompletionTargetAlgebra :
    Algebra ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalField p hp) :=
  (rationalOriginalPrimeCompletionEquiv p hp).toRingHom.toAlgebra

/-- Embed the original completion in the same prime-local closure. -/
local instance rationalOriginalCompletionClosureAlgebra :
    Algebra ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp) :=
  ((algebraMap (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).comp
    (rationalOriginalPrimeCompletionEquiv p hp).toRingHom).toAlgebra

/-- The closure embedding factors through the original local field. -/
local instance rationalOriginalCompletionClosureTower :
    IsScalarTower ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Retain the original norm valuation on the number-field completion. -/
local instance rationalOriginalCompletionValuation :
    ValuativeRel ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) :=
  ValuativeRel.ofValuation (NormedField.valuation
    (K := (rationalOriginalPrimePlace p hp).adicCompletion ℚ))

/-- It is the genuine nonarchimedean local completion. -/
local instance rationalOriginalCompletionLocalField :
    IsNonarchimedeanLocalField ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) :=
  originalAdic_isNonarchimedeanLocalField ℚ (rationalOriginalPrimePlace p hp)

/-- The constructed completion isomorphism preserves the original valuation relation. -/
local instance rationalOriginalCompletionValuationExtension :
    (ValuativeRel.valuation ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)).HasExtension
      (ValuativeRel.valuation (rationalPrimeLocalField p hp)) :=
  originalLocalCompletionMap_hasExtension ℚ (rationalPrimeLocalField p hp) p hp

/-- The same actual algebraic closure is Galois over the isomorphic original completion. -/
local instance rationalOriginalCompletionGalois :
    IsGalois ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp) := by
  let e := rationalOriginalPrimeCompletionEquiv p hp
  apply IsGalois.of_equiv_equiv (F := rationalPrimeLocalField p hp)
    (E := rationalPrimeLocalClosure p hp) (f := e.symm) (g := RingEquiv.refl _)
  apply RingHom.ext
  intro x
  change algebraMap (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (e (e.symm x)) = _
  rw [e.apply_symm_apply]
  rfl

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalClosure p hp))]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The same original local H2 class keeps its normalized invariant under
the actual completion isomorphism; no compatibility or normalization hypothesis remains. -/
theorem rationalOriginalPrimeCompletion_invariant
    (x : GaloisUnitContinuousH2 (K := (rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (Ω := rationalPrimeLocalClosure p hp)) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (continuousGaloisUnitBaseChangeH2 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) x) =
      localFieldContinuousH2InvariantEquiv ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalClosure p hp) x :=
  localFieldContinuousInvariant_surjective_baseChange
    ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) (rationalOriginalPrimeCompletionEquiv p hp).surjective x

end
end Dubon2026
