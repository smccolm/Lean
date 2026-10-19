import Dubon2026.ArithmeticTraceSUnitLocalHom
import Dubon2026.ContinuousCohomologyCoefficientMap
import Dubon2026.ContinuousCohomologyRestriction

/-! The actual S-unit-to-local-unit coefficient map induces restriction
on continuous H1. This supplies the map needed to recover the prescribed
local classes of DUB-17's constructed global trace-dual class. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticTraceSUnitHomContinuousSMul
  primeTraceUnitHomContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0) (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))]

/-- Restrict the original global S-unit Hom H1 and then apply the actual
arithmetic map from S-units to the original prime-local field units. -/
def rationalTraceSUnitLocalH1Map :
    ContinuousRepresentationH1 (rationalArithmeticTraceSUnitHomRep a ha q σ)
      (rationalArithmeticTraceSUnitHomAction_continuous a ha q σ hσ hqa hn) →ₗ[ℤ]
    ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomAction_continuous p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn) :=
  let A := rationalArithmeticTraceSUnitHomRep a ha q σ
  let B := rationalPrimeTraceUnitHomRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp))
  let j := rationalPrimeArithmeticRestriction a p hp
  let hA := rationalArithmeticTraceSUnitHomAction_continuous a ha q σ hσ hqa hn
  let hB := rationalPrimeTraceUnitHomAction_continuous p hp q
    (σ.comp j) (hσ.comp j.continuous) hn
  (continuousCoefficientH1Map (restrictedCoefficientRep A j.toMonoidHom) B
    (rationalTraceSUnitLocalHomMap a ha q σ p hp) continuous_of_discreteTopology
    (rationalTraceSUnitLocalHomMap_equivariant a ha q σ p hp)
    (restrictedCoefficientAction_continuous A j.toMonoidHom j.continuous hA) hB).comp
      (continuousRepresentationH1Restriction A hA j.toMonoidHom j.continuous)

/-- The actual H1 map retains the pointwise restricted and localized
original S-unit Hom cocycle. -/
theorem rationalTraceSUnitLocalH1Map_mk
    (c : continuousRepresentationCocyclesOne (rationalArithmeticTraceSUnitHomRep a ha q σ)) :
    rationalTraceSUnitLocalH1Map a ha q σ hσ hqa hn p hp (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk
        (continuousCoefficientCocycleOneMap
          (restrictedCoefficientRep (rationalArithmeticTraceSUnitHomRep a ha q σ)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
          (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
          (rationalTraceSUnitLocalHomMap a ha q σ p hp) continuous_of_discreteTopology
          (rationalTraceSUnitLocalHomMap_equivariant a ha q σ p hp)
          (continuousRepresentationCocycleOneRestriction
            (rationalArithmeticTraceSUnitHomRep a ha q σ)
            (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalPrimeArithmeticRestriction a p hp).continuous c)) := rfl

end
end Dubon2026
