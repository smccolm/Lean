import Dubon2026.ArithmeticTraceSUnitLocalH1
import Dubon2026.RationalTraceLocalH1TargetValue

/-! Identify the actual S-unit Hom localization with normalized original
trace-dual localization. This comparison retains the original H1 classes
and the arithmetic normalization required for DUB-17's local recovery. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module
attribute [local instance] arithmeticTraceSUnitHomContinuousSMul
  primeTraceUnitHomContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

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

/-- The exact normalized original trace-dual H1 localization square. -/
abbrev RationalTraceSUnitLocalH1Comparison : Prop :=
    ∀ x : RationalArithmeticTraceDualH1 a q hqa σ hσ,
    rationalTraceSUnitLocalH1Map a ha q σ hσ hqa hn p hp
      (rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn x) =
    rationalPrimeTraceUnitH1Equiv p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn
      (rationalArithmeticLocalNormalizationScalar a q hqa p hp •
        rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)

/-- Localization in original S-unit Hom coefficients equals original
trace-dual localization with the proved arithmetic coordinate factor. -/
theorem rationalTraceSUnitLocalH1Map_traceDual :
    RationalTraceSUnitLocalH1Comparison a ha q σ hσ hqa hn p hp := by
  unfold RationalTraceSUnitLocalH1Comparison
  intro x
  induction x using Quotient.inductionOn with
  | h c =>
    let cG := continuousCocycleOneAdditiveEquiv
      (matrixTraceZeroCharacterRep σ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (rationalArithmeticTraceSUnitHomRep a ha q σ)
      (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) c
    let cL := continuousCoefficientCocycleOneMap
      (restrictedCoefficientRep (rationalArithmeticTraceSUnitHomRep a ha q σ)
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom)
      (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalTraceSUnitLocalHomMap a ha q σ p hp) continuous_of_discreteTopology
      (rationalTraceSUnitLocalHomMap_equivariant a ha q σ p hp)
      (continuousRepresentationCocycleOneRestriction
        (rationalArithmeticTraceSUnitHomRep a ha q σ)
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous cG)
    change Submodule.Quotient.mk cL = _
    refine Eq.trans ?_ (rationalTraceLocalH1Target_mk a q σ hσ hqa hn p hp c).symm
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply LinearMap.ext
    intro Y
    change
      (show rationalPrimeTraceZeroIntegerRep p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp)) →ₗ[ℤ]
        Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) from
        rationalTraceSUnitLocalHomMap a ha q σ p hp
          (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn
            (c.val (rationalPrimeArithmeticRestriction a p hp g)))) Y =
      rationalPrimeTraceUnitDualEquiv p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp)) hn
        (rationalArithmeticLocalNormalizationScalar a q hqa p hp •
          (continuousCocycleOneCoefficientCongr
            (rationalArithmeticTraceZeroCyclotomicTwist_restriction a q hqa σ p hp)
            (continuousRepresentationCocycleOneRestriction
              (matrixTraceZeroCharacterRep σ
                (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
              (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
              (rationalPrimeArithmeticRestriction a p hp).continuous c)).val g) Y
    rw [continuousCocycleOneCoefficientCongr_apply]
    exact rationalTraceSUnitLocalHomMap_coherent_value a ha q σ p hp hqa hn
      (c.val (rationalPrimeArithmeticRestriction a p hp g)) Y

end
end Dubon2026
