import Dubon2026.RationalTraceOriginalCartierCocycle
import Dubon2026.ContinuousH1GroupReindex
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.GaloisTowerLocalRelationContinuity

/-! Lift the existing original completion cocycle identification to its
actual continuous H1 equivalence. This identifies the source-local dual
connecting class with the prime-local class for DUB-17's cup separation. -/
namespace Dubon2026
noncomputable section
private def h1RestrictionCongrEquiv
    {R G H : Type} [CommRing R] [Group G] [Group H]
    [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
    (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)
    (σ : Representation R H A) (hσ : A.ρ.comp e.toMonoidHom = σ)
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (hB : Continuous (fun z : H × A => σ z.1 z.2)) :
    ContinuousRepresentationH1 A hA ≃+
      ContinuousRepresentationH1 (Rep.of σ) hB :=
  (continuousH1GroupEquiv A e he hei hA).trans
    (continuousH1CoefficientCongr (R := R) (G := H) (V := A) hσ
      (restrictedCoefficientAction_continuous A e.toMonoidHom he hA) hB).toAddEquiv

private theorem h1RestrictionCongrEquiv_mk
    {R G H : Type} [CommRing R] [Group G] [Group H]
    [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
    (e : H ≃* G) (he : Continuous e) (hei : Continuous e.symm)
    (σ : Representation R H A) (hσ : A.ρ.comp e.toMonoidHom = σ)
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (hB : Continuous (fun z : H × A => σ z.1 z.2))
    (c : continuousRepresentationCocyclesOne A) :
    h1RestrictionCongrEquiv A e he hei σ hσ hA hB (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneRestrictionCongr A e.toMonoidHom he σ hσ c) := by
  change continuousH1CoefficientCongr (R := R) (G := H) (V := A) hσ
    (restrictedCoefficientAction_continuous A e.toMonoidHom he hA) hB
    (Submodule.Quotient.mk (continuousRepresentationCocycleOneRestriction A e.toMonoidHom he c)) = _
  refine (continuousH1CoefficientCongr_mk (R := R) (G := H) (V := A) hσ
    (restrictedCoefficientAction_continuous A e.toMonoidHom he hA) hB
    (continuousRepresentationCocycleOneRestriction A e.toMonoidHom he c)).trans ?_
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact continuousCocycleOneCoefficientCongr_apply hσ
    (continuousRepresentationCocycleOneRestriction A e.toMonoidHom he c) g

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

attribute [local instance] traceOriginalFiniteRepFinite
  traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul

/-- The original finite-completion unit Hom has its derived continuous action. -/
theorem rationalTraceOriginalLocalHomAction_continuous :
    Continuous (fun z : Gal(rationalPrimeLocalClosure p hp /
      (rationalOriginalPrimePlace p hp).adicCompletion ℚ) ×
      rationalTraceOriginalLocalHomRep a q σ F hker p hp =>
      (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ z.1 z.2) :=
  galoisTowerLocalCoefficientUnitHomAction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker)

variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The actual original-completion Hom H1, with its native coefficient and topology. -/
abbrev RationalTraceOriginalLocalHomH1 :=
  ContinuousRepresentationH1 (rationalTraceOriginalLocalHomRep a q σ F hker p hp)
    (rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp)

/-- The proved actual group restriction and original action equality
identify the genuine local Hom H1 quotients on their unchanged coefficient. -/
def rationalTraceOriginalLocalHomH1Equiv :
    ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomAction_continuous p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn) ≃+
      RationalTraceOriginalLocalHomH1 a q σ F hker p hp :=
  h1RestrictionCongrEquiv (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalOriginalCompletionGaloisEquiv p hp).symm
    (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp)
    (rationalOriginalCompletionGaloisEquiv_continuous p hp)
    (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ
    (rationalTraceOriginalLocalHomRepresentation_eq a q σ F hker p hp)
    (rationalPrimeTraceUnitHomAction_continuous p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn)
    (rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp)

/-- Every original H1 representative is carried by the existing literal
completion cocycle map, without a replacement cocycle or quotient. -/
theorem rationalTraceOriginalLocalHomH1Equiv_mk
    (c : continuousRepresentationCocyclesOne (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))) :
    rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (rationalTraceOriginalLocalHomCocycleMap a q σ F hker p hp c) :=
  h1RestrictionCongrEquiv_mk (rationalPrimeTraceUnitHomRep p hp q (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalOriginalCompletionGaloisEquiv p hp).symm
    (rationalOriginalCompletionGaloisEquiv_symm_continuous p hp)
    (rationalOriginalCompletionGaloisEquiv_continuous p hp)
    (rationalTraceOriginalLocalHomRep a q σ F hker p hp).ρ
    (rationalTraceOriginalLocalHomRepresentation_eq a q σ F hker p hp)
    (rationalPrimeTraceUnitHomAction_continuous p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn)
    (rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp) c

end
end Dubon2026
