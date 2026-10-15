import Dubon2026.ArithmeticTraceSUnitCartierDuality
import Dubon2026.ArithmeticExceptionalLocalization
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv

/-! # Original continuous trace cohomology in S-unit Hom coefficients

The already proved coefficient identification is applied to the original
continuous cocycle quotients. This retains the original global dual H1 used
by localization; it is not a comparison with equivariant Ext.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

private theorem continuous_action_of_addEquiv {G A B : Type}
    [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]
    [AddCommGroup A] [AddCommGroup B]
    (α : G → A → A) (β : G → B → B) (e : A ≃+ B)
    (he : Continuous e) (hei : Continuous e.symm)
    (hα : Continuous (fun z : G × A => α z.1 z.2))
    (heρ : ∀ g x, e (α g x) = β g (e x)) :
    Continuous (fun z : G × B => β z.1 z.2) := by
  have hfun : (fun z : G × B => β z.1 z.2) = (fun z => e (α z.1 (e.symm z.2))) := by
    funext z
    rw [heρ, e.apply_symm_apply]
  rw [hfun]
  exact he.comp (hα.comp (continuous_fst.prodMk (hei.comp continuous_snd)))

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- Integer-linear Hom from the original trace adjoint to the original arithmetic S-units. -/
def rationalArithmeticTraceSUnitHomRep : Rep ℤ (rationalArithmeticGaloisGroup a) :=
  Rep.of (Representation.linHom (rationalArithmeticTraceZeroIntegerRep a q σ).ρ
    (originalArithmeticSUnitRepresentation ℚ (AlgebraicClosure ℚ) a ha).ρ)

variable (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  [TopologicalSpace (rationalArithmeticTraceSUnitHomRep a ha q σ)]
  [DiscreteTopology (rationalArithmeticTraceSUnitHomRep a ha q σ)]

local instance arithmeticTraceSUnitHomContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticTraceSUnitHomRep a ha q σ)
      (rationalArithmeticTraceSUnitHomRep a ha q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

include hσ hqa hn in
/-- The actual S-unit Hom action is continuous through its proved trace coefficient identification. -/
theorem rationalArithmeticTraceSUnitHomAction_continuous :
    Continuous (fun z : rationalArithmeticGaloisGroup a ×
      rationalArithmeticTraceSUnitHomRep a ha q σ =>
        (rationalArithmeticTraceSUnitHomRep a ha q σ).ρ z.1 z.2) := by
  exact continuous_action_of_addEquiv
    (fun g x => rationalArithmeticTraceZeroCyclotomicTwist a q hqa σ g x)
    (fun g x => (rationalArithmeticTraceSUnitHomRep a ha q σ).ρ g x)
    (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (matrixTraceZeroCharacterAction_continuous σ hσ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)
    (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn)

/-- The original global dual H1 is the actual continuous H1 of S-unit Hom coefficients. -/
def rationalArithmeticTraceSUnitH1Equiv :
    RationalArithmeticTraceDualH1 a q hqa σ hσ ≃+
      ContinuousRepresentationH1 (rationalArithmeticTraceSUnitHomRep a ha q σ)
        (rationalArithmeticTraceSUnitHomAction_continuous a ha q σ hσ hqa hn) :=
  continuousH1AdditiveCoefficientEquiv _ _
    (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) _ _

/-- The same original coefficient identification acts on the actual continuous H2 quotient. -/
def rationalArithmeticTraceSUnitH2Equiv :
    ContinuousRepresentationH2 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous) ≃+
      ContinuousRepresentationH2 (rationalArithmeticTraceSUnitHomRep a ha q σ)
        (rationalArithmeticTraceSUnitHomAction_continuous a ha q σ hσ hqa hn) :=
  continuousH2AdditiveCoefficientEquiv _ _
    (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) _ _

/-- The H1 comparison carries every actual cocycle to its pointwise S-unit Hom image. -/
theorem rationalArithmeticTraceSUnitH1Equiv_mk
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    rationalArithmeticTraceSUnitH1Equiv a ha q σ hσ hqa hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv _ _
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) c) := rfl

/-- The H2 comparison retains each original continuous two-cocycle under pointwise coefficient transport. -/
theorem rationalArithmeticTraceSUnitH2Equiv_mk
    (c : continuousRepresentationCocyclesTwo (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)) :
    rationalArithmeticTraceSUnitH2Equiv a ha q σ hσ hqa hn (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoAdditiveEquiv _ _
        (rationalArithmeticTraceSUnitDualEquiv a ha q σ hqa hn)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (rationalArithmeticTraceSUnitDualEquiv_equivariant a ha q σ hqa hn) c) := rfl

end
end Dubon2026
