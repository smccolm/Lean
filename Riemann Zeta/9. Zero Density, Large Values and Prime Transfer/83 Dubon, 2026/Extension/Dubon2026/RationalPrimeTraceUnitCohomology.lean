import Dubon2026.RationalPrimeTraceUnitCartierDuality
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! # The actual prime-local dual H1 in unit Hom coefficients

The native continuous cocycle equivalence transports the original local dual
H1 to its literal unit Hom coefficients, retaining the actual cocycle values.
This is the Cartier input for the finite relation construction, not yet its
canonical total or a reverse localization theorem.
-/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module

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
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- Integer-linear Hom from the original trace adjoint to the original prime-local extension-field units. -/
def rationalPrimeTraceUnitHomRep : Rep ℤ (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :=
  Rep.of (Representation.linHom (rationalPrimeTraceZeroIntegerRep p hp q σ).ρ
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)).ρ)

variable (hσ : Continuous σ)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q σ)]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q σ)]

local instance primeTraceUnitHomContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceUnitHomRep p hp q σ)
      (rationalPrimeTraceUnitHomRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

include hσ hn in
/-- The actual extension-field unit Hom action is continuous through its proved trace coefficient identification. -/
theorem rationalPrimeTraceUnitHomAction_continuous :
    Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ×
      rationalPrimeTraceUnitHomRep p hp q σ =>
        (rationalPrimeTraceUnitHomRep p hp q σ).ρ z.1 z.2) := by
  exact continuous_action_of_addEquiv
    (fun g x => coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation σ)
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom g x)
    (fun g x => (rationalPrimeTraceUnitHomRep p hp q σ).ρ g x)
    (rationalPrimeTraceUnitDualEquiv p hp q σ hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (matrixTraceZeroCharacterAction_continuous σ hσ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)
    (rationalPrimeTraceUnitDualEquiv_equivariant p hp q σ hn)

/-- The original local dual H1 is the actual continuous H1 of extension-field unit Hom coefficients. -/
def rationalPrimeTraceUnitH1Equiv :
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃+
      ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q σ)
        (rationalPrimeTraceUnitHomAction_continuous p hp q σ hσ hn) :=
  continuousH1AdditiveCoefficientEquiv _ _
    (rationalPrimeTraceUnitDualEquiv p hp q σ hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalPrimeTraceUnitDualEquiv_equivariant p hp q σ hn) _ _

end
end Dubon2026
