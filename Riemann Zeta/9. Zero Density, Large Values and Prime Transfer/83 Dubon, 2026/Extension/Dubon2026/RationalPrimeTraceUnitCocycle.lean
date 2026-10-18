import Dubon2026.RationalPrimeTraceUnitCohomology

/-! The original Cartier equivalence on actual continuous local trace
cocycles. Its literal unit values feed DUB-17's finite relation construction
and preserve the normalization already proved for the local trace cup. -/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q))
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q σ)]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q σ)]

attribute [local instance] primeTraceUnitHomContinuousSMul

/-- The original local trace dual cocycle is identified with its actual unit Hom cocycle. -/
def rationalPrimeTraceUnitCocycleEquiv :
    continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom) ≃+
    continuousRepresentationCocyclesOne (rationalPrimeTraceUnitHomRep p hp q σ) :=
  continuousCocycleOneAdditiveEquiv _ _
    (rationalPrimeTraceUnitDualEquiv p hp q σ hn)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalPrimeTraceUnitDualEquiv_equivariant p hp q σ hn)

/-- The actual Cartier cocycle keeps the literal normalized trace-dual unit value. -/
theorem rationalPrimeTraceUnitCocycleEquiv_apply
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom))
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    (rationalPrimeTraceUnitCocycleEquiv p hp q σ hn c).val g =
      rationalPrimeTraceUnitDualEquiv p hp q σ hn (c.val g) := rfl

end
end Dubon2026
