import Dubon2026.RationalPrimeTraceIntegerCohomology

/-! The existing integer coefficient equivalence on literal prime-local
trace-zero cocycles. This keeps the actual representative available for
DUB-17's completion-cup and source-restriction comparison. -/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module
attribute [local instance] primeTraceIntegerContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q))

/-- View the same original continuous trace-zero cocycle over the integers. -/
def rationalPrimeTraceIntegerCocycle (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q ρ) :=
  continuousCocycleOneAdditiveEquiv (matrixTraceZeroAdjointRep ρ)
    (rationalPrimeTraceZeroIntegerRep p hp q ρ) (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl)
    ⟨c.val, c.property⟩

/-- Conversion keeps every original trace-zero matrix value. -/
theorem rationalPrimeTraceIntegerCocycle_apply (c : continuousTraceZeroAdjointCocycles ρ)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    (rationalPrimeTraceIntegerCocycle p hp q ρ c).val g = c.val g := rfl

/-- Conversion on representatives is exactly the existing integer H1 equivalence. -/
theorem rationalPrimeTraceIntegerCocycle_class (hρ : Continuous ρ)
    (c : continuousTraceZeroAdjointCocycles ρ) :
    rationalPrimeTraceIntegerH1Equiv p hp q ρ hρ (Quotient.mk _ c) =
      Quotient.mk _ (rationalPrimeTraceIntegerCocycle p hp q ρ c) := rfl

end
end Dubon2026
