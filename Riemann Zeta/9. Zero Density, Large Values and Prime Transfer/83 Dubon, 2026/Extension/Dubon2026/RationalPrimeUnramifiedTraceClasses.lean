import Dubon2026.RationalPrimeUnramifiedDimension
import Dubon2026.ContinuousAdjointRestrictionComparison

/-! Use the original trace-zero deformation cohomology, and its original
restriction, for the prime-local unramified condition. The existing
coefficient comparison transfers the proved local dimension to this
actual space. This is the DUB-17 local tangent dimension dependency. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- Native coefficient comparison preserves the zero restriction
condition on the original trace-zero deformation classes. -/
theorem continuousTraceZeroH1Restriction_ker_eq_generic
    {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (j : H →* G) (hj : Continuous j) :
    (continuousTraceZeroH1Restriction ρ hρ j hj).ker =
      (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj).ker := by
  ext x
  change continuousTraceZeroH1Restriction ρ hρ j hj x = 0 ↔
    continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
      (matrixTraceZeroAdjointAction_continuous ρ hρ) j hj x = 0
  have he := continuousTraceZeroH1GeneralEquiv_restriction ρ hρ j hj x
  have hz := congrArg (fun z => z = 0) he
  simpa only [LinearEquiv.map_eq_zero_iff] using (Iff.of_eq hz).symm

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)

/-- The actual unramified subspace of the original prime-local trace-zero
deformation cohomology, defined by its own original inertia restriction. -/
def rationalPrimeUnramifiedTraceClasses :
    Submodule (ZMod q) (ContinuousTraceZeroAdjointH1 ρ hρ) :=
  (continuousTraceZeroH1Restriction ρ hρ
    (rationalPrimeNormInertia p hp).subtype continuous_subtype_val).ker

/-- The original deformation restriction kernel equals the generic
continuous-cohomology kernel under the native coefficient comparison. -/
theorem rationalPrimeUnramifiedTraceClasses_eq_generic :
    rationalPrimeUnramifiedTraceClasses p hp q ρ hρ =
      (continuousRepresentationH1Restriction (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ)
        (rationalPrimeNormInertia p hp).subtype continuous_subtype_val).ker := by
  exact continuousTraceZeroH1Restriction_ker_eq_generic ρ hρ
    (rationalPrimeNormInertia p hp).subtype continuous_subtype_val

/-- The actual original prime-local unramified deformation cohomology
has exactly the invariant dimension of its original trace-zero action. -/
theorem rationalPrimeUnramifiedTraceClasses_finrank :
    Module.finrank (ZMod q) (rationalPrimeUnramifiedTraceClasses p hp q ρ hρ) =
      Module.finrank (ZMod q) (matrixTraceZeroAdjointRep ρ).ρ.invariants := by
  have he := congrArg (fun S : Submodule (ZMod q) (ContinuousTraceZeroAdjointH1 ρ hρ) =>
      Module.finrank (ZMod q) S)
    (rationalPrimeUnramifiedTraceClasses_eq_generic p hp q ρ hρ)
  exact he.trans (rationalPrime_unramified_finrank_eq_invariants p hp q
    (matrixTraceZeroAdjointRep ρ) (matrixTraceZeroAdjointAction_continuous ρ hρ))

end
end Dubon2026
