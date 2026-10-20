import Dubon2026.PolarizedDualStrictConjugacy
import Dubon2026.ClosedMatrixTraceAlgebra

/-! A genuine coefficient descent inherits the original conjugate-dual
trace identity. This derives the equal-trace input needed to construct
the polarization over the actual CM trace algebra in DUB-17. -/

namespace Dubon2026
open Matrix

variable {G ι O R k : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing k] [Algebra O R]

/-- Actual strict matrix descent carries the original polarization's
trace identity into the coefficient subalgebra, using its genuine inclusion. -/
theorem coefficientPolarization_traceDescent
    (S : Subalgebra O R) (r : R →+* k)
    (ρ : G →* GeneralLinearGroup ι R) (τ : G →* GeneralLinearGroup ι S)
    (μ : G →* Sˣ) (c : G →* G) (B : GeneralLinearGroup ι R)
    (hτ : MatrixStrictlyConjugate r ((GeneralLinearGroup.map S.val.toRingHom).comp τ) ρ)
    (hpol : ∀ g, ρ (c g) = B *
      polarizedTwistedDual ρ ((Units.map S.val.toMonoidHom).comp μ) g * B⁻¹) :
    ∀ g, Matrix.trace (τ (c g)).val = Matrix.trace (polarizedTwistedDual τ μ g).val := by
  have hd := matrixStrictlyConjugate_twistedDual r
    ((GeneralLinearGroup.map S.val.toRingHom).comp τ) ρ
    ((Units.map S.val.toMonoidHom).comp μ) hτ
  rw [← polarizedTwistedDual_map S.val.toRingHom τ μ] at hd
  intro g
  apply Subtype.val_injective
  change S.val (Matrix.trace (τ (c g)).val) = S.val (Matrix.trace (polarizedTwistedDual τ μ g).val)
  rw [AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  have hl := matrixStrictlyConjugate_trace r _ _ hτ (c g)
  have hr := matrixStrictlyConjugate_trace r _ _ hd g
  calc
    _ = Matrix.trace (ρ (c g)).val := hl.symm
    _ = Matrix.trace (polarizedTwistedDual ρ ((Units.map S.val.toMonoidHom).comp μ) g).val := by
      rw [hpol g]
      exact Matrix.trace_units_conj B _
    _ = _ := hr

end Dubon2026
