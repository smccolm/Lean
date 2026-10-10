import Dubon2026.TraceFreeAdjointCoboundaries

/-! # The actual trace-zero coefficient subrepresentation of the original adjoint action -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original trace-zero matrix coefficient module. -/
def matrixTraceZeroSubmodule (ι R : Type) [Fintype ι] [CommRing R] :
    Submodule R (Matrix ι ι R) :=
  (Matrix.traceLinearMap ι R R).ker

/-- The original adjoint action preserves the actual matrix trace. -/
theorem matrixAdjointRepresentation_trace (ρ : G →* GeneralLinearGroup ι R)
    (g : G) (X : Matrix ι ι R) :
    Matrix.trace (matrixAdjointRepresentation ρ g X) = Matrix.trace X := by
  change Matrix.trace ((ρ g).val * X * (ρ g⁻¹).val) = Matrix.trace X
  rw [map_inv, Matrix.trace_units_conj]

/-- Restrict the same original adjoint action to its genuine trace-zero matrix coefficient module. -/
def matrixTraceZeroAdjointRepresentation (ρ : G →* GeneralLinearGroup ι R) :
    Representation R G (matrixTraceZeroSubmodule ι R) :=
  (matrixAdjointRepresentation ρ).subrepresentation (matrixTraceZeroSubmodule ι R) (by
    intro g X hX
    change Matrix.trace (matrixAdjointRepresentation ρ g X) = 0
    exact (matrixAdjointRepresentation_trace ρ g X).trans hX)

/-- The actual trace-zero adjoint representation as an object of the original representation category. -/
abbrev matrixTraceZeroAdjointRep (ρ : G →* GeneralLinearGroup ι R) : Rep R G :=
  Rep.of (matrixTraceZeroAdjointRepresentation ρ)

/-- The original trace-zero coefficient action has the same entire original conjugation matrix. -/
theorem matrixTraceZeroAdjointRep_apply (ρ : G →* GeneralLinearGroup ι R)
    (g : G) (X : matrixTraceZeroSubmodule ι R) :
    ((matrixTraceZeroAdjointRep ρ).ρ g X).val = matrixAdjointRepresentation ρ g X.val := rfl

/-- The genuine trace-zero coefficient coboundary includes as the original adjoint coboundary of the same matrix. -/
theorem matrixTraceZeroAdjointCoboundary_val (ρ : G →* GeneralLinearGroup ι R)
    (X : matrixTraceZeroSubmodule ι R) (g : G) :
    (groupCohomology.d₀₁ (matrixTraceZeroAdjointRep ρ) X g).val =
      groupCohomology.d₀₁ (matrixAdjointRep ρ) X.val g := rfl

end
end Dubon2026
