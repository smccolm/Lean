import Dubon2026.DistinctDiagonalTraceFixed
import Dubon2026.RepresentationConjugateFixedSpace
import Dubon2026.FiniteSymmetricRegularDiagonal

/-! Exact trace-zero fixed-space dimensions for the regular symmetric
torus elements and their conjugates used in auxiliary-prime selection.
These are the matrix dimensions required by DUB-17's local deformation
calculation; the original local Galois and deformation comparison is open. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- A regular symmetric torus element has trace-zero adjoint fixed-space
dimension equal to the symmetric degree, using its actual native weights. -/
theorem symmetric_unitDiagonal_traceFixed_finrank
    {K : Type} [Field K] (u : Kˣ) (n : ℕ) (hu : 2 * n < orderOf u) :
    Module.finrank K (LinearMap.ker
      ((matrixTraceZeroAdjointRep ((homogeneousSymmetricGL n).comp
        SpecialLinearGroup.toGL)).ρ (ringSL2UnitDiagonal u) - 1)) = n := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  have hd := matrixDistinctDiagonalTraceFixed_finrank ψ (ringSL2UnitDiagonal u)
    (fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val))
    (symmetric_unit_weights_injective u n hu) (homogeneousSymmetricGL_unitDiagonal u n)
  rw [Fintype.card_fin] at hd
  exact Nat.add_right_cancel hd

/-- The same dimension holds for every original conjugate of the regular
symmetric torus element, including those used by the trace detector. -/
theorem symmetric_conjugate_unitDiagonal_traceFixed_finrank
    {K : Type} [Field K] (u : Kˣ) (n : ℕ) (hu : 2 * n < orderOf u)
    (h : SL(2, K)) :
    Module.finrank K (LinearMap.ker
      ((matrixTraceZeroAdjointRep ((homogeneousSymmetricGL n).comp
        SpecialLinearGroup.toGL)).ρ (h * ringSL2UnitDiagonal u * h⁻¹) - 1)) = n := by
  rw [representationConjugateFixed_finrank]
  exact symmetric_unitDiagonal_traceFixed_finrank u n hu

end
end Dubon2026
