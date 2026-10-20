import Dubon2026.PolarizedStrictConjugation
import Dubon2026.PolarizedFirstOrderFiber

/-! A genuine fixed-similitude polarized lift produces a cocycle for the
source full adjoint representation. This discharges the algebraic tangent
map needed for the CM Selmer comparison in DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual first-order coordinates of a polarized lift satisfy the full adjoint cocycle law. -/
theorem polarizedFirstOrderCoordinate_mul (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g h : G) :
    polarizedFirstOrderCoordinate ρ τ (g * h) =
      polarizedAdjointRepresentation (ρ g) (polarizedFirstOrderCoordinate ρ τ h) +
        polarizedFirstOrderCoordinate ρ τ g := by
  apply polarizedStrictPoint_injective
  rw [polarizedStrictPoint_add, polarizedFirstOrderCoordinate_difference]
  have hconj := polarizedStrictPoint_conjugate (polarizedDualConstant (ρ g))
    (polarizedFirstOrderCoordinate ρ τ h)
  rw [polarizedDualReduction_constant] at hconj
  rw [← hconj, polarizedFirstOrderCoordinate_difference,
    polarizedFirstOrderCoordinate_difference]
  have hcomm := congrArg polarizedStrictPoint
    (add_comm (polarizedFirstOrderCoordinate ρ τ g)
      (polarizedAdjointRepresentation (ρ g) (polarizedFirstOrderCoordinate ρ τ h)))
  rw [polarizedStrictPoint_add, polarizedStrictPoint_add,
    ← hconj, polarizedFirstOrderCoordinate_difference,
    polarizedFirstOrderCoordinate_difference] at hcomm
  rw [← hcomm]
  simp only [polarizedFirstOrderDifference, map_mul, _root_.mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]

/-- The original polarized representation with its full matrix adjoint coefficient module. -/
abbrev polarizedAdjointRep (ρ : G →* PolarizedGaloisGroup ι R) : Rep R G :=
  Rep.of (polarizedAdjointRepresentation.comp ρ)

/-- The actual first-order coordinates define Mathlib's original full adjoint cocycle. -/
def polarizedFirstOrderCocycle (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) : groupCohomology.cocycles₁ (polarizedAdjointRep ρ) := by
  refine ⟨polarizedFirstOrderCoordinate ρ τ, ?_⟩
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  exact polarizedFirstOrderCoordinate_mul ρ τ g h

/-- The cocycle retains the actual infinitesimal matrix of the original lift difference. -/
theorem polarizedFirstOrderCocycle_apply (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedFirstOrderCocycle ρ τ g =
      dualMatrixInfinitesimal (τ.val g * (polarizedDualConstant (ρ g))⁻¹).left.1 := rfl

end
end Dubon2026
