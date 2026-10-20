import Dubon2026.PolarizedCocycleLift
import Mathlib.Tactic.Abel

/-! The exact source strict change of basis acts on full adjoint cocycles
by the original coboundary. This connects the source fixed-similitude
deformation classes with cohomology on the DUB-17 Selmer route. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Inversion in the original strict kernel negates its full matrix coordinate. -/
theorem polarizedStrictPoint_inv (X : Matrix ι ι R) :
    (polarizedStrictPoint X)⁻¹ = polarizedStrictPoint (-X) := by
  change (polarizedLinearInclusion (R := DualNumber R) (ι := ι) (dualMatrixStrictUnit X))⁻¹ = _
  rw [← map_inv, dualMatrixStrictUnit_inv]
  rfl

/-- Strict change of basis has its actual source coboundary formula on the reconstructed lift. -/
theorem polarizedFirstOrderStrictConjugate_apply (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (X : Matrix ι ι R) (g : G) :
    polarizedStrictPoint X * τ.val g * (polarizedStrictPoint X)⁻¹ =
      polarizedStrictPoint (polarizedFirstOrderCocycle ρ τ g + X -
        polarizedAdjointRepresentation (ρ g) X) * polarizedDualConstant (ρ g) := by
  have hconj := polarizedStrictPoint_conjugate (polarizedDualConstant (ρ g)) (-X)
  rw [polarizedDualReduction_constant] at hconj
  rw [← polarizedFirstOrderCoordinate_reconstruct ρ τ g, polarizedStrictPoint_inv]
  calc
    _ = (polarizedStrictPoint X * polarizedStrictPoint (polarizedFirstOrderCoordinate ρ τ g)) *
        (polarizedDualConstant (ρ g) * polarizedStrictPoint (-X) *
          (polarizedDualConstant (ρ g))⁻¹) * polarizedDualConstant (ρ g) := by
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by
      rw [hconj, ← polarizedStrictPoint_add, ← polarizedStrictPoint_add, map_neg]
      congr 2
      change X + polarizedFirstOrderCocycle ρ τ g +
        -polarizedAdjointRepresentation (ρ g) X = _
      abel

/-- Pointwise strict conjugacy is exactly the original full-adjoint coboundary identity. -/
theorem polarizedFirstOrderConjugate_iff (ρ : G →* PolarizedGaloisGroup ι R)
    (τ σ : PolarizedFirstOrderLift ρ) (X : Matrix ι ι R) :
    (∀ g, σ.val g = polarizedStrictPoint X * τ.val g * (polarizedStrictPoint X)⁻¹) ↔
      ∀ g, polarizedFirstOrderCocycle ρ σ g = polarizedFirstOrderCocycle ρ τ g + X -
        polarizedAdjointRepresentation (ρ g) X := by
  constructor
  · intro h g
    apply polarizedStrictPoint_injective
    apply mul_right_cancel (b := polarizedDualConstant (ρ g))
    exact (polarizedFirstOrderCoordinate_reconstruct ρ σ g).trans
      ((h g).trans (polarizedFirstOrderStrictConjugate_apply ρ τ X g))
  · intro h g
    rw [polarizedFirstOrderStrictConjugate_apply, ← h g]
    exact (polarizedFirstOrderCoordinate_reconstruct ρ σ g).symm

/-- The source strict conjugator is an actual identity-reducing GL_n point with multiplier one. -/
def PolarizedFirstOrderStrictlyConjugate (ρ : G →* PolarizedGaloisGroup ι R)
    (τ σ : PolarizedFirstOrderLift ρ) : Prop :=
  ∃ U : PolarizedGaloisGroup ι (DualNumber R), polarizedDualReduction U = 1 ∧
    polarizedSimilitude U = 1 ∧ ∀ g, σ.val g = U * τ.val g * U⁻¹

/-- The genuine strict conjugacy relation is exactly equality in the original full adjoint H1. -/
theorem polarizedFirstOrderStrictlyConjugate_iff (ρ : G →* PolarizedGaloisGroup ι R)
    (τ σ : PolarizedFirstOrderLift ρ) :
    PolarizedFirstOrderStrictlyConjugate ρ τ σ ↔
      groupCohomology.H1π (polarizedAdjointRep ρ) (polarizedFirstOrderCocycle ρ τ) =
        groupCohomology.H1π (polarizedAdjointRep ρ) (polarizedFirstOrderCocycle ρ σ) := by
  rw [groupCohomology.H1π_eq_iff]
  constructor
  · rintro ⟨U, hr, hν, hconj⟩
    let X := dualMatrixInfinitesimal U.left.1
    have hU : polarizedStrictPoint X = U := polarizedStrictPoint_of_kernel U hr hν
    have hc := (polarizedFirstOrderConjugate_iff ρ τ σ X).mp (by simpa only [hU] using hconj)
    refine ⟨X, ?_⟩
    funext g
    change polarizedAdjointRepresentation (ρ g) X - X =
      polarizedFirstOrderCocycle ρ τ g - polarizedFirstOrderCocycle ρ σ g
    rw [hc g]
    abel
  · rintro ⟨X, hX⟩
    refine ⟨polarizedStrictPoint X, polarizedStrictPoint_reduction X,
      polarizedStrictPoint_similitude X, ?_⟩
    apply (polarizedFirstOrderConjugate_iff ρ τ σ X).mpr
    intro g
    have h := congrFun hX g
    change polarizedAdjointRepresentation (ρ g) X - X =
      polarizedFirstOrderCocycle ρ τ g - polarizedFirstOrderCocycle ρ σ g at h
    calc
      _ = polarizedFirstOrderCocycle ρ τ g -
          (polarizedFirstOrderCocycle ρ τ g - polarizedFirstOrderCocycle ρ σ g) := by abel
      _ = _ := by rw [← h]; abel

end
end Dubon2026
