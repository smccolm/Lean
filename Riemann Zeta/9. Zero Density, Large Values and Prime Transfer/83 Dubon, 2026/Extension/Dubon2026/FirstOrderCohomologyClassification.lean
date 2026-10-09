import Dubon2026.FirstOrderStrictConjugation

/-! # Original strict conjugacy classes and Mathlib's actual first cohomology -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Actual strict conjugacy requires an original invertible change of basis reducing to the identity. -/
def MatrixFirstOrderStrictlyConjugate (ρ : G →* GeneralLinearGroup ι R)
    (τ σ : MatrixFirstOrderLift ρ) : Prop :=
  ∃ U : GeneralLinearGroup ι (DualNumber R), dualMatrixReduction U = 1 ∧
    ∀ g, σ.val g = U * τ.val g * U⁻¹

/-- Equality in Mathlib's original adjoint first cohomology is exactly strict conjugacy of the genuine original lifts. -/
theorem matrixFirstOrderStrictlyConjugate_iff (ρ : G →* GeneralLinearGroup ι R)
    (τ σ : MatrixFirstOrderLift ρ) :
    MatrixFirstOrderStrictlyConjugate ρ τ σ ↔
      groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ) =
        groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ σ) := by
  rw [groupCohomology.H1π_eq_iff]
  constructor
  · rintro ⟨U, hU, hconj⟩
    have he : σ = matrixFirstOrderConjugate ρ τ (dualMatrixInfinitesimal U) := by
      apply Subtype.ext
      apply MonoidHom.ext
      intro g
      rw [matrixFirstOrderConjugate_apply, dualMatrixStrictUnit_of_reduction U hU]
      exact hconj g
    rw [he]
    change ∃ X, (groupCohomology.d₀₁ (matrixAdjointRep ρ)).hom X = _
    refine ⟨dualMatrixInfinitesimal U, ?_⟩
    exact (matrixFirstOrderConjugate_coboundary ρ τ (dualMatrixInfinitesimal U)).symm
  · intro h
    change ∃ X, (groupCohomology.d₀₁ (matrixAdjointRep ρ)).hom X = _ at h
    obtain ⟨X, hX⟩ := h
    have he : matrixFirstOrderConjugate ρ τ X = σ := by
      apply (matrixFirstOrderLiftEquiv ρ).injective
      apply groupCohomology.cocycles₁_ext
      intro g
      change matrixFirstOrderCocycle ρ (matrixFirstOrderConjugate ρ τ X) g =
        matrixFirstOrderCocycle ρ σ g
      rw [matrixFirstOrderConjugate_cocycle]
      have hx := congrFun hX g
      change (ρ g).val * X * (ρ g⁻¹).val - X =
        matrixFirstOrderCocycle ρ τ g - matrixFirstOrderCocycle ρ σ g at hx
      calc
        _ = matrixFirstOrderCocycle ρ τ g - ((ρ g).val * X * (ρ g⁻¹).val - X) := by abel
        _ = _ := by rw [hx]; abel
    refine ⟨dualMatrixStrictUnit X, dualMatrixStrictUnit_reduction X, ?_⟩
    intro g
    rw [← he]
    exact matrixFirstOrderConjugate_apply ρ τ X g

/-- Every element of the actual adjoint first cohomology is represented by an original genuine first-order lift. -/
theorem matrixFirstOrderCohomology_surjective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Surjective (fun τ : MatrixFirstOrderLift ρ =>
      groupCohomology.H1π (matrixAdjointRep ρ) (matrixFirstOrderCocycle ρ τ)) := by
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    refine ⟨firstOrderLiftFromCocycle ρ c, ?_⟩
    change groupCohomology.H1π (matrixAdjointRep ρ)
      (matrixFirstOrderCocycle ρ (firstOrderLiftFromCocycle ρ c)) = _
    rw [matrixFirstOrderCocycle_fromCocycle]

end
end Dubon2026
