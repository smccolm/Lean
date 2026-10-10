import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Strict conjugacy of actual whole original matrix representations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing K]

/-- Two whole original representations are strictly conjugate if an actual change of basis reducing to the identity conjugates every original group element. -/
def MatrixStrictlyConjugate (r : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι A) : Prop :=
  ∃ U : GeneralLinearGroup ι A, GeneralLinearGroup.map r U = 1 ∧
    ∀ g, σ g = U * ρ g * U⁻¹

/-- The identity change of basis gives strict conjugacy of the same whole representation. -/
theorem matrixStrictlyConjugate_refl (r : A →+* K)
    (ρ : G →* GeneralLinearGroup ι A) : MatrixStrictlyConjugate r ρ ρ := by
  refine ⟨1, map_one _, ?_⟩
  intro g
  simp

/-- Inverting the actual original conjugator reverses strict conjugacy and still reduces to the identity. -/
theorem matrixStrictlyConjugate_symm (r : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate r ρ σ) :
    MatrixStrictlyConjugate r σ ρ := by
  obtain ⟨U, hU, h⟩ := h
  refine ⟨U⁻¹, ?_, ?_⟩
  · simp only [map_inv, hU, inv_one]
  · intro g
    rw [h g]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- Multiplying the actual original changes of basis composes strict conjugacies on every group element. -/
theorem matrixStrictlyConjugate_trans (r : A →+* K)
    (ρ σ τ : G →* GeneralLinearGroup ι A)
    (h₁ : MatrixStrictlyConjugate r ρ σ) (h₂ : MatrixStrictlyConjugate r σ τ) :
    MatrixStrictlyConjugate r ρ τ := by
  obtain ⟨U, hU, h₁⟩ := h₁
  obtain ⟨V, hV, h₂⟩ := h₂
  refine ⟨V * U, ?_, ?_⟩
  · simp only [map_mul, hV, hU, one_mul]
  · intro g
    rw [h₂ g, h₁ g]
    simp only [_root_.mul_inv_rev, mul_assoc]

/-- Actual whole strict conjugacy is an equivalence relation, with its original residue map retained. -/
theorem matrixStrictlyConjugate_equivalence (r : A →+* K) :
    Equivalence (MatrixStrictlyConjugate (G := G) (ι := ι) r) :=
  ⟨matrixStrictlyConjugate_refl r,
    fun h => matrixStrictlyConjugate_symm r _ _ h,
    fun h₁ h₂ => matrixStrictlyConjugate_trans r _ _ _ h₁ h₂⟩

/-- Strict conjugacy preserves the full original residual representation, not only its trace or determinant. -/
theorem matrixStrictlyConjugate_reduction (r : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι A) (h : MatrixStrictlyConjugate r ρ σ) :
    (GeneralLinearGroup.map r).comp σ = (GeneralLinearGroup.map r).comp ρ := by
  obtain ⟨U, hU, h⟩ := h
  apply MonoidHom.ext
  intro g
  change GeneralLinearGroup.map r (σ g) = GeneralLinearGroup.map r (ρ g)
  rw [h g]
  simp only [map_mul, map_inv, hU, one_mul, inv_one, mul_one]

end
end Dubon2026
