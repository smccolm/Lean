import Dubon2026.FixedDeterminantFirstOrderLift

/-! # Original adjoint coboundaries and their trace-free representatives -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Remove the actual scalar trace part of the original matrix. The trace-zero conclusion below requires the matrix dimension to be nonzero in the original field. -/
def matrixTraceFreePart (X : Matrix ι ι K) : Matrix ι ι K :=
  X - (Matrix.trace X / (Fintype.card ι : K)) • (1 : Matrix ι ι K)

/-- Over the original coefficient field in which the actual matrix dimension is nonzero, the original scalar correction has trace zero. -/
theorem matrixTraceFreePart_trace (hn : (Fintype.card ι : K) ≠ 0)
    (X : Matrix ι ι K) : Matrix.trace (matrixTraceFreePart X) = 0 := by
  rw [matrixTraceFreePart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  change Matrix.trace X - Matrix.trace X / (Fintype.card ι : K) * (Fintype.card ι : K) = 0
  rw [div_mul_cancel₀ _ hn, sub_self]

/-- Subtracting the original scalar trace part leaves the entire original adjoint coboundary unchanged. -/
theorem matrixTraceFreePart_coboundary (ρ : G →* GeneralLinearGroup ι K)
    (X : Matrix ι ι K) (g : G) :
    groupCohomology.d₀₁ (matrixAdjointRep ρ) (matrixTraceFreePart X) g =
      groupCohomology.d₀₁ (matrixAdjointRep ρ) X g := by
  have hone : matrixAdjointRepresentation ρ g (1 : Matrix ι ι K) = 1 := by
    change (ρ g).val * 1 * (ρ g⁻¹).val = 1
    rw [mul_one, map_inv, Units.mul_inv]
  change matrixAdjointRepresentation ρ g
    (X - (Matrix.trace X / (Fintype.card ι : K)) • (1 : Matrix ι ι K)) -
      (X - (Matrix.trace X / (Fintype.card ι : K)) • (1 : Matrix ι ι K)) =
        matrixAdjointRepresentation ρ g X - X
  rw [map_sub, map_smul, hone]
  abel

/-- Every original matrix adjoint coboundary has a genuine trace-zero matrix representative when the matrix dimension is invertible in the original field. -/
theorem matrixAdjointCoboundary_traceFree_representative
    (hn : (Fintype.card ι : K) ≠ 0) (ρ : G →* GeneralLinearGroup ι K)
    (X : Matrix ι ι K) :
    ∃ Y : Matrix ι ι K, Matrix.trace Y = 0 ∧
      ∀ g, groupCohomology.d₀₁ (matrixAdjointRep ρ) Y g =
        groupCohomology.d₀₁ (matrixAdjointRep ρ) X g :=
  ⟨matrixTraceFreePart X, matrixTraceFreePart_trace hn X, matrixTraceFreePart_coboundary ρ X⟩

end
end Dubon2026
