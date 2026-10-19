import Dubon2026.TraceCocycleKernelDetection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The matrix part of the local dimension calculation at regular auxiliary
Frobenius. This serves DUB-17 through the local deformation dimensions in
arithmetic patching. Identifying the original local Galois condition with
this fixed space is a separate arithmetic obligation. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped BigOperators

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- A matrix commutes with a diagonal matrix of distinct entries exactly
when it is itself diagonal, in the original coordinates. -/
theorem matrix_commute_distinct_diagonal_iff
    (w : ι → K) (hw : Function.Injective w) (M : Matrix ι ι K) :
    Matrix.diagonal w * M = M * Matrix.diagonal w ↔ M = Matrix.diagonal M.diag := by
  constructor
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · have he := congrFun (congrFun h i) j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
      have hz : M i j = 0 := by
        by_contra hn
        rw [mul_comm (M i j)] at he
        exact hij (hw (mul_right_cancel₀ hn he))
      simp [hij, hz]
  · intro h
    rw [h]
    exact (Matrix.commute_diagonal _ _).eq

/-- The fixed vectors of the original trace-zero adjoint action are the
actual trace-zero matrices commuting with that residual element. -/
theorem matrixTraceZeroAdjoint_fixed_iff_commute
    (ρ : G →* GeneralLinearGroup ι K) (g : G)
    (M : matrixTraceZeroSubmodule ι K) :
    (matrixTraceZeroAdjointRep ρ).ρ g M = M ↔ (ρ g).val * M.val = M.val * (ρ g).val := by
  refine ⟨?_, matrixTraceZeroAdjoint_fixed_of_commute ρ g M⟩
  intro h
  have he := congrArg Subtype.val h
  change (ρ g).val * M.val * (ρ g⁻¹).val = M.val at he
  have hmul := congrArg (fun X => X * (ρ g).val) he
  dsimp only at hmul
  rw [mul_assoc ((ρ g).val * M.val), map_inv, Units.inv_mul, mul_one] at hmul
  exact hmul

/-- Sum of the original diagonal coordinates, equal to matrix trace. -/
def diagonalCoordinateSum : (ι → K) →ₗ[K] K where
  toFun d := ∑ i, d i
  map_add' d e := Finset.sum_add_distrib
  map_smul' t d := by simp [Finset.mul_sum]

/-- For a residual element with distinct diagonal entries, its trace-zero
fixed space is exactly the original diagonal coordinate space of sum zero. -/
def matrixDistinctDiagonalTraceFixedEquiv
    (ρ : G →* GeneralLinearGroup ι K) (g : G) (w : ι → K)
    (hw : Function.Injective w) (hdiag : (ρ g).val = Matrix.diagonal w) :
    LinearMap.ker ((matrixTraceZeroAdjointRep ρ).ρ g - 1) ≃ₗ[K]
      LinearMap.ker (diagonalCoordinateSum (ι := ι) (K := K)) where
  toFun M := ⟨M.val.val.diag, M.val.property⟩
  invFun d := ⟨⟨Matrix.diagonal d.val, by
    change Matrix.trace (Matrix.diagonal d.val) = 0
    simpa only [Matrix.trace_diagonal] using d.property⟩, by
      change (matrixTraceZeroAdjointRep ρ).ρ g _ - _ = 0
      apply sub_eq_zero.mpr
      apply matrixTraceZeroAdjoint_fixed_of_commute
      change (ρ g).val * Matrix.diagonal d.val = Matrix.diagonal d.val * (ρ g).val
      rw [hdiag]
      exact (Matrix.commute_diagonal _ _).eq⟩
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    have hfix : (matrixTraceZeroAdjointRep ρ).ρ g M.val = M.val :=
      sub_eq_zero.mp M.property
    have hcomm := (matrixTraceZeroAdjoint_fixed_iff_commute ρ g M.val).mp hfix
    rw [hdiag] at hcomm
    exact ((matrix_commute_distinct_diagonal_iff w hw M.val.val).mp hcomm).symm
  right_inv d := by apply Subtype.ext; exact Matrix.diag_diagonal d.val
  map_add' M N := rfl
  map_smul' t M := rfl

/-- The sum-zero diagonal space has codimension one; its dimension does
not require division by the matrix size. -/
theorem diagonalCoordinateSum_ker_finrank [Nonempty ι] :
    Module.finrank K (LinearMap.ker (diagonalCoordinateSum (ι := ι) (K := K))) + 1 =
      Fintype.card ι := by
  have hsurj : Function.Surjective (diagonalCoordinateSum (ι := ι) (K := K)) := by
    intro t
    let i : ι := Classical.choice inferInstance
    refine ⟨Pi.single i t, ?_⟩
    simp [diagonalCoordinateSum]
  have hdim := (diagonalCoordinateSum (ι := ι) (K := K)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi,
    Module.finrank_self] at hdim
  omega

/-- The original trace-zero adjoint Frobenius fixed space has dimension
one less than the number of distinct diagonal residual eigenvalues. -/
theorem matrixDistinctDiagonalTraceFixed_finrank [Nonempty ι]
    (ρ : G →* GeneralLinearGroup ι K) (g : G) (w : ι → K)
    (hw : Function.Injective w) (hdiag : (ρ g).val = Matrix.diagonal w) :
    Module.finrank K (LinearMap.ker ((matrixTraceZeroAdjointRep ρ).ρ g - 1)) + 1 =
      Fintype.card ι := by
  rw [(matrixDistinctDiagonalTraceFixedEquiv ρ g w hw hdiag).finrank_eq]
  exact diagonalCoordinateSum_ker_finrank

end
end Dubon2026
