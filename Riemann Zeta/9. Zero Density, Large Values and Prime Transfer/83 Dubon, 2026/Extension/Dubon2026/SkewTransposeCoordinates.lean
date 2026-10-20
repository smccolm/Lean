import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-! Finite coordinates for the skew-transpose matrices appearing in CHT
Lemma 2.1.3 at the actual odd real place. This computes the required
infinite-place invariant dimension on DUB-17's polarized Selmer route. -/

namespace Dubon2026
noncomputable section
open Matrix

variable (n : ℕ) (K : Type) [Field K]

/-- The actual kernel of transpose plus identity on the original matrix module. -/
def skewTransposeMatrices : Submodule K (Matrix (Fin n) (Fin n) K) :=
  ((Matrix.transposeLinearEquiv (Fin n) (Fin n) K K).toLinearMap + LinearMap.id).ker

/-- Strict upper-triangular positions, retaining both original matrix indices. -/
abbrev StrictUpperIndex := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- The unique skew-transpose matrix with the prescribed strict upper entries and zero diagonal. -/
def skewTransposeMatrixFromUpper (v : StrictUpperIndex n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if h : i < j then v ⟨(i,j), h⟩
    else if h' : j < i then -v ⟨(j,i), h'⟩ else 0

/-- The constructed matrix is skew under the actual transpose. -/
theorem skewTransposeMatrixFromUpper_mem (v : StrictUpperIndex n → K) :
    skewTransposeMatrixFromUpper n K v ∈ skewTransposeMatrices n K := by
  change (skewTransposeMatrixFromUpper n K v)ᵀ + skewTransposeMatrixFromUpper n K v = 0
  apply Matrix.ext
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewTransposeMatrixFromUpper, h, not_lt_of_gt h]
  · subst j
    simp [skewTransposeMatrixFromUpper]
  · simp [skewTransposeMatrixFromUpper, h, not_lt_of_gt h]

/-- Over a field of characteristic different from two, the strict upper entries give all skew-transpose matrices linearly and uniquely. -/
def skewTransposeUpperLinearEquiv (h2 : (2 : K) ≠ 0) :
    skewTransposeMatrices n K ≃ₗ[K] (StrictUpperIndex n → K) where
  toFun X ij := X.val ij.val.1 ij.val.2
  invFun v := ⟨skewTransposeMatrixFromUpper n K v, skewTransposeMatrixFromUpper_mem n K v⟩
  left_inv X := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hx := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) X.property
    change X.val j i + X.val i j = 0 at hx
    rcases lt_trichotomy i j with h | h | h
    · simp [skewTransposeMatrixFromUpper, h]
    · subst j
      have hd : X.val i i = 0 := (mul_eq_zero.mp (show (2 : K) * X.val i i = 0 by
        simpa only [two_mul] using hx)).resolve_left h2
      simp [skewTransposeMatrixFromUpper, hd]
    · simp only [skewTransposeMatrixFromUpper, not_lt_of_gt h, ↓reduceDIte, h]
      exact neg_eq_of_add_eq_zero_left (by simpa only [add_comm] using hx)
  right_inv v := by
    funext ij
    simp [skewTransposeMatrixFromUpper, ij.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Strict upper indices are the usual triangular finite family, with no matrix coordinates discarded. -/
def strictUpperIndexEquiv : StrictUpperIndex n ≃ (j : Fin n) × Fin j.val where
  toFun ij := ⟨ij.val.2, ⟨ij.val.1.val, ij.property⟩⟩
  invFun ji := ⟨(⟨ji.2.val, lt_trans ji.2.isLt ji.1.isLt⟩, ji.1), ji.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact number of strict upper entries is the source triangular dimension. -/
theorem strictUpperIndex_card : Fintype.card (StrictUpperIndex n) = n * (n - 1) / 2 := by
  rw [Fintype.card_congr (strictUpperIndexEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i => i) n).trans (Finset.sum_range_id n)

/-- The skew-transpose matrix dimension is the exact real-place term in the source odd polarized adjoint. -/
theorem skewTransposeMatrices_finrank (h2 : (2 : K) ≠ 0) :
    Module.finrank K (skewTransposeMatrices n K) = n * (n - 1) / 2 := by
  rw [(skewTransposeUpperLinearEquiv n K h2).finrank_eq]
  simpa only [Module.finrank_pi, CommSemiring.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] using strictUpperIndex_card n

end
end Dubon2026
