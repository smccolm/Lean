/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/GaloisCohomology/Cyclic/Herbrand/Permutation/Lattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.EquivariantLatticeAveraging
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # PermutationLatticeIndependence

Diagonal dominance makes the actual equivariantly averaged lattice vectors independent. This discharges the rank input to DUB-17's finite-index permutation sublattice.
-/

namespace Dubon2026
noncomputable section
open Module Submodule
open scoped BigOperators
universe uG uι
variable {G : Type uG} {ι : Type uι}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The coordinate matrix whose columns are the averaged lattice
vectors. -/
def averagedLatticeMatrix
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) : Matrix ι ι ℝ :=
  fun row column ↦
    (averagedLatticeVector ρ L hL t column :
      ι → ℝ) row

/-- The constructed averaged matrix is strictly column diagonally dominant. -/
theorem averagedLatticeMatrix_sum_col_lt_diag
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∀ k : ι,
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) j k‖ <
        ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) k k‖ := by
  intro k
  let B : ℝ := latticeApproximationRadius L
  let n : ℝ := Fintype.card G
  let s : ℝ := Fintype.card ι
  let t : ℝ := permutationLatticeScale L
  let E : ℝ := n * B
  have hB : 0 ≤ B :=
    latticeApproximationRadius_nonneg L
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hs : 0 ≤ s := by positivity
  have hE : 0 ≤ E := mul_nonneg hn.le hB
  have hoff (j : ι) (hjk : j ≠ k) :
      ‖averagedLatticeMatrix ρ L hL t j k‖ ≤ E := by
    change
      |(averagedLatticeVector ρ L hL t k :
        ι → ℝ) j| ≤ E
    exact averagedLatticeVector_offDiagonal_bound
      ρ L hL t hjk
  have hsum :
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
        s * E := by
    calc
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
          ∑ _j ∈ Finset.univ.erase k, E :=
        Finset.sum_le_sum fun j hj ↦
          hoff j (Finset.ne_of_mem_erase hj)
      _ ≤ ∑ _j : ι, E :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset k Finset.univ)
          (fun _ _ _ ↦ hE)
      _ = s * E := by simp [s]
  have hdiag :
      |(averagedLatticeMatrix ρ L hL t k k) -
          n * t| ≤ E := by
    exact averagedLatticeVector_diagonal_bound
      ρ L hL t k
  have hdiagLower :
      n * t - E ≤
        |averagedLatticeMatrix ρ L hL t k k| := by
    have hleft := (abs_le.mp hdiag).1
    have hself :
        averagedLatticeMatrix ρ L hL t k k ≤
          |averagedLatticeMatrix ρ L hL t k k| :=
      le_abs_self _
    nlinarith
  have hnumeric : s * E < n * t - E := by
    dsimp only [E, n, s, t, B]
    unfold permutationLatticeScale
    nlinarith
  calc
    ∑ j ∈ Finset.univ.erase k,
        ‖averagedLatticeMatrix ρ L hL
          (permutationLatticeScale L) j k‖ =
        ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ := by rfl
    _ ≤ s * E := hsum
    _ < n * t - E := hnumeric
    _ ≤ |averagedLatticeMatrix ρ L hL t k k| :=
      hdiagLower
    _ = ‖averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) k k‖ := by
      rfl

/-- Diagonal dominance proves that the actual averaged coordinate matrix is nonsingular. -/
theorem averagedLatticeMatrix_det_ne_zero
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    (averagedLatticeMatrix ρ L hL
      (permutationLatticeScale L)).det ≠ 0 :=
  det_ne_zero_of_sum_col_lt_diag
    (averagedLatticeMatrix_sum_col_lt_diag ρ L hL)

/-- The actual averaged lattice vectors are linearly independent over the reals. -/
theorem averagedLatticeVector_linearIndependent
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    LinearIndependent ℝ
      (fun i ↦
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i :
            ι → ℝ)) := by
  have hcols :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (averagedLatticeMatrix_det_ne_zero ρ L hL)
  change LinearIndependent ℝ
    (fun i j ↦
      averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) j i) at hcols
  simpa only [averagedLatticeMatrix] using hcols

/-- The original finite-group action permutes the actual averaged lattice vectors exactly. -/
theorem averagedLatticeVector_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (g : G) (i : ι) :
    permutationLatticeEquiv ρ L hL g
        (averagedLatticeVector ρ L hL t i) =
      averagedLatticeVector ρ L hL t (ρ g i) := by
  classical
  apply Subtype.ext
  ext j
  simp only [coe_permutationLatticeEquiv,
    permutationRepresentation, coordinatePermutation_apply,
    averagedLatticeVector_apply]
  let F : G → ℝ := fun h ↦
      (latticeApproximation L
        (t • Pi.single ((ρ h).symm i) (1 : ℝ)) :
          ι → ℝ) ((ρ h).symm ((ρ g).symm j))
  let H : G → ℝ := fun k ↦
      (latticeApproximation L
        (t • Pi.single ((ρ k).symm (ρ g i)) (1 : ℝ)) :
          ι → ℝ) ((ρ k).symm j)
  have hterm (h : G) : F h = H (g * h) := by
    dsimp only [F, H]
    have hindex :
        (ρ (g * h)).symm (ρ g i) = (ρ h).symm i := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    have hcoordinate :
        (ρ (g * h)).symm j =
          (ρ h).symm ((ρ g).symm j) := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    rw [hindex, hcoordinate]
  calc
    ∑ h : G, F h = ∑ h : G, H (g * h) := by
      exact Finset.sum_congr rfl fun h _ ↦ hterm h
    _ = ∑ k : G, H k := by
      exact Fintype.sum_bijective (g * ·)
        (Group.mulLeft_bijective g) (fun h ↦ H (g * h)) H
        fun _ ↦ rfl

end
end Dubon2026
