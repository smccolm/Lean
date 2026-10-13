/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/GaloisCohomology/Cyclic/Herbrand/Permutation/Lattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.PermutationLatticeApproximation

/-! # EquivariantLatticeAveraging

Actual finite-group averages of original lattice approximations with their necessary coordinate error bounds. These feed DUB-17's S-unit permutation-lattice comparison.
-/

namespace Dubon2026
noncomputable section
open Module Submodule
open scoped BigOperators
universe uG uι
variable {G : Type uG} {ι : Type uι}
variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The action of `g` on the coordinate space for a permutation
representation `ρ`. -/
def permutationRepresentation
    (ρ : G →* Equiv.Perm ι) (g : G) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  coordinatePermutation (ρ g)

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
/-- The identity group element acts identically on the original coordinate space. -/
@[simp]
theorem permutationRepresentation_one
    (ρ : G →* Equiv.Perm ι) :
    permutationRepresentation ρ 1 =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  change coordinatePermutation (ρ 1) =
    LinearEquiv.refl ℝ (ι → ℝ)
  rw [map_one]
  exact coordinatePermutation_refl

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
/-- The actual coordinate representation preserves group multiplication. -/
theorem permutationRepresentation_mul
    (ρ : G →* Equiv.Perm ι) (g h : G) :
    permutationRepresentation ρ (g * h) =
      (permutationRepresentation ρ h).trans
        (permutationRepresentation ρ g) := by
  simp only [permutationRepresentation, map_mul]
  exact coordinatePermutation_mul _ _

/-- Restrict a permutation representation to an invariant lattice. -/
def permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) : L ≃ₗ[ℤ] L where
  toFun x :=
    ⟨permutationRepresentation ρ g x.1, hL g x.1 x.2⟩
  invFun x :=
    ⟨permutationRepresentation ρ g⁻¹ x.1,
      hL g⁻¹ x.1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g⁻¹)
      (coordinatePermutation (ρ g) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g)
      (coordinatePermutation (ρ g⁻¹) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' n x := by
    apply Subtype.ext
    exact map_zsmul _ _ _

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
/-- Restricting to the actual invariant lattice retains the original coordinate action. -/
@[simp]
theorem coe_permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (x : L) :
    ((permutationLatticeEquiv ρ L hL g x : L) : ι → ℝ) =
      permutationRepresentation ρ g x :=
  rfl

/-- The equivariant average of lattice approximations to the large
coordinate vectors. -/
def averagedLatticeVector
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) : L :=
  ∑ g : G,
    permutationLatticeEquiv ρ L hL g
      (latticeApproximation L
        (t • Pi.single ((ρ g).symm i) (1 : ℝ)))

/-- A scale large enough to make the averaged lattice vectors strictly
column diagonally dominant. -/
def permutationLatticeScale
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
      latticeApproximationRadius L + 1

omit [DecidableEq ι] in
/-- The actual scale chosen for diagonal dominance is positive. -/
theorem permutationLatticeScale_pos
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    0 < permutationLatticeScale L := by
  have hB := latticeApproximationRadius_nonneg L
  have hs : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  unfold permutationLatticeScale
  nlinarith

/-- The actual averaged lattice vector is the finite sum of its transported coordinates. -/
@[simp]
theorem averagedLatticeVector_apply
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i j : ι) :
    (averagedLatticeVector ρ L hL t i : ι → ℝ) j =
      ∑ g : G,
        (latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
            ι → ℝ) ((ρ g).symm j) := by
  simp [averagedLatticeVector, permutationRepresentation]

omit [Fintype G] in
/-- Each diagonal averaging summand has the original uniform approximation error. -/
theorem averagingSummand_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) (i : ι) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i) - t| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm i)
  simpa using h

omit [Fintype G] in
/-- Each off-diagonal averaging summand is bounded by the original approximation radius. -/
theorem averagingSummand_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) {i j : ι}
    (hji : j ≠ i) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm j)
  have hne : (ρ g).symm j ≠ (ρ g).symm i :=
    (ρ g).symm.injective.ne hji
  simpa [hne] using h

/-- The actual averaged diagonal differs from group cardinality times scale by the stated bound. -/
theorem averagedLatticeVector_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) i -
        (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i)
  change |(∑ g : G, a g) -
    (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L
  have ha (g : G) :
      |a g - t| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_diagonal_bound ρ L t g i
  have heq :
      (∑ g : G, a g) -
          (Fintype.card G : ℝ) * t =
        ∑ g : G, (a g - t) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    |∑ g : G, (a g - t)| ≤
        ∑ g : G, |a g - t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

/-- Every actual off-diagonal averaged coordinate satisfies the group-cardinality error bound. -/
theorem averagedLatticeVector_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) {i j : ι} (hji : j ≠ i) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) j| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)
  change |∑ g : G, a g| ≤
    (Fintype.card G : ℝ) *
      latticeApproximationRadius L
  have ha (g : G) :
      |a g| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_offDiagonal_bound
        ρ L t g hji
  calc
    |∑ g : G, a g| ≤ ∑ g : G, |a g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

end
end Dubon2026
