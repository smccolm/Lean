/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/GaloisCohomology/Cyclic/Herbrand/Permutation/Lattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # PermutationLatticeApproximation

The actual bounded lattice approximation required for DUB-17's finite-index permutation comparison. The unused general-basis transport is omitted.
-/

namespace Dubon2026
noncomputable section
open Module Submodule
open scoped BigOperators
universe uG uι
variable {G : Type uG} {ι : Type uι}
/-- The linear coordinate permutation attached to a permutation of the
indexing type. -/
def coordinatePermutation (σ : Equiv.Perm ι) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of the original coordinate permutation. -/
@[simp]
theorem coordinatePermutation_apply
    (σ : Equiv.Perm ι) (x : ι → ℝ) (i : ι) :
    coordinatePermutation σ x i = x (σ.symm i) :=
  rfl

/-- The identity permutation acts as the identity linear equivalence. -/
@[simp]
theorem coordinatePermutation_refl :
    coordinatePermutation (Equiv.refl ι) =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  ext x i
  rfl

/-- Composition of actual coordinate permutations agrees with multiplication. -/
theorem coordinatePermutation_mul
    (σ τ : Equiv.Perm ι) :
    coordinatePermutation (σ * τ) =
      (coordinatePermutation τ).trans
        (coordinatePermutation σ) := by
  ext x i
  rfl

/-- The inverse permutation induces the inverse linear equivalence. -/
@[simp]
theorem coordinatePermutation_inv
    (σ : Equiv.Perm ι) :
    coordinatePermutation σ⁻¹ =
      (coordinatePermutation σ).symm := by
  rw [show σ⁻¹ = σ.symm from rfl]
  ext x i
  rfl
section Approximation

variable [Fintype ι]

/-- A canonical lattice point whose difference from `x` lies in the
fundamental parallelepiped of a chosen lattice basis. -/
def latticeApproximation
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) : L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  refine ⟨ZSpan.floor bℝ x, ?_⟩
  let z : ι → ℝ := (ZSpan.floor bℝ x).1
  change z ∈ L
  rw [← b.ofZLatticeBasis_span ℝ]
  exact (ZSpan.floor bℝ x).property

/-- A uniform approximation radius for the canonical lattice
approximation. -/
def latticeApproximationRadius
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  ∑ i, ‖bℝ i‖

/-- The actual lattice approximation radius is nonnegative. -/
theorem latticeApproximationRadius_nonneg
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    0 ≤ latticeApproximationRadius L := by
  unfold latticeApproximationRadius
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- The chosen original lattice point approximates every vector within the fixed radius. -/
theorem norm_sub_latticeApproximation_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) :
    ‖x - (latticeApproximation L x : ι → ℝ)‖ ≤
      latticeApproximationRadius L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  simpa only [latticeApproximation, latticeApproximationRadius,
    ZSpan.fract] using ZSpan.norm_fract_le bℝ x

/-- Each coordinate error is bounded by the actual lattice approximation radius. -/
theorem abs_latticeApproximation_sub_apply_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) (i : ι) :
    |(latticeApproximation L x : ι → ℝ) i - x i| ≤
      latticeApproximationRadius L := by
  have hcoord :
      ‖(x - (latticeApproximation L x : ι → ℝ)) i‖ ≤
        ‖x - (latticeApproximation L x : ι → ℝ)‖ :=
    norm_le_pi_norm (x - (latticeApproximation L x : ι → ℝ)) i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] at hcoord
  exact hcoord.trans (norm_sub_latticeApproximation_le L x)

end Approximation

end
end Dubon2026
