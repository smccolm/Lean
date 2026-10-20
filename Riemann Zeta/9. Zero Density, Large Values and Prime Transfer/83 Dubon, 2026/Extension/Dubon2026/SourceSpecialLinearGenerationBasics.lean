/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Authors: Anne Baanen, Wen Yang

Modified for Project 83 from leanprover-community/mathlib4 at
8af27d91704d4e7c4a0cdf149d8ce56034e96c93. Only the diagonal and
transvection generation dependency is adapted to pinned Mathlib.
All declarations are locally renamed. No upstream elaborator options
are adopted.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! Determinant-one diagonal decomposition required to recover original
special-linear group stability from the actual source Lie action. -/

namespace Dubon2026
noncomputable section
open Matrix
variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- The transvection `1 + b · E_{i,j}` (the identity plus `b` in position `(i, j)`)
as an element of `SL ι F`, when `i ≠ j`. -/
def sourceSLTransvection {i j : ι} (hij : i ≠ j) (b : F) :
    Matrix.SpecialLinearGroup ι F :=
  ⟨Matrix.transvection i j b, Matrix.det_transvection_of_ne i j hij b⟩


/-- The elementary determinant-one matrix has its literal original matrix entries. -/
lemma sourceSLTransvection_coe {i j : ι} (hij : i ≠ j) (b : F) :
    (sourceSLTransvection hij b) = (1 : Matrix ι ι F) + single i j b := rfl

/-- The zero-parameter elementary matrix is the identity. -/
theorem sourceSLTransvection_zero {i j : ι} (hij : i ≠ j) :
    sourceSLTransvection hij (0 : F) = 1 := by
  apply Subtype.ext
  simp [sourceSLTransvection_coe]

/-- An element in SLₙ(F) induced by a diagonal matrix `1` on any other entries and `a`, `a⁻¹` on
  positition `i` and `j` respectively where `i ≠ j`. -/
noncomputable def sourceSLPairDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (a : F)
    (ha : a ≠ 0) : SpecialLinearGroup ι F :=
  ⟨diagonal (fun k ↦ if k = i then a else if k = j then a⁻¹ else 1), by
    simp [Finset.prod_ite, hij.symm, Finset.card_eq_one (s := {x : ι | x = i}).2 ⟨i, by grind⟩,
      mul_inv_cancel₀ ha]⟩

/-- The two-coordinate diagonal has the specified diagonal entries. -/
lemma sourceSLPairDiagonal_coe {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (a : F)
    (ha : a ≠ 0) : (sourceSLPairDiagonal hij a ha).1 = diagonal (fun k ↦
      if k = i then a else if k = j then a⁻¹ else 1) := rfl

/-- The coercion to matrices as a monoid homomorphism. -/
def sourceSLMatrixHom : SpecialLinearGroup ι F →* Matrix ι ι F where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The matrix homomorphism is the original subtype value. -/
@[simp]
lemma sourceSLMatrixHom_apply (g : SpecialLinearGroup ι F) : sourceSLMatrixHom g = (g : Matrix ι ι F) := rfl

/-- Passing to the underlying matrix loses no determinant-one element. -/
lemma sourceSLMatrixHom_injective : Function.Injective (sourceSLMatrixHom : SpecialLinearGroup ι F → _) :=
  Subtype.val_injective

private lemma sourceSL_diagonal_decompose (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    Finset.prod {i | i ≠ i₀} (fun i k ↦ if k = i then D i else
      if k = i₀ then (D i)⁻¹ else 1 : ι → ι → F) = D := by
  rw [det_diagonal, show Finset.univ = insert i₀ ({i | i ≠ i₀} : Finset ι) by grind,
    Finset.prod_insert (by grind), mul_eq_one_iff_eq_inv₀ (by grind),
    ← Finset.prod_inv_distrib] at hD
  ext x
  by_cases hx : x = i₀
  · simpa [hx, hD, -Finset.prod_inv_distrib] using Finset.prod_congr rfl (by grind)
  · simp [hx]

/-- Every entry of a determinant-one diagonal matrix is nonzero. -/
lemma sourceSL_diagonal_ne_zero (D : ι → F) (hD : det (diagonal D) = 1) (j : ι) :
    D j ≠ 0 := fun h ↦ by
  rw [det_diagonal, show Finset.univ = insert j ({i | i ≠ j} : Finset ι) by grind,
    Finset.prod_insert (by grind), h, zero_mul] at hD
  exact zero_ne_one hD

/-- The two-coordinate diagonal factors in the determinant-one decomposition commute. -/
lemma sourceSL_diagonal_commute (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    (({i | i ≠ i₀} : Finset ι) : Set ι).Pairwise (Function.onFun Commute fun i ↦
      if hi : i ≠ i₀ then sourceSLPairDiagonal hi (D i) (sourceSL_diagonal_ne_zero D hD i) else 1) := by
  intro i1 hi1 i2 hi2 hi12
  ext i j
  simp [apply_dite, sourceSLPairDiagonal_coe]
  split_ifs <;> simp [diagonal_apply]; grind

/-- Every determinant-one diagonal matrix is the actual finite product of two-coordinate diagonals. -/
lemma sourceSL_diagonal_product (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    (⟨diagonal D, hD⟩ : SpecialLinearGroup ι F) =
      Finset.noncommProd {i : ι | i ≠ i₀} (fun i ↦ if hi : i ≠ i₀ then
      sourceSLPairDiagonal hi (D i) (sourceSL_diagonal_ne_zero D hD i) else 1) (sourceSL_diagonal_commute i₀ D hD) := by
  set g : ι → ι → F := fun i k ↦ if k = i then D i else if k = i₀ then (D i)⁻¹ else 1 with hg_def
  apply sourceSLMatrixHom_injective
  rw [Finset.map_noncommProd]
  simp_rw [sourceSLMatrixHom_apply, apply_dite, SpecialLinearGroup.coe_one]
  rw [Finset.noncommProd_congr (s₂ := {i | i ≠ i₀}) rfl (fun i hi ↦
      (dif_pos (Finset.mem_filter.1 hi).2 : _ = (sourceSLPairDiagonal (Finset.mem_filter.1 hi).2 _ _).1))]
  convert_to! _ = Finset.noncommProd {i | i ≠ i₀} (fun x ↦ diagonal (g x)) _
  simp_rw [← diagonalRingHom_apply]
  rw [← Finset.map_noncommProd _ _ (fun _ _ _ _ _ ↦ Commute.all _ _), Finset.noncommProd_eq_prod]
  rw [sourceSL_diagonal_decompose i₀ D hD]


end
end Dubon2026
