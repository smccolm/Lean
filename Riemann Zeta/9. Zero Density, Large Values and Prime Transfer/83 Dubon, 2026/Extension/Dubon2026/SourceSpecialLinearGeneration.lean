/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Authors: Anne Baanen, Wen Yang, Chris Birkbeck, The Tau Ceti contributors

Modified for Project 83 from Mathlib 8af27d91704d4e7c4a0cdf149d8ce56034e96c93
and TauCeti cc73e43d461427571b62274c83057192b01aa567.
Only field-valued generation is adapted, with local names and no
changes to the pinned toolchain or elaborator options.
-/
import Dubon2026.SourceSpecialLinearGenerationBasics

/-! Generation by elementary matrices for recovery of the actual
special-linear action on the original source coefficient module. -/

namespace Dubon2026
noncomputable section
open Matrix
variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- A determinant-one matrix is a product of elementary matrices, a determinant-one diagonal matrix, and elementary matrices. -/
theorem sourceSL_diagonal_transvection_decomposition (M : SpecialLinearGroup ι F) :
    ∃ (L L' : List (TransvectionStruct ι F)) (D : ι → F) (hD : det (diagonal D) = 1),
      M = (L.map (fun t => sourceSLTransvection t.hij t.c)).prod * ⟨diagonal D, hD⟩ *
        (L'.map (fun t => sourceSLTransvection t.hij t.c)).prod := by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.1
  refine ⟨L, L', D, by simpa [hM] using M.2, ?_⟩
  apply sourceSLMatrixHom_injective
  simp only [map_mul, map_list_prod, List.map_map]
  exact hM

/-- The two-coordinate determinant-one diagonal is a product of six elementary matrices. -/
theorem sourceSL_pairDiagonal_decompose {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    sourceSLPairDiagonal hij a ha =
      sourceSLTransvection hij a * sourceSLTransvection hij.symm (-a⁻¹) *
        sourceSLTransvection hij a * sourceSLTransvection hij (-1) *
        sourceSLTransvection hij.symm 1 * sourceSLTransvection hij (-1) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, sourceSLPairDiagonal_coe, sourceSLTransvection_coe]
  ext p q
  simp only [Matrix.mul_add, mul_one, Matrix.add_mul, one_mul, Matrix.single_mul_single_same,
    mul_neg, mul_inv_cancel₀ ha,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, add_zero, neg_mul,
    inv_mul_cancel₀ ha, neg_neg, ne_eq, hij, not_false_eq_true,
    Matrix.single_mul_single_of_ne, Matrix.add_apply]
  by_cases hpi : p = i <;> by_cases hpj : p = j <;>
    by_cases hqi : q = i <;> by_cases hqj : q = j
  all_goals simp_all [Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, eq_comm]

/-- Every property of determinant-one matrices containing the identity and elementary matrices and closed under multiplication holds for every determinant-one matrix over the field. -/
theorem sourceSL_transvection_induction (P : SpecialLinearGroup ι F → Prop)
    (h1 : P 1)
    (ht : ∀ (i j : ι) (hij : i ≠ j) (a : F), P (sourceSLTransvection hij a))
    (hmul : ∀ A B, P A → P B → P (A * B)) (M : SpecialLinearGroup ι F) : P M := by
  by_cases hn : Nonempty ι
  · letI := hn
    let i₀ : ι := Classical.choice hn
    have hpair (i j : ι) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
        P (sourceSLPairDiagonal hij a ha) := by
      rw [sourceSL_pairDiagonal_decompose]
      exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _
        (ht i j hij a) (ht j i hij.symm (-a⁻¹))) (ht i j hij a))
        (ht i j hij (-1))) (ht j i hij.symm 1)) (ht i j hij (-1))
    have hdiag (D : ι → F) (hD : det (diagonal D) = 1) : P ⟨diagonal D, hD⟩ := by
      rw [sourceSL_diagonal_product i₀ D hD]
      refine Finset.noncommProd_induction _ _ _ P hmul h1 fun i hi => ?_
      simp [(Finset.mem_filter.1 hi).2, hpair]
    have hlist (L : List (TransvectionStruct ι F)) :
        P (L.map (fun t => sourceSLTransvection t.hij t.c)).prod := by
      induction L with
      | nil => simpa using h1
      | cons t L ih =>
        rw [List.map_cons, List.prod_cons]
        exact hmul _ _ (ht t.i t.j t.hij t.c) ih
    obtain ⟨L, L', D, hD, hM⟩ := sourceSL_diagonal_transvection_decomposition M
    exact hM ▸ hmul _ _ (hmul _ _ (hlist L) (hdiag D hD)) (hlist L')
  · letI : IsEmpty ι := not_nonempty_iff.mp hn
    have hM : M = 1 := Subtype.ext (Matrix.ext fun i => isEmptyElim i)
    rwa [hM]

end
end Dubon2026
