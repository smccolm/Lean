import Dubon2026.SourceSL2CocycleMatrices

/-! DUB-17/18 -> residual Galois association -> the detected finite-order
branch of original weight-two H1 -> Hecke eigenvalues ell+1.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
The local reuse search found no finite-order diagonal-Hecke conjugacy
calculation. Existing original integral conjugation and native H1 are reused.
-/
namespace Dubon2026.SourceFiniteOrder
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The integral recurrence expressing powers of the original determinant-one matrix. -/
def U (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (k + 2) => t * U t (k + 1) - U t k

/-- The recurrence has zero constant-index value. -/
@[scoped simp] theorem U_zero (t : ℤ) : U t 0 = 0 := rfl
/-- The recurrence has unit first-index value. -/
@[scoped simp] theorem U_one (t : ℤ) : U t 1 = 1 := rfl
/-- The recurrence satisfies its exact second-order relation. -/
theorem U_add_two (t : ℤ) (k : ℕ) : U t (k + 2) = t * U t (k + 1) - U t k := rfl

/-- At trace of absolute value at least two, the recurrence grows strictly in absolute value. -/
theorem U_growth (t : ℤ) (ht : 2 ≤ |t|) :
    ∀ k : ℕ, (k : ℤ) ≤ |U t k| ∧ |U t k| + 1 ≤ |U t (k + 1)| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by push_cast; omega, ?_⟩
    rw [U_add_two]
    have h1 : |t * U t (k + 1)| - |U t k| ≤ |t * U t (k + 1) - U t k| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (U t (k + 1)), abs_nonneg t, abs_nonneg (U t k)]

/-- The original determinant-one matrix satisfies its entrywise quadratic characteristic identity. -/
theorem mul_self_apply (M : SL(2, ℤ)) (i j : Fin 2) :
    M i 0 * M 0 j + M i 1 * M 1 j = (M 0 0 + M 1 1) * M i j - (if i = j then 1 else 0) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at hdet
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination -hdet

/-- Every positive power of the original matrix has the exact recurrence expansion. -/
theorem pow_succ_apply (M : SL(2, ℤ)) (k : ℕ) : ∀ i j : Fin 2,
    (M ^ (k + 1)) i j =
      U (M 0 0 + M 1 1) (k + 1) * M i j - U (M 0 0 + M 1 1) k * (if i = j then 1 else 0) := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    have ch := mul_self_apply M i j
    have h0 := ih i 0
    have h1 := ih i 1
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, h1,
      U_add_two]
    fin_cases i <;> fin_cases j <;> simp at ch ⊢ <;>
      linear_combination (U (M 0 0 + M 1 1) (k + 1)) * ch

/-- An actual finite-order integral determinant-one matrix is diagonal or has trace of absolute value at most one. -/
theorem offDiag_eq_zero_or_natAbs_trace_le_one (M : SL(2, ℤ)) {n : ℕ} (hn : 0 < n)
    (h : M ^ n = 1) : (M 0 1 = 0 ∧ M 1 0 = 0) ∨ (M 0 0 + M 1 1).natAbs ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set t := M 0 0 + M 1 1 with ht
  have e01 : U t (k + 1) * M 0 1 = 0 := by
    have := pow_succ_apply M k 0 1
    rw [h] at this
    simpa using this.symm
  have e10 : U t (k + 1) * M 1 0 = 0 := by
    have := pow_succ_apply M k 1 0
    rw [h] at this
    simpa using this.symm
  by_cases hU : U t (k + 1) = 0
  · right
    by_contra hlt
    have h2 : 2 ≤ |t| := by
      rw [Int.abs_eq_natAbs]; omega
    have := (U_growth t h2 (k + 1)).1
    rw [hU, abs_zero] at this
    push_cast at this
    omega
  · left
    exact ⟨(mul_eq_zero.mp e01).resolve_left hU, (mul_eq_zero.mp e10).resolve_left hU⟩


end
end Dubon2026.SourceFiniteOrder
