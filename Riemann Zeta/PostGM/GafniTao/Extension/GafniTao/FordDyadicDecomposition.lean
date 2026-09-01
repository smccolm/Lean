import GafniTao.FordExponentialSumAbel

/-!
# Exact dyadic decomposition in Ford Lemma 7.3

The last shell is cut at the literal integer endpoint `M`; it is not enlarged
to a full dyadic block.  This records the boundary truncation that is implicit
in the paper's `min(t,2^(j+1))` notation.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordShiftedWeightedBlock_add
    (sigma : ℝ) {A B C : ℕ} (u t : ℝ)
    (hAB : A ≤ B) (hBC : B ≤ C) :
    fordShiftedWeightedBlock sigma A B u t +
        fordShiftedWeightedBlock sigma B C u t =
      fordShiftedWeightedBlock sigma A C u t := by
  unfold fordShiftedWeightedBlock
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.Ioc_union_Ioc_eq_Ioc hAB hBC]

def fordDyadicWeightedShellSum
    (sigma : ℝ) (r M : ℕ) (u t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range r,
    fordShiftedWeightedBlock sigma (2 ^ j)
      (min M (2 ^ (j + 1))) u t

def fordDyadicRawMajorant
    (sigma : ℝ) (j : ℕ) (u t : ℝ) : ℝ :=
  (((2 ^ j + 1 : ℕ) : ℝ) + u) ^ (-sigma) *
    fordTheorem2Majorant (2 ^ j) t

/-- Theorem 2 controls a literal (possibly terminally truncated) shell. -/
theorem norm_fordShiftedWeightedBlock_dyadic_le_raw
    (hFord : FordTheorem2)
    {sigma u t : ℝ} {j M : ℕ}
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (huOne : u ≤ 1)
    (hMt : (M : ℝ) ≤ t) :
    ‖fordShiftedWeightedBlock sigma (2 ^ j)
        (min M (2 ^ (j + 1))) u t‖ ≤
      fordDyadicRawMajorant sigma j u t := by
  by_cases hNonempty : 2 ^ j < min M (2 ^ (j + 1))
  · have hNM : 2 ^ j ≤ M :=
      (Nat.le_of_lt hNonempty).trans (min_le_left _ _)
    have hNt : ((2 ^ j : ℕ) : ℝ) ≤ t := by
      exact (by exact_mod_cast hNM : ((2 ^ j : ℕ) : ℝ) ≤ M).trans hMt
    have hUpper : min M (2 ^ (j + 1)) ≤ 2 * 2 ^ j := by
      calc
        min M (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
        _ = 2 * 2 ^ j := by rw [pow_succ]; omega
    exact norm_fordShiftedWeightedBlock_le_of_fordTheorem2 hFord hsigma
      (pow_pos (by omega) _) hNt hu huOne hNonempty hUpper
  · have hEmpty : Finset.Ioc (2 ^ j) (min M (2 ^ (j + 1))) = ∅ :=
      Finset.Ioc_eq_empty hNonempty
    rw [fordShiftedWeightedBlock, hEmpty, Finset.sum_empty, norm_zero]
    unfold fordDyadicRawMajorant fordTheorem2Majorant
    positivity

/-- Triangle inequality after applying the exact bound to every retained
dyadic shell. -/
theorem norm_fordDyadicWeightedShellSum_le_raw_sum
    (hFord : FordTheorem2)
    {sigma u t : ℝ} {r M : ℕ}
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (huOne : u ≤ 1)
    (hMt : (M : ℝ) ≤ t) :
    ‖fordDyadicWeightedShellSum sigma r M u t‖ ≤
      ∑ j ∈ Finset.range r, fordDyadicRawMajorant sigma j u t := by
  unfold fordDyadicWeightedShellSum
  calc
    ‖∑ j ∈ Finset.range r,
        fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) u t‖ ≤
      ∑ j ∈ Finset.range r,
        ‖fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) u t‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range r,
        fordDyadicRawMajorant sigma j u t := by
      apply Finset.sum_le_sum
      intro j _hj
      exact norm_fordShiftedWeightedBlock_dyadic_le_raw hFord
        hsigma hu huOne hMt

/-- The first `r` dyadic shells are exactly `(1,min(M,2^r)]`. -/
theorem fordDyadicWeightedShellSum_eq_block
    (sigma : ℝ) (r M : ℕ) (u t : ℝ) :
    fordDyadicWeightedShellSum sigma r M u t =
      fordShiftedWeightedBlock sigma 1 (min M (2 ^ r)) u t := by
  induction r with
  | zero =>
      simp [fordDyadicWeightedShellSum, fordShiftedWeightedBlock]
  | succ r ih =>
      rw [fordDyadicWeightedShellSum, Finset.sum_range_succ]
      change fordDyadicWeightedShellSum sigma r M u t +
          fordShiftedWeightedBlock sigma (2 ^ r)
            (min M (2 ^ (r + 1))) u t = _
      rw [ih]
      by_cases hM : M ≤ 2 ^ r
      · have hMinLeft : min M (2 ^ r) = M := min_eq_left hM
        have hPow : 2 ^ r ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hUpper : min M (2 ^ (r + 1)) ≤ 2 ^ r := by
          exact (min_le_left _ _).trans hM
        rw [hMinLeft]
        have hMinSucc : min M (2 ^ (r + 1)) = M :=
          min_eq_left (hM.trans hPow)
        rw [hMinSucc]
        unfold fordShiftedWeightedBlock
        rw [Finset.Ioc_eq_empty_of_le hM, Finset.sum_empty, add_zero]
      · have hPowM : 2 ^ r ≤ M := by omega
        have hPowSucc : 2 ^ r ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hMiddle : 2 ^ r ≤ min M (2 ^ (r + 1)) :=
          le_min hPowM hPowSucc
        rw [min_eq_right hPowM]
        exact fordShiftedWeightedBlock_add sigma u t
          (one_le_pow₀ (by omega : (1 : ℕ) ≤ 2)) hMiddle

/-- Once `M ≤ 2^r`, the dyadic shell sum reaches the exact endpoint `M`. -/
theorem fordDyadicWeightedShellSum_eq_full_block
    (sigma : ℝ) {r M : ℕ} (u t : ℝ) (hM : M ≤ 2 ^ r) :
    fordDyadicWeightedShellSum sigma r M u t =
      fordShiftedWeightedBlock sigma 1 M u t := by
  rw [fordDyadicWeightedShellSum_eq_block, min_eq_left hM]

/-- The source sum `1 ≤ n ≤ M` is its first term plus the exact dyadic
shells. -/
theorem ford_sum_Icc_eq_first_add_dyadic
    (sigma : ℝ) {r M : ℕ} {u t : ℝ}
    (hMPos : 1 ≤ M) (hM : M ≤ 2 ^ r) :
    (∑ n ∈ Finset.Icc 1 M,
        ((n : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase n u t) =
      ((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t +
        fordDyadicWeightedShellSum sigma r M u t := by
  rw [Finset.Icc_eq_cons_Ioc hMPos, Finset.sum_cons]
  rw [fordDyadicWeightedShellSum_eq_full_block sigma u t hM]
  simp only [fordShiftedWeightedBlock, Nat.cast_one]

#print axioms fordShiftedWeightedBlock_add
#print axioms norm_fordShiftedWeightedBlock_dyadic_le_raw
#print axioms norm_fordDyadicWeightedShellSum_le_raw_sum
#print axioms fordDyadicWeightedShellSum_eq_block
#print axioms ford_sum_Icc_eq_first_add_dyadic

end

end GafniTao
