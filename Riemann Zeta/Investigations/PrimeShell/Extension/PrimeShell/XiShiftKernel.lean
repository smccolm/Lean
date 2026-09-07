import PrimeShell.TwoBandSourceSplit
import PrimeShell.ShiftKernel
import Zeta23.XiPrime.PrimeSide.PP

namespace PrimeShell

noncomputable section

open scoped BigOperators
open Zeta23 Zeta23.PrimeSide Zeta23.XiPrime Zeta23.ThmE

/-- One ordered dyadic difference-frequency pair for the actual complex
coefficient density `P_c`. -/
def xiDyadicDifferencePair
    (Φ : ℝ → ℝ) (T : ℝ) (c : ℕ → ℂ) (n m : ℕ) : ℝ :=
  wcoef c n * wcoef c m *
    AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg

/-- The literal two-orientation kernel for the complex coefficient pair at
positive shift `h`.  The coefficient phases remain inside the kernel. -/
def xiDyadicShiftKernel
    (Φ : ℝ → ℝ) (T : ℝ) (c : ℕ → ℂ) (n h : ℕ) : ℝ :=
  AminusPh Φ T (Real.log n) (Real.log (n + h))
      (c n).arg (c (n + h)).arg +
    AminusPh Φ T (Real.log (n + h)) (Real.log n)
      (c (n + h)).arg (c n).arg

/-- The nonnegative magnitude factor attached to a shifted complex
coefficient pair. -/
def xiDyadicCoeffWeight (c : ℕ → ℂ) (n h : ℕ) : ℝ :=
  wcoef c n * wcoef c (n + h)

theorem xiDyadicCoeffWeight_nonneg (c : ℕ → ℂ) (n h : ℕ) :
    0 ≤ xiDyadicCoeffWeight c n h := by
  exact mul_nonneg (wcoef_nonneg c n) (wcoef_nonneg c (n + h))

/-- The exact shifted dyadic sum for `P_c`, including both orientations
and the literal dyadic endpoint. -/
def xiDyadicShiftSum
    (Φ : ℝ → ℝ) (T : ℝ) (c : ℕ → ℂ) (N H : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N),
    if n + h ∈ Finset.Ioc N (2 * N) then
      xiDyadicCoeffWeight c n h * xiDyadicShiftKernel Φ T c n h
    else 0

private theorem xiStrictUpperTriangle_eq_shiftSum
    (Φ : ℝ → ℝ) (T : ℝ) (c : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), ∑ m ∈ Finset.Ioc N (2 * N),
      if n < m then
        xiDyadicDifferencePair Φ T c n m +
          xiDyadicDifferencePair Φ T c m n
      else 0) = xiDyadicShiftSum Φ T c N N := by
  let S := Finset.Ioc N (2 * N)
  have hfixed : ∀ n ∈ S,
      (∑ m ∈ S with n < m,
        (xiDyadicDifferencePair Φ T c n m +
          xiDyadicDifferencePair Φ T c m n)) =
      ∑ h ∈ Finset.Icc 1 N with n + h ∈ S,
        xiDyadicCoeffWeight c n h * xiDyadicShiftKernel Φ T c n h := by
    intro n hn
    apply Finset.sum_bij'
        (fun m _ => m - n) (fun h _ => n + h)
    · intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      rcases hm with ⟨hmS, hnm⟩
      have hnlow : N < n := (Finset.mem_Ioc.mp hn).1
      have hmhigh : m ≤ 2 * N := (Finset.mem_Ioc.mp hmS).2
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · rw [Nat.add_sub_of_le hnm.le]
        exact hmS
    · intro h hh
      simp only [Finset.mem_filter] at hh ⊢
      rcases hh with ⟨hhIcc, hmem⟩
      exact ⟨hmem, Nat.lt_add_of_pos_right (Finset.mem_Icc.mp hhIcc).1⟩
    · intro m hm
      simp only [Finset.mem_filter] at hm
      exact Nat.add_sub_of_le hm.2.le
    · intro h hh
      simp only [Finset.mem_filter] at hh
      exact Nat.add_sub_cancel_left n h
    · intro m hm
      simp only [Finset.mem_filter] at hm
      rcases hm with ⟨hmS, hnm⟩
      unfold xiDyadicDifferencePair xiDyadicCoeffWeight xiDyadicShiftKernel
      have hadd : n + (m - n) = m := Nat.add_sub_of_le hnm.le
      rw [← Nat.cast_add, hadd]
      ring
  unfold xiDyadicShiftSum
  change (∑ n ∈ S, ∑ m ∈ S, if n < m then
      xiDyadicDifferencePair Φ T c n m +
        xiDyadicDifferencePair Φ T c m n else 0) = _
  simp_rw [← Finset.sum_filter]
  calc
    (∑ n ∈ S, ∑ m ∈ S with n < m,
        (xiDyadicDifferencePair Φ T c n m +
          xiDyadicDifferencePair Φ T c m n)) =
        ∑ n ∈ S, ∑ h ∈ Finset.Icc 1 N with n + h ∈ S,
          xiDyadicCoeffWeight c n h * xiDyadicShiftKernel Φ T c n h := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hfixed n hn
    _ = ∑ h ∈ Finset.Icc 1 N, ∑ n ∈ S with n + h ∈ S,
          xiDyadicCoeffWeight c n h * xiDyadicShiftKernel Φ T c n h := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]

/-- Exact `m=n+h` rewrite of the complete dyadic `P_c` difference
off-diagonal.  This is the arithmetic boundary for the actual `xiCoeff`
sequence; the von Mangoldt-only rewrite is not substituted for it. -/
theorem xiDyadicDifferenceOffDiagonal_eq_shiftSum
    (Φ : ℝ → ℝ) (T : ℝ) (c : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), ∑ m ∈ Finset.Ioc N (2 * N),
      if n = m then 0 else xiDyadicDifferencePair Φ T c n m) =
      xiDyadicShiftSum Φ T c N N := by
  rw [offDiagonal_eq_strictUpperTriangle]
  exact xiStrictUpperTriangle_eq_shiftSum Φ T c N

end

end PrimeShell
