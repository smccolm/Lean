import PrimeShell.XiShiftKernel
import PrimeShell.Admissible
import Zeta23.XiPrime.PrimeSide.PP

namespace PrimeShell

noncomputable section

open scoped BigOperators
open MeasureTheory Zeta23 Zeta23.PrimeSide Zeta23.ThmE Zeta23.XiPrime

/-- The complete difference-frequency off-diagonal for a complex
coefficient sequence.  This is the `O₁` term of the exact `P_c` trace. -/
def xiDifferenceOffDiagonal
    (Φ : ℝ → ℝ) (T X : ℝ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else
      wcoef c n * wcoef c m *
        AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg

/-- The complete sum-frequency off-diagonal for a complex coefficient
sequence.  This is the `O₂` term of the exact `P_c` trace. -/
def xiSumOffDiagonal
    (Φ : ℝ → ℝ) (T X : ℝ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    wcoef c n * wcoef c m *
      AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg

/-- The narrow arithmetic boundary for a beyond-support-one `P_c`
calculation.  It controls the two literal pair kernels and does not mention
matrices, traces, zero counts, or a spectral conclusion. -/
def XiPairArithmeticControl
    (Φ : ℝ → ℝ) (T X : ℝ) (c : ℕ → ℂ) (E : ℝ) : Prop :=
  |xiDifferenceOffDiagonal Φ T X c + xiSumOffDiagonal Φ T X c| ≤ E

/-- Exact three-piece decomposition of the complex-coefficient prime
trace.  Both off-diagonals remain separately accessible. -/
theorem Mform_Pc_Pc_eq_diagonal_add_pair_terms
    (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) (c : ℕ → ℂ) :
    Mform Φ T (Pc X c) (Pc X c) =
      (1 / (2 * Real.pi ^ 2)) *
        ((∑ n ∈ primeRange X,
            wcoef c n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)) +
          xiDifferenceOffDiagonal Φ T X c +
          xiSumOffDiagonal Φ T X c) := by
  simpa [xiDifferenceOffDiagonal, xiSumOffDiagonal] using
    Zeta23.XiPrime.Mform_Pc_Pc hT hΦ c X

/-- Complete analytic consumer of the literal pair-kernel boundary.  The
diagonal error is proved from Fourier inversion; the supplied arithmetic
input is used only for the two exact off-diagonal sums. -/
theorem abs_Mform_Pc_Pc_sub_diagonalMain_le
    (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦtwo : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|)
    {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * Real.pi * g y)
    (X : ℝ) (c : ℕ → ℂ) {E : ℝ}
    (hpair : XiPairArithmeticControl Φ T X c E) :
    |Mform Φ T (Pc X c) (Pc X c) -
        T / Real.pi *
          (∑ n ∈ primeRange X, ‖c n‖ ^ 2 / n * g (Real.log n))| ≤
      (1 / Real.pi ^ 2) *
          ((1 / 2) * (∑ n ∈ primeRange X, wcoef c n ^ 2) *
            ∫ x, Φ x ^ 2 * |x|) +
        (1 / (2 * Real.pi ^ 2)) * E := by
  have hdiag := diag_estimate_w hT hΦ hΦtwo hΦabs hFT X (wcoef c)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale : 0 ≤ (1 / Real.pi ^ 2 : ℝ) := by positivity
  have hhalf : 0 ≤ (1 / (2 * Real.pi ^ 2) : ℝ) := by positivity
  have hweight :
      (∑ n ∈ primeRange X, wcoef c n ^ 2 * g (Real.log n)) =
        ∑ n ∈ primeRange X, ‖c n‖ ^ 2 / n * g (Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [wcoef_sq]
  rw [Mform_Pc_Pc_eq_diagonal_add_pair_terms hT hΦ, ← hweight]
  let D := ∑ n ∈ primeRange X,
    wcoef c n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)
  let O := xiDifferenceOffDiagonal Φ T X c +
    xiSumOffDiagonal Φ T X c
  let G := ∑ n ∈ primeRange X, wcoef c n ^ 2 * g (Real.log n)
  have hsplit :
      (1 / (2 * Real.pi ^ 2)) * (D + O) - T / Real.pi * G =
        (1 / Real.pi ^ 2) * ((1 / 2) * D - Real.pi * T * G) +
          (1 / (2 * Real.pi ^ 2)) * O := by
    field_simp
    ring
  rw [show D + xiDifferenceOffDiagonal Φ T X c +
      xiSumOffDiagonal Φ T X c = D + O by
        dsimp [O]
        ring, hsplit]
  calc
    |(1 / Real.pi ^ 2) * ((1 / 2) * D - Real.pi * T * G) +
        (1 / (2 * Real.pi ^ 2)) * O| ≤
        |(1 / Real.pi ^ 2) * ((1 / 2) * D - Real.pi * T * G)| +
          |(1 / (2 * Real.pi ^ 2)) * O| := abs_add_le _ _
    _ = (1 / Real.pi ^ 2) * |(1 / 2) * D - Real.pi * T * G| +
          (1 / (2 * Real.pi ^ 2)) * |O| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hscale, abs_of_nonneg hhalf]
    _ ≤ (1 / Real.pi ^ 2) *
          ((1 / 2) * (∑ n ∈ primeRange X, wcoef c n ^ 2) *
            ∫ x, Φ x ^ 2 * |x|) +
          (1 / (2 * Real.pi ^ 2)) * E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hdiag hscale
      · exact mul_le_mul_of_nonneg_left hpair hhalf

end

noncomputable section

open scoped BigOperators
open MeasureTheory Zeta23 Zeta23.PrimeSide Zeta23.ThmE Zeta23.XiPrime

/-- The exact arithmetic boundary at the coefficient sequence used by the
ξ′ trace.  In particular, it is not silently replaced by `Λ`. -/
def XiCoeffPairArithmeticControl
    (A : PrimeShellAdmissible) (T E : ℝ) : Prop :=
  XiPairArithmeticControl (A.P.PhiR T) T (A.P.X T)
    (Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T)) E

/-- The source-specific consumer for the actual `xiCoeff (LT T)` prime
polynomial.  All analytic window facts are derived from the admissible
taper; the only premise left at the boundary is the literal pair-sum
estimate above. -/
theorem abs_actualXiPrimeTrace_sub_diagonalMain_le
    (A : PrimeShellAdmissible) {T E : ℝ}
    (hT : 0 ≤ T) (hTwo : 2 * A.P.w ≤ A.P.L T)
    (hpair : XiCoeffPairArithmeticControl A T E) :
    |Mform (A.P.PhiR T) T
          (Pc (A.P.X T) (Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T)))
          (Pc (A.P.X T) (Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T))) -
        T / Real.pi *
          (∑ n ∈ primeRange (A.P.X T),
            ‖Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T) n‖ ^ 2 / n *
              A.P.g T (Real.log n))| ≤
      (1 / Real.pi ^ 2) *
          ((1 / 2) *
              (∑ n ∈ primeRange (A.P.X T),
                wcoef (Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T)) n ^ 2) *
            ∫ x, A.P.PhiR T x ^ 2 * |x|) +
        (1 / (2 * Real.pi ^ 2)) * E := by
  have hwPos : 0 < A.P.w := one_pos.trans_le A.one_le_w
  apply abs_Mform_Pc_Pc_sub_diagonalMain_le hT
    (Taper.PhiR_continuous A.taper hwPos hTwo)
    (Taper.integrable_PhiR_sq A.taper hwPos hTwo)
    (Taper.integrable_PhiR_sq_mul_abs A.taper hwPos hTwo)
    (Taper.integral_PhiR_sq_mul_cos A.taper hwPos hTwo)
    (A.P.X T) (Zeta23.XiPrime.xiCoeff (Zeta23.XiPrime.LT T)) hpair

end

end PrimeShell
