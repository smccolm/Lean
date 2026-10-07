import Dubon2026.CuspCosetTrace
import Dubon2026.CuspPeriodRankinSeries
import Mathlib.NumberTheory.LSeries.Linearity

/-! # Actual normalized coefficients of the finite cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

variable {N : ℕ} {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)]
  (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)

/-- The genuine finite sum of normalized common-period cusp coefficient squares. -/
def cuspTraceSquareCoefficients (n : ℕ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ H, ‖normalizedCuspPeriodCoefficients (cuspCosetFamily hH f q) N n‖ ^ 2

/-- Every actual trace-square coefficient is nonnegative. -/
theorem cuspTraceSquareCoefficients_nonneg (n : ℕ) :
    0 ≤ cuspTraceSquareCoefficients hH f n := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The zero coefficient vanishes because every genuine translated form is cuspidal. -/
theorem cuspTraceSquareCoefficients_zero (hN : 0 < N) : cuspTraceSquareCoefficients hH f 0 = 0 := by
  unfold cuspTraceSquareCoefficients
  apply Finset.sum_eq_zero
  intro q _
  rw [normalizedCuspPeriodCoefficients_zero _ (by exact_mod_cast hN) (by simp [strictPeriods_Gamma])]
  simp

/-- The actual trace coefficient has the exact weight shift from its unnormalized q-expansions. -/
theorem cuspTraceSquareCoefficients_eq (n : ℕ) :
    cuspTraceSquareCoefficients hH f n =
      (∑ q : SL(2, ℤ) ⧸ H, ‖(qExpansion (N : ℝ) (cuspCosetFamily hH f q)).coeff n‖ ^ 2) *
        (n : ℝ) ^ (1 - (k : ℝ)) := by
  simp only [cuspTraceSquareCoefficients, norm_sq_normalizedCuspPeriodCoefficients, Finset.sum_mul]

/-- The true finite trace coefficients have a linear summatory bound derived from their actual period Parseval estimates. -/
theorem exists_cuspTraceSquare_sum_upper [NeZero N] (hk : 0 < k) :
    ∃ B : ℝ, 0 < B ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, cuspTraceSquareCoefficients hH f n) ≤ B * X := by
  have hb (q : SL(2, ℤ) ⧸ H) := exists_normalized_cusp_period_square_upper
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast Nat.pos_of_neZero N)
    (by simp [strictPeriods_Gamma]) hk
  choose B hB hb using hb
  have hsum : 0 ≤ ∑ q : SL(2, ℤ) ⧸ H, B q := Finset.sum_nonneg (fun q _ => (hB q).le)
  refine ⟨1 + ∑ q : SL(2, ℤ) ⧸ H, B q, by positivity, fun X => ?_⟩
  simp only [cuspTraceSquareCoefficients]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q : SL(2, ℤ) ⧸ H, B q * X := Finset.sum_le_sum (fun q _ => hb q X)
    _ = (∑ q : SL(2, ℤ) ⧸ H, B q) * X := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + ∑ q : SL(2, ℤ) ⧸ H, B q) * X := by nlinarith [Nat.cast_nonneg (α := ℝ) X]

/-- The actual trace-square Dirichlet series converges absolutely to the right of one. -/
theorem cuspTraceSquare_lseriesSummable [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (cuspTraceSquareCoefficients hH f n : ℂ)) s := by
  have hb (q : SL(2, ℤ) ⧸ H) := normalized_cusp_period_square_lseries_summable
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast Nat.pos_of_neZero N)
    (by simp [strictPeriods_Gamma]) hk hs
  simpa only [cuspTraceSquareCoefficients, Complex.ofReal_sum, Finset.sum_fn] using
    LSeriesSummable.sum (S := Finset.univ) (fun q _ => hb q)

/-- The genuine trace Dirichlet series is exactly the finite sum of its cusp-period Rankin series. -/
theorem cuspTraceSquare_LSeries [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (cuspTraceSquareCoefficients hH f n : ℂ)) s =
      ∑ q : SL(2, ℤ) ⧸ H, cuspPeriodRankinSeries (cuspCosetFamily hH f q) N s := by
  have hb (q : SL(2, ℤ) ⧸ H) := normalized_cusp_period_square_lseries_summable
    (cuspCosetFamily hH f q) (h := (N : ℝ)) (by exact_mod_cast Nat.pos_of_neZero N)
    (by simp [strictPeriods_Gamma]) hk hs
  simpa only [cuspTraceSquareCoefficients, Complex.ofReal_sum, cuspPeriodRankinSeries, Finset.sum_fn] using
    LSeries_sum (S := Finset.univ) (fun q _ => hb q)

end
end Dubon2026
