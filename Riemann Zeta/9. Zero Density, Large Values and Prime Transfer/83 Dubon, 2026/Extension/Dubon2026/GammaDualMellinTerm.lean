import Dubon2026.RankinPerronDualInterchange

/-! # The genuine Mellin transform for arbitrary positive dual conductors -/

namespace Dubon2026

open Complex

noncomputable section

/-- The actual positive conductor and positive-index Mellin powers combine without a square-root normalization. -/
theorem positive_conductor_mellin_power {A x n : ℝ} (hA : 0 < A) (hx : 0 < x) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ (s + 2) * (A : ℂ) ^ s * (n : ℂ) ^ (s - 1) =
      ((x : ℂ) ^ 2 / (n : ℂ)) * ((A * n * x : ℝ) : ℂ) ^ s := by
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hn0 := Complex.ofReal_ne_zero.mpr hn.ne'
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_nonneg hA.le hn.le) hx.le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hA.le hn.le,
    Complex.cpow_add _ _ hx0, Complex.cpow_sub _ _ hn0, Complex.cpow_one]
  norm_num only [Complex.cpow_ofNat]
  ring

/-- Every real coefficient's reflected Dirichlet term has the precise reciprocal index and positive-conductor Gamma Mellin factor. -/
theorem coefficient_reflected_mellin_term (a : ℕ → ℝ) (ha0 : a 0 = 0) (k : ℝ) {A x : ℝ}
    (hA : 0 < A) (hx : 0 < x) (s : ℂ) (n : ℕ) :
    ((x : ℂ) ^ (s + 2) * (A : ℂ) ^ s * gammaRieszSymbol k 2 s) *
      LSeries.term (fun n => (a n : ℂ)) (1 - s) n =
        (((a n / (n : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ 2) * gammaRieszMellinFunction k 2 (A * n * x) s := by
  rw [LSeries.term_def₀ (by simp only [ha0, ofReal_zero]), show -(1 - s) = s - 1 by ring]
  by_cases hn : n = 0
  · simp [hn, ha0]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he := positive_conductor_mellin_power hA hx hn0 s
    simp only [Complex.ofReal_natCast] at he
    rw [gammaRieszMellinFunction]
    calc
      _ = (a n : ℂ) * gammaRieszSymbol k 2 s *
          ((x : ℂ) ^ (s + 2) * (A : ℂ) ^ s * (n : ℂ) ^ (s - 1)) := by ring
      _ = _ := by rw [he]; push_cast; ring

/-- Each actual coefficient's finite reflected vertical integral equals the literal weighted Gamma cutoff. -/
theorem coefficient_reflected_mellin_term_integral (a : ℕ → ℝ) (ha0 : a 0 = 0) (k : ℝ) {A x : ℝ}
    (hA : 0 < A) (hx : 0 < x) (T : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t in -T..T,
      ((x : ℂ) ^ (gammaVerticalPoint (-1 / 8) t + 2) *
        (A : ℂ) ^ (gammaVerticalPoint (-1 / 8) t) * gammaRieszSymbol k 2 (gammaVerticalPoint (-1 / 8) t)) *
          LSeries.term (fun n => (a n : ℂ)) (1 - gammaVerticalPoint (-1 / 8) t) n) =
      gammaRieszDualCutoffTerm a k A x T n := by
  simp_rw [coefficient_reflected_mellin_term a ha0 k hA hx]
  rw [intervalIntegral.integral_const_mul]
  simp only [gammaRieszDualCutoffTerm, gammaRieszVerticalCutoff, gammaRieszLine,
    show (3 / 8 : ℝ) - 2 / 4 = -1 / 8 by norm_num, Complex.real_smul]
  ring

end
end Dubon2026
