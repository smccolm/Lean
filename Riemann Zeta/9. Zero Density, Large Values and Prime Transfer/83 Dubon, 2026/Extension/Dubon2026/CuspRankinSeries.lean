import Dubon2026.CuspComplexMellin
import Mathlib.NumberTheory.LSeries.Deriv

/-! # The actual normalized square Dirichlet series in its convergent half-plane -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- Squared automorphic normalization uses precisely n^(1-k). -/
theorem norm_sq_normalizedCuspCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    ‖normalizedCuspCoefficients f n‖ ^ 2 =
      ‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (1 - (k : ℝ)) := by
  rw [norm_normalizedCuspCoefficients, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

/-- The actual normalized square Dirichlet term is the classical term with the full weight shift. -/
theorem normalized_cusp_square_term {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (s : ℂ) (n : ℕ) :
    ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) =
      ((‖cuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(s + (k : ℂ) - 1)) := by
  rw [norm_sq_normalizedCuspCoefficients]
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), mul_assoc]
    push_cast
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    congr 2
    ring

/-- The normalized squared coefficients give an actual absolutely convergent series for Re(s)>1. -/
theorem summable_normalized_cusp_square_dirichlet {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
  have ht : (k : ℝ) < (s + (k : ℂ) - 1).re := by simp; linarith
  exact (summable_cusp_complex_square_dirichlet f hk ht).congr
    (fun n => (normalized_cusp_square_term f s n).symm)

/-- Mathlib's L-series term has the literal normalized square-coefficient summand, also at zero. -/
theorem normalized_cusp_square_lseries_term {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => ((‖normalizedCuspCoefficients f m‖ ^ 2 : ℝ) : ℂ)) s n =
      ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · subst n
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  · rw [if_neg hn, Complex.cpow_neg, div_eq_mul_inv]

/-- The genuine normalized square L-series converges throughout Re(s)>1. -/
theorem normalized_cusp_square_lseries_summable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ)) s := by
  apply (summable_normalized_cusp_square_dirichlet f hk hs).congr
  intro n
  exact (normalized_cusp_square_lseries_term f s n).symm

/-- The Rankin square series of the actual automorphically normalized Fourier coefficients. -/
def cuspRankinSeries {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (s : ℂ) : ℂ :=
  LSeries (fun n => ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ)) s

/-- The constructed Rankin series is the literal infinite sum, not an independently supplied analytic function. -/
theorem cuspRankinSeries_eq_tsum {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (s : ℂ) :
    cuspRankinSeries f s =
      ∑' n : ℕ, ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  unfold cuspRankinSeries LSeries
  apply tsum_congr
  exact normalized_cusp_square_lseries_term f s

/-- The actual normalized square series is holomorphic in its open half-plane of convergence. -/
theorem cuspRankinSeries_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k) :
    AnalyticOnNhd ℂ (cuspRankinSeries f) {s : ℂ | 1 < s.re} := by
  have hb : LSeries.abscissaOfAbsConv (fun n =>
      ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => normalized_cusp_square_lseries_summable f hk (s := (y : ℂ)) hy)
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact hb.trans_lt (by exact_mod_cast hs)

/-- The real modular weight gives the exact shifted complex Mellin identity for the genuine Rankin series. -/
theorem cuspRankinSeries_mellin {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s + (k : ℂ) - 2) * (cuspHorizontalEnergy f y : ℂ)) =
      ((4 * Real.pi : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        cuspRankinSeries f s := by
  have ht : (k : ℝ) < (s + (k : ℂ) - 1).re := by simp; linarith
  have hi := cusp_complex_mellin_energy_identity f hk ht
  rw [cuspRankinSeries_eq_tsum]
  simp_rw [normalized_cusp_square_term]
  convert hi using 2
  funext y
  congr 2
  ring

/-- The normalized Rankin Mellin identity is an absolutely convergent integral for Re(s)>1. -/
theorem integrableOn_cuspRankin_mellin {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s + (k : ℂ) - 2) *
      (cuspHorizontalEnergy f y : ℂ)) (Ioi 0) := by
  have ht : (k : ℝ) < (s + (k : ℂ) - 1).re := by simp; linarith
  have hi := integrableOn_cusp_complex_mellin_energy f hk ht
  convert hi using 1
  funext y
  congr 2
  ring

end
end Dubon2026
