import GafniTao.FordLemma51
import RiemannZeta.GuthMaynard.HughesYoungEquation98Bounds
import RiemannZeta.External.PNT.ZetaBoundsUpstream

/-!
# Ford's elementary half-plane bounds

This file proves the Euler-series portions of the lemma called `zeta basic`
in Ford's zero-free-region paper.  In particular, both zeta and its
reciprocal on a vertical line are controlled by the positive real-axis
zeta value, and the logarithmic derivative is largest on the real axis.
The remaining explicit numerical comparison with
`0.6 + 1 / (sigma - 1)` is kept as a separate source obligation.
-/

open Complex
open scoped ComplexOrder

namespace GafniTao

theorem ford_norm_eq_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) :
    ‖z‖ = z.re := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  rw [Complex.norm_def, Complex.normSq_apply, ← him]
  rw [zero_mul, add_zero, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hre]

theorem ford_riemannZeta_real_norm {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖riemannZeta (sigma : ℂ)‖ = (riemannZeta (sigma : ℂ)).re := by
  have hpos : 0 < riemannZeta (sigma : ℂ) := riemannZeta_pos_of_one_lt hsigma
  exact ford_norm_eq_re_of_nonneg hpos.le

theorem ford_norm_riemannZeta_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hsumS : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  have hsumSigma : LSeriesSummable (1 : ℕ → ℂ) (sigma : ℂ) :=
    LSeriesSummable_one_iff.mpr hsigma
  rw [← LSeries_one_eq_riemannZeta hs,
    ← LSeries_one_eq_riemannZeta hsigma, LSeries, LSeries]
  calc
    ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤
        ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hsumS.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      apply hsumS.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re
          (1 : ℕ → ℂ) (by simp [s]) n)
        hsumSigma.norm
    _ = ‖∑' n, LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      have hnonneg (n : ℕ) :
          0 ≤ LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n :=
        LSeries.term_nonneg (by norm_num : (0 : ℂ) ≤ 1) sigma
      have hnormTerm (n : ℕ) :
          ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ =
            (LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n).re := by
        exact ford_norm_eq_re_of_nonneg (hnonneg n)
      simp_rw [hnormTerm]
      rw [← Complex.re_tsum hsumSigma]
      exact (ford_norm_eq_re_of_nonneg (tsum_nonneg hnonneg)).symm

theorem ford_norm_riemannZeta_inv_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖(riemannZeta ((sigma : ℂ) + Complex.I * t))⁻¹‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hsumMobius : LSeriesSummable
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsumOne : LSeriesSummable (1 : ℕ → ℂ) (sigma : ℂ) :=
    LSeriesSummable_one_iff.mpr hsigma
  rw [RiemannZeta.GuthMaynard.riemannZeta_inv_eq_moebiusLSeries hs,
    ← LSeries_one_eq_riemannZeta hsigma, LSeries, LSeries]
  calc
    ‖∑' n, LSeries.term
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
        ∑' n, ‖LSeries.term
          (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsumMobius.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      apply hsumMobius.norm.tsum_le_tsum _ hsumOne.norm
      intro n
      exact (LSeries.norm_term_le s
        (RiemannZeta.GuthMaynard.moebius_coeff_norm_le_one n)).trans
        (LSeries.norm_term_le_of_re_le_re (1 : ℕ → ℂ) (by simp [s]) n)
    _ = ‖∑' n, LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      have hnonneg (n : ℕ) :
          0 ≤ LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n :=
        LSeries.term_nonneg (by norm_num : (0 : ℂ) ≤ 1) sigma
      have hnormTerm (n : ℕ) :
          ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ =
            (LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n).re := by
        exact ford_norm_eq_re_of_nonneg (hnonneg n)
      simp_rw [hnormTerm]
      rw [← Complex.re_tsum hsumOne]
      exact (ford_norm_eq_re_of_nonneg (tsum_nonneg hnonneg)).symm

theorem ford_norm_logDerivative_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖-deriv riemannZeta ((sigma : ℂ) + Complex.I * t) /
        riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ)‖ := by
  simpa [mul_comm] using
    dlog_riemannZeta_bdd_on_vertical_lines_generalized
      sigma sigma t hsigma le_rfl

end GafniTao
