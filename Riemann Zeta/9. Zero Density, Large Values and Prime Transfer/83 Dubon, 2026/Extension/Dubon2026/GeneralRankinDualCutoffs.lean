import Dubon2026.DivisorGammaDualSeries
import Dubon2026.RankinPerronCutoffs

/-! # Actual finite-contour decomposition into the genuine divisor Gamma series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup MeasureTheory

noncomputable section

/-- The literal Mellin weight and convergent actual coefficient series of one level-divisor component. -/
def divisorRankinMellinIntegrand {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (x : ℝ) (s : ℂ) : ℂ :=
  ((x : ℂ) ^ (s + 2) * (divisorRankinConductor Q d.val : ℂ) ^ s * gammaRieszSymbol k 2 s) *
    LSeries (divisorRectangularDualCoefficients f d) (1 - s)

/-- The original continued Perron integrand is the exact finite sum of actual reflected divisor components. -/
theorem general_rankinPerronContinuation_reflected {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (x : ℝ) {s : ℂ}
    (hl : -1 < s.re) (hr : s.re < 0) :
    rankinPerronContinuation f x s =
      ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k * divisorRankinMellinIntegrand f d x s := by
  rw [rankinPerronContinuation, mul_div_assoc, general_rankinConvolution_riesz_reflection f hk hl hr,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold divisorRankinMellinIntegrand
  ring

/-- The actual divisor coefficient series is analytic throughout its proved absolute-convergence half-plane. -/
theorem divisorRectangularDualSeries_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors) :
    AnalyticOnNhd ℂ (LSeries (divisorRectangularDualCoefficients f d)) {s : ℂ | 1 < s.re} := by
  have hb : LSeries.abscissaOfAbsConv (divisorRectangularDualCoefficients f d) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => divisorRectangularDual_lseriesSummable f hk d (s := (y : ℂ)) hy)
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact hb.trans_lt (by exact_mod_cast hs)

/-- The genuine reflected component is continuous at every height of the left vertical line. -/
theorem continuous_divisorRankinMellinIntegrand_left {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (d : Q.divisors)
    {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => divisorRankinMellinIntegrand f d x (gammaVerticalPoint (-1 / 8) t)) := by
  have hL : Continuous (fun t : ℝ => LSeries (divisorRectangularDualCoefficients f d)
      (1 - gammaVerticalPoint (-1 / 8) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((divisorRectangularDualSeries_analyticOnNhd f (by omega) d)
      (1 - gammaVerticalPoint (-1 / 8) t) (by norm_num [gammaVerticalPoint_re])).continuousAt.comp (f := fun u : ℝ => 1 - gammaVerticalPoint (-1 / 8) u)
        (show ContinuousAt (fun u : ℝ => 1 - gammaVerticalPoint (-1 / 8) u) t by
          unfold gammaVerticalPoint; fun_prop)
  exact (continuous_positive_conductor_mellin_weight (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    (divisorRankinConductor_pos d) hx).mul hL

/-- The genuine normalized finite integral of one divisor component equals its actual convergent Gamma cutoff series. -/
theorem divisorRankinMellinIntegrand_cutoff {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (d : Q.divisors)
    {x : ℝ} (hx : 0 < x) (T : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t in -T..T,
      divisorRankinMellinIntegrand f d x (gammaVerticalPoint (-1 / 8) t)) =
        ∑' n : ℕ, gammaRieszDualCutoffTerm (fun n => (divisorRectangularDualCoefficients f d n).re)
          k (divisorRankinConductor Q d.val) x T n := by
  have hc0 : (divisorRectangularDualCoefficients f d 0).re = 0 := by
    rw [(divisorRectangularDualCoefficients_positive f d).1, zero_re]
  have hc : LSeriesSummable (fun n => ((divisorRectangularDualCoefficients f d n).re : ℂ))
      ((9 / 8 : ℝ) : ℂ) := by
    simp only [divisorRectangularDualCoefficients_ofReal_re]
    exact divisorRectangularDual_lseriesSummable f (by omega) d (by norm_num)
  have he := positive_conductor_mellin_cutoff_eq_series _ hc0 hc
    (by exact_mod_cast hk : (2 : ℝ) ≤ k) (divisorRankinConductor_pos d) hx T
  simpa only [divisorRectangularDual_LSeries_re, divisorRankinMellinIntegrand] using he

/-- The actual left Perron cutoff is exactly the finite signed sum of genuine coefficient-weighted Gamma cutoffs, with all component conductors retained. -/
theorem general_rankinPerronVerticalCutoff_eq_dualCutoffs {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    rankinPerronVerticalCutoff f x (-1 / 8) T =
      ∑ d : Q.divisors, divisorRankinAmplitude Q d.val k *
        ∑' n : ℕ, gammaRieszDualCutoffTerm (fun n => (divisorRectangularDualCoefficients f d n).re)
          k (divisorRankinConductor Q d.val) x T n := by
  have hi (d : Q.divisors) : IntervalIntegrable (fun t : ℝ => divisorRankinAmplitude Q d.val k *
      divisorRankinMellinIntegrand f d x (gammaVerticalPoint (-1 / 8) t)) volume (-T) T :=
    ((continuous_divisorRankinMellinIntegrand_left f hk d hx).const_mul _).intervalIntegrable _ _
  rw [rankinPerronVerticalCutoff]
  simp_rw [general_rankinPerronContinuation_reflected f (by omega : 0 < k) x
    (s := gammaVerticalPoint (-1 / 8) _) (by norm_num [gammaVerticalPoint_re])
    (by norm_num [gammaVerticalPoint_re])]
  rw [intervalIntegral.integral_finsetSum (fun d _ => hi d), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [intervalIntegral.integral_const_mul, ← divisorRankinMellinIntegrand_cutoff f hk d hx T]
  simp only [Complex.real_smul]
  ring

end
end Dubon2026
