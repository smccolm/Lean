import Dubon2026.CuspPeriodRankinSeries
import Dubon2026.ExponentialMellinSeries

/-! # Exact common-period Mellin factors for genuine cusp forms -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups

noncomputable section

/-- The actual q-expansion at every positive strict cusp period has zero constant coefficient. -/
theorem qExpansion_cusp_period_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = 0 := by
  letI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hh hΓ⟩
  rw [UpperHalfPlane.qExpansion_coeff_zero hh
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)]
  exact (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero

/-- The actual raw and normalized period-square L-series terms agree with the precise weight shift. -/
theorem cusp_period_square_lseries_term_shift {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun m => ((‖(qExpansion h f).coeff m‖ ^ 2 : ℝ) : ℂ)) (s + (k : ℂ) - 1) n =
      LSeries.term (fun m => ((‖normalizedCuspPeriodCoefficients f h m‖ ^ 2 : ℝ) : ℂ)) s n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      norm_sq_normalizedCuspPeriodCoefficients, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [mul_assoc, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    congr 2
    ring

/-- The raw actual square series is convergent with the full weight shift. -/
theorem cusp_period_raw_lseriesSummable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => ((‖(qExpansion h f).coeff m‖ ^ 2 : ℝ) : ℂ)) (s + (k : ℂ) - 1) := by
  exact (normalized_cusp_period_square_lseries_summable f hh hΓ hk hs).congr
    (fun n => (cusp_period_square_lseries_term_shift f h s n).symm)

/-- The raw actual series equals the already constructed normalized period Rankin series. -/
theorem cusp_period_raw_LSeries {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (s : ℂ) :
    LSeries (fun m => ((‖(qExpansion h f).coeff m‖ ^ 2 : ℝ) : ℂ)) (s + (k : ℂ) - 1) =
      cuspPeriodRankinSeries f h s :=
  tsum_congr (cusp_period_square_lseries_term_shift f h s)

/-- The genuine average over a full period, parametrized on the unit interval. -/
def cuspPeriodHorizontalEnergy {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex (((h * x : ℝ) : ℂ) + y * Complex.I))‖ ^ 2

/-- Actual period Parseval gives the precise scaled exponential series. -/
theorem hasSum_cuspPeriodHorizontalEnergy {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ‖(qExpansion h f).coeff n‖ ^ 2 * Real.exp (-((4 * Real.pi / h) * n) * y))
      (cuspPeriodHorizontalEnergy f h y) := by
  have he (n : ℕ) : -((4 * Real.pi / h) * n) * y = -4 * Real.pi * n * y / h := by ring
  simp_rw [he]
  convert hasSum_cusp_period_horizontal_energy f hh hΓ hy using 1
  unfold cuspPeriodHorizontalEnergy
  congr 1
  funext x
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]

/-- The exact Mellin transform of the actual period energy has the full (4pi/h) factor and the original weight shift. -/
theorem cuspPeriodRankinSeries_mellin {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) ^ (s + (k : ℂ) - 2) * (cuspPeriodHorizontalEnergy f h y : ℂ)) =
      (((4 * Real.pi / h : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Complex.Gamma (s + (k : ℂ) - 1)) *
        cuspPeriodRankinSeries f h s := by
  have hs0 : 0 < (s + (k : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hi := mellin_exponential_series
    (a := fun n => ((‖(qExpansion h f).coeff n‖ ^ 2 : ℝ) : ℂ))
    (by simp [qExpansion_cusp_period_zero f hh hΓ]) hs0
    (cusp_period_raw_lseriesSummable f hh hΓ hk hs)
    (show 0 < 4 * Real.pi / h by positivity)
    (F := fun y => (cuspPeriodHorizontalEnergy f h y : ℂ))
    (fun y hy => by simpa only [Complex.ofReal_mul] using
      Complex.hasSum_ofReal.mpr (hasSum_cuspPeriodHorizontalEnergy f hh hΓ hy))
  rw [cusp_period_raw_LSeries] at hi
  convert hi using 1
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  simp only [smul_eq_mul]
  congr 2
  ring

/-- The exact period Rankin Mellin integral is absolutely convergent on its actual half-plane. -/
theorem integrableOn_cuspPeriodRankin_mellin {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (hk : 0 < k)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s + (k : ℂ) - 2) *
      (cuspPeriodHorizontalEnergy f h y : ℂ)) (Ioi 0) := by
  have hs0 : 0 < (s + (k : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hi := integrableOn_exponential_series_mellin
    (a := fun n => ((‖(qExpansion h f).coeff n‖ ^ 2 : ℝ) : ℂ))
    (by simp [qExpansion_cusp_period_zero f hh hΓ]) hs0
    (cusp_period_raw_lseriesSummable f hh hΓ hk hs)
    (show 0 < 4 * Real.pi / h by positivity)
    (F := fun y => (cuspPeriodHorizontalEnergy f h y : ℂ))
    (fun y hy => by simpa only [Complex.ofReal_mul] using
      Complex.hasSum_ofReal.mpr (hasSum_cuspPeriodHorizontalEnergy f hh hΓ hy))
  convert hi using 1
  funext y
  congr 2
  ring

end
end Dubon2026
