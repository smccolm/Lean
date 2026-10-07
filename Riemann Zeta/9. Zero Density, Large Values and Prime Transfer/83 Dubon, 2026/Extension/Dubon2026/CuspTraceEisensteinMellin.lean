import Dubon2026.FullLevelTraceUnfolding
import Dubon2026.CuspTraceStripMellin
import Dubon2026.CuspRankinRealContinuation

/-! # The actual real-axis Eisenstein Mellin identity for the finite cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups ENNReal

noncomputable section

variable {N : ℕ} {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)]
  (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)

/-- The actual trace horizontal energy is nonnegative at every height. -/
theorem cuspTraceHorizontalEnergy_nonneg (y : ℝ) : 0 ≤ cuspTraceHorizontalEnergy hH f y :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The actual real-axis Mellin integrand is exactly the real coercion of the complex one. -/
theorem cuspTrace_mellin_real_integrand (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ((y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y : ℝ) : ℂ) =
      (y : ℂ) ^ ((σ : ℂ) + (k : ℂ) - 2) * (cuspTraceHorizontalEnergy hH f y : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hy.le]
  push_cast
  rfl

/-- The actual real-axis trace Mellin integral is absolutely integrable. -/
theorem integrableOn_cuspTrace_real_mellin [NeZero N] (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun y : ℝ => y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y) (Ioi 0) := by
  have hi := (integrableOn_cuspTrace_mellin hH f hk (s := (σ : ℂ)) hσ).re
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [← cuspTrace_mellin_real_integrand hH f σ hy]
  rfl

/-- The full-level actual Eisenstein trace integral equals the nonnegative real Mellin integral. -/
theorem cuspTrace_eisenstein_lintegral [NeZero N] (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in ModularGroup.fdo, ENNReal.ofReal (gamma0Eisenstein 1 (σ : ℂ) z).re *
      ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖)) =
      ENNReal.ofReal (∫ y : ℝ in Ioi 0, y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y) := by
  rw [fullLevel_eisenstein_cuspTrace_unfold hH f hσ, cuspTrace_unitStrip_mellin,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_cuspTrace_real_mellin hH f hk hσ)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact mul_nonneg (Real.rpow_nonneg hy.le _) (cuspTraceHorizontalEnergy_nonneg hH f y)

/-- The genuine real Eisenstein trace product is absolutely integrable on the full-level domain. -/
theorem integrableOn_cuspTrace_eisenstein [NeZero N] (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun z : ℍ => (gamma0Eisenstein 1 (σ : ℂ) z).re *
      ∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖) ModularGroup.fdo := by
  have htrace : Continuous (fun z : ℍ => ∑ q : SL(2, ℤ) ⧸ H,
      ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖) :=
    continuous_finsetSum _ (fun q _ => (petersson_continuous k
      (ModularFormClass.continuous (cuspCosetFamily hH f q))
      (ModularFormClass.continuous (cuspCosetFamily hH f q))).norm)
  refine ⟨((measurable_gamma0Eisenstein_re 1 hσ).mul htrace.measurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => mul_nonneg
    (gamma0Eisenstein_re_nonneg 1 σ z) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))))]
  simp_rw [ENNReal.ofReal_mul (gamma0Eisenstein_re_nonneg 1 σ _)]
  rw [cuspTrace_eisenstein_lintegral hH f hk hσ]
  exact ENNReal.ofReal_lt_top

/-- The literal real Eisenstein trace integral equals the actual real Mellin integral, with no integral-value hypothesis. -/
theorem cuspTrace_eisenstein_integral [NeZero N] (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫ z in ModularGroup.fdo, (gamma0Eisenstein 1 (σ : ℂ) z).re *
      ∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖) =
      ∫ y : ℝ in Ioi 0, y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y := by
  have hn (z : ℍ) : 0 ≤ (gamma0Eisenstein 1 (σ : ℂ) z).re *
      ∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖ :=
    mul_nonneg (gamma0Eisenstein_re_nonneg 1 σ z) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hr : 0 ≤ ∫ y : ℝ in Ioi 0, y ^ (σ + (k : ℝ) - 2) * cuspTraceHorizontalEnergy hH f y :=
    setIntegral_nonneg measurableSet_Ioi (fun y hy => mul_nonneg (Real.rpow_nonneg hy.le _)
      (cuspTraceHorizontalEnergy_nonneg hH f y))
  have he := cuspTrace_eisenstein_lintegral hH f hk hσ
  simp_rw [← ENNReal.ofReal_mul (gamma0Eisenstein_re_nonneg 1 σ _)] at he
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_cuspTrace_eisenstein hH f hk hσ)
    (ae_of_all _ hn)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_ofReal hr] using ht

/-- The actual complex Eisenstein trace product is the coercion of its real nonnegative density on the real axis. -/
theorem cuspTrace_eisenstein_real_integrand (σ : ℝ) (z : ℍ) :
    gamma0Eisenstein 1 (σ : ℂ) z *
      ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z =
        (((gamma0Eisenstein 1 (σ : ℂ) z).re *
          ∑ q : SL(2, ℤ) ⧸ H, ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖ : ℝ) : ℂ) := by
  have hE : ((gamma0Eisenstein 1 (σ : ℂ) z).re : ℂ) = gamma0Eisenstein 1 (σ : ℂ) z := by
    rw [gamma0Eisenstein_real_value, Complex.ofReal_re]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, hE]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact petersson_self_eq_ofReal_norm k _ z

/-- Genuine finite-coset unfolding gives the exact complex Gamma factor and actual trace-square series on the real convergence axis. -/
theorem cuspTrace_eisenstein_mellin [NeZero N] (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∫ z : ℍ in ModularGroup.fdo, gamma0Eisenstein 1 (σ : ℂ) z *
      ∑ q : SL(2, ℤ) ⧸ H, petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z) =
      (((4 * Real.pi / N : ℝ) : ℂ) ^ (-((σ : ℂ) + (k : ℂ) - 1)) *
        Complex.Gamma ((σ : ℂ) + (k : ℂ) - 1)) *
          LSeries (fun n => (cuspTraceSquareCoefficients hH f n : ℂ)) (σ : ℂ) := by
  simp_rw [cuspTrace_eisenstein_real_integrand]
  rw [integral_complex_ofReal, cuspTrace_eisenstein_integral hH f hk hσ]
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ y : ℝ in Ioi 0, (y : ℂ) ^ ((σ : ℂ) + (k : ℂ) - 2) *
        (cuspTraceHorizontalEnergy hH f y : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact cuspTrace_mellin_real_integrand hH f σ hy
    _ = _ := cuspTrace_mellin_identity hH f hk hσ

end
end Dubon2026
