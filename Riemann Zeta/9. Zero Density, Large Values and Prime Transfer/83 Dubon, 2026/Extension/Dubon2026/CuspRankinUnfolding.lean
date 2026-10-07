import Dubon2026.Gamma0EisensteinUnfolding
import Dubon2026.PeterssonStripMellin
import Dubon2026.CuspRankinSeries

/-! # The actual Rankin unfolding identity in the convergent real half-plane -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups CongruenceSubgroup ENNReal

noncomputable section

/-- Actual horizontal Fourier energy is nonnegative. -/
theorem cuspHorizontalEnergy_nonneg {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (y : ℝ) :
    0 ≤ cuspHorizontalEnergy f y :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)

/-- The real square series has precisely the same actual coefficient normalization shift. -/
theorem normalized_cusp_real_square_term {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (σ : ℝ) (n : ℕ) :
    ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ) =
      ‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-(σ + (k : ℝ) - 1)) := by
  rw [norm_sq_normalizedCuspCoefficients]
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    congr 2
    ring

/-- Unfolding the literal Eisenstein series gives the true normalized square series with its exact Gamma factor. -/
theorem cusp_rankin_unfolding_lintegral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      ENNReal.ofReal (gamma0Eisenstein Q (σ : ℂ) z).re * ENNReal.ofReal ‖petersson k f f z‖) =
      ENNReal.ofReal (((4 * Real.pi) ^ (-(σ + (k : ℝ) - 1)) *
        Real.Gamma (σ + (k : ℝ) - 1)) *
          ∑' n : ℕ, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ)) := by
  have hs : (k : ℝ) < σ + (k : ℝ) - 1 := by linarith
  have he : σ + (k : ℝ) - 1 - 1 = σ + (k : ℝ) - 2 := by ring
  have hi := integrableOn_cusp_mellin_energy f hk hs
  rw [he] at hi
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun y : ℝ => y ^ (σ + (k : ℝ) - 2) * cuspHorizontalEnergy f y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (Real.rpow_nonneg hy.le _) (cuspHorizontalEnergy_nonneg f y)
  rw [gamma0_eisenstein_petersson_unfold f hσ, petersson_unitStrip_mellin,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, ← he,
    cusp_mellin_energy_identity f hk hs]
  simp_rw [normalized_cusp_real_square_term]

/-- The actual unfolded Eisenstein-Petersson integral is finite throughout the real convergent half-plane. -/
theorem cusp_rankin_unfolding_lintegral_lt_top {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      ENNReal.ofReal (gamma0Eisenstein Q (σ : ℂ) z).re * ENNReal.ofReal ‖petersson k f f z‖) < ⊤ := by
  rw [cusp_rankin_unfolding_lintegral f hk hσ]
  exact ENNReal.ofReal_lt_top

/-- The actual parabolic-coset sum is measurable as a function of the upper-half-plane point. -/
theorem measurable_gamma0CosetEisensteinNN (Q : ℕ) (σ : ℝ) :
    Measurable (gamma0CosetEisensteinNN Q σ) := by
  have hi : Continuous (fun z : ℍ => z.im ^ σ) :=
    UpperHalfPlane.continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  exact Measurable.tsum (fun q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q =>
    (hi.measurable.comp (measurable_const_smul q.out⁻¹)).ennreal_ofReal)

/-- Real Eisenstein values are nonnegative for the actual primitive-row definition. -/
theorem gamma0Eisenstein_re_nonneg (Q : ℕ) (σ : ℝ) (z : ℍ) :
    0 ≤ (gamma0Eisenstein Q (σ : ℂ) z).re := by
  rw [gamma0Eisenstein_real_value, Complex.ofReal_re]
  exact mul_nonneg (by norm_num)
    (tsum_nonneg (fun v => Real.rpow_nonneg (eisensteinRowHeight_nonneg v.val z) σ))

/-- The real part of the genuine convergent Eisenstein series is measurable in z. -/
theorem measurable_gamma0Eisenstein_re (Q : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Measurable (fun z : ℍ => (gamma0Eisenstein Q (σ : ℂ) z).re) := by
  have he : (fun z : ℍ => (gamma0Eisenstein Q (σ : ℂ) z).re) =
      (fun z : ℍ => (gamma0CosetEisensteinNN Q σ z).toReal) := by
    funext z
    rw [← gamma0Eisenstein_re_eq_cosetNN Q hσ z,
      ENNReal.toReal_ofReal (gamma0Eisenstein_re_nonneg Q σ z)]
  rw [he]
  exact (measurable_gamma0CosetEisensteinNN Q σ).ennreal_toReal

/-- The actual Eisenstein-Petersson product is absolutely integrable on the true Γ₀ domain. -/
theorem integrableOn_gamma0_eisenstein_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun z : ℍ => (gamma0Eisenstein Q (σ : ℂ) z).re * ‖petersson k f f z‖)
      (gamma0FundamentalDomain Q) := by
  refine ⟨((measurable_gamma0Eisenstein_re Q hσ).mul
    (petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f)).norm.measurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z =>
    mul_nonneg (gamma0Eisenstein_re_nonneg Q σ z) (norm_nonneg _)))]
  simp_rw [ENNReal.ofReal_mul (gamma0Eisenstein_re_nonneg Q σ _)]
  exact cusp_rankin_unfolding_lintegral_lt_top f hk hσ

/-- The real Rankin unfolding formula consumes the genuine cusp form and Eisenstein series without supplied analytic certificates. -/
theorem cusp_rankin_unfolding_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫ z in gamma0FundamentalDomain Q,
      (gamma0Eisenstein Q (σ : ℂ) z).re * ‖petersson k f f z‖) =
      ((4 * Real.pi) ^ (-(σ + (k : ℝ) - 1)) * Real.Gamma (σ + (k : ℝ) - 1)) *
        ∑' n : ℕ, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ) := by
  have hn : ∀ z : ℍ, 0 ≤ (gamma0Eisenstein Q (σ : ℂ) z).re * ‖petersson k f f z‖ :=
    fun z => mul_nonneg (gamma0Eisenstein_re_nonneg Q σ z) (norm_nonneg _)
  have hs0 : 0 < σ + (k : ℝ) - 1 := by
    have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hr : 0 ≤ ((4 * Real.pi) ^ (-(σ + (k : ℝ) - 1)) *
      Real.Gamma (σ + (k : ℝ) - 1)) *
        ∑' n : ℕ, ‖normalizedCuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-σ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.Gamma_pos_of_pos hs0).le)
      (tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
  have he := cusp_rankin_unfolding_lintegral f hk hσ
  simp_rw [← ENNReal.ofReal_mul (gamma0Eisenstein_re_nonneg Q σ _)] at he
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_gamma0_eisenstein_petersson f hk hσ)
    (ae_of_all _ hn)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_ofReal hr] using ht

end
end Dubon2026
