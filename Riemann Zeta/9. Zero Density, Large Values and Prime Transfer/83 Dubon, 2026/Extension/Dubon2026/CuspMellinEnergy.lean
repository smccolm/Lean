import Dubon2026.CuspSquareDirichlet
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # The genuine Mellin identity for cusp-form square coefficients -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The actual squared norm averaged over one horizontal period. -/
def cuspHorizontalEnergy {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖f (UpperHalfPlane.ofComplex ((x : ℂ) + y * Complex.I))‖ ^ 2

/-- Parseval identifies the genuine horizontal integral at every positive height. -/
theorem cuspHorizontalEnergy_eq_tsum {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {y : ℝ} (hy : 0 < y) :
    cuspHorizontalEnergy f y =
      ∑' n : ℕ, ‖cuspCoefficients f n‖ ^ 2 * Real.exp (-4 * Real.pi * n * y) := by
  rw [(hasSum_cusp_horizontal_energy f hy).tsum_eq]
  unfold cuspHorizontalEnergy
  congr 1
  funext x
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]

/-- Each actual Fourier Mellin term is integrable; the cusp's zero constant coefficient is retained. -/
theorem integrableOn_cusp_mellin_term {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun y : ℝ => ‖cuspCoefficients f n‖ ^ 2 *
      (y ^ (s - 1) * Real.exp (-4 * Real.pi * n * y))) (Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · have hb : 0 < 4 * Real.pi * (n : ℝ) := by positivity
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s - 1) (p := 1)
      (by linarith) le_rfl hb
    simpa only [Real.rpow_one, neg_mul] using hi.const_mul (‖cuspCoefficients f n‖ ^ 2)

/-- The Mellin integral of each genuine term has the exact Gamma and 4π factors. -/
theorem integral_cusp_mellin_term {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, ‖cuspCoefficients f n‖ ^ 2 *
      (y ^ (s - 1) * Real.exp (-4 * Real.pi * n * y))) =
      ((4 * Real.pi) ^ (-s) * Real.Gamma s) *
        (‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-s)) := by
  by_cases hn : n = 0
  · subst n
    simp [cuspCoefficients_zero]
  · have hb : 0 < 4 * Real.pi * (n : ℝ) := by positivity
    rw [integral_const_mul]
    simp_rw [show ∀ y : ℝ, -4 * Real.pi * n * y = -(4 * Real.pi * n * y) by intro y; ring]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hb, one_div, Real.inv_rpow hb.le,
      ← Real.rpow_neg hb.le,
      Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (Nat.cast_nonneg n)]
    ring

/-- Absolute convergence justifies integrating the true Fourier expansion term by term. -/
theorem cusp_mellin_energy_identity {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℝ} (hs : (k : ℝ) < s) :
    (∫ y : ℝ in Ioi 0, y ^ (s - 1) * cuspHorizontalEnergy f y) =
      ((4 * Real.pi) ^ (-s) * Real.Gamma s) *
        ∑' n : ℕ, ‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-s) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by exact_mod_cast hk) hs
  let F : ℕ → ℝ → ℝ := fun n y => ‖cuspCoefficients f n‖ ^ 2 *
    (y ^ (s - 1) * Real.exp (-4 * Real.pi * n * y))
  have hn (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖F n y‖) =
      ((4 * Real.pi) ^ (-s) * Real.Gamma s) *
        (‖cuspCoefficients f n‖ ^ 2 * (n : ℝ) ^ (-s)) := by
    rw [← integral_cusp_mellin_term f hs0 n]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hy) _) (Real.exp_pos _).le))
  have hi := hasSum_integral_of_summable_integral_norm (F := F)
    (integrableOn_cusp_mellin_term f hs0)
    (by simp_rw [hn]; exact (summable_cusp_square_dirichlet f hk hs).mul_left _)
  have he : (∫ y : ℝ in Ioi 0, ∑' n, F n y) =
      ∫ y : ℝ in Ioi 0, y ^ (s - 1) * cuspHorizontalEnergy f y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change (∑' n, F n y) = y ^ (s - 1) * cuspHorizontalEnergy f y
    rw [cuspHorizontalEnergy_eq_tsum f hy, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [F]
    ring
  change HasSum (fun n => ∫ y : ℝ in Ioi 0, F n y) _ at hi
  rw [he] at hi
  simp_rw [F, integral_cusp_mellin_term f hs0] at hi
  exact hi.unique ((summable_cusp_square_dirichlet f hk hs).hasSum.mul_left _)

/-- The Mellin integral is a genuine convergent integral throughout the same half-plane. -/
theorem integrableOn_cusp_mellin_energy {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (hk : 0 ≤ k)
    {s : ℝ} (hs : (k : ℝ) < s) :
    IntegrableOn (fun y : ℝ => y ^ (s - 1) * cuspHorizontalEnergy f y) (Ioi 0) := by
  by_cases hz : ∀ n, cuspCoefficients f n = 0
  · apply (integrable_zero ℝ ℝ (volume.restrict (Ioi 0))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [cuspHorizontalEnergy_eq_tsum f hy]
    simp [hz]
  · push Not at hz
    obtain ⟨n, hn⟩ := hz
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact hn (cuspCoefficients_zero f)
    have hs0 : 0 < s := lt_of_le_of_lt (by exact_mod_cast hk) hs
    have hp : 0 < ∑' m : ℕ, ‖cuspCoefficients f m‖ ^ 2 * (m : ℝ) ^ (-s) :=
      (summable_cusp_square_dirichlet f hk hs).tsum_pos (fun m => by positivity) n
        (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hn))
          (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) _))
    have hi : 0 < ∫ y : ℝ in Ioi 0, y ^ (s - 1) * cuspHorizontalEnergy f y := by
      rw [cusp_mellin_energy_identity f hk hs]
      exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
        (Real.Gamma_pos_of_pos hs0)) hp
    by_contra hnot
    rw [integral_undef hnot] at hi
    exact (lt_irrefl (0 : ℝ)) hi

end
end Dubon2026
