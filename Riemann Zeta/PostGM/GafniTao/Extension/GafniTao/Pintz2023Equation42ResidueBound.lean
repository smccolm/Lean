import GafniTao.Pintz2023Equation42CompleteShift

/-!
# Pintz (2023), equation (4.2): the translated-pole error

The crossed residue is bounded here with every factor visible.  In
particular, the finite Möbius polynomial at one contributes the exact
harmonic factor; it is not silently absorbed into big-O notation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's source zero coordinate `rho_j = 1-eta_j+i gamma_j`, kept in
the source-specific chain without importing the older adaptive detector. -/
noncomputable def pintz2023Rho (etaJ gamma : ℝ) : ℂ :=
  (1 - etaJ : ℝ) + I * gamma

theorem norm_zetaMollifier_one_le_harmonic (X : ℕ) :
    ‖zetaMollifier X 1‖ ≤ (harmonic X : ℝ) := by
  have h := norm_zetaMollifier_le_sum_rpow X (1 : ℂ)
  calc
    ‖zetaMollifier X 1‖ ≤
        ∑ n ∈ Finset.Icc 1 X, ((n : ℝ)⁻¹) := by
      simpa [Real.rpow_neg_one] using h
    _ = (harmonic X : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

theorem one_sub_pintzRho
    (etaJ gamma : ℝ) :
    (1 : ℂ) - pintz2023Rho etaJ gamma =
      (etaJ : ℂ) + I * (-gamma : ℝ) := by
  apply Complex.ext <;> simp [pintz2023Rho]

theorem norm_pintz2023PoleResidue_le
    {X : ℕ} {etaJ gamma lambda : ℝ}
    (hlambda : 0 < lambda) (hgamma : gamma ≠ 0) :
    ‖pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda‖ ≤
      (harmonic X : ℝ) * |gamma|⁻¹ *
        Real.exp ((etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ) := by
  have hden : |gamma| ≤ ‖(1 : ℂ) - pintz2023Rho etaJ gamma‖ := by
    rw [one_sub_pintzRho]
    simpa using Complex.abs_im_le_norm
      ((etaJ : ℂ) + I * (-gamma : ℝ))
  have hgammaPos : 0 < |gamma| := abs_pos.mpr hgamma
  have hdenPos : 0 < ‖(1 : ℂ) - pintz2023Rho etaJ gamma‖ :=
    hgammaPos.trans_le hden
  have hinv : ‖(1 : ℂ) - pintz2023Rho etaJ gamma‖⁻¹ ≤ |gamma|⁻¹ :=
    (inv_le_inv₀ hdenPos hgammaPos).2 hden
  have hgauss :
      ‖pintzGaussianNumerator lambda
          ((1 : ℂ) - pintz2023Rho etaJ gamma)‖ =
        Real.exp ((etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ) := by
    rw [one_sub_pintzRho]
    simpa only [neg_sq] using
      norm_pintzGaussianNumerator_vertical lambda etaJ (-gamma) hlambda
  unfold pintz2023PoleResidue
  rw [norm_div, norm_mul, hgauss, div_eq_mul_inv]
  have hHarmonic : 0 ≤ (harmonic X : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  calc
    ‖zetaMollifier X 1‖ *
        Real.exp ((etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ) *
          ‖(1 : ℂ) - pintz2023Rho etaJ gamma‖⁻¹ ≤
      (harmonic X : ℝ) *
        Real.exp ((etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ) *
          |gamma|⁻¹ := by
      exact mul_le_mul
        (mul_le_mul (norm_zetaMollifier_one_le_harmonic X) le_rfl
          (Real.exp_pos _).le hHarmonic)
        hinv (inv_nonneg.mpr (norm_nonneg _))
        (mul_nonneg hHarmonic (Real.exp_pos _).le)
    _ = (harmonic X : ℝ) * |gamma|⁻¹ *
        Real.exp ((etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ) := by
      ring

theorem norm_pintz2023PoleResidue_le_eta
    {X : ℕ} {eta etaJ gamma lambda : ℝ}
    (hlambda : 0 < lambda) (hgamma : gamma ≠ 0)
    (hetaJNonneg : 0 ≤ etaJ) (hetaJ : etaJ ≤ eta) :
    ‖pintz2023PoleResidue X (pintz2023Rho etaJ gamma) lambda‖ ≤
      (harmonic X : ℝ) * |gamma|⁻¹ *
        Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) := by
  have hbase := norm_pintz2023PoleResidue_le
    (X := X) (etaJ := etaJ) hlambda hgamma
  have hetaNonneg : 0 ≤ eta := hetaJNonneg.trans hetaJ
  have hsquare : etaJ ^ 2 ≤ eta ^ 2 := by nlinarith
  have hexp :
      (etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ ≤
        eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda := by
    calc
      (etaJ ^ 2 - gamma ^ 2) / lambda + lambda * etaJ =
          etaJ ^ 2 / lambda - gamma ^ 2 / lambda + lambda * etaJ := by ring
      _ ≤ eta ^ 2 / lambda - gamma ^ 2 / lambda + lambda * eta := by
        gcongr
      _ = eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda := by ring
  have hHarmonic : 0 ≤ (harmonic X : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp)
    (mul_nonneg hHarmonic (inv_nonneg.mpr (abs_nonneg gamma))))

#print axioms norm_zetaMollifier_one_le_harmonic
#print axioms one_sub_pintzRho
#print axioms norm_pintz2023PoleResidue_le
#print axioms norm_pintz2023PoleResidue_le_eta

end

end GafniTao
