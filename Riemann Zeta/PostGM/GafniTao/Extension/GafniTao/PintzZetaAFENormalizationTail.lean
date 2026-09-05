import GafniTao.PintzZetaAFEHead

/-!
# Explicit height dependence of the AFE normalization

The generic horizontal-edge estimate is termwise but hides the inverse
normalization inside its constant.  This file exposes that dependence.  The
lower bound comes from the exact norm identity on `Re z = 1/2`, transported
to `Re z = r/2` by the already proved horizontal Gamma estimate.
-/

open Complex

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- An exact upper bound for the inverse Gamma factor at `r/2 + it/2`.
No asymptotic notation or implicit height-dependent constant occurs. -/
theorem exists_norm_Gamma_halfstrip_inv_le
    {r : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      ‖(Complex.Gamma (((r / 2 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I))⁻¹‖ ≤
        Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) := by
  obtain ⟨D, hD, hright⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := r / 2) (b := (1 / 2 : ℝ)) (by linarith)
  refine ⟨D, hD, ?_⟩
  intro t
  let z : ℂ := ((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I
  let d : ℝ := (1 - r) / 2
  let zhalf : ℂ := (1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I
  have hzRe : z.re = r / 2 := by simp [z]
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hzadd : z + (d : ℂ) = zhalf := by
    apply Complex.ext
    · simp [z, zhalf, d]
      ring
    · simp [z, zhalf, d]
  have hdisp := hright z d (by simp [z]) (by simp [z, d]; linarith) hd
  rw [hzadd] at hdisp
  have hzPos : 0 < z.re := by rw [hzRe]; linarith
  have hzNe : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hzPos
  have hhalfPos : 0 < zhalf.re := by simp [zhalf]
  have hhalfNe : Complex.Gamma zhalf ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hhalfPos
  let E : ℝ := Real.exp ((Real.log (|z.im| + 2) + D) * d)
  have hE : 0 < E := Real.exp_pos _
  have hInvTransport :
      ‖Complex.Gamma z‖⁻¹ ≤ E * ‖Complex.Gamma zhalf‖⁻¹ := by
    rw [show E * ‖Complex.Gamma zhalf‖⁻¹ =
        E / ‖Complex.Gamma zhalf‖ by rw [div_eq_mul_inv]]
    apply (le_div_iff₀ (norm_pos_iff.mpr hhalfNe)).2
    rw [mul_comm]
    have hdiv : ‖Complex.Gamma zhalf‖ / ‖Complex.Gamma z‖ ≤ E := by
      rw [div_le_iff₀ (norm_pos_iff.mpr hzNe)]
      simpa only [E, mul_comm] using hdisp
    simpa only [div_eq_mul_inv] using hdiv
  have hhalfSq := Gamma_half_add_mul_I_norm_sq (t / 2)
  have hInvHalfSq :
      ‖Complex.Gamma zhalf‖⁻¹ ^ 2 =
        Real.cosh (Real.pi * (t / 2)) / Real.pi := by
    have hnormSq :
        ‖Complex.Gamma zhalf‖ ^ 2 =
          Real.pi / Real.cosh (Real.pi * (t / 2)) := by
      simpa only [zhalf] using hhalfSq
    rw [inv_pow, hnormSq]
    field_simp [Real.pi_ne_zero, (Real.cosh_pos _).ne']
  have hInvHalf :
      ‖Complex.Gamma zhalf‖⁻¹ ≤
        1 + Real.cosh (Real.pi * (t / 2)) / Real.pi := by
    calc
      ‖Complex.Gamma zhalf‖⁻¹ ≤
          1 + ‖Complex.Gamma zhalf‖⁻¹ ^ 2 := by
        nlinarith [sq_nonneg (‖Complex.Gamma zhalf‖⁻¹ - 1 / 2)]
      _ = 1 + Real.cosh (Real.pi * (t / 2)) / Real.pi := by rw [hInvHalfSq]
  rw [norm_inv]
  calc
    ‖Complex.Gamma z‖⁻¹ ≤ E * ‖Complex.Gamma zhalf‖⁻¹ := hInvTransport
    _ ≤ E * (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) :=
      mul_le_mul_of_nonneg_left hInvHalf hE.le
    _ = Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
        (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) := by
      dsimp only [E, d]
      rw [show z.im = t / 2 by simp [z]]

/-- Explicit inverse bound for the full completed-zeta normalization.  The
two polynomial factors are retained rather than hidden in a constant. -/
theorem exists_norm_pintzZetaAFENormalization_inv_le
    {r : ℝ} (hrLower : 1 / 2 < r) (hrUpper : r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖(pintzZetaAFENormalization
          (((r : ℝ) : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        Real.pi ^ (r / 2) *
          Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) := by
  obtain ⟨D, hD, hgamma⟩ :=
    exists_norm_Gamma_halfstrip_inv_le hrLower hrUpper
  refine ⟨D, hD, ?_⟩
  intro t ht
  let s : ℂ := ((r : ℝ) : ℂ) + (t : ℂ) * I
  have hsNorm : 1 ≤ ‖s‖ := by
    exact ht.trans (by
      have him : s.im = t := by simp [s]
      simpa [him] using Complex.abs_im_le_norm s)
  have hOneSubNorm : 1 ≤ ‖1 - s‖ := by
    have him : (1 - s).im = -t := by simp [s]
    have habs : |t| = |(1 - s).im| := by rw [him, abs_neg]
    exact ht.trans (habs.le.trans (Complex.abs_im_le_norm (1 - s)))
  have hpolyInv : ‖(s * (1 - s))⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul]
    apply inv_le_one_of_one_le₀
    calc
      1 = 1 * 1 := by ring
      _ ≤ ‖s‖ * ‖1 - s‖ :=
        mul_le_mul hsNorm hOneSubNorm zero_le_one (norm_nonneg _)
  have hgammaR :
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤
        Real.pi ^ (r / 2) *
          (Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
            (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi)) := by
    rw [Complex.Gammaℝ_def, mul_inv, norm_mul, norm_inv,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hpow : (Real.pi ^ (-s / 2).re)⁻¹ =
        Real.pi ^ (r / 2) := by
      rw [show (-s / 2).re = -(r / 2) by
        simp [s]
        ring]
      rw [Real.rpow_neg Real.pi_pos.le, inv_inv]
    rw [hpow]
    gcongr
    rw [show s / 2 = ((r / 2 : ℝ) : ℂ) +
        ((t / 2 : ℝ) : ℂ) * I by
      apply Complex.ext <;> simp [s]]
    simpa only [norm_inv] using hgamma t
  unfold pintzZetaAFENormalization
  rw [mul_inv, norm_mul]
  calc
    ‖(s * (1 - s))⁻¹‖ * ‖(Complex.Gammaℝ s)⁻¹‖ ≤
        1 * ‖(Complex.Gammaℝ s)⁻¹‖ :=
      mul_le_mul_of_nonneg_right hpolyInv (norm_nonneg _)
    _ ≤ Real.pi ^ (r / 2) *
          Real.exp ((Real.log (|t / 2| + 2) + D) * ((1 - r) / 2)) *
          (1 + Real.cosh (Real.pi * (t / 2)) / Real.pi) := by
      simpa only [one_mul, mul_assoc] using hgammaR

#print axioms exists_norm_Gamma_halfstrip_inv_le
#print axioms exists_norm_pintzZetaAFENormalization_inv_le

end

end GafniTao
