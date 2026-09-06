import GafniTao.Pintz2023KernelMass
import GafniTao.Pintz2023NearOneGlobalZeta
import GafniTao.Pintz2023Equation48Mollifier

/-!
# Pintz (2023), equation (4.10): the left vertical integral

This file inserts the source mollifier and near-one zeta estimates into the
literal equation-(4.2) left line.  The Gaussian moment and every parameter
factor are retained explicitly for the later source-scale calculation.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

private theorem abs_add_three_le_product_left
    (t u : ℝ) :
    |t + u| + 3 ≤ (|t| + 3) * (|u| + 1) := by
  have hadd := abs_add_le t u
  nlinarith [abs_nonneg t, abs_nonneg u]

private theorem pintz2023_left_zeta_exponent_le_two
    {d epsilon : ℝ}
    (hd : 0 ≤ d) (hdUpper : d ≤ 1 / 12)
    (hepsilonUpper : epsilon ≤ 1) :
    (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon ≤ 2 := by
  have hpow : d ^ (3 / 2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_one hd (by linarith) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  linarith

/-- A deliberately elementary quadratic Gaussian moment.  The coarse
constant is harmless, while the displayed `lambda^(3/2)` scale is needed in
the later exponent ledger. -/
theorem integral_abs_add_one_sq_mul_pintz_gaussian_le
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    Integrable (fun u : ℝ =>
      (|u| + 1) ^ (2 : ℕ) * Real.exp (-(1 / lambda) * u ^ 2)) ∧
    (∫ u : ℝ,
      (|u| + 1) ^ (2 : ℕ) * Real.exp (-(1 / lambda) * u ^ 2)) ≤
      6 * lambda * Real.sqrt (2 * Real.pi * lambda) := by
  have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
  let f : ℝ → ℝ := fun u =>
    (|u| + 1) ^ (2 : ℕ) * Real.exp (-(1 / lambda) * u ^ 2)
  let g : ℝ → ℝ := fun u =>
    6 * lambda * Real.exp (-(1 / (2 * lambda)) * u ^ 2)
  have hb : 0 < 1 / (2 * lambda) := by positivity
  have hgauss : Integrable (fun u : ℝ =>
      Real.exp (-(1 / (2 * lambda)) * u ^ 2)) := by
    simpa only using (integrable_exp_neg_mul_sq_iff.mpr hb)
  have hg : Integrable g := hgauss.const_mul (6 * lambda)
  have hpoint : ∀ u : ℝ, f u ≤ g u := by
    intro u
    have hsq : (|u| + 1) ^ (2 : ℕ) ≤ 2 * (u ^ 2 + 1) := by
      nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
    let x : ℝ := u ^ 2 / (2 * lambda)
    have hx : 0 ≤ x := by dsimp only [x]; positivity
    have hux : u ^ 2 ≤ 2 * lambda * Real.exp x := by
      have hexp := Real.add_one_le_exp x
      have hscale : u ^ 2 = 2 * lambda * x := by
        dsimp only [x]
        field_simp [hlambdaPos.ne']
      rw [hscale]
      nlinarith [mul_nonneg (show 0 ≤ 2 * lambda by positivity)
        (sub_nonneg.mpr (le_trans (le_add_of_nonneg_right zero_le_one) hexp))]
    have hexpSplit :
        Real.exp x * Real.exp (-(1 / lambda) * u ^ 2) =
          Real.exp (-(1 / (2 * lambda)) * u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [x]
      field_simp [hlambdaPos.ne']
      ring
    have hexpMono :
        Real.exp (-(1 / lambda) * u ^ 2) ≤
          Real.exp (-(1 / (2 * lambda)) * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hu : 0 ≤ u ^ 2 := sq_nonneg u
      have hinv : 1 / (2 * lambda) ≤ 1 / lambda := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * lambda)
          hlambdaPos).2
        nlinarith
      nlinarith
    have hfirst :
        u ^ 2 * Real.exp (-(1 / lambda) * u ^ 2) ≤
          2 * lambda * Real.exp (-(1 / (2 * lambda)) * u ^ 2) := by
      calc
        u ^ 2 * Real.exp (-(1 / lambda) * u ^ 2) ≤
            (2 * lambda * Real.exp x) *
              Real.exp (-(1 / lambda) * u ^ 2) := by
                gcongr
        _ = 2 * lambda *
              Real.exp (-(1 / (2 * lambda)) * u ^ 2) := by
                rw [mul_assoc, hexpSplit]
    dsimp only [f, g]
    have hnonneg : 0 ≤ Real.exp (-(1 / lambda) * u ^ 2) :=
      (Real.exp_pos _).le
    calc
      (|u| + 1) ^ (2 : ℕ) * Real.exp (-(1 / lambda) * u ^ 2) ≤
          (2 * (u ^ 2 + 1)) * Real.exp (-(1 / lambda) * u ^ 2) :=
            mul_le_mul_of_nonneg_right hsq hnonneg
      _ ≤ 2 * (2 * lambda *
            Real.exp (-(1 / (2 * lambda)) * u ^ 2) +
          Real.exp (-(1 / (2 * lambda)) * u ^ 2)) := by
            nlinarith
      _ ≤ 6 * lambda *
          Real.exp (-(1 / (2 * lambda)) * u ^ 2) := by
            have he : 0 ≤ Real.exp (-(1 / (2 * lambda)) * u ^ 2) :=
              (Real.exp_pos _).le
            nlinarith
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hf : Integrable f := hg.mono' hfContinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [f]; positivity)]
      exact hpoint u)
  refine ⟨hf, ?_⟩
  calc
    ∫ u : ℝ, f u ≤ ∫ u : ℝ, g u :=
      integral_mono hf hg hpoint
    _ = 6 * lambda * Real.sqrt (2 * Real.pi * lambda) := by
      dsimp only [g]
      rw [integral_const_mul, integral_gaussian]
      congr 2
      field_simp [hlambdaPos.ne']

/-- Quantitative form of Pintz (4.10).  Here `etaJ` is the individual
distance of the zero from one, whereas `eta` is the common auxiliary contour
parameter.  They are intentionally not identified. -/
theorem exists_norm_pintz2023Equation42_left_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ) (eta etaJ gamma lambda : ℝ),
        0 < X → 0 < eta → 0 < etaJ → etaJ ≤ eta →
        eta ≤ 1 / 24 → 1 ≤ lambda →
        ‖VerticalIntegral'
            (pintz2023Equation42Integrand X
              (pintz2023Rho etaJ gamma) lambda) (-eta)‖ ≤
          C * (X : ℝ) ^ (eta + etaJ) * (harmonic X : ℝ) *
            eta⁻¹ * (eta + etaJ)⁻¹ *
            (|gamma| + 3) ^ ((1 / 2 : ℝ) *
              (eta + etaJ) ^ (3 / 2 : ℝ) + epsilon) *
            Real.exp (eta ^ 2 / lambda - lambda * eta) *
            (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) := by
  obtain ⟨C, hC, hZeta⟩ :=
    exists_norm_riemannZeta_le_pintz_nearOne_global hepsilon
  refine ⟨C, hC, ?_⟩
  intro X eta etaJ gamma lambda hX heta hetaJPos hetaJ hetaUpper hlambda
  let d : ℝ := eta + etaJ
  let p : ℝ := (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon
  let A : ℝ := C * (X : ℝ) ^ d * (harmonic X : ℝ) *
    eta⁻¹ * d⁻¹ * (|gamma| + 3) ^ p *
      Real.exp (eta ^ 2 / lambda - lambda * eta)
  let q : ℝ → ℝ := fun u =>
    (|u| + 1) ^ (2 : ℕ) * Real.exp (-(1 / lambda) * u ^ 2)
  have hd : 0 < d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 / 12 := by dsimp only [d]; linarith
  have hsigmaLower : 11 / 12 ≤ 1 - d := by linarith
  have hsigmaUpper : 1 - d < 1 := by linarith
  have hp : 0 < p := by dsimp only [p]; positivity
  have hpUpper : p ≤ 2 := by
    apply pintz2023_left_zeta_exponent_le_two hd.le (by linarith) hepsilonUpper
  have hHarmonic : 0 ≤ (harmonic X : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨hq, hqBound⟩ :=
    integral_abs_add_one_sq_mul_pintz_gaussian_le hlambda
  have hContour : Integrable (fun u : ℝ =>
      pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda
        (((-eta : ℝ) : ℂ) + (u : ℂ) * I)) := by
    apply integrable_pintz2023Equation42Integrand_left
    · linarith
    · linarith
    · simp [pintz2023Rho]
      linarith
    · simp [pintz2023Rho]
      linarith
  have hPoint : ∀ u : ℝ,
      ‖pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda
        (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ A * q u := by
    intro u
    have hmoll := norm_zetaMollifier_pintz2023_left_le
      (X := X) (eta := eta) (etaJ := etaJ) (gamma := gamma) (t := u) hd.le
    have hzeta := hZeta (1 - d) (gamma + u) hsigmaLower hsigmaUpper
    have hkernel := norm_pintzGaussianKernel_vertical_le
      (lambda := lambda) (left := -eta) (u := u) (by linarith) (by linarith)
    have hheight := abs_add_three_le_product_left gamma u
    have hheightPow :
        (|gamma + u| + 3) ^ p ≤
          (|gamma| + 3) ^ p * (|u| + 1) ^ p := by
      calc
        (|gamma + u| + 3) ^ p ≤
            ((|gamma| + 3) * (|u| + 1)) ^ p :=
          Real.rpow_le_rpow (by positivity) hheight hp.le
        _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]
    have huPow : (|u| + 1) ^ p ≤ (|u| + 1) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by linarith [abs_nonneg u]) hpUpper
    have hshift :
        pintz2023Rho etaJ gamma +
            (((-eta : ℝ) : ℂ) + (u : ℂ) * I) =
          (((1 - d : ℝ) : ℂ) + I * ((gamma + u : ℝ) : ℂ)) := by
      apply Complex.ext <;> simp [pintz2023Rho, d]
      all_goals ring
    have hshiftM :
        pintz2023Rho etaJ gamma +
            (((-eta : ℝ) : ℂ) + I * (u : ℂ)) =
          (((1 - d : ℝ) : ℂ) + I * ((gamma + u : ℝ) : ℂ)) := by
      simpa only [mul_comm I (u : ℂ)] using hshift
    rw [hshiftM] at hmoll
    rw [pintz2023Equation42Integrand, norm_mul, norm_mul, hshift]
    have hkernel' :
        ‖pintzGaussianKernel lambda (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
          eta⁻¹ * Real.exp
            (eta ^ 2 / lambda - lambda * eta - (1 / lambda) * u ^ 2) := by
      simpa [abs_of_pos heta, abs_neg] using hkernel
    have hexp :
        Real.exp (eta ^ 2 / lambda - lambda * eta - (1 / lambda) * u ^ 2) =
          Real.exp (eta ^ 2 / lambda - lambda * eta) *
            Real.exp (-(1 / lambda) * u ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hzeta' :
        ‖riemannZeta
          (((1 - d : ℝ) : ℂ) + I * ((gamma + u : ℝ) : ℂ))‖ ≤
          C * d⁻¹ * (|gamma + u| + 3) ^ p := by
      simpa only [sub_sub_cancel, d, p] using hzeta
    have hMNonneg :
        0 ≤ (X : ℝ) ^ d * (harmonic X : ℝ) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) hHarmonic
    have hZNonneg :
        0 ≤ C * d⁻¹ * (|gamma + u| + 3) ^ p := by positivity
    have hKNonneg :
        0 ≤ eta⁻¹ * Real.exp
          (eta ^ 2 / lambda - lambda * eta - (1 / lambda) * u ^ 2) := by
      positivity
    have hheightSquared :
        (|gamma + u| + 3) ^ p ≤
          (|gamma| + 3) ^ p * (|u| + 1) ^ (2 : ℕ) :=
      hheightPow.trans
        (mul_le_mul_of_nonneg_left huPow (Real.rpow_nonneg (by positivity) _))
    have hZGrowth :
        C * d⁻¹ * (|gamma + u| + 3) ^ p ≤
          C * d⁻¹ *
            ((|gamma| + 3) ^ p * (|u| + 1) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hheightSquared (by positivity)
    calc
      ‖zetaMollifier X
          (((1 - d : ℝ) : ℂ) + I * ((gamma + u : ℝ) : ℂ))‖ *
          ‖riemannZeta
            (((1 - d : ℝ) : ℂ) + I * ((gamma + u : ℝ) : ℂ))‖ *
          ‖pintzGaussianKernel lambda
            (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        ((X : ℝ) ^ d * (harmonic X : ℝ)) *
          (C * d⁻¹ * (|gamma + u| + 3) ^ p) *
          (eta⁻¹ * Real.exp
            (eta ^ 2 / lambda - lambda * eta - (1 / lambda) * u ^ 2)) := by
              exact mul_le_mul
                (mul_le_mul (by simpa only [d] using hmoll) hzeta'
                  (norm_nonneg _)
                  (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _)
                    hHarmonic))
                hkernel' (norm_nonneg _) (mul_nonneg hMNonneg hZNonneg)
      _ ≤ ((X : ℝ) ^ d * (harmonic X : ℝ)) *
          (C * d⁻¹ * ((|gamma| + 3) ^ p * (|u| + 1) ^ (2 : ℕ))) *
          (eta⁻¹ * (Real.exp (eta ^ 2 / lambda - lambda * eta) *
            Real.exp (-(1 / lambda) * u ^ 2))) := by
              rw [hexp]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hZGrowth hMNonneg)
                (by positivity)
      _ = A * q u := by dsimp only [A, q]; ring
  have hAq : Integrable (fun u : ℝ => A * q u) := hq.const_mul A
  have hint :
      ‖∫ u : ℝ,
          pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda
            (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        A * (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) := by
    calc
      _ ≤ ∫ u : ℝ,
          ‖pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda
            (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖ :=
              norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, A * q u :=
        integral_mono hContour.norm hAq hPoint
      _ = A * ∫ u : ℝ, q u := by rw [integral_const_mul]
      _ ≤ A * (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) :=
        mul_le_mul_of_nonneg_left hqBound hA
  unfold VerticalIntegral' VerticalIntegral
  rw [norm_smul, norm_smul]
  have hnormal :
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖I‖ ≤ 1 := by
    simpa [norm_mul] using norm_pintz2023_vertical_normalization_le_one
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (‖I‖ * ‖∫ u : ℝ,
          pintz2023Equation42Integrand X (pintz2023Rho etaJ gamma) lambda
            (((-eta : ℝ) : ℂ) + (u : ℂ) * I)‖) ≤
      1 * (A * (6 * lambda * Real.sqrt (2 * Real.pi * lambda))) := by
        rw [← mul_assoc]
        gcongr
    _ = C * (X : ℝ) ^ (eta + etaJ) * (harmonic X : ℝ) *
          eta⁻¹ * (eta + etaJ)⁻¹ *
          (|gamma| + 3) ^ ((1 / 2 : ℝ) *
            (eta + etaJ) ^ (3 / 2 : ℝ) + epsilon) *
          Real.exp (eta ^ 2 / lambda - lambda * eta) *
          (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) := by
            dsimp only [A, d, p]
            ring

#print axioms integral_abs_add_one_sq_mul_pintz_gaussian_le
#print axioms exists_norm_pintz2023Equation42_left_le

end

end GafniTao
