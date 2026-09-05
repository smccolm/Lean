import GafniTao.Pintz2023NearOneGlobalZeta

/-!
# Pintz's near-one estimate on the exact smoothed zeta sum

This file inserts the global coefficient-one-half zeta bound into the exact
left-line Mellin identity from Lemma 3.4.  The quadratic Mellin moment absorbs
the translated height uniformly; the pole-crossing residue is kept explicit.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

private theorem abs_add_three_le_product
    (t u : ℝ) :
    |t + u| + 3 ≤ (|t| + 3) * (|u| + 1) := by
  have hadd := abs_add_le t u
  nlinarith [abs_nonneg t, abs_nonneg u]

private theorem pintz_nearOne_mellin_exponent_le_two
    {sigma epsilon : ℝ}
    (hsigmaLower : 11 / 12 ≤ sigma) (hsigmaUpper : sigma < 1)
    (hepsilonUpper : epsilon ≤ 1) :
    (1 / 2 : ℝ) * (1 - sigma) ^ (3 / 2 : ℝ) + epsilon ≤ 2 := by
  have hdNonneg : 0 ≤ 1 - sigma := by linarith
  have hdUpper : 1 - sigma ≤ 1 := by linarith
  have hpow : (1 - sigma) ^ (3 / 2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_one hdNonneg hdUpper (by norm_num : (0 : ℝ) ≤ 3 / 2)
  linarith

/-- Uniform left-line integral bound in the near-one strip.  This is the
analytic estimate which turns the exact contour shift into Pintz (3.5). -/
theorem exists_norm_pintz2023MellinContourIntegral_nearOne_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (sigma t : ℝ),
      0 < N → 11 / 12 ≤ sigma → sigma < 1 →
      ‖∫ u : ℝ, pintz2023MellinContourIntegrand N
          ((sigma : ℂ) + I * (t : ℂ)) ((u : ℂ) * I)‖ ≤
        B * (1 - sigma)⁻¹ *
          (|t| + 3) ^ ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨C, hC, hZeta⟩ :=
    exists_norm_riemannZeta_le_pintz_nearOne_global hepsilon
  obtain ⟨L, hL, hMoment⟩ :=
    exists_pintz2023MellinWeight_imaginary_quadratic_moment
  let B : ℝ := C * L
  have hB : 0 < B := mul_pos hC hL
  refine ⟨B, hB, ?_⟩
  intro N sigma t hN hsigmaLower hsigmaUpper
  let d : ℝ := 1 - sigma
  let p : ℝ := (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon
  let a : ℝ := C * d⁻¹ * (|t| + 3) ^ p
  let q : ℝ → ℝ := fun u =>
    ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ * (|u| + 1) ^ (2 : ℕ)
  have hd : 0 < d := by dsimp only [d]; linarith
  have hp : 0 < p := by dsimp only [p]; positivity
  have hpUpper : p ≤ 2 := by
    simpa only [d, p] using
      pintz_nearOne_mellin_exponent_le_two hsigmaLower hsigmaUpper hepsilonUpper
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hContourInt : Integrable (fun u : ℝ =>
      pintz2023MellinContourIntegrand N
        ((sigma : ℂ) + I * (t : ℂ)) ((u : ℂ) * I)) := by
    apply integrable_pintz2023MellinContourIntegrand_left hN
    · norm_num at hsigmaLower ⊢
      linarith
    · simpa using hsigmaUpper
  obtain ⟨hqInt, hqBound⟩ := hMoment N hN
  have hPoint : ∀ u : ℝ,
      ‖pintz2023MellinContourIntegrand N
          ((sigma : ℂ) + I * (t : ℂ)) ((u : ℂ) * I)‖ ≤ a * q u := by
    intro u
    have hShift :
        ((sigma : ℂ) + I * (t : ℂ)) + (u : ℂ) * I =
          (sigma : ℂ) + I * ((t + u : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have hz := hZeta sigma (t + u) hsigmaLower hsigmaUpper
    rw [pintz2023MellinContourIntegrand, norm_mul, hShift]
    have hHeight := abs_add_three_le_product t u
    have hHeightPow :
        (|t + u| + 3) ^ p ≤
          (|t| + 3) ^ p * (|u| + 1) ^ p := by
      calc
        (|t + u| + 3) ^ p ≤
            ((|t| + 3) * (|u| + 1)) ^ p :=
          Real.rpow_le_rpow (by positivity) hHeight hp.le
        _ = (|t| + 3) ^ p * (|u| + 1) ^ p := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
    have huPow : (|u| + 1) ^ p ≤ (|u| + 1) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) hpUpper
    calc
      ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          ‖riemannZeta ((sigma : ℂ) + I * ((t + u : ℝ) : ℂ))‖ ≤
        ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          (C * d⁻¹ * (|t + u| + 3) ^ p) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa only [d, p] using hz) (norm_nonneg _)
      _ ≤ ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          (C * d⁻¹ * ((|t| + 3) ^ p * (|u| + 1) ^ p)) := by
            gcongr
      _ ≤ ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ *
          (C * d⁻¹ * ((|t| + 3) ^ p * (|u| + 1) ^ (2 : ℕ))) := by
            gcongr
      _ = a * q u := by dsimp only [a, q]; ring
  have haqInt : Integrable (fun u : ℝ => a * q u) := hqInt.const_mul a
  calc
    ‖∫ u : ℝ, pintz2023MellinContourIntegrand N
        ((sigma : ℂ) + I * (t : ℂ)) ((u : ℂ) * I)‖ ≤
      ∫ u : ℝ, ‖pintz2023MellinContourIntegrand N
        ((sigma : ℂ) + I * (t : ℂ)) ((u : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, a * q u :=
      integral_mono hContourInt.norm haqInt hPoint
    _ = a * ∫ u : ℝ, q u := by rw [integral_const_mul]
    _ ≤ a * L := mul_le_mul_of_nonneg_left hqBound ha
    _ = B * d⁻¹ * (|t| + 3) ^ p := by
      dsimp only [a, B]
      ring
    _ = B * (1 - sigma)⁻¹ *
        (|t| + 3) ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by rfl

/-- The exact smoothed sum after subtracting the pole-crossing residue. -/
theorem exists_norm_pintz2023SmoothedZetaSum_sub_residue_nearOne_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (sigma t : ℝ),
      0 < N → 11 / 12 ≤ sigma → sigma < 1 →
      ‖pintz2023SmoothedZetaSum N ((sigma : ℂ) + I * (t : ℂ)) -
          pintz2023MellinWeight N
            (1 - ((sigma : ℂ) + I * (t : ℂ)))‖ ≤
        B * (1 - sigma)⁻¹ *
          (|t| + 3) ^ ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨B₀, hB₀, hIntegral⟩ :=
    exists_norm_pintz2023MellinContourIntegral_nearOne_le
      hepsilon hepsilonUpper
  let B : ℝ := (1 / (2 * Real.pi)) * B₀
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro N sigma t hN hsigmaLower hsigmaUpper
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hsRe : s.re = sigma := by simp [s]
  have hShift := pintz2023SmoothedZetaSum_eq_left_contour_add_residue
    (s := s) hN (by rw [hsRe]; linarith) (by rw [hsRe]; exact hsigmaUpper)
  have hDiff :
      pintz2023SmoothedZetaSum N s - pintz2023MellinWeight N (1 - s) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u : ℝ, pintz2023MellinContourIntegrand N s ((u : ℂ) * I)) := by
    linear_combination hShift
  rw [show ((sigma : ℂ) + I * (t : ℂ)) = s by rfl, hDiff, norm_mul,
    norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ u : ℝ, pintz2023MellinContourIntegrand N s ((u : ℂ) * I)‖ ≤
      (1 / (2 * Real.pi)) *
        (B₀ * (1 - sigma)⁻¹ *
          (|t| + 3) ^ ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
        gcongr
        simpa only [s] using hIntegral N sigma t hN hsigmaLower hsigmaUpper
    _ = B * (1 - sigma)⁻¹ *
        (|t| + 3) ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
      dsimp only [B]
      ring

#print axioms exists_norm_pintz2023MellinContourIntegral_nearOne_le
#print axioms exists_norm_pintz2023SmoothedZetaSum_sub_residue_nearOne_le

end

end GafniTao
