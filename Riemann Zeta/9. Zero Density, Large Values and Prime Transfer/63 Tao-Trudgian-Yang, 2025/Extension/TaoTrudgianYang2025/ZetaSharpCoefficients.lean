import GuthMaynard.ZetaTruncation

/-!
# Uniform sharp-truncation coefficients at arbitrary strip points

These generalize the geometric coefficient bounds in the local foundation.
No vanishing of zeta, or membership in a zero set, is assumed.
-/

noncomputable section
open Complex Set
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem sharpZetaPhase_mem_of_im_range {T : ℝ} {s : ℂ}
    (hT : 3/4 ≤ T) (him : s.im ∈ Set.Icc T (2*T)) :
    Real.pi * sharpZetaTheta s (sharpZetaCutoff T) ∈
      Set.Icc (1/12 : ℝ) (1/4 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hCutPos : 0 < sharpZetaCutoff T :=
    (by linarith : 0 < 4 * T).trans (four_mul_lt_sharpZetaCutoff T)
  rw [pi_mul_sharpZetaTheta_eq s hCutPos.ne']
  constructor
  · rw [le_div_iff₀ (by positivity : 0 < 2 * sharpZetaCutoff T)]
    have hCutUpper := sharpZetaCutoff_le_six_mul hT
    nlinarith [him.1]
  · rw [div_le_iff₀ (by positivity : 0 < 2 * sharpZetaCutoff T)]
    nlinarith [him.2, four_mul_lt_sharpZetaCutoff T]


theorem sharpZetaBoundaryCoeff_le_of_phase (s : ℂ) (a : ℝ)
    (hphase : Real.pi * sharpZetaTheta s a ∈ Set.Icc (1/12 : ℝ) (1/4 : ℝ)) :
    ‖sharpZetaBoundaryCoeff s a‖ ≤ 14 := by
  let θ := sharpZetaTheta s (a)
  let x := Real.pi * θ
  have hx : x ∈ Set.Icc (1 / 12 : ℝ) (1 / 4 : ℝ) := by
    simpa [x, θ] using hphase
  have hsinLower : 1 / 16 ≤ Real.sin x := one_sixteenth_le_sin_of_mem_Icc hx
  have hsinPos : 0 < Real.sin x := by linarith
  have hxPos : 0 < x := by linarith [hx.1]
  have hθ : θ ≠ 0 := by
    intro h
    have : x = 0 := by simp [x, h]
    linarith
  have hθ' : sharpZetaTheta s (a) ≠ 0 := by
    simpa [θ] using hθ
  have hsinNorm : ‖Complex.sin (x : ℂ)‖ = Real.sin x := by
    have hs : Complex.sin (x : ℂ) = (Real.sin x : ℂ) :=
      (Complex.ofReal_sin x).symm
    rw [hs, norm_real, Real.norm_eq_abs, abs_of_pos hsinPos]
  have hxNorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hxPos]
  have hInvSin : ‖(1 : ℂ) / Complex.sin (x : ℂ)‖ ≤ 16 := by
    rw [norm_div, norm_one, hsinNorm]
    rw [div_le_iff₀ hsinPos]
    nlinarith
  have hInvX : ‖(1 : ℂ) / (x : ℂ)‖ ≤ 12 := by
    rw [norm_div, norm_one, hxNorm]
    rw [div_le_iff₀ hxPos]
    nlinarith [hx.1]
  rw [sharpZetaBoundaryCoeff, if_pos hθ']
  have hxComplex :
      (Real.pi : ℂ) * (sharpZetaTheta s (a) : ℂ) = (x : ℂ) := by
    simp [x, θ]
  rw [hxComplex, norm_mul]
  have hI : ‖Complex.I / (2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hI]
  calc
    (1 / 2 : ℝ) * ‖(1 : ℂ) / Complex.sin (x : ℂ) - 1 / (x : ℂ)‖ ≤
        (1 / 2 : ℝ) *
          (‖(1 : ℂ) / Complex.sin (x : ℂ)‖ + ‖(1 : ℂ) / (x : ℂ)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) * (16 + 12) := by gcongr
    _ = 14 := by norm_num



set_option maxHeartbeats 800000 in
theorem sharpZetaErrorCoeff_le_of_phase (s : ℂ) (a : ℝ)
    (hphase : Real.pi * sharpZetaTheta s a ∈ Set.Icc (1/12 : ℝ) (1/4 : ℝ))
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    sharpZetaErrorCoeff s a ≤ 129 := by
  let θ := sharpZetaTheta s (a)
  let x := Real.pi * θ
  have hx : x ∈ Set.Icc (1 / 12 : ℝ) (1 / 4 : ℝ) := by
    simpa [x, θ] using hphase
  have hxPos : 0 < x := by linarith [hx.1]
  have hθPos : 0 < θ := by
    have hpi := Real.pi_pos
    dsimp [x] at hxPos
    nlinarith
  have hθUpper : θ ≤ 1 / 4 := by
    have hpi := Real.pi_gt_three
    dsimp [x] at hx
    nlinarith [hx.2]
  have hθAbs : |θ| = θ := abs_of_pos hθPos
  have hsinLower : 1 / 16 ≤ Real.sin x := one_sixteenth_le_sin_of_mem_Icc hx
  have hsinPos : 0 < Real.sin x := by linarith
  have hsComplex :
      Complex.sin ((Real.pi : ℂ) * (θ : ℂ)) = (Real.sin x : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
  have hxComplex : (Real.pi : ℂ) * (θ : ℂ) = (x : ℂ) := by simp [x]
  have hsinNorm : ‖Complex.sin ((Real.pi : ℂ) * (θ : ℂ))‖ = Real.sin x := by
    rw [hsComplex, norm_real, Real.norm_eq_abs, abs_of_pos hsinPos]
  have hA :
      (1 / (Complex.sin ((Real.pi : ℂ) * (θ : ℂ)) ^ 2 : ℂ)).re ≤ 256 := by
    calc
      _ ≤ ‖1 / (Complex.sin ((Real.pi : ℂ) * (θ : ℂ)) ^ 2 : ℂ)‖ :=
        Complex.re_le_norm _
      _ = 1 / (Real.sin x) ^ 2 := by
        rw [norm_div, norm_one, norm_pow, hsinNorm]
      _ ≤ 256 := by
        rw [div_le_iff₀ (sq_pos_of_pos hsinPos)]
        nlinarith
  have hB :
      0 ≤ (1 / (((Real.pi : ℂ) * (θ : ℂ)) ^ 2 : ℂ)).re := by
    rw [hxComplex]
    have heq : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [heq]
    norm_cast
    positivity
  have hOneMinus : 3 / 4 ≤ 1 - |θ| := by rw [hθAbs]; linarith
  have hOneMinusPos : 0 < 1 - |θ| := by linarith
  have hCube : 1 / (1 - |θ|) ^ 3 ≤ 4 := by
    rw [div_le_iff₀ (pow_pos hOneMinusPos 3)]
    nlinarith [sq_nonneg (1 - |θ|)]
  have hzetaNorm : ‖riemannZeta (3 : ℂ)‖ ≤ 2 := by
    simpa using zeta_right_half_plane_bound 3 0 (by norm_num)
  have hzetaRe : (riemannZeta 3).re ≤ 2 :=
    (Complex.re_le_norm _).trans hzetaNorm
  have hFirst : s.re / 2 *
        ((1 / (Complex.sin ((Real.pi : ℂ) * (θ : ℂ)) ^ 2 : ℂ)).re -
          (1 / (((Real.pi : ℂ) * (θ : ℂ)) ^ 2 : ℂ)).re) ≤ 128 := by
    have hhalf : 0 ≤ s.re / 2 := by positivity
    calc
      _ ≤ s.re / 2 * 256 := by gcongr; linarith
      _ ≤ 128 := by nlinarith
  have hDen : 18 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hSecond : |θ| / (2 * Real.pi ^ 2) *
        (1 / (1 - |θ|) ^ 3 + 2 * (riemannZeta 3).re - 1) ≤ 1 := by
    have hCoeffNonneg : 0 ≤ |θ| / (2 * Real.pi ^ 2) := by positivity
    have hCoeff : |θ| / (2 * Real.pi ^ 2) ≤ 1 / 72 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
      rw [hθAbs]
      nlinarith [hθUpper, hDen]
    have hBracket :
        1 / (1 - |θ|) ^ 3 + 2 * (riemannZeta 3).re - 1 ≤ 7 := by
      linarith
    by_cases hBracketNonneg : 0 ≤
        1 / (1 - |θ|) ^ 3 + 2 * (riemannZeta 3).re - 1
    · calc
        _ ≤ (1 / 72 : ℝ) * 7 :=
          mul_le_mul hCoeff hBracket hBracketNonneg (by norm_num)
        _ ≤ 1 := by norm_num
    · have := mul_nonpos_of_nonneg_of_nonpos hCoeffNonneg (le_of_not_ge hBracketNonneg)
      linarith
  rw [sharpZetaErrorCoeff, if_pos hθPos.ne']
  have hNum : (128 : ℝ) + 1 ≤ 129 := by norm_num
  have hTotal := (add_le_add hFirst hSecond).trans hNum
  simpa only [θ] using hTotal


end TaoTrudgianYang2025

