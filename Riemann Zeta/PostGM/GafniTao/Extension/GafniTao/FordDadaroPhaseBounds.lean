import GafniTao.FordDadaroTruncation

/-!
# Uniform coefficient bounds at Ford's Dadaro cutoff

The cutoff lies just above the physical height.  Consequently Dadaro's phase
lies in the fixed compact interval `[1/3, 1/2]`.  This file proves that fact
and bounds the two explicit correction coefficients occurring in the exact
truncation formula.
-/

open Complex Set

namespace GafniTao

noncomputable section

def fordDadaroPhase (sigma t : ℝ) : ℝ :=
  Real.pi * RiemannZeta.GuthMaynard.sharpZetaTheta
    (fordComplexHeight sigma t) (fordDadaroCutoff t)

theorem fordDadaroPhase_eq (sigma t : ℝ) :
    fordDadaroPhase sigma t = t / (2 * fordDadaroCutoff t) := by
  unfold fordDadaroPhase
  rw [RiemannZeta.GuthMaynard.pi_mul_sharpZetaTheta_eq _
    (fordDadaroCutoff_pos t).ne']
  simp [fordComplexHeight]

theorem fordDadaroPhase_mem_Icc
    {sigma t : ℝ} (ht : 3 ≤ t) :
    fordDadaroPhase sigma t ∈ Set.Icc (1 / 3 : ℝ) (1 / 2 : ℝ) := by
  have htPos : 0 < t := by linarith
  have hcutPos : 0 < fordDadaroCutoff t := fordDadaroCutoff_pos t
  have hcutUpper := fordDadaroCutoff_le_add htPos.le
  have hcutStrict := lt_fordDadaroCutoff t
  rw [fordDadaroPhase_eq]
  constructor
  · rw [le_div_iff₀ (mul_pos two_pos hcutPos)]
    nlinarith
  · rw [div_le_iff₀ (mul_pos two_pos hcutPos)]
    nlinarith

theorem one_fourth_le_sin_of_mem_fordDadaroPhase {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 3 : ℝ) (1 / 2 : ℝ)) :
    1 / 4 ≤ Real.sin x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    linarith [hx.2]
  have hbound := Real.sin_bound hxabs
  have hlow := (abs_le.mp hbound).1
  rw [abs_of_nonneg hx0] at hlow
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx.2)]
  have hx3 : x ^ 3 ≤ x / 4 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2)]
  have hx4 : x ^ 4 ≤ x / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hx3 hx0
    nlinarith [hx.2]
  nlinarith [hx.1]

theorem fordDadaroBoundaryCoeff_le_four
    {sigma t : ℝ} (ht : 3 ≤ t) :
    ‖RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff
        (fordComplexHeight sigma t) (fordDadaroCutoff t)‖ ≤ 4 := by
  let theta := RiemannZeta.GuthMaynard.sharpZetaTheta
    (fordComplexHeight sigma t) (fordDadaroCutoff t)
  let x := Real.pi * theta
  have hx : x ∈ Set.Icc (1 / 3 : ℝ) (1 / 2 : ℝ) := by
    simpa [x, theta, fordDadaroPhase] using
      (fordDadaroPhase_mem_Icc (sigma := sigma) ht)
  have hsinLower : 1 / 4 ≤ Real.sin x :=
    one_fourth_le_sin_of_mem_fordDadaroPhase hx
  have hsinPos : 0 < Real.sin x := by linarith
  have hxPos : 0 < x := by linarith [hx.1]
  have htheta : theta ≠ 0 := by
    intro h
    have : x = 0 := by simp [x, h]
    linarith
  have hsinNorm : ‖Complex.sin (x : ℂ)‖ = Real.sin x := by
    have hs : Complex.sin (x : ℂ) = (Real.sin x : ℂ) :=
      (Complex.ofReal_sin x).symm
    rw [hs, norm_real, Real.norm_eq_abs, abs_of_pos hsinPos]
  have hxNorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hxPos]
  have hInvSin : ‖(1 : ℂ) / Complex.sin (x : ℂ)‖ ≤ 4 := by
    rw [norm_div, norm_one, hsinNorm]
    rw [div_le_iff₀ hsinPos]
    nlinarith
  have hInvX : ‖(1 : ℂ) / (x : ℂ)‖ ≤ 3 := by
    rw [norm_div, norm_one, hxNorm]
    rw [div_le_iff₀ hxPos]
    nlinarith [hx.1]
  rw [RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff, if_pos htheta]
  have hxComplex :
      (Real.pi : ℂ) * (theta : ℂ) = (x : ℂ) := by simp [x]
  rw [hxComplex, norm_mul]
  have hI : ‖Complex.I / (2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hI]
  calc
    (1 / 2 : ℝ) * ‖(1 : ℂ) / Complex.sin (x : ℂ) - 1 / (x : ℂ)‖ ≤
        (1 / 2 : ℝ) *
          (‖(1 : ℂ) / Complex.sin (x : ℂ)‖ + ‖(1 : ℂ) / (x : ℂ)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) * (4 + 3) := by gcongr
    _ ≤ 4 := by norm_num

set_option maxHeartbeats 800000 in
theorem fordDadaroErrorCoeff_le_nine
    {sigma t : ℝ} (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ t) :
    RiemannZeta.GuthMaynard.sharpZetaErrorCoeff
        (fordComplexHeight sigma t) (fordDadaroCutoff t) ≤ 9 := by
  let theta := RiemannZeta.GuthMaynard.sharpZetaTheta
    (fordComplexHeight sigma t) (fordDadaroCutoff t)
  let x := Real.pi * theta
  have hx : x ∈ Set.Icc (1 / 3 : ℝ) (1 / 2 : ℝ) := by
    simpa [x, theta, fordDadaroPhase] using
      (fordDadaroPhase_mem_Icc (sigma := sigma) ht)
  have hxPos : 0 < x := by linarith [hx.1]
  have hthetaPos : 0 < theta := by
    have hpi := Real.pi_pos
    dsimp [x] at hxPos
    nlinarith
  have hthetaUpper : theta ≤ 1 / 6 := by
    have hpi := Real.pi_gt_three
    dsimp [x] at hx
    nlinarith [hx.2]
  have hthetaAbs : |theta| = theta := abs_of_pos hthetaPos
  have hsinLower : 1 / 4 ≤ Real.sin x :=
    one_fourth_le_sin_of_mem_fordDadaroPhase hx
  have hsinPos : 0 < Real.sin x := by linarith
  have hsComplex :
      Complex.sin ((Real.pi : ℂ) * (theta : ℂ)) = (Real.sin x : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
  have hxComplex : (Real.pi : ℂ) * (theta : ℂ) = (x : ℂ) := by simp [x]
  have hsinNorm :
      ‖Complex.sin ((Real.pi : ℂ) * (theta : ℂ))‖ = Real.sin x := by
    rw [hsComplex, norm_real, Real.norm_eq_abs, abs_of_pos hsinPos]
  have hA :
      (1 / (Complex.sin ((Real.pi : ℂ) * (theta : ℂ)) ^ 2 : ℂ)).re ≤ 16 := by
    calc
      _ ≤ ‖1 / (Complex.sin ((Real.pi : ℂ) * (theta : ℂ)) ^ 2 : ℂ)‖ :=
        Complex.re_le_norm _
      _ = 1 / (Real.sin x) ^ 2 := by
        rw [norm_div, norm_one, norm_pow, hsinNorm]
      _ ≤ 16 := by
        rw [div_le_iff₀ (sq_pos_of_pos hsinPos)]
        nlinarith
  have hB :
      0 ≤ (1 / (((Real.pi : ℂ) * (theta : ℂ)) ^ 2 : ℂ)).re := by
    rw [hxComplex]
    have heq : ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := by norm_cast
    rw [heq]
    norm_cast
    positivity
  have hOneMinus : 1 / 2 ≤ 1 - |theta| := by
    rw [hthetaAbs]
    linarith
  have hOneMinusPos : 0 < 1 - |theta| := by linarith
  have hCube : 1 / (1 - |theta|) ^ 3 ≤ 8 := by
    rw [div_le_iff₀ (pow_pos hOneMinusPos 3)]
    nlinarith [sq_nonneg (1 - |theta|)]
  have hzetaNorm : ‖riemannZeta (3 : ℂ)‖ ≤ 2 := by
    simpa using RiemannZeta.GuthMaynard.zeta_right_half_plane_bound 3 0
      (by norm_num)
  have hzetaRe : (riemannZeta 3).re ≤ 2 :=
    (Complex.re_le_norm _).trans hzetaNorm
  have hFirst : sigma / 2 *
        ((1 / (Complex.sin ((Real.pi : ℂ) * (theta : ℂ)) ^ 2 : ℂ)).re -
          (1 / (((Real.pi : ℂ) * (theta : ℂ)) ^ 2 : ℂ)).re) ≤ 8 := by
    have hhalf : 0 ≤ sigma / 2 := by positivity
    calc
      _ ≤ sigma / 2 * 16 := by gcongr; linarith
      _ ≤ 8 := by nlinarith
  have hDen : 18 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hSecond : |theta| / (2 * Real.pi ^ 2) *
        (1 / (1 - |theta|) ^ 3 + 2 * (riemannZeta 3).re - 1) ≤ 1 := by
    have hCoeffNonneg : 0 ≤ |theta| / (2 * Real.pi ^ 2) := by positivity
    have hCoeff : |theta| / (2 * Real.pi ^ 2) ≤ 1 / 108 := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
      rw [hthetaAbs]
      nlinarith [hthetaUpper, hDen]
    have hBracket :
        1 / (1 - |theta|) ^ 3 + 2 * (riemannZeta 3).re - 1 ≤ 11 := by
      linarith
    by_cases hBracketNonneg : 0 ≤
        1 / (1 - |theta|) ^ 3 + 2 * (riemannZeta 3).re - 1
    · calc
        _ ≤ (1 / 108 : ℝ) * 11 :=
          mul_le_mul hCoeff hBracket hBracketNonneg (by norm_num)
        _ ≤ 1 := by norm_num
    · have hnonpos := mul_nonpos_of_nonneg_of_nonpos hCoeffNonneg
          (le_of_not_ge hBracketNonneg)
      linarith
  rw [RiemannZeta.GuthMaynard.sharpZetaErrorCoeff,
    if_pos hthetaPos.ne']
  have hTotal := add_le_add hFirst hSecond
  norm_num at hTotal
  simpa [fordComplexHeight, theta] using hTotal

#print axioms fordDadaroPhase_mem_Icc
#print axioms one_fourth_le_sin_of_mem_fordDadaroPhase
#print axioms fordDadaroBoundaryCoeff_le_four
#print axioms fordDadaroErrorCoeff_le_nine

end

end GafniTao
