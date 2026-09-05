import GafniTao.PintzGammaHorizontalTwoSided

/-!
# Sharp vertical Gamma ratios on a positive half-strip

Both Gamma factors are moved horizontally to `Re z = 1/2`.  The opposite
logarithmic powers cancel, and the exact half-line identity controls the
remaining change in imaginary height.  This avoids a Stirling postulate and
retains only an exponential envelope in the vertical displacement.
-/

open Complex Set

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

set_option maxHeartbeats 1000000

/-- At a fixed real part in `(0,1/2]`, changing the imaginary height by `u`
inside the central range costs only `exp(C + pi*|u|/2)`. -/
theorem exists_norm_Gamma_vertical_ratio_same_re_le
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      2 ≤ t → |u| ≤ t / 2 →
      ‖Complex.Gamma ((b : ℂ) + ((t + u : ℝ) : ℂ) * I) /
          Complex.Gamma ((b : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp (C + Real.pi * |u| / 2) := by
  obtain ⟨Dminus, hDminus, hleft⟩ :=
    exists_norm_Gamma_left_displacement_le
      (a := b) (b := (1 / 2 : ℝ)) hb
  obtain ⟨Dplus, hDplus, hright⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := b) (b := (1 / 2 : ℝ)) hb
  let e : ℝ := 1 / 2 - b
  let C : ℝ := 1 + (Dminus + Dplus + Real.log 2) * e
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp only [C]
    have : 0 ≤ (Dminus + Dplus + Real.log 2) * e := by positivity
    linarith
  refine ⟨C, hC, ?_⟩
  intro t u ht hu
  let zY : ℂ := (1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I
  let zT : ℂ := (b : ℂ) + (t : ℂ) * I
  let zHalfT : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have htPos : 0 < t := by linarith
  have htu : t / 2 ≤ t + u := by
    rw [abs_le] at hu
    linarith
  have htuPos : 0 < t + u := by linarith
  have hlogCompare :
      Real.log (|t| + 2) - Real.log (|t + u| + 2) ≤ Real.log 2 := by
    rw [abs_of_pos htPos, abs_of_pos htuPos]
    have harg : t + 2 ≤ 2 * (t + u + 2) := by linarith
    have hdenPos : 0 < t + u + 2 := by linarith
    have hlog := Real.log_le_log (by linarith : 0 < t + 2) harg
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt hdenPos)] at hlog
    linarith
  have hzYRe : zY.re = 1 / 2 := by simp [zY]
  have hzYIm : zY.im = t + u := by simp [zY]
  have hzTRe : zT.re = b := by simp [zT]
  have hzTIm : zT.im = t := by simp [zT]
  have hzHalfTRe : zHalfT.re = 1 / 2 := by simp [zHalfT]
  have hleftBound :
      ‖Complex.Gamma (zY - (e : ℂ))‖ ≤
        ‖Complex.Gamma zY‖ *
          Real.exp ((Dminus - Real.log (|t + u| + 2)) * e) := by
    have h := hleft zY e (by simp [zY, e]) (by simp [zY]) he
    rw [hzYIm] at h
    exact h
  have hrightBound :
      ‖Complex.Gamma zHalfT‖ ≤
        ‖Complex.Gamma zT‖ *
          Real.exp ((Real.log (|t| + 2) + Dplus) * e) := by
    have h := hright zT e (by simp [zT]) (by simp [zT, e]) he
    rw [hzTIm] at h
    have harg : zT + (e : ℂ) = zHalfT := by
      apply Complex.ext
      · simp [zHalfT, zT, e]
      · simp [zHalfT, zT, e]
    rw [harg] at h
    exact h
  have hGammaT : 0 < ‖Complex.Gamma zT‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simpa [zT] using hb)
  have hGammaHalfT : 0 < ‖Complex.Gamma zHalfT‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [zHalfT])
  have hInvRight :
      ‖(Complex.Gamma zT)⁻¹‖ ≤
        ‖(Complex.Gamma zHalfT)⁻¹‖ *
          Real.exp ((Real.log (|t| + 2) + Dplus) * e) := by
    rw [norm_inv, norm_inv]
    have hquot : (1 : ℝ) / ‖Complex.Gamma zT‖ ≤
        Real.exp ((Real.log (|t| + 2) + Dplus) * e) /
          ‖Complex.Gamma zHalfT‖ := by
      rw [div_le_div_iff₀ hGammaT hGammaHalfT]
      nlinarith [Real.exp_pos ((Real.log (|t| + 2) + Dplus) * e)]
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hquot
  have hhalf :
      ‖Complex.Gamma zY‖ * ‖(Complex.Gamma zHalfT)⁻¹‖ ≤
        Real.exp (Real.pi * |u| / 2) := by
    have h := norm_Gamma_half_t_sub_u_div_half_t_add_u_le
      (t + u / 2) (-u / 2)
    have hnum : t + u / 2 - (-u / 2) = t + u := by ring
    have hden : t + u / 2 + (-u / 2) = t := by ring
    rw [hnum, hden, abs_div, abs_neg] at h
    norm_num at h
    have hExpArg : Real.pi * (|u| / 2) = Real.pi * |u| / 2 := by ring
    rw [hExpArg] at h
    simpa [zY, zHalfT, div_eq_mul_inv] using h
  have hExp :
      Real.exp ((Dminus - Real.log (|t + u| + 2)) * e) *
          Real.exp ((Real.log (|t| + 2) + Dplus) * e) ≤
        Real.exp ((Dminus + Dplus + Real.log 2) * e) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have harg :
      ((b : ℂ) + ((t + u : ℝ) : ℂ) * I) = zY - (e : ℂ) := by
    apply Complex.ext <;> simp [zY, e]
  rw [harg, div_eq_mul_inv, norm_mul]
  calc
    ‖Complex.Gamma (zY - (e : ℂ))‖ * ‖(Complex.Gamma zT)⁻¹‖ ≤
        (‖Complex.Gamma zY‖ *
          Real.exp ((Dminus - Real.log (|t + u| + 2)) * e)) *
        (‖(Complex.Gamma zHalfT)⁻¹‖ *
          Real.exp ((Real.log (|t| + 2) + Dplus) * e)) := by gcongr
    _ = (‖Complex.Gamma zY‖ * ‖(Complex.Gamma zHalfT)⁻¹‖) *
        (Real.exp ((Dminus - Real.log (|t + u| + 2)) * e) *
          Real.exp ((Real.log (|t| + 2) + Dplus) * e)) := by ring
    _ ≤ Real.exp (Real.pi * |u| / 2) *
        Real.exp ((Dminus + Dplus + Real.log 2) * e) := by gcongr
    _ = Real.exp (Real.pi * |u| / 2 +
        (Dminus + Dplus + Real.log 2) * e) := by rw [← Real.exp_add]
    _ ≤ Real.exp (C + Real.pi * |u| / 2) := by
      apply Real.exp_le_exp.mpr
      dsimp only [C]
      linarith

#print axioms exists_norm_Gamma_vertical_ratio_same_re_le

/-- The central-range Gamma quotient after a left displacement `q` of the
physical complex variable.  The displayed negative logarithm is the exact
conductor saving `t^(-q/2)` up to the harmless comparison of `t/4+2` with
`t`. -/
theorem exists_norm_Gamma_left_vertical_ratio_le
    {r q : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      4 ≤ t → |u| ≤ t / 2 →
      ‖Complex.Gamma
          ((((r - q) / 2 : ℝ) : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I) /
          Complex.Gamma
            (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤
        Real.exp (C + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2)) := by
  have hb : 0 < r / 2 := by linarith
  have hbHalf : r / 2 ≤ 1 / 2 := by linarith
  have ha : 0 < (r - q) / 2 := by linarith
  obtain ⟨Cvert, hCvert, hvert⟩ :=
    exists_norm_Gamma_vertical_ratio_same_re_le hb hbHalf
  obtain ⟨D, hD, hleft⟩ :=
    exists_norm_Gamma_left_displacement_le
      (a := (r - q) / 2) (b := r / 2) ha
  let d : ℝ := q / 2
  let C : ℝ := 1 + Cvert + D * d
  have hd : 0 < d := by dsimp only [d]; linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u ht hu
  let zY : ℂ := ((r / 2 : ℝ) : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I
  let zT : ℂ := ((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I
  have htHalf : 2 ≤ t / 2 := by linarith
  have huHalf : |u / 2| ≤ (t / 2) / 2 := by
    rw [abs_div]
    norm_num
    linarith
  have hvertBound :
      ‖Complex.Gamma zY / Complex.Gamma zT‖ ≤
        Real.exp (Cvert + Real.pi * |u| / 4) := by
    have h := hvert (t / 2) (u / 2) htHalf huHalf
    have hsum : t / 2 + u / 2 = (t + u) / 2 := by ring
    rw [hsum, abs_div] at h
    norm_num at h
    have hExpArg : Real.pi * (|u| / 2) / 2 = Real.pi * |u| / 4 := by ring
    rw [hExpArg] at h
    rw [norm_div]
    simpa [zY, zT] using h
  have htPos : 0 < t := by linarith
  have htu : t / 2 ≤ t + u := by
    rw [abs_le] at hu
    linarith
  have htuPos : 0 < t + u := by linarith
  have hYPos : 0 < (t + u) / 2 := by positivity
  have hlogLower : Real.log (t / 4 + 2) ≤
      Real.log (|(t + u) / 2| + 2) := by
    rw [abs_of_pos hYPos]
    apply Real.log_le_log (by linarith)
    linarith
  have hzYRe : zY.re = r / 2 := by simp [zY]
  have hzYIm : zY.im = (t + u) / 2 := by simp [zY]
  have hleftBound :
      ‖Complex.Gamma (zY - (d : ℂ))‖ ≤
        ‖Complex.Gamma zY‖ *
          Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d) := by
    have hLower : (r - q) / 2 ≤ zY.re - d := by
      rw [hzYRe]
      dsimp only [d]
      linarith
    have h := hleft zY d hLower (by simp [zY]) hd.le
    rw [hzYIm] at h
    exact h
  have hGammaT : Complex.Gamma zT ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa [zT] using hb)
  have hExp :
      Real.exp (Cvert + Real.pi * |u| / 4) *
          Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d) ≤
        Real.exp (C + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * d) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [C]
    nlinarith
  have harg :
      ((((r - q) / 2 : ℝ) : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I) =
        zY - (d : ℂ) := by
    apply Complex.ext
    · simp [zY, d]
      ring
    · simp [zY, d]
  rw [harg]
  calc
    ‖Complex.Gamma (zY - (d : ℂ)) / Complex.Gamma zT‖ ≤
        ‖Complex.Gamma zY / Complex.Gamma zT‖ *
          Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d) := by
      rw [norm_div, norm_div]
      have hInv : 0 ≤ ‖Complex.Gamma zT‖⁻¹ := by positivity
      calc
        ‖Complex.Gamma (zY - (d : ℂ))‖ * ‖Complex.Gamma zT‖⁻¹ ≤
            (‖Complex.Gamma zY‖ *
              Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d)) *
                ‖Complex.Gamma zT‖⁻¹ :=
          mul_le_mul_of_nonneg_right hleftBound hInv
        _ = (‖Complex.Gamma zY‖ * ‖Complex.Gamma zT‖⁻¹) *
            Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d) := by ring
    _ ≤ Real.exp (Cvert + Real.pi * |u| / 4) *
        Real.exp ((D - Real.log (|(t + u) / 2| + 2)) * d) := by gcongr
    _ ≤ Real.exp (C + Real.pi * |u| / 4 -
        Real.log (t / 4 + 2) * d) := hExp
    _ = Real.exp (C + Real.pi * |u| / 4 -
        Real.log (t / 4 + 2) * (q / 2)) := by rfl

#print axioms exists_norm_Gamma_left_vertical_ratio_le

/-- Exact norm expansion of Deligne's real Gamma factor at physical real and
imaginary coordinates. -/
theorem norm_GammaR_real_im (r t : ℝ) :
    ‖Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
      Real.pi ^ (-r / 2) *
        ‖Complex.Gamma (((r / 2 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · congr 1
    simp
  · congr 2
    push_cast
    ring

/-- Central-range real-Gamma quotient used by the single-zeta AFE.  The
`pi^(q/2)` normalization is absorbed into the constant while the exact
negative conductor logarithm remains visible. -/
theorem exists_norm_GammaR_left_vertical_ratio_le
    {r q : ℝ} (hq : 0 < q) (hqr : q < r) (hr : r ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      4 ≤ t → |u| ≤ t / 2 →
      ‖Complex.Gammaℝ
          (((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp (C + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2)) := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_Gamma_left_vertical_ratio_le hq hqr hr
  let C : ℝ := 1 + Cgamma + Real.log Real.pi * (q / 2)
  have hpiOne : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hlogPi : 0 < Real.log Real.pi := Real.log_pos hpiOne
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u ht hu
  have hordinary := hgamma t u ht hu
  have hpi :
      Real.pi ^ (-(r - q) / 2) / Real.pi ^ (-r / 2) =
        Real.pi ^ (q / 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg Real.pi_pos.le,
      ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hpDen : 0 < Real.pi ^ (-r / 2) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have hgammaDen :
      0 < ‖Complex.Gamma
        (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hnorm :
      ‖Complex.Gammaℝ
          (((r - q : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((r : ℂ) + (t : ℂ) * I)‖ =
        Real.pi ^ (q / 2) *
          ‖Complex.Gamma
            ((((r - q) / 2 : ℝ) : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I) /
            Complex.Gamma
              (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    rw [norm_div, norm_GammaR_real_im, norm_GammaR_real_im, norm_div]
    calc
      Real.pi ^ (-(r - q) / 2) *
            ‖Complex.Gamma
              ((((r - q) / 2 : ℝ) : ℂ) +
                (((t + u) / 2 : ℝ) : ℂ) * I)‖ /
          (Real.pi ^ (-r / 2) *
            ‖Complex.Gamma
              (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) =
          (Real.pi ^ (-(r - q) / 2) / Real.pi ^ (-r / 2)) *
            (‖Complex.Gamma
                ((((r - q) / 2 : ℝ) : ℂ) +
                  (((t + u) / 2 : ℝ) : ℂ) * I)‖ /
              ‖Complex.Gamma
                (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) := by
            field_simp [ne_of_gt hpDen, ne_of_gt hgammaDen]
      _ = Real.pi ^ (q / 2) *
            (‖Complex.Gamma
                ((((r - q) / 2 : ℝ) : ℂ) +
                  (((t + u) / 2 : ℝ) : ℂ) * I)‖ /
              ‖Complex.Gamma
                (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖) := by
          rw [hpi]
  rw [hnorm]
  calc
    Real.pi ^ (q / 2) *
        ‖Complex.Gamma
          ((((r - q) / 2 : ℝ) : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I) /
          Complex.Gamma
            (((r / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤
      Real.pi ^ (q / 2) *
        Real.exp (Cgamma + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2)) := by gcongr
    _ = Real.exp (Real.log Real.pi * (q / 2) +
        (Cgamma + Real.pi * |u| / 4 -
          Real.log (t / 4 + 2) * (q / 2))) := by
      rw [Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_add]
    _ ≤ Real.exp (C + Real.pi * |u| / 4 -
        Real.log (t / 4 + 2) * (q / 2)) := by
      apply Real.exp_le_exp.mpr
      dsimp only [C]
      linarith

#print axioms norm_GammaR_real_im
#print axioms exists_norm_GammaR_left_vertical_ratio_le

end

end GafniTao
