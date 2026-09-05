import GafniTao.Pintz2023NearOneSmoothedZeta

/-!
# The moving-pole residue in Pintz's Mellin lemma

The residue is estimated at its literal argument `1-s`.  Its `N^(1-Re s)`
factor and exponential height decay remain visible, as required in (3.4).
-/

open Complex Set

namespace GafniTao

noncomputable section

theorem norm_pintz2023MellinPowerDiff_nearOne_le
    {N : ℕ} (hN : 0 < N) {d t : ℝ} (hdUpper : d ≤ 1) :
    ‖pintz2023MellinPowerDiff N ((d : ℂ) - I * (t : ℂ))‖ ≤
      3 * (N : ℝ) ^ d := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := hNreal.le
  have hTwoNreal : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast mul_pos (by norm_num : (0 : ℕ) < 2) hN
  have hTwoPow :
      ‖((2 * N : ℕ) : ℂ) ^ ((d : ℂ) - I * (t : ℂ))‖ =
        ((2 * N : ℕ) : ℝ) ^ d := by
    rw [show ((2 * N : ℕ) : ℂ) = (((2 * N : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hTwoNreal)]
    simp
  have hOnePow :
      ‖(N : ℂ) ^ ((d : ℂ) - I * (t : ℂ))‖ = (N : ℝ) ^ d := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hNreal]
    simp
  have hTwoFactor : (2 : ℝ) ^ d ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hdUpper
  have hProduct : ((2 * N : ℕ) : ℝ) ^ d ≤ 2 * (N : ℝ) ^ d := by
    rw [show ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) by norm_num,
      Real.mul_rpow (by norm_num) hNnonneg]
    exact mul_le_mul_of_nonneg_right hTwoFactor (Real.rpow_nonneg hNnonneg d)
  rw [pintz2023MellinPowerDiff]
  calc
    ‖((2 * N : ℕ) : ℂ) ^ ((d : ℂ) - I * (t : ℂ)) -
        (N : ℂ) ^ ((d : ℂ) - I * (t : ℂ))‖ ≤
      ‖((2 * N : ℕ) : ℂ) ^ ((d : ℂ) - I * (t : ℂ))‖ +
        ‖(N : ℂ) ^ ((d : ℂ) - I * (t : ℂ))‖ := norm_sub_le _ _
    _ = ((2 * N : ℕ) : ℝ) ^ d + (N : ℝ) ^ d := by rw [hTwoPow, hOnePow]
    _ ≤ 3 * (N : ℝ) ^ d := by linarith

private theorem exists_norm_Gamma_nearOne_vertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (d t : ℝ),
      0 < d → d ≤ 1 / 12 → 1 ≤ |t| →
      ‖Complex.Gamma ((d : ℂ) - I * (t : ℂ))‖ ≤
        C * d⁻¹ * (|t| + 2) *
          Real.exp (-(Real.pi * |t|) / 2) := by
  obtain ⟨D, hD, hDisplace⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (by norm_num)
  let C : ℝ := 3 * Real.exp D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro d t hd hdUpper ht
  let w : ℂ := (d : ℂ) - I * (t : ℂ)
  let z : ℂ := (1 / 2 : ℂ) - I * (t : ℂ)
  let q : ℝ := d + 1 / 2
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have hqUpper : q ≤ 1 := by dsimp only [q]; linarith
  have hzRe : z.re = 1 / 2 := by simp [z]
  have hzIm : |z.im| = |t| := by simp [z]
  have hzAdd : z + (q : ℂ) = w + 1 := by
    apply Complex.ext
    · simp [z, q, w]
      ring
    · simp [z, q, w]
  have hShift := hDisplace z q (by rw [hzRe])
    (by rw [hzRe]; dsimp only [q]; linarith) hq
  have hHalf := norm_Gamma_half_vertical_le_exp (-t)
  have hHalfArg :
      (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = z := by
    apply Complex.ext <;> simp [z]
  rw [hHalfArg, abs_neg] at hHalf
  have hlogPos : 0 < Real.log (|t| + 2) + D := by
    have hlogNonneg : 0 ≤ Real.log (|t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hExp :
      Real.exp ((Real.log (|t| + 2) + D) * q) ≤
        (|t| + 2) * Real.exp D := by
    calc
      Real.exp ((Real.log (|t| + 2) + D) * q) ≤
          Real.exp (Real.log (|t| + 2) + D) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (|t| + 2) * Real.exp D := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hzIm, hzAdd] at hShift
  have hGammaSucc :
      ‖Complex.Gamma (w + 1)‖ ≤
        C * (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by
    calc
      ‖Complex.Gamma (w + 1)‖ ≤
          ‖Complex.Gamma z‖ *
            Real.exp ((Real.log (|t| + 2) + D) * q) := hShift
      _ ≤ (3 * Real.exp (-(Real.pi * |t|) / 2)) *
          ((|t| + 2) * Real.exp D) := by gcongr
      _ = C * (|t| + 2) *
          Real.exp (-(Real.pi * |t|) / 2) := by
        dsimp only [C]
        ring
  have hw : w ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [w] at hre
    linarith
  have hRec := Complex.Gamma_add_one w hw
  have hNormRec : ‖w‖ * ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ := by
    rw [hRec, norm_mul]
  have hwd : d ≤ ‖w‖ := by
    rw [← abs_of_pos hd]
    have := Complex.abs_re_le_norm w
    simpa [w] using this
  have hScaled :
      d * ‖Complex.Gamma w‖ ≤
        C * (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by
    calc
      d * ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ := by gcongr
      _ = ‖Complex.Gamma (w + 1)‖ := hNormRec
      _ ≤ _ := hGammaSucc
  have hDiv := (le_div_iff₀ hd).2 (by simpa [mul_comm] using hScaled)
  calc
    ‖Complex.Gamma ((d : ℂ) - I * (t : ℂ))‖ ≤
        (C * (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2)) / d := by
      dsimp only [w] at hDiv
      convert hDiv using 1
      all_goals ring
    _ = C * d⁻¹ * (|t| + 2) *
        Real.exp (-(Real.pi * |t|) / 2) := by
      rw [div_eq_mul_inv]
      ring

/-- Uniform bound for the literal pole residue in Pintz (3.4). -/
theorem exists_norm_pintz2023Mellin_residue_nearOne_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (sigma t : ℝ),
      0 < N → 11 / 12 ≤ sigma → sigma < 1 → 1 ≤ |t| →
      ‖pintz2023MellinWeight N
          (1 - ((sigma : ℂ) + I * (t : ℂ)))‖ ≤
        C * (1 - sigma)⁻¹ * (N : ℝ) ^ (1 - sigma) *
          (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by
  obtain ⟨C₀, hC₀, hGamma⟩ := exists_norm_Gamma_nearOne_vertical_le
  let C : ℝ := 3 * C₀
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N sigma t hN hsigmaLower hsigmaUpper ht
  let d : ℝ := 1 - sigma
  have hd : 0 < d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 / 12 := by dsimp only [d]; linarith
  have hw : (1 : ℂ) - ((sigma : ℂ) + I * (t : ℂ)) =
      (d : ℂ) - I * (t : ℂ) := by
    apply Complex.ext <;> simp [d]
  rw [hw, pintz2023MellinWeight_eq (by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [d] at hre
    linarith), norm_mul]
  have hPower := norm_pintz2023MellinPowerDiff_nearOne_le
    (t := t) hN (hdUpper.trans (by norm_num))
  have hGammaBound := hGamma d t hd hdUpper ht
  calc
    ‖pintz2023MellinPowerDiff N ((d : ℂ) - I * (t : ℂ))‖ *
        ‖Complex.Gamma ((d : ℂ) - I * (t : ℂ))‖ ≤
      (3 * (N : ℝ) ^ d) *
        (C₀ * d⁻¹ * (|t| + 2) *
          Real.exp (-(Real.pi * |t|) / 2)) := by gcongr
    _ = C * d⁻¹ * (N : ℝ) ^ d * (|t| + 2) *
        Real.exp (-(Real.pi * |t|) / 2) := by
      dsimp only [C]
      ring
    _ = C * (1 - sigma)⁻¹ * (N : ℝ) ^ (1 - sigma) *
        (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by rfl

/-- Source-shaped quantitative version of Pintz Lemma 3.4 in the strict
near-one strip.  The zeta contribution and moving-pole residue are separate. -/
theorem exists_norm_pintz2023SmoothedZetaSum_nearOne_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ B R : ℝ, 0 < B ∧ 0 < R ∧ ∀ (N : ℕ) (sigma t : ℝ),
      0 < N → 11 / 12 ≤ sigma → sigma < 1 → 1 ≤ |t| →
      ‖pintz2023SmoothedZetaSum N ((sigma : ℂ) + I * (t : ℂ))‖ ≤
        B * (1 - sigma)⁻¹ *
            (|t| + 3) ^ ((1 / 2 : ℝ) *
              (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) +
          R * (1 - sigma)⁻¹ * (N : ℝ) ^ (1 - sigma) *
            (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by
  obtain ⟨B, hB, hMain⟩ :=
    exists_norm_pintz2023SmoothedZetaSum_sub_residue_nearOne_le
      hepsilon hepsilonUpper
  obtain ⟨R, hR, hResidue⟩ :=
    exists_norm_pintz2023Mellin_residue_nearOne_le
  refine ⟨B, R, hB, hR, ?_⟩
  intro N sigma t hN hsigmaLower hsigmaUpper ht
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  let residue : ℂ := pintz2023MellinWeight N (1 - s)
  calc
    ‖pintz2023SmoothedZetaSum N s‖ =
        ‖(pintz2023SmoothedZetaSum N s - residue) + residue‖ := by ring_nf
    _ ≤ ‖pintz2023SmoothedZetaSum N s - residue‖ + ‖residue‖ := norm_add_le _ _
    _ ≤ B * (1 - sigma)⁻¹ *
            (|t| + 3) ^ ((1 / 2 : ℝ) *
              (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) +
          R * (1 - sigma)⁻¹ * (N : ℝ) ^ (1 - sigma) *
            (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2) := by
      apply add_le_add
      · simpa only [s, residue] using
          hMain N sigma t hN hsigmaLower hsigmaUpper
      · simpa only [s, residue] using
          hResidue N sigma t hN hsigmaLower hsigmaUpper ht

#print axioms exists_norm_pintz2023Mellin_residue_nearOne_le
#print axioms exists_norm_pintz2023SmoothedZetaSum_nearOne_le
#print axioms norm_pintz2023MellinPowerDiff_nearOne_le

end

end GafniTao
