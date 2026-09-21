import TaoTrudgianYang2025.PointMeanGammaDecay

/-!
Adapted from node 74 `GafniTao/HeathBrownGammaKernel.lean` to the current native
foundation. No adjacent extension or new dependency pin is imported.

# The Gamma kernel in Heath--Brown (1978), equation (41)

This file proves a uniform version of the two Gamma estimates used when the
Mellin contour is moved from `Re w = δ` to `Re w = -δ`.  The denominator
`δ + |v|` is retained: it is the logarithmic singularity which later produces
the single factor `log t` in Lemma 3.
-/

open Complex

namespace TaoTrudgianYang2025

noncomputable section

/-- The elementary absorption which converts the half-line Gamma decay into
the exponential kernel printed by Heath--Brown. -/
theorem add_two_mul_exp_neg_pi_half_le_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
      2 * Real.exp (-x) := by
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hExpLower : 1 + x / 2 ≤ Real.exp (x / 2) :=
    by simpa [add_comm] using Real.add_one_le_exp (x / 2)
  have hExponent : x / 2 ≤ (Real.pi / 2 - 1) * x := by
    nlinarith
  have hExpMono : Real.exp (x / 2) ≤
      Real.exp ((Real.pi / 2 - 1) * x) := Real.exp_le_exp.mpr hExponent
  have hLinear : x + 2 ≤
      2 * Real.exp ((Real.pi / 2 - 1) * x) := by
    calc
      x + 2 = 2 * (1 + x / 2) := by ring
      _ ≤ 2 * Real.exp (x / 2) := by gcongr
      _ ≤ 2 * Real.exp ((Real.pi / 2 - 1) * x) := by gcongr
  calc
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
        (2 * Real.exp ((Real.pi / 2 - 1) * x)) *
          Real.exp (-(Real.pi * x) / 2) := by gcongr
    _ = 2 * Real.exp (-x) := by
      rw [show 2 * Real.exp ((Real.pi / 2 - 1) * x) *
          Real.exp (-(Real.pi * x) / 2) =
        2 * (Real.exp ((Real.pi / 2 - 1) * x) *
          Real.exp (-(Real.pi * x) / 2)) by ring,
        ← Real.exp_add]
      congr 1
      ring_nf

/-- A version of the elementary Gamma absorption retaining exponential rate
`4/3`.  The reserve beyond rate one is used in the double convolution in
Heath--Brown's Lemma 3. -/
theorem add_two_mul_exp_neg_pi_half_le_six_mul_exp_neg_four_thirds
    (x : ℝ) (hx : 0 ≤ x) :
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
      6 * Real.exp (-(4 / 3 : ℝ) * x) := by
  have hExpLower : 1 + x / 6 ≤ Real.exp (x / 6) :=
    by simpa [add_comm] using Real.add_one_le_exp (x / 6)
  have hExponent : x / 6 ≤ (Real.pi / 2 - 4 / 3) * x := by
    nlinarith [Real.pi_gt_three]
  have hLinear : x + 2 ≤
      6 * Real.exp ((Real.pi / 2 - 4 / 3) * x) := by
    calc
      x + 2 ≤ 6 * (1 + x / 6) := by linarith
      _ ≤ 6 * Real.exp (x / 6) := by gcongr
      _ ≤ 6 * Real.exp ((Real.pi / 2 - 4 / 3) * x) := by
        gcongr
  calc
    (x + 2) * Real.exp (-(Real.pi * x) / 2) ≤
        (6 * Real.exp ((Real.pi / 2 - 4 / 3) * x)) *
          Real.exp (-(Real.pi * x) / 2) := by gcongr
    _ = 6 * Real.exp (-(4 / 3 : ℝ) * x) := by
      rw [show 6 * Real.exp ((Real.pi / 2 - 4 / 3) * x) *
          Real.exp (-(Real.pi * x) / 2) =
        6 * (Real.exp ((Real.pi / 2 - 4 / 3) * x) *
          Real.exp (-(Real.pi * x) / 2)) by ring,
        ← Real.exp_add]
      congr 1
      ring_nf

/-- Both real and imaginary coordinates are controlled by the complex norm.
This deliberately uses the harmless factor `2` instead of introducing a
square root into the later recurrence calculation. -/
theorem add_abs_le_two_mul_norm_ofReal_add_mul_I (a v : ℝ) (ha : 0 ≤ a) :
    a + |v| ≤ 2 * ‖(a : ℂ) + (v : ℂ) * I‖ := by
  have hre : a ≤ ‖(a : ℂ) + (v : ℂ) * I‖ := by
    simpa [abs_of_nonneg ha] using
      Complex.abs_re_le_norm ((a : ℂ) + (v : ℂ) * I)
  have him : |v| ≤ ‖(a : ℂ) + (v : ℂ) * I‖ := by
    simpa using Complex.abs_im_le_norm ((a : ℂ) + (v : ℂ) * I)
  linarith

/-- Uniform exponential decay for Gamma on the compact positive strip needed
after applying the recurrence to `Γ(±δ+iv)`. -/
theorem exists_norm_Gamma_heathBrown_positive_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      3 / 4 ≤ a → a ≤ 5 / 4 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) := by
  obtain ⟨D, hD, hShift⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (by norm_num)
  let C : ℝ := 6 * Real.exp D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a v haLower haUpper
  let z : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  let d : ℝ := a - 1 / 2
  have hdLower : 0 ≤ d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 := by dsimp only [d]; linarith
  have hzRe : z.re = 1 / 2 := by simp [z]
  have hzIm : |z.im| = |v| := by simp [z]
  have hzAdd : z + (d : ℂ) = (a : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [z, d]
  have hDisplaced := hShift z d (by rw [hzRe])
    (by rw [hzRe]; dsimp only [d]; linarith) hdLower
  have hHalf := norm_Gamma_half_vertical_le_exp v
  have hLogNonneg : 0 ≤ Real.log (|v| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg v])
  have hRatePos : 0 ≤ Real.log (|v| + 2) + D := by linarith
  have hExponent :
      (Real.log (|v| + 2) + D) * d ≤
        Real.log (|v| + 2) + D := by
    nlinarith
  have hExpShift :
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
        (|v| + 2) * Real.exp D := by
    calc
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
          Real.exp (Real.log (|v| + 2) + D) :=
        Real.exp_le_exp.mpr hExponent
      _ = (|v| + 2) * Real.exp D := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hzIm, hzAdd] at hDisplaced
  calc
    ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|v| + 2) + D) * d) := hDisplaced
    _ ≤ (3 * Real.exp (-(Real.pi * |v|) / 2)) *
        ((|v| + 2) * Real.exp D) := by
      gcongr
    _ ≤ (3 * (2 * Real.exp (-|v|))) * Real.exp D := by
      have hAbsorb := add_two_mul_exp_neg_pi_half_le_exp_neg |v| (abs_nonneg v)
      nlinarith [Real.exp_pos D]
    _ = C * Real.exp (-|v|) := by
      dsimp only [C]
      ring

/-- Strong positive-strip Gamma bound with enough exponential reserve for
the source double-convolution estimate. -/
theorem exists_norm_Gamma_heathBrown_positive_strip_strong_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      3 / 4 ≤ a → a ≤ 5 / 4 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  obtain ⟨D, hD, hShift⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (by norm_num)
  let C : ℝ := 18 * Real.exp D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a v haLower haUpper
  let z : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  let d : ℝ := a - 1 / 2
  have hdLower : 0 ≤ d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 := by dsimp only [d]; linarith
  have hzRe : z.re = 1 / 2 := by simp [z]
  have hzIm : |z.im| = |v| := by simp [z]
  have hzAdd : z + (d : ℂ) = (a : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [z, d]
  have hDisplaced := hShift z d (by rw [hzRe])
    (by rw [hzRe]; dsimp only [d]; linarith) hdLower
  have hHalf := norm_Gamma_half_vertical_le_exp v
  have hLogNonneg : 0 ≤ Real.log (|v| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg v])
  have hRatePos : 0 ≤ Real.log (|v| + 2) + D := by linarith
  have hExponent :
      (Real.log (|v| + 2) + D) * d ≤
        Real.log (|v| + 2) + D := by
    nlinarith
  have hExpShift :
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
        (|v| + 2) * Real.exp D := by
    calc
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
          Real.exp (Real.log (|v| + 2) + D) :=
        Real.exp_le_exp.mpr hExponent
      _ = (|v| + 2) * Real.exp D := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hzIm, hzAdd] at hDisplaced
  calc
    ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|v| + 2) + D) * d) := hDisplaced
    _ ≤ (3 * Real.exp (-(Real.pi * |v|) / 2)) *
        ((|v| + 2) * Real.exp D) := by
      gcongr
    _ ≤ (3 * (6 * Real.exp (-(4 / 3 : ℝ) * |v|))) * Real.exp D := by
      have hAbsorb :=
        add_two_mul_exp_neg_pi_half_le_six_mul_exp_neg_four_thirds
          |v| (abs_nonneg v)
      nlinarith [Real.exp_pos D]
    _ = C * Real.exp (-(4 / 3 : ℝ) * |v|) := by
      dsimp only [C]
      ring

/-- Heath--Brown's equation (41), simultaneously on the two shifted lines.
The result is in product form so no information at `v = 0` is lost. -/
theorem exists_heathBrown_Gamma_shift_kernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ v : ℝ),
      0 < δ → δ ≤ 1 / 4 →
      (δ + |v|) * ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ ≤
          C * Real.exp (-|v|) ∧
      (δ + |v|) * ‖Complex.Gamma ((-δ : ℝ) + (v : ℂ) * I)‖ ≤
          C * Real.exp (-|v|) := by
  obtain ⟨B, hB, hStrip⟩ := exists_norm_Gamma_heathBrown_positive_strip_le
  let C : ℝ := 2 * B
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro δ v hδ hδUpper
  have hδNonneg : 0 ≤ δ := hδ.le
  have hwPlus : (δ : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hwMinus : ((-δ : ℝ) : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hPlusRec := Complex.Gamma_add_one
    ((δ : ℂ) + (v : ℂ) * I) hwPlus
  have hMinusRec := Complex.Gamma_add_one
    (((-δ : ℝ) : ℂ) + (v : ℂ) * I) hwMinus
  have hPlusArg :
      (δ : ℂ) + (v : ℂ) * I + 1 =
        ((1 + δ : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp
    ring
  have hMinusArg :
      ((-δ : ℝ) : ℂ) + (v : ℂ) * I + 1 =
        ((1 - δ : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp
    ring
  have hPlusStrip :
      ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        B * Real.exp (-|v|) :=
    hStrip (1 + δ) v (by linarith) (by linarith)
  have hMinusStrip :
      ‖Complex.Gamma (((1 - δ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        B * Real.exp (-|v|) :=
    hStrip (1 - δ) v (by linarith) (by linarith)
  have hCoordPlus :=
    add_abs_le_two_mul_norm_ofReal_add_mul_I δ v hδNonneg
  have hCoordMinus :
      δ + |v| ≤ 2 * ‖((-δ : ℝ) : ℂ) + (v : ℂ) * I‖ := by
    have hre : δ ≤ ‖((-δ : ℝ) : ℂ) + (v : ℂ) * I‖ := by
      have h := Complex.abs_re_le_norm
        (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
      simpa [abs_of_pos hδ] using h
    have him : |v| ≤ ‖((-δ : ℝ) : ℂ) + (v : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm
        (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
    linarith
  constructor
  · calc
      (δ + |v|) * ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ ≤
          (2 * ‖(δ : ℂ) + (v : ℂ) * I‖) *
            ‖Complex.Gamma ((δ : ℂ) + (v : ℂ) * I)‖ := by gcongr
      _ = 2 * ‖Complex.Gamma (((1 + δ : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
        rw [← hPlusArg, hPlusRec, norm_mul]
        ring
      _ ≤ 2 * (B * Real.exp (-|v|)) := by gcongr
      _ = C * Real.exp (-|v|) := by dsimp only [C]; ring
  · calc
      (δ + |v|) * ‖Complex.Gamma ((-δ : ℝ) + (v : ℂ) * I)‖ ≤
          (2 * ‖((-δ : ℝ) : ℂ) + (v : ℂ) * I‖) *
            ‖Complex.Gamma ((-δ : ℝ) + (v : ℂ) * I)‖ := by gcongr
      _ = 2 * ‖Complex.Gamma (((1 - δ : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
        rw [← hMinusArg, hMinusRec, norm_mul]
        ring
      _ ≤ 2 * (B * Real.exp (-|v|)) := by gcongr
      _ = C * Real.exp (-|v|) := by dsimp only [C]; ring

/-- Equation (41) with the harmless exponential reserve retained. -/
theorem exists_heathBrown_Gamma_shift_kernel_strong_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      (delta + |v|) *
          ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ ≤
            C * Real.exp (-(4 / 3 : ℝ) * |v|) ∧
      (delta + |v|) *
          ‖Complex.Gamma ((-delta : ℝ) + (v : ℂ) * I)‖ ≤
            C * Real.exp (-(4 / 3 : ℝ) * |v|) := by
  obtain ⟨B, hB, hStrip⟩ :=
    exists_norm_Gamma_heathBrown_positive_strip_strong_le
  let C : ℝ := 2 * B
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro delta v hdelta hdeltaUpper
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hwPlus : (delta : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hwMinus : ((-delta : ℝ) : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hPlusRec := Complex.Gamma_add_one
    ((delta : ℂ) + (v : ℂ) * I) hwPlus
  have hMinusRec := Complex.Gamma_add_one
    (((-delta : ℝ) : ℂ) + (v : ℂ) * I) hwMinus
  have hPlusArg :
      (delta : ℂ) + (v : ℂ) * I + 1 =
        ((1 + delta : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp
    ring
  have hMinusArg :
      ((-delta : ℝ) : ℂ) + (v : ℂ) * I + 1 =
        ((1 - delta : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp
    ring
  have hPlusStrip := hStrip (1 + delta) v (by linarith) (by linarith)
  have hMinusStrip := hStrip (1 - delta) v (by linarith) (by linarith)
  have hCoordPlus :=
    add_abs_le_two_mul_norm_ofReal_add_mul_I delta v hdeltaNonneg
  have hCoordMinus :
      delta + |v| ≤ 2 * ‖((-delta : ℝ) : ℂ) + (v : ℂ) * I‖ := by
    have hre : delta ≤ ‖((-delta : ℝ) : ℂ) + (v : ℂ) * I‖ := by
      have h := Complex.abs_re_le_norm
        (((-delta : ℝ) : ℂ) + (v : ℂ) * I)
      simpa [abs_of_pos hdelta] using h
    have him : |v| ≤ ‖((-delta : ℝ) : ℂ) + (v : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm
        (((-delta : ℝ) : ℂ) + (v : ℂ) * I)
    linarith
  constructor
  · calc
      (delta + |v|) * ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ ≤
          (2 * ‖(delta : ℂ) + (v : ℂ) * I‖) *
            ‖Complex.Gamma ((delta : ℂ) + (v : ℂ) * I)‖ := by gcongr
      _ = 2 * ‖Complex.Gamma (((1 + delta : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
        rw [← hPlusArg, hPlusRec, norm_mul]
        ring
      _ ≤ 2 * (B * Real.exp (-(4 / 3 : ℝ) * |v|)) := by gcongr
      _ = C * Real.exp (-(4 / 3 : ℝ) * |v|) := by dsimp only [C]; ring
  · calc
      (delta + |v|) *
          ‖Complex.Gamma ((-delta : ℝ) + (v : ℂ) * I)‖ ≤
          (2 * ‖((-delta : ℝ) : ℂ) + (v : ℂ) * I‖) *
            ‖Complex.Gamma ((-delta : ℝ) + (v : ℂ) * I)‖ := by gcongr
      _ = 2 * ‖Complex.Gamma (((1 - delta : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
        rw [← hMinusArg, hMinusRec, norm_mul]
        ring
      _ ≤ 2 * (B * Real.exp (-(4 / 3 : ℝ) * |v|)) := by gcongr
      _ = C * Real.exp (-(4 / 3 : ℝ) * |v|) := by dsimp only [C]; ring

end

end TaoTrudgianYang2025
