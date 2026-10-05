import DongWangWangZhang2026.WeightedZeroForcing
import DongWangWangZhang2026.ZeroSumUpperBound
import DongWangWangZhang2026.ZeroCounts

/-!
# Near/far geometry for actual zero counts

The closed complement of the source open disk is compared to the
positive real resolvent at the farther horizontal shift.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set
open scoped Classical

/-- Moving right from Re(s)=1 increases the distance to each actual nontrivial zero. -/
theorem norm_zero_distance_shift_mono {a : ℝ} (ha : 0 ≤ a) (φ : ℝ) (p : XiZero) :
    ‖(1 + (φ : ℂ) * I) - xiZeroPoint p‖ ≤
      ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, add_re, add_im,
    one_re, one_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add]
  have hr := (xiZeroPoint_re p).2.le
  nlinarith

/-- The source far-zero geometry has the exact nine-twentieth separation loss. -/
theorem source_far_zero_separation {a l η φ : ℝ} (hl : 0 ≤ l) (hla : l ≤ a)
    (hη : |η| ≤ a / 10) (p : XiZero)
    (hfar : 2 * a ≤ ‖(1 + (φ : ℂ) * I) - xiZeroPoint p‖) :
    (9 / 20 : ℝ) * ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ ≤
      ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ := by
  have ha : 0 ≤ a := hl.trans hla
  have hA := hfar.trans (norm_zero_distance_shift_mono ha φ p)
  have htri :
      ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ ≤
        ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ +
          (a - l + |η|) := by
    calc
      _ = ‖((((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p) +
          (((a - l : ℝ) : ℂ) + ((-η : ℝ) : ℂ) * I)‖ := by
        congr 1
        push_cast
        ring
      _ ≤ ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ +
          ‖((a - l : ℝ) : ℂ) + ((-η : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (by
        have h := norm_le_abs_re_add_abs_im (((a - l : ℝ) : ℂ) + ((-η : ℝ) : ℂ) * I)
        simpa [abs_of_nonneg (sub_nonneg.mpr hla)] using h)
  linarith

/-- Each far inverse-square kernel is bounded by five times the farther kernel. -/
theorem source_far_inverse_square_le {a l η φ : ℝ} (hl : 0 < l) (hla : l ≤ a)
    (hη : |η| ≤ a / 10) (p : XiZero)
    (hfar : 2 * a ≤ ‖(1 + (φ : ℂ) * I) - xiZeroPoint p‖) :
    l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 ≤
      5 * l / ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
  have ha : 0 < a := hl.trans_le hla
  have hA : 0 < ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ :=
    (by positivity : 0 < 2 * a).trans_le
      (hfar.trans (norm_zero_distance_shift_mono ha.le φ p))
  have hsep := source_far_zero_separation hl.le hla hη p hfar
  have hB : 0 < ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ :=
    (mul_pos (by norm_num) hA).trans_le hsep
  have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hsep
  have hnorm : ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ ^ 2 ≤
      5 * ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖]
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hA)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hnorm hl.le]

/-- The farther inverse-square kernel is controlled by its actual positive real resolvent. -/
theorem source_inverse_square_le_real_resolvent (a : ℝ)
    (φ : ℝ) (p : XiZero) :
    a / ‖(((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p‖ ^ 2 ≤
      (1 / ((((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p)).re := by
  rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hr := (xiZeroPoint_re p).2.le
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    zero_mul, sub_zero, add_zero]
  linarith

/-- Each actual zero contributes at most the reciprocal small horizontal shift. -/
theorem source_zero_kernel_le_reciprocal {l : ℝ} (hl : 0 < l) (v : ℝ) (p : XiZero) :
    l / ‖(((1 + l : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p‖ ^ 2 ≤ 1 / l := by
  have hre : l ≤ ‖(((1 + l : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p‖ := by
    have h := re_le_norm ((((1 + l : ℝ) : ℂ) + (v : ℂ) * I) - xiZeroPoint p)
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      zero_mul, sub_zero, add_zero] at h
    linarith [(xiZeroPoint_re p).2.le]
  have hn := hl.trans_le hre
  have hsq := (sq_le_sq₀ hl.le (norm_nonneg _)).mpr hre
  apply (div_le_div_iff₀ (sq_pos_of_pos hn) hl).mpr
  nlinarith only [hsq]


/-- Far zeros are dominated pointwise by the actual real resolvent at the farther shift. -/
theorem source_far_kernel_le_real_resolvent {a l η φ : ℝ} (hl : 0 < l) (hla : l ≤ a)
    (hη : |η| ≤ a / 10) (p : XiZero)
    (hfar : 2 * a ≤ ‖(1 + (φ : ℂ) * I) - xiZeroPoint p‖) :
    l / ‖(((1 + l : ℝ) : ℂ) + ((φ + η : ℝ) : ℂ) * I) - xiZeroPoint p‖ ^ 2 ≤
      (5 * l / a) * (1 / ((((1 + a : ℝ) : ℂ) + (φ : ℂ) * I) - xiZeroPoint p)).re := by
  have ha : 0 < a := hl.trans_le hla
  apply (source_far_inverse_square_le hl hla hη p hfar).trans
  have h := mul_le_mul_of_nonneg_left (source_inverse_square_le_real_resolvent a φ p)
    (by positivity : 0 ≤ 5 * l / a)
  convert h using 1
  field_simp

/-- The source shift bound is small enough for the exact near/far geometry. -/
theorem source_eta_le_outer_tenth {l Y Q η : ℝ} (hl : 0 < l) (hY : 0 < Y)
    (hYQ : Y ≤ Q / 2) (hη : |η| ≤ 2 * l * Real.sqrt (Q / Y)) :
    l ≤ 20 * l * Q / Y ∧ |η| ≤ (20 * l * Q / Y) / 10 := by
  have hratio : 1 ≤ Q / Y := (le_div_iff₀ hY).mpr (by linarith)
  have hroot : Real.sqrt (Q / Y) ≤ Q / Y :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have he : 20 * l * Q / Y = 20 * l * (Q / Y) := by ring
  rw [he]
  constructor
  · nlinarith
  · have h := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2 * l)
    nlinarith

end
end DongWangWangZhang2026
