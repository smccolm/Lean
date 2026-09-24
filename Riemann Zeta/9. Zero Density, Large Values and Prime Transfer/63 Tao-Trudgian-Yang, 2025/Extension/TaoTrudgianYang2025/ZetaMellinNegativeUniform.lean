import TaoTrudgianYang2025.ZetaMellinNegative

/-!
# Uniform kernels for reciprocal-weighted interval completion

The first derivative gives decay everywhere on real line -1, including
zero imaginary part. Higher derivatives are used only away from zero.
All constants are masses of the fixed smooth transition.
-/

noncomputable section
open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem cutoff_negative_mellin_weighted_bound {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (u : ℝ) :
    (1+|u|)*‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
        ((-1 : ℂ)+(u : ℂ)*I)‖ ≤
      2*zetaCutoffDerivativeMass 1/((a : ℝ)-1/2) := by
  let hg := zetaIntervalCutoffTest a b ha
  let hd := mellinIteratedDerivativeTest hg 1
  have hmass := integral_norm_complex_cutoff_deriv_le hab (by norm_num : 0 < (1 : ℕ))
  have hnorm := norm_mellin_le_lower_mass hd
    (s := (u : ℂ)*I) (by simp)
  norm_num only [mul_re,ofReal_re,I_re,mul_zero,ofReal_im,I_im,zero_mul,
    sub_self,zero_sub,Real.rpow_neg_one,iteratedDeriv_one] at hnorm hmass
  have hweighted := mellin_negative_one_weighted_norm_le_derivative hg u
  have hlower : hd.lower = (a : ℝ)-1/2 := rfl
  rw [hlower] at hnorm
  calc
    _ ≤ 2*‖mellin (deriv (fun x => (zetaIntervalCutoff a b x : ℂ))) ((u : ℂ)*I)‖ :=
      hweighted
    _ ≤ 2*(((a : ℝ)-1/2)⁻¹*zetaCutoffDerivativeMass 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hnorm.trans (mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hg.lower_pos.le))
    _ = _ := by ring

theorem cutoff_negative_mellin_bound {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
        ((-1 : ℂ)+(u : ℂ)*I)‖ ≤
      (2*zetaCutoffDerivativeMass 1/((a : ℝ)-1/2))/(1+|u|) := by
  apply (le_div_iff₀ (by positivity : 0 < 1+|u|)).2
  simpa only [mul_comm] using cutoff_negative_mellin_weighted_bound ha hab u

theorem cutoff_negative_mellin_high_order {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {u : ℝ} (hu : u ≠ 0) (j : ℕ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
        ((-1 : ℂ)+(u : ℂ)*I)‖ ≤
      ((b : ℝ)+1/2)^j*zetaCutoffDerivativeMass (j+2)/|u|^(j+2) := by
  let hg := zetaIntervalCutoffTest a b ha
  let hd := mellinIteratedDerivativeTest hg (j+2)
  have hmass := integral_norm_complex_cutoff_deriv_le hab (by omega : 0 < j+2)
  have hw := mellin_imaginary_weighted_norm_le_derivative hg (-1) hu (j+2)
  have hn := norm_mellin_le_upper_mass hd
    (s := ((-1 : ℂ)+(u : ℂ)*I)+(j+2 : ℕ))
    (by simp; linarith [Nat.cast_nonneg (α := ℝ) j])
  have hreal : (((-1 : ℂ)+(u : ℂ)*I)+(j+2 : ℕ)).re-1 = (j : ℝ) := by
    push_cast
    simp
    ring
  have hupper : hd.upper = (b : ℝ)+1/2 := by
    change max (a : ℝ) b + 1/2 = _
    rw [max_eq_right (by exact_mod_cast hab)]
  rw [hreal,Real.rpow_natCast,hupper] at hn
  apply (le_div_iff₀ (pow_pos (abs_pos.mpr hu) _)).2
  calc
    _ = |u|^(j+2)*‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
        ((-1 : ℂ)+(u : ℂ)*I)‖ := by ring
    _ ≤ _ := by simpa only [ofReal_neg,ofReal_one] using hw
    _ ≤ _ := hn.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

end TaoTrudgianYang2025
