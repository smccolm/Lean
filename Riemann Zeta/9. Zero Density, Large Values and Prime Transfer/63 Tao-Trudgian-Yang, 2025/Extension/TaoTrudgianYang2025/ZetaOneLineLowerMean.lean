import TaoTrudgianYang2025.ZetaOneLineMean

/-!
# A linear lower bound for the first absolute moment on Re s = 1

The fixed cutoff ceil(H^2) makes the integrated Abel tail bounded.
The remaining harmonic error is logarithmic and hence smaller than H/2.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem norm_integral_zetaOneLine_sub_length_le_log {H : ℝ} (hH : 1 ≤ H) :
    ‖(∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))-(H : ℂ)‖ ≤
      4+(2/Real.log 2)*(1+Real.log 2+2*Real.log H) := by
  let b : ℕ := ⌈H^2⌉₊
  have hHpos : 0 < H := by linarith
  have hceil : H^2 ≤ (b : ℝ) := Nat.le_ceil _
  have hbReal : (1 : ℝ) ≤ b := by nlinarith
  have hb : 1 ≤ b := by exact_mod_cast hbReal
  have hbp : (0 : ℝ) < b := by linarith
  have hbUpper : (b : ℝ) ≤ 2*H^2 := by
    have hh : (b : ℝ) < H^2+1 := Nat.ceil_lt_add_one (sq_nonneg H)
    nlinarith
  have herror : (1/H+(1+2*H)/(b : ℝ))*H ≤ 4 := by
    field_simp
    nlinarith
  have hlog : Real.log (b : ℝ) ≤ Real.log 2+2*Real.log H := by
    have hh := Real.log_le_log hbp hbUpper
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hHpos.ne'),
      Real.log_pow] at hh
    exact hh
  have hh := norm_integral_zetaOneLine_sub_length hb hH
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 2/Real.log 2)
  nlinarith

theorem eventually_integral_zetaOneLine_norm_ge :
    ∀ᶠ H : ℝ in atTop,
      H/2 ≤ ∫ t in H..2*H, zetaMomentLineNorm 1 t := by
  let a : ℝ := 4+(2/Real.log 2)*(1+Real.log 2)
  let B : ℝ := 4/Real.log 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left B).bound
    (by norm_num : (0 : ℝ) < 1/4)
  filter_upwards [hsmall,eventually_ge_atTop (1 : ℝ),eventually_ge_atTop (4*a)] with
    H hsmall hH ha
  have hHp : 0 < H := by linarith
  simp only [Real.rpow_one,Real.norm_eq_abs] at hsmall
  rw [abs_of_nonneg (mul_nonneg hB (Real.log_nonneg hH)),abs_of_pos hHp] at hsmall
  have herror := norm_integral_zetaOneLine_sub_length_le_log hH
  have hsmallError : ‖(∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))-(H : ℂ)‖ ≤ H/2 := by
    have heq : 4+(2/Real.log 2)*(1+Real.log 2+2*Real.log H) = a+B*Real.log H := by
      dsimp [a,B]
      ring
    rw [heq] at herror
    linarith
  have htri : H ≤ ‖∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I)‖+
      ‖(∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))-(H : ℂ)‖ := by
    have hh := norm_sub_le
      (∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))
      ((∫ t in H..2*H, riemannZeta (1+(t : ℂ)*I))-(H : ℂ))
    simpa only [sub_sub_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hHp] using hh
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun t : ℝ => riemannZeta (1+(t : ℂ)*I)) (by linarith : H ≤ 2*H)
  change H/2 ≤ ∫ t in H..2*H, ‖riemannZeta (((1 : ℝ) : ℂ)+(t : ℂ)*I)‖
  norm_num only [Complex.ofReal_one]
  linarith

end TaoTrudgianYang2025
