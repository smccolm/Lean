import TaoTrudgianYang2025.ZetaMellinDerivative

/-!
# Mellin derivative bounds away from the real axis

The logarithmic reflection completion uses real line -1. Its derivative
factors are controlled by their imaginary parts; no positive-real-part
assumption or division by a vanishing real-axis factor is made.
-/

noncomputable section
open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem mellin_iteratedDeriv_norm_off_real {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {s : ℂ} (hs : s.im ≠ 0) (j : ℕ) :
    ‖mellin (iteratedDeriv j g) (s+j)‖ =
      (∏ m ∈ Finset.range j, ‖s+(m : ℂ)‖)*‖mellin g s‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hne : s+(j : ℂ) ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp only [add_im,natCast_im,add_zero,zero_im] at him
        exact hs him
      have harg : s+((j+1 : ℕ) : ℂ) = (s+(j : ℂ))+1 := by push_cast; ring
      rw [harg,iteratedDeriv_succ,mellin_derivative_recurrence
        (mellinIteratedDerivativeTest hg j) hne,norm_mul,norm_neg,ih,
        Finset.prod_range_succ]
      ring

theorem mellin_imaginary_weighted_norm_le_derivative {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (σ : ℝ) {u : ℝ} (hu : u ≠ 0) (j : ℕ) :
    |u|^j*‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖ ≤
      ‖mellin (iteratedDeriv j g) (((σ : ℂ)+(u : ℂ)*I)+(j : ℂ))‖ := by
  have hprod := Finset.prod_le_prod
    (s := Finset.range j) (f := fun _ => |u|)
    (g := fun m : ℕ => ‖((σ : ℂ)+(u : ℂ)*I)+(m : ℂ)‖)
    (fun _ _ => abs_nonneg u) (fun m _ => by
      simpa using Complex.abs_im_le_norm (((σ : ℂ)+(u : ℂ)*I)+(m : ℂ)))
  simp only [Finset.prod_const,Finset.card_range] at hprod
  rw [mellin_iteratedDeriv_norm_off_real hg (by simpa using hu)]
  exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

theorem norm_mellin_le_lower_mass {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {s : ℂ} (hs : s.re ≤ 1) :
    ‖mellin g s‖ ≤ hg.lower^(s.re-1)*∫ x : ℝ, ‖g x‖ := by
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hg.hasCompactSupport
  have hmi := (mellinConvergent_complex_of_test hg s).norm
  have hdom := hgi.norm.const_mul (hg.lower^(s.re-1))
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, ‖(x : ℂ)^(s-1)*g x‖ := by
      simpa only [mellin,smul_eq_mul] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun x : ℝ => (x : ℂ)^(s-1)*g x)
    _ ≤ ∫ x : ℝ in Ioi 0, hg.lower^(s.re-1)*‖g x‖ := by
      apply integral_mono_ae
        (by simpa only [MellinConvergent,smul_eq_mul] using hmi) hdom.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      by_cases hgx : g x = 0
      · simp [hgx]
      · rw [norm_mul,norm_cpow_eq_rpow_re_of_pos hx,sub_re,one_re]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hg.lower_pos (hg.support_subset hgx).1 (by linarith))
          (norm_nonneg _)
    _ ≤ ∫ x : ℝ, hg.lower^(s.re-1)*‖g x‖ :=
      setIntegral_le_integral hdom (Eventually.of_forall fun x =>
        mul_nonneg (Real.rpow_nonneg hg.lower_pos.le _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

theorem one_add_abs_le_two_negative_mellin_factor (u : ℝ) :
    1+|u| ≤ 2*‖(-1 : ℂ)+(u : ℂ)*I‖ := by
  have hre := Complex.abs_re_le_norm ((-1 : ℂ)+(u : ℂ)*I)
  have him := Complex.abs_im_le_norm ((-1 : ℂ)+(u : ℂ)*I)
  norm_num only [add_re,neg_re,one_re,ofReal_re,mul_re,ofReal_im,I_re,
    mul_zero,I_im,sub_zero,add_zero,abs_neg,abs_one,add_im,neg_im,one_im,
    neg_zero,mul_im,mul_one,zero_add] at hre him
  linarith

theorem mellin_negative_one_weighted_norm_le_derivative {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (u : ℝ) :
    (1+|u|)*‖mellin g ((-1 : ℂ)+(u : ℂ)*I)‖ ≤
      2*‖mellin (deriv g) ((u : ℂ)*I)‖ := by
  have hne : (-1 : ℂ)+(u : ℂ)*I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hrec := congrArg norm (mellin_derivative_recurrence hg hne)
  have harg : ((-1 : ℂ)+(u : ℂ)*I)+1 = (u : ℂ)*I := by ring
  rw [harg,norm_mul,norm_neg] at hrec
  rw [hrec]
  nlinarith [one_add_abs_le_two_negative_mellin_factor u,
    norm_nonneg (mellin g ((-1 : ℂ)+(u : ℂ)*I))]

end TaoTrudgianYang2025
