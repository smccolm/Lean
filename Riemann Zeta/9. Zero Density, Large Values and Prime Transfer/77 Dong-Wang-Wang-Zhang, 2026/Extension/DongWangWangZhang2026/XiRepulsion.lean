import DongWangWangZhang2026.XiLogDerivative
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# A quantitative quotient bound for the actual xi product

The genus-one factors are compared before taking their convergent product.
The polynomial contribution combines with the actual logarithmic derivative;
no value for a Hadamard coefficient is assumed.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Complex.Hadamard Set Filter
open scoped Topology

/-- The quadratic exponential majorant retains the real linear term. -/
theorem norm_one_add_le_exp_re_quadratic (z : ℂ) :
    ‖1 + z‖ ≤ Real.exp (z.re + ‖z‖ ^ 2 / 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  have hs : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, add_im, one_re, one_im]
    ring
  rw [hs]
  calc
    1 + 2 * z.re + ‖z‖ ^ 2 ≤ Real.exp (2 * z.re + ‖z‖ ^ 2) := by
      linarith [Real.add_one_le_exp (2 * z.re + ‖z‖ ^ 2)]
    _ = Real.exp (z.re + ‖z‖ ^ 2 / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring

/-- A single genus-one factor obeys the exact quadratic resolvent bound. -/
theorem norm_weierstrass_one_sub_real_le {s ρ : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ)
    (r : ℝ) :
    ‖weierstrassFactor 1 ((s - (r : ℂ)) / ρ)‖ ≤
      ‖weierstrassFactor 1 (s / ρ)‖ *
        Real.exp (-r * (1 / (s - ρ) + 1 / ρ).re +
          r ^ 2 / (2 * ‖s - ρ‖ ^ 2)) := by
  have hw : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hlin : 1 - (s - (r : ℂ)) / ρ =
      (1 - s / ρ) * (1 - (r : ℂ) / (s - ρ)) := by
    field_simp [hρ, hw]
    ring
  have he : weierstrassFactor 1 ((s - (r : ℂ)) / ρ) =
      weierstrassFactor 1 (s / ρ) *
        (1 - (r : ℂ) / (s - ρ)) * Complex.exp (-(r : ℂ) / ρ) := by
    have hE (z : ℂ) : weierstrassFactor 1 z = (1 - z) * Complex.exp z := by
      simp [weierstrassFactor_def, partialLogSum_eq_sum]
    rw [hE, hE, hlin, sub_div, Complex.exp_sub, neg_div, Complex.exp_neg]
    ring
  have hb := norm_one_add_le_exp_re_quadratic (-(r : ℂ) / (s - ρ))
  have hre : (-(r : ℂ) / (s - ρ)).re = -r * (1 / (s - ρ)).re := by
    rw [div_eq_mul_inv, mul_re]
    simp [one_div]
  have hrρ : (-(r : ℂ) / ρ).re = -r * (1 / ρ).re := by
    rw [div_eq_mul_inv, mul_re]
    simp [one_div]
  have hn : ‖-(r : ℂ) / (s - ρ)‖ ^ 2 = r ^ 2 / ‖s - ρ‖ ^ 2 := by
    simp [norm_neg, norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  simp only [neg_div, ← sub_eq_add_neg] at hb
  rw [he, norm_mul, norm_mul, norm_exp, hrρ]
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (Real.exp_pos _).le).trans_eq
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  rw [neg_div] at hre hn
  rw [hre, hn, add_re]
  ring

/-- The convergent actual canonical product inherits the quadratic factor bound. -/
theorem norm_xi_canonicalProduct_sub_real_le {s : ℂ} (hs : 1 < s.re) (r : ℝ) :
    ‖divisorCanonicalProduct 1 riemannXi univ (s - (r : ℂ))‖ ≤
      ‖divisorCanonicalProduct 1 riemannXi univ s‖ *
        Real.exp (-r * (∑' p : XiZero, (1 / (s - xiZeroPoint p) +
          1 / xiZeroPoint p).re) +
          (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2) := by
  have havoid : ∀ p : XiZero, s ≠ xiZeroPoint p := by
    intro p he
    have hr := congrArg Complex.re he
    linarith [(xiZeroPoint_re p).2]
  have hreal := (Complex.hasSum_re
    (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ havoid).hasSum).summable
  have hkernel := summable_xiZero_inverse_square hs
  let H : XiZero → ℝ := fun p =>
    -r * (1 / (s - xiZeroPoint p) + 1 / xiZeroPoint p).re +
      (r ^ 2 / 2) * (1 / ‖s - xiZeroPoint p‖ ^ 2)
  have hH : Summable H := (hreal.mul_left (-r)).add (hkernel.mul_left (r ^ 2 / 2))
  have hprod := hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    1 riemannXi summable_xiZero_norm_inv_sq
  have h0 := (hprod.hasProd (mem_univ s)).norm
  have h1 := (hprod.hasProd (mem_univ (s - (r : ℂ)))).norm
  have hlim := le_of_tendsto_of_tendsto h1
    (h0.mul hH.hasSum.rexp) (Eventually.of_forall (fun F : Finset XiZero => by
      change (∏ p ∈ F, ‖weierstrassFactor 1 ((s - (r : ℂ)) / xiZeroPoint p)‖) ≤
        ∏ p ∈ F, (‖weierstrassFactor 1 (s / xiZeroPoint p)‖ * Real.exp (H p))
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p _
      convert norm_weierstrass_one_sub_real_le
        (divisorZeroIndex₀_val_ne_zero p) (havoid p) r using 1
      dsimp only [H]
      congr 2
      ring))
  convert hlim using 1
  congr 2
  exact (((hreal.mul_left (-r)).tsum_add (hkernel.mul_left (r ^ 2 / 2))).trans
    (by rw [tsum_mul_left, tsum_mul_left])).symm

/-- The actual xi function satisfies the quadratic zero-kernel quotient estimate. -/
theorem norm_xi_sub_real_le {s : ℂ} (hs : 1 < s.re) (r : ℝ) :
    ‖riemannXi (s - (r : ℂ))‖ ≤ ‖riemannXi s‖ *
      Real.exp (-r * (logDeriv riemannXi s).re +
        (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2) := by
  obtain ⟨P, hP, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have havoid : ∀ p : XiZero, s ≠ xiZeroPoint p := by
    intro p he
    have hr := congrArg Complex.re he
    linarith [(xiZeroPoint_re p).2]
  have hder : P.derivative.eval s = P.coeff 1 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hP]
    simp
  have hlog := congrArg Complex.re
    (logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac havoid)
  rw [hder, add_re,
    Complex.re_tsum (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ havoid)] at hlog
  have heval (z : ℂ) : P.eval z = P.coeff 1 * z + P.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hP]
    simp
  have hdiff : (P.eval (s - (r : ℂ))).re =
      (P.eval s).re - r * (P.coeff 1).re := by
    rw [heval, heval]
    simp only [add_re, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    ring
  have hb := norm_xi_canonicalProduct_sub_real_le hs r
  rw [hfac, hfac, norm_mul, norm_mul, norm_exp, norm_exp]
  apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq
  calc
    Real.exp (P.eval (s - (r : ℂ))).re *
        (‖divisorCanonicalProduct 1 riemannXi univ s‖ *
          Real.exp (-r * (∑' p : XiZero, (1 / (s - xiZeroPoint p) +
            1 / xiZeroPoint p).re) +
            (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2)) =
      ‖divisorCanonicalProduct 1 riemannXi univ s‖ *
        Real.exp ((P.eval (s - (r : ℂ))).re -
          r * (∑' p : XiZero, (1 / (s - xiZeroPoint p) + 1 / xiZeroPoint p).re) +
          (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2) := by
            rw [show (P.eval (s - (r : ℂ))).re -
              r * (∑' p : XiZero, (1 / (s - xiZeroPoint p) + 1 / xiZeroPoint p).re) +
              (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2 =
                (P.eval (s - (r : ℂ))).re +
                  (-r * (∑' p : XiZero, (1 / (s - xiZeroPoint p) +
                    1 / xiZeroPoint p).re) +
                    (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2) by ring,
              Real.exp_add]
            simp only [Real.exp_add]
            ring
    _ = ‖divisorCanonicalProduct 1 riemannXi univ s‖ *
        Real.exp ((P.eval s).re + (-r * (logDeriv riemannXi s).re +
          (r ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2)) := by
            congr 2
            rw [hdiff, hlog]
            ring
    _ = _ := by simp only [Real.exp_add]; ring

end
end DongWangWangZhang2026
