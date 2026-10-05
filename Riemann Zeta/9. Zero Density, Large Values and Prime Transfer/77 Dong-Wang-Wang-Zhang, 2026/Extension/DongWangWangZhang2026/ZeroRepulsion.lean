import DongWangWangZhang2026.XiRepulsion
import DongWangWangZhang2026.GammaRatioBounds
import DongWangWangZhang2026.ZetaLogDerivativeBounds
import DongWangWangZhang2026.ZetaUniformBounds
import DongWangWangZhang2026.MeanValueAssembly

/-!
# Zeta growth controlled by the actual zero kernel

The actual xi quotient is combined with gamma and rational factors.
The logarithmic gamma growth cancels against the real xi logarithmic
derivative, leaving an absolute prefactor and the exact source kernel.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set

/-- The real xi logarithmic derivative has the exact source lower logarithm. -/
theorem exists_re_xi_logDeriv_source_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ u : ℝ,
      (1 / 2) * Real.log (2 + |u|) - 1 / a - C ≤
        (logDeriv riemannXi (((1 + a : ℝ) : ℂ) + (u : ℂ) * I)).re := by
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_norm_logDeriv_zeta_le_pole
  refine ⟨Cζ + (14 + |Real.eulerMascheroniConstant| + Real.log 2) / 2 +
    |Real.log Real.pi| / 2, by positivity, ?_⟩
  intro a ha u
  let s : ℂ := ((1 + a : ℝ) : ℂ) + (u : ℂ) * I
  have hre : s.re = 1 + a := by simp [s]
  have hs : 1 < s.re := by rw [hre]; linarith
  have hrat₀ : 0 ≤ (1 / s).re := by
    rw [one_div, inv_re]
    exact div_nonneg (by linarith) (normSq_nonneg _)
  have hrat₁ : 0 ≤ (1 / (s - 1)).re := by
    rw [one_div, inv_re]
    exact div_nonneg (by simp only [sub_re, one_re]; linarith) (normSq_nonneg _)
  have hzn := hζ s hs
  rw [hre, add_sub_cancel_left] at hzn
  have hzl := (abs_le.mp (abs_re_le_norm (logDeriv riemannZeta s))).1
  have hgamma := re_digamma_source_lower ha u
  have hπ : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    simp [Complex.log_re]
  change _ ≤ (logDeriv riemannXi s).re
  rw [xi_logDeriv_eq_zeta_gamma hs]
  simp only [add_re, sub_re, div_ofNat_re, hπ]
  change Real.log (2 + |u|) - (14 + |Real.eulerMascheroniConstant| + Real.log 2) ≤
    (logDeriv Gamma (s / 2)).re at hgamma
  linarith [le_abs_self (Real.log Real.pi)]

/-- The source rational xi factors have a uniform quotient at both height signs. -/
theorem norm_source_rational_factor_le {a u : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * I) *
      ((((1 + a : ℝ) : ℂ) + (u : ℂ) * I) - 1)‖ ≤
      2 * ‖(((1 - a : ℝ) : ℂ) + (u : ℂ) * I) *
        ((((1 - a : ℝ) : ℂ) + (u : ℂ) * I) - 1)‖ := by
  let s₀ : ℂ := ((1 + a : ℝ) : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := ((1 - a : ℝ) : ℂ) + (u : ℂ) * I
  have him : s₁.im = u := by simp [s₁]
  have hlarge : 2 ≤ ‖s₁‖ := by
    exact hu.trans (by simpa [him] using abs_im_le_norm s₁)
  have he : s₀ = s₁ + (2 * a : ℝ) := by dsimp only [s₀, s₁]; push_cast; ring
  have hn : ‖s₀‖ ≤ 2 * ‖s₁‖ := by
    have h := norm_add_le s₁ ((2 * a : ℝ) : ℂ)
    rw [← he, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * a)] at h
    linarith
  have hsame : ‖s₀ - 1‖ = ‖s₁ - 1‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [Complex.sq_norm, normSq_apply, s₀, s₁]
  change ‖s₀ * (s₀ - 1)‖ ≤ 2 * ‖s₁ * (s₁ - 1)‖
  rw [norm_mul, norm_mul, hsame]
  nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg (s₁ - 1))]

/-- Consume the actual xi quotient and every gamma/rational factor, with no product premise. -/
theorem norm_zeta_source_xi_bound {a u : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hu : 2 ≤ |u|) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      2 * ‖riemannZeta (((1 + a : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        Real.exp (a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|)) -
          2 * a * (logDeriv riemannXi (((1 + a : ℝ) : ℂ) + (u : ℂ) * I)).re +
          2 * a ^ 2 * ∑' p : XiZero,
            1 / ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * I) - xiZeroPoint p‖ ^ 2) := by
  let s₀ : ℂ := ((1 + a : ℝ) : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := ((1 - a : ℝ) : ℂ) + (u : ℂ) * I
  let F : ℂ → ℂ := fun s => s * (s - 1) * Gammaℝ s / 2
  have hr₀ : s₀.re = 1 + a := by simp [s₀]
  have hr₁ : s₁.re = 1 - a := by simp [s₁]
  have hs₀ : 1 < s₀.re := by rw [hr₀]; linarith
  have hs₁ : 0 < s₁.re := by rw [hr₁]; linarith
  have hn₀ : s₀ ≠ 1 := by intro h; simp [h] at hs₀
  have hn₁ : s₁ ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hr₁, one_re] at hr
    linarith
  have hnz₁ : s₁ ≠ 0 := by intro h; simp [h] at hs₁
  have hF : 0 < ‖F s₁‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (mul_ne_zero
      (mul_ne_zero hnz₁ (sub_ne_zero.mpr hn₁))
      (Gammaℝ_ne_zero_of_re_pos hs₁)) (by norm_num)
  let G : ℝ := a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|))
  let E : ℝ := -(2 * a) * (logDeriv riemannXi s₀).re +
    ((2 * a) ^ 2 / 2) * ∑' p : XiZero, 1 / ‖s₀ - xiZeroPoint p‖ ^ 2
  have hFbound : ‖F s₀‖ ≤ 2 * ‖F s₁‖ * Real.exp G := by
    have hr := norm_source_rational_factor_le ha ha2 hu
    have hg := norm_GammaReal_source_ratio_le ha ha2 hu
    change ‖s₀ * (s₀ - 1)‖ ≤ 2 * ‖s₁ * (s₁ - 1)‖ at hr
    change ‖Gammaℝ s₀‖ ≤ ‖Gammaℝ s₁‖ * Real.exp G at hg
    have hm := mul_le_mul hr hg (norm_nonneg _) (by positivity)
    dsimp only [F]
    simp only [norm_div, norm_mul, norm_ofNat] at hm ⊢
    nlinarith
  have hxi := norm_xi_sub_real_le hs₀ (2 * a)
  have he : s₀ - ((2 * a : ℝ) : ℂ) = s₁ := by
    dsimp only [s₀, s₁]
    push_cast
    ring
  rw [he, xi_eq_factor_mul_zeta hs₁ hn₁,
    xi_eq_factor_mul_zeta (lt_trans zero_lt_one hs₀) hn₀, norm_mul, norm_mul] at hxi
  change ‖F s₁‖ * ‖riemannZeta s₁‖ ≤ ‖F s₀‖ * ‖riemannZeta s₀‖ * Real.exp E at hxi
  have hfinal : ‖riemannZeta s₁‖ ≤ 2 * ‖riemannZeta s₀‖ * Real.exp (G + E) := by
    apply (mul_le_mul_iff_right₀ hF).mp
    calc
      ‖F s₁‖ * ‖riemannZeta s₁‖ ≤ ‖F s₀‖ * ‖riemannZeta s₀‖ * Real.exp E := hxi
      _ ≤ (2 * ‖F s₁‖ * Real.exp G) * ‖riemannZeta s₀‖ * Real.exp E := by
        gcongr
      _ = ‖F s₁‖ * (2 * ‖riemannZeta s₀‖ * Real.exp (G + E)) := by
        rw [Real.exp_add G E]
        ring
  convert hfinal using 1
  dsimp only [G, E]
  congr 2
  ring

/-- Source Lemma 3.2: every height, the exact quadratic kernel, and one absolute prefactor. -/
theorem exists_source_zero_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ 1 / 2 →
      Summable (fun p : XiZero =>
        2 * a ^ 2 / ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * I) - xiZeroPoint p‖ ^ 2) ∧
      ‖riemannZeta (((1 - a : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        (C / a) * Real.exp (∑' p : XiZero,
          2 * a ^ 2 / ‖(((1 + a : ℝ) : ℂ) + (u : ℂ) * I) - xiZeroPoint p‖ ^ 2) := by
  obtain ⟨C₀, hC₀, hlower⟩ := exists_re_xi_logDeriv_source_lower
  let D : ℝ := 2 + (14 + |Real.eulerMascheroniConstant|) / 2 + C₀
  refine ⟨max 32 (4 * Real.exp D), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro a u ha ha2
  let s : ℂ := ((1 + a : ℝ) : ℂ) + (u : ℂ) * I
  have hs : 1 < s.re := by simp [s]; linarith
  have hsum := (summable_xiZero_inverse_square hs).mul_left (2 * a ^ 2)
  simp only [mul_one_div] at hsum
  refine ⟨hsum, ?_⟩
  let K : ℝ := ∑' p : XiZero, 2 * a ^ 2 / ‖s - xiZeroPoint p‖ ^ 2
  have hK : K = 2 * a ^ 2 * ∑' p : XiZero, 1 / ‖s - xiZeroPoint p‖ ^ 2 := by
    rw [← tsum_mul_left]
    simp only [K, mul_one_div]
  have hKnonneg : 0 ≤ K := tsum_nonneg fun _ => by positivity
  have hExpK : 1 ≤ Real.exp K := Real.one_le_exp_iff.mpr hKnonneg
  change ‖riemannZeta (((1 - a : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
    (max 32 (4 * Real.exp D) / a) * Real.exp K
  by_cases hu : 2 ≤ |u|
  · have h := norm_zeta_source_xi_bound ha ha2 hu
    rw [← hK] at h
    have hlow := hlower a ha u
    have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * a)
    have hpole : 2 * a * (1 / a) = 2 := by field_simp
    have hγ : a * (14 + |Real.eulerMascheroniConstant|) ≤
        (14 + |Real.eulerMascheroniConstant|) / 2 := by
      nlinarith [abs_nonneg Real.eulerMascheroniConstant]
    have hc : 2 * a * C₀ ≤ C₀ := by nlinarith
    have he : a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|)) -
        2 * a * (logDeriv riemannXi s).re + K ≤ D + K := by
      dsimp only [D]
      change (1 / 2) * Real.log (2 + |u|) - 1 / a - C₀ ≤
        (logDeriv riemannXi s).re at hlow
      change 2 * a * ((1 / 2) * Real.log (2 + |u|) - 1 / a - C₀) ≤
        2 * a * (logDeriv riemannXi s).re at hmul
      nlinarith
    have hz := norm_shifted_zeta_le_reciprocal (1 + a) 0 u (by linarith)
    simp only [sub_zero, add_sub_cancel_left] at hz
    have hright : 2 * ‖riemannZeta s‖ ≤ 4 / a := by
      have hi : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by linarith)
      change ‖riemannZeta s‖ ≤ 1 + 1 / a at hz
      simp only [div_eq_mul_inv, one_mul] at hz hi ⊢
      linarith
    calc
      _ ≤ 2 * ‖riemannZeta s‖ *
          Real.exp (a * (Real.log (2 + |u|) + (14 + |Real.eulerMascheroniConstant|)) -
            2 * a * (logDeriv riemannXi s).re + K) := h
      _ ≤ (4 / a) * Real.exp (D + K) :=
        mul_le_mul hright (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
      _ = ((4 * Real.exp D) / a) * Real.exp K := by rw [Real.exp_add D K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (le_max_right _ _) ha.le) (Real.exp_pos _).le
  · have hp : (2 + |u|) ^ a ≤ 4 := by
      calc
        _ ≤ 2 + |u| := Real.rpow_le_self_of_one_le (by linarith [abs_nonneg u]) (by linarith)
        _ ≤ 4 := by linarith
    have hz := norm_zeta_left_strip_le a u ha ha2
    have hsmall : ‖riemannZeta (((1 - a : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ 32 / a :=
      hz.trans (div_le_div_of_nonneg_right (by linarith) ha.le)
    exact hsmall.trans ((div_le_div_of_nonneg_right (le_max_left _ _) ha.le).trans
      (le_mul_of_one_le_right (by positivity) hExpK))

end
end DongWangWangZhang2026
