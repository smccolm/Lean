import DongWangWangZhang2026.GaussianConcentration

/-!
# Large sums give a Gaussian lower bound

The comparison at the original maximizing twist supplies the central
value. Uniform error absorption then consumes the proved Gaussian
evaluation, with a single twist chosen before all Gaussian scales.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Filter MeasureTheory
open scoped Topology

/-- The inverse comparison factor cannot decrease the magnitude of the original sum. -/
theorem one_le_norm_inverse_comparisonFactor {x : ℝ} (hx : 0 < x) (a : ℝ) :
    1 ≤ ‖((a : ℂ) * I + 1) * (x : ℂ) ^ (-((a : ℂ) * I))‖ := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, neg_zero, Real.rpow_zero, mul_one]
  simpa using Complex.re_le_norm ((a : ℂ) * I + 1)

/-- Actual comparison and the large-sum equality give a normalized central-value lower bound. -/
theorem normalized_twisted_sum_lower {x N C t t₀ : ℝ} (hx : 0 < x) (hN : 0 < N)
    (hsum : ‖zetaSum x t‖ = x / N)
    (hcomp : ‖zetaSum x (t - t₀) -
      (((t₀ : ℂ) * I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * I))) * zetaSum x t‖ ≤
        C * x / (Real.log x) ^ (3 / 4 : ℝ)) :
    1 / N - C / (Real.log x) ^ (3 / 4 : ℝ) ≤
      ‖zetaSum x (t - t₀) / (x : ℂ)‖ := by
  let g := ((t₀ : ℂ) * I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * I))
  have hg : 1 ≤ ‖g‖ := one_le_norm_inverse_comparisonFactor hx t₀
  have hmain : x / N ≤ ‖g * zetaSum x t‖ := by
    rw [norm_mul, hsum]
    exact le_mul_of_one_le_left (div_pos hx hN).le hg
  have hnorm := norm_sub_norm_le (g * zetaSum x t) (zetaSum x (t - t₀))
  rw [norm_sub_rev] at hnorm
  have hraw : x / N - C * x / (Real.log x) ^ (3 / 4 : ℝ) ≤
      ‖zetaSum x (t - t₀)‖ := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx.le]
  apply (le_div_iff₀ hx).mpr
  convert hraw using 1
  ring

/-- One absolute logarithmic threshold controls displacement and central comparison error. -/
theorem exists_large_sum_gaussian_threshold {C : ℝ} (hC : 0 ≤ C) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℝ,
      1 ≤ N → N ≤ L ^ (1 / 100 : ℝ) →
      C * N ≤ L / 2 ∧ C / L ^ (3 / 4 : ℝ) ≤ 1 / (4 * N) := by
  obtain ⟨L₁, h₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).eventually_ge_atTop (2 * C))
  obtain ⟨L₂, h₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 37 / 50)).eventually_ge_atTop (4 * C))
  refine ⟨max 1 (max L₁ L₂), le_max_left _ _, ?_⟩
  intro L hL₀ N hN hNtop
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL₀
  have hL : 0 < L := by linarith
  have hpow₁ := h₁ L ((le_max_left L₁ L₂).trans ((le_max_right _ _).trans hL₀))
  have hpow₂ := h₂ L ((le_max_right L₁ L₂).trans ((le_max_right _ _).trans hL₀))
  have hCN : C * N ≤ C * L ^ (1 / 100 : ℝ) := mul_le_mul_of_nonneg_left hNtop hC
  have h₁' := mul_le_mul_of_nonneg_right hpow₁ (Real.rpow_nonneg hL.le (1 / 100))
  have h₂' := mul_le_mul_of_nonneg_right hpow₂ (Real.rpow_nonneg hL.le (1 / 100))
  rw [← Real.rpow_add hL] at h₁' h₂'
  norm_num at h₁' h₂'
  refine ⟨by linarith, ?_⟩
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hL _) (by positivity : 0 < 4 * N)).mpr
  nlinarith

/-- The sixth-power lower cutoff absorbs the exact one-sixth Gaussian error uniformly in N. -/
theorem gaussian_error_absorbed {K c a L N : ℝ} (hK : 0 ≤ K) (haL : 0 < a * L)
    (hN : 0 < N) (hc : (2 * K / Real.pi) ^ (6 : ℕ) ≤ c)
    (hscale : c * N ^ (6 : ℕ) ≤ a * L) :
    K / (a * L) ^ (1 / 6 : ℝ) ≤ Real.pi / (2 * N) := by
  have hp : (2 * K * N / Real.pi) ^ (6 : ℝ) ≤ a * L := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc
      _ = (2 * K / Real.pi) ^ (6 : ℕ) * N ^ (6 : ℕ) := by ring
      _ ≤ c * N ^ (6 : ℕ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ _ := hscale
  have hroot := (Real.le_rpow_inv_iff_of_pos
    (by positivity : 0 ≤ 2 * K * N / Real.pi) haL.le (by norm_num : (0 : ℝ) < 6)).mpr hp
  have hroot' : 2 * K * N ≤ Real.pi * (a * L) ^ (1 / 6 : ℝ) := by
    have h := (div_le_iff₀ Real.pi_pos).mp hroot
    simpa only [one_div, mul_comm Real.pi] using h
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos haL _) (by positivity : 0 < 2 * N)).mpr
  nlinarith

/-- The original large sum gives the source Gaussian lower bound at one twist for every scale. -/
theorem exists_large_sum_gaussian_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          (Real.pi / N) * Real.exp (a * Real.log x / 2) ≤
            ‖(Real.sqrt (2 * Real.pi * (a / Real.log x)) : ℂ) *
              (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
                (Real.exp ((a - 1) * y - (a / Real.log x) * y ^ 2 / 2) : ℂ))‖ := by
  obtain ⟨C, hC, x₁, hx₁, htwist⟩ := exists_large_sum_maximizing_twist
  obtain ⟨L₁, hL₁, herror⟩ := exists_maximizingTwist_source_gaussian_error
  obtain ⟨L₂, hL₂, hthreshold⟩ := exists_large_sum_gaussian_threshold hC.le
  let K := Real.sqrt (2 * Real.pi) * dilationLipschitzConstant * gaussianMomentConstant
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (by linarith [dilationLipschitzConstant_ge_four])) gaussianMomentConstant_nonneg
  let c := max 1 (max C ((2 * K / Real.pi) ^ (6 : ℕ)))
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc : 0 < c := by linarith
  have hcC : C ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcK : (2 * K / Real.pi) ^ (6 : ℕ) ≤ c :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, hc, max x₁ (Real.exp (max L₁ L₂)), hx₁.trans (le_max_left _ _), ?_⟩
  intro x hx₀ t N hN hNtop hsum
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx₀
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : max L₁ L₂ ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (max L₁ L₂)) ((le_max_right _ _).trans hx₀)
    simpa only [Real.log_exp] using h
  have hlog₁ : L₁ ≤ Real.log x := (le_max_left _ _).trans hlog
  have hlog₂ : L₂ ≤ Real.log x := (le_max_right _ _).trans hlog
  have hL : 0 < Real.log x := Real.log_pos hx
  obtain ⟨t₀, ht₀, hmax, hdisplace, _, _, hcomp⟩ := htwist x hxx₁ t N hN hNtop hsum
  have hthresholds := hthreshold (Real.log x) hlog₂ N hN hNtop
  have ht₀half : |t₀| ≤ Real.log x / 2 := hdisplace.trans hthresholds.1
  have hcentral := normalized_twisted_sum_lower hx0 hN0 hsum hcomp
  have hcentral' : 3 / (4 * N) ≤ ‖zetaSum x (t - t₀) / (x : ℂ)‖ := by
    have hfrac : 1 / N - 1 / (4 * N) = 3 / (4 * N) := by field_simp; ring
    linarith [hthresholds.2]
  refine ⟨t₀, ht₀, hmax, hdisplace.trans (mul_le_mul_of_nonneg_right hcC hN0.le), ?_⟩
  intro a halow ha2
  have ha : 0 < a := (div_pos (mul_pos hc (pow_pos hN0 _)) hL).trans_le halow
  have hscale : c * N ^ (6 : ℕ) ≤ a * Real.log x := (div_le_iff₀ hL).mp halow
  have habsorb := gaussian_error_absorbed hK (mul_pos ha hL) hN0 hcK hscale
  have herr := herror x t t₀ hx hlog₁ hmax ht₀half a ha ha2
  rw [Real.exp_log hx0] at herr
  let E := Real.exp (a * Real.log x / 2)
  let F := zetaSum x (t - t₀) / (x : ℂ)
  let G := (Real.sqrt (2 * Real.pi * (a / Real.log x)) : ℂ) *
    (∫ y : ℝ, zetaSum (Real.exp y) (t - t₀) *
      (Real.exp ((a - 1) * y - (a / Real.log x) * y ^ 2 / 2) : ℂ))
  change ‖G - (2 * Real.pi : ℂ) * (E : ℂ) * F‖ ≤
    K * E / (a * Real.log x) ^ (1 / 6 : ℝ) at herr
  have herr' : ‖G - (2 * Real.pi : ℂ) * (E : ℂ) * F‖ ≤
      Real.pi / (2 * N) * E := herr.trans (by
    have h := mul_le_mul_of_nonneg_right habsorb (Real.exp_pos (a * Real.log x / 2)).le
    simpa only [div_mul_eq_mul_div] using h)
  have hmain : (2 * Real.pi) * E * (3 / (4 * N)) ≤
      ‖(2 * Real.pi : ℂ) * (E : ℂ) * F‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left hcentral' (by positivity)
  have hnorm := norm_sub_norm_le ((2 * Real.pi : ℂ) * (E : ℂ) * F) G
  rw [norm_sub_rev] at hnorm
  change Real.pi / N * E ≤ ‖G‖
  have hfractions : (2 * Real.pi) * E * (3 / (4 * N)) -
      Real.pi / (2 * N) * E = Real.pi / N * E := by field_simp; ring
  linarith

end
end DongWangWangZhang2026
