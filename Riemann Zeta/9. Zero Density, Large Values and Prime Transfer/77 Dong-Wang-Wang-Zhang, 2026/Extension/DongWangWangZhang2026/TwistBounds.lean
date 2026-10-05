import DongWangWangZhang2026.MeanValueAssembly

/-!
# Quantitative bounds for the actual maximizing twist

This branch consumes the large-sum prime-distance theorem and the proved
comparison formula. It keeps one maximizing witness throughout the deductions.
-/

open Complex Filter

namespace DongWangWangZhang2026
noncomputable section

theorem norm_comparisonFactor_le_reciprocal {x : ℝ} (hx : 0 < x) (a : ℝ) :
    ‖comparisonFactor x a‖ ≤ 2 / (1 + |a|) := by
  have hreal : 1 ≤ ‖(a : ℂ) * I + 1‖ := by
    simpa using Complex.re_le_norm ((a : ℂ) * I + 1)
  have himag : |a| ≤ ‖(a : ℂ) * I + 1‖ := by
    simpa using Complex.abs_im_le_norm ((a : ℂ) * I + 1)
  rw [comparisonFactor, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, Real.rpow_zero]
  apply (div_le_div_iff₀ (by linarith : 0 < ‖(a : ℂ) * I + 1‖) (by positivity : 0 < 1 + |a|)).mpr
  linarith

theorem norm_inverse_comparisonFactor_le {x : ℝ} (hx : 0 < x) (a : ℝ) :
    ‖((a : ℂ) * I + 1) * (x : ℂ) ^ (-((a : ℂ) * I))‖ ≤ 1 + |a| := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, neg_zero, Real.rpow_zero, mul_one]
  have h := norm_add_le ((a : ℂ) * I) 1
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    norm_one, add_comm] using h

theorem inverse_comparisonFactor_mul {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (((a : ℂ) * I + 1) * (x : ℂ) ^ (-((a : ℂ) * I))) * comparisonFactor x a = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : (x : ℂ) ^ ((a : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hd : (a : ℂ) * I + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  rw [comparisonFactor, Complex.cpow_neg]
  field_simp

private theorem eventually_log_log_add_le (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.log (Real.log L) + C ≤ Real.log L / 300 := by
  have hu : ∀ᶠ u : ℝ in atTop, Real.log u + C ≤ u / 300 := by
    filter_upwards [(Real.isLittleO_log_id_atTop).bound (by norm_num : (0 : ℝ) < 1 / 600),
      eventually_ge_atTop (max (600 * |C|) 1)] with u hlog hu
    have hu1 : 1 ≤ u := (le_max_right _ _).trans hu
    have huC : 600 * |C| ≤ u := (le_max_left _ _).trans hu
    simp only [id_eq, Real.norm_of_nonneg (Real.log_nonneg hu1),
      Real.norm_of_nonneg (zero_le_one.trans hu1)] at hlog
    have hc := le_abs_self C
    linarith
  exact Real.tendsto_log_atTop.eventually hu

/-- The proved distance scale makes the actual comparison majorant uniformly
smaller than `L^(-4/5)`. This will be consumed with the large-sum witness. -/
theorem eventually_distance_comparison_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ M a : ℝ,
      M ≤ (1 / 100 : ℝ) * Real.log L + Real.log (Real.log L) + C → |a| ≤ L →
      (42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8) * Real.log (Real.exp 1 + |a|) / L *
        Real.exp (Real.sqrt (2 * M * (Real.log (1 + L) + 2 * (Real.log 4 + 4)))) ≤
          L ^ (-4 / 5 : ℝ) := by
  let K := 42 * (2 * (Real.log 4 + 4) + 1) * Real.exp 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogSmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).bound
    (show 0 < 1 / (2 * K) by positivity)
  have hlogLarge := Real.tendsto_log_atTop.eventually_ge_atTop
    (24 * (1 + 2 * (Real.log 4 + 4)))
  filter_upwards [eventually_log_log_add_le C, hlogSmall, hlogLarge,
    eventually_ge_atTop (8 : ℝ)] with L hlogM hlogPow hlogR hL
  intro M a hMupper ha
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hMsmall : M ≤ Real.log L / 75 := by linarith
  have hlogOne : Real.log (1 + L) ≤ 1 + Real.log L := by
    have h := Real.log_le_log (by positivity : 0 < 1 + L) (show 1 + L ≤ 2 * L by linarith)
    rw [Real.log_mul (by norm_num) hL0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hR : Real.log (1 + L) + 2 * (Real.log 4 + 4) ≤ 25 * Real.log L / 24 := by
    linarith
  have hR0 : 0 ≤ Real.log (1 + L) + 2 * (Real.log 4 + 4) :=
    add_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hroot : Real.sqrt (2 * M * (Real.log (1 + L) + 2 * (Real.log 4 + 4))) ≤
      Real.log L / 6 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hmul := mul_le_mul hMsmall hR hR0 (show 0 ≤ Real.log L / 75 by positivity)
    nlinarith
  have hexp : Real.exp (Real.sqrt (2 * M * (Real.log (1 + L) + 2 * (Real.log 4 + 4)))) ≤
      L ^ (1 / 6 : ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlogA : Real.log (Real.exp 1 + |a|) ≤ 2 * Real.log L := by
    have hbound : Real.exp 1 + |a| ≤ L ^ 2 := by nlinarith [Real.exp_one_lt_three]
    have h := Real.log_le_log (show 0 < Real.exp 1 + |a| by positivity) hbound
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogA0 : 0 ≤ Real.log (Real.exp 1 + |a|) := by
    apply Real.log_nonneg
    linarith [Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 1 by norm_num), abs_nonneg a]
  simp only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlogPow
  have hcoef : K * (2 * Real.log L) ≤ L ^ (1 / 30 : ℝ) := by
    have h := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp
      (show Real.log L ≤ L ^ (1 / 30 : ℝ) / (2 * K) by
        simpa only [one_div_mul_eq_div] using hlogPow)
    nlinarith
  change K * Real.log (Real.exp 1 + |a|) / L * _ ≤ _
  calc
    _ ≤ (K * (2 * Real.log L) / L) * L ^ (1 / 6 : ℝ) := mul_le_mul
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogA hK.le) hL0.le)
      hexp (Real.exp_pos _).le (by positivity)
    _ ≤ (L ^ (1 / 30 : ℝ) / L) * L ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hL0.le) (by positivity)
    _ = L ^ (-4 / 5 : ℝ) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hL0]
      have hpow : L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      conv_lhs => arg 2; rw [hpow]
      rw [← Real.rpow_sub hL0]
      norm_num

/-- The three non-Lipschitz conclusions of Lemma 2.2 at one actual maximizer:
source prime distance, displacement, and the full reversed comparison error.
The constants and threshold are independent of height and large-value size. -/
theorem exists_large_sum_twist_bounds :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ 4 * N ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C ∧
          ‖zetaSum x (t - t₀) -
            (((t₀ : ℂ) * I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * I))) * zetaSum x t‖ ≤
              4 * x / (Real.log x) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, x₁, hx₁, hdist⟩ := exists_large_sum_prime_distance_bound
  have hevent := ((eventually_distance_comparison_error C).and
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 79 / 100)).eventually_ge_atTop 2)).and
      (eventually_ge_atTop (8 : ℝ))
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hevent
  refine ⟨C, hC, max x₁ (Real.exp L₁), hx₁.trans (le_max_left _ _), ?_⟩
  intro x hx₀ t N hN hNtop hsum
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx₀
  have hxexp : Real.exp L₁ ≤ x := (le_max_right _ _).trans hx₀
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hN0 : 0 < N := by linarith
  let L := Real.log x
  have hL0 : 0 < L := Real.log_pos hx
  have hLlower : L₁ ≤ L := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L₁) hxexp
  obtain ⟨⟨hcomparison, hpower⟩, hL⟩ := hL₁ L hLlower
  obtain ⟨a, ha, hmax, hM⟩ := hdist x hxx₁ t N hN hNtop hsum
  have herr : ‖zetaSum x t / (x : ℂ) - comparisonFactor x a *
      (zetaSum x (t - a) / (x : ℂ))‖ ≤ L ^ (-4 / 5 : ℝ) :=
    (norm_normalized_mean_comparison_le_distance t a x hx (by change 1 ≤ L; linarith)).trans
      (hcomparison (primePhaseDistance x (t - a)) a hM ha)
  have hprod : N * L ^ (-4 / 5 : ℝ) ≤ L ^ (-79 / 100 : ℝ) := by
    calc
      _ ≤ L ^ (1 / 100 : ℝ) * L ^ (-4 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hNtop (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]; norm_num
  have hhalf : L ^ (-4 / 5 : ℝ) ≤ 1 / (2 * N) := by
    have hnegative : L ^ (-79 / 100 : ℝ) ≤ 1 / 2 := by
      rw [show (-79 / 100 : ℝ) = -(79 / 100) by norm_num, Real.rpow_neg hL0.le, ← one_div]
      exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hL0 _) (by norm_num : (0 : ℝ) < 2)).mpr
        (by simpa using hpower)
    have hh := hprod.trans hnegative
    apply (le_div_iff₀ (show 0 < 2 * N by positivity)).mpr
    nlinarith
  have hnormS : ‖zetaSum x t / (x : ℂ)‖ = 1 / N := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le, hsum]
    field_simp
  have htwist : ‖zetaSum x (t - a) / (x : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    exact (div_le_one hx0).mpr (norm_zetaSum_le hx0.le _)
  have hnormprod : ‖comparisonFactor x a * (zetaSum x (t - a) / (x : ℂ))‖ ≤ 2 / (1 + |a|) := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left htwist (norm_nonneg (comparisonFactor x a))
    rw [mul_one] at h
    exact h.trans (norm_comparisonFactor_le_reciprocal hx0 a)
  have hnorm := (norm_sub_norm_le (zetaSum x t / (x : ℂ))
    (comparisonFactor x a * (zetaSum x (t - a) / (x : ℂ)))).trans herr
  rw [hnormS] at hnorm
  have hdisplace : 1 + |a| ≤ 4 * N := by
    have hh : 1 / (2 * N) ≤ 2 / (1 + |a|) := by
      have hid : 1 / N = 2 * (1 / (2 * N)) := by ring
      rw [hid] at hnorm
      linarith
    have hc := (div_le_div_iff₀ (show 0 < 2 * N by positivity)
      (show 0 < 1 + |a| by positivity)).mp hh
    nlinarith
  refine ⟨a, ha, hmax, by linarith, hM, ?_⟩
  have hforward : ‖zetaSum x t - comparisonFactor x a * zetaSum x (t - a)‖ ≤
      L ^ (-4 / 5 : ℝ) * x := by
    have heq : zetaSum x t / (x : ℂ) - comparisonFactor x a *
        (zetaSum x (t - a) / (x : ℂ)) =
          (zetaSum x t - comparisonFactor x a * zetaSum x (t - a)) / (x : ℂ) := by ring
    rw [heq, norm_div, Complex.norm_real, Real.norm_of_nonneg hx0.le] at herr
    exact (div_le_iff₀ hx0).mp herr
  let g := ((a : ℂ) * I + 1) * (x : ℂ) ^ (-((a : ℂ) * I))
  have hg : g * comparisonFactor x a = 1 := inverse_comparisonFactor_mul hx0 a
  have heq : zetaSum x (t - a) - g * zetaSum x t =
      -g * (zetaSum x t - comparisonFactor x a * zetaSum x (t - a)) := by
    calc
      _ = -g * zetaSum x t + (g * comparisonFactor x a) * zetaSum x (t - a) := by rw [hg]; ring
      _ = _ := by ring
  have hgnorm : ‖g‖ ≤ 4 * N := (norm_inverse_comparisonFactor_le hx0 a).trans hdisplace
  have hprod' : N * L ^ (-4 / 5 : ℝ) ≤ L ^ (-3 / 4 : ℝ) := hprod.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by norm_num))
  change ‖zetaSum x (t - a) - g * zetaSum x t‖ ≤ 4 * x / L ^ (3 / 4 : ℝ)
  rw [heq, norm_mul, norm_neg]
  calc
    _ ≤ (4 * N) * (L ^ (-4 / 5 : ℝ) * x) := mul_le_mul hgnorm hforward (norm_nonneg _) (by positivity)
    _ = (4 * x) * (N * L ^ (-4 / 5 : ℝ)) := by ring
    _ ≤ (4 * x) * L ^ (-3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = _ := by rw [show (-3 / 4 : ℝ) = -(3 / 4) by norm_num, Real.rpow_neg hL0.le]; ring

end
end DongWangWangZhang2026
