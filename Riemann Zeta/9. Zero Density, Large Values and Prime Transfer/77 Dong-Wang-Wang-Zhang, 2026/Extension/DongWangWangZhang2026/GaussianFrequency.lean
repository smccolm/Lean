import DongWangWangZhang2026.GaussianLowerBound
import DongWangWangZhang2026.ZetaUniformBounds

/-!
# The residue and frequency integral in Proposition 4.1

The actual positive pole term from the Gaussian identity is bounded
before it is removed from the large-sum lower bound.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

/-- The exact real exponent of the source pole term retains its negative height square. -/
theorem source_gaussian_residue_exponent (a t V : ℝ) :
    ((((a : ℂ) + (t : ℂ) * I) ^ 2) / (2 * (V : ℂ))).re =
      (a ^ 2 - t ^ 2) / (2 * V) := by
  rw [show (2 : ℂ) * (V : ℂ) = ((2 * V : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re]
  congr 1
  simp [pow_two]

/-- Uniform magnitude of the actual pole residue, with its Gaussian decay preserved. -/
theorem norm_source_gaussian_residue_le (a t V : ℝ) (ht : t ≠ 0) :
    ‖(2 * Real.pi : ℂ) / (1 + (t : ℂ) * I) *
      Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * (V : ℂ)))‖ ≤
      (2 * Real.pi / |t|) * Real.exp ((a ^ 2 - t ^ 2) / (2 * V)) := by
  have hden : |t| ≤ ‖1 + (t : ℂ) * I‖ := by
    simpa using Complex.abs_im_le_norm (1 + (t : ℂ) * I)
  rw [norm_mul, norm_div, Complex.norm_exp, source_gaussian_residue_exponent]
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr ht) hden) (Real.exp_pos _).le

/-- On the linked source scale, discarding the negative square already gives a sufficient bound. -/
theorem norm_source_gaussian_residue_linked {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    {t : ℝ} (ht : t ≠ 0) :
    ‖(2 * Real.pi : ℂ) / (1 + (t : ℂ) * I) *
      Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * ((a / L : ℝ) : ℂ)))‖ ≤
      (2 * Real.pi / |t|) * Real.exp (a * L / 2) := by
  apply (norm_source_gaussian_residue_le a t (a / L) ht).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2 * (a / L))).mpr
  have he : (a * L / 2) * (2 * (a / L)) = a ^ 2 := by field_simp
  rw [he]
  linarith [sq_nonneg t]

/-- A height separation of four times N makes the actual residue at most half the lower bound. -/
theorem norm_source_gaussian_residue_half {a L N t : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hN : 0 < N) (ht : 4 * N ≤ |t|) :
    ‖(2 * Real.pi : ℂ) / (1 + (t : ℂ) * I) *
      Complex.exp (((a : ℂ) + (t : ℂ) * I) ^ 2 / (2 * ((a / L : ℝ) : ℂ)))‖ ≤
      (Real.pi / (2 * N)) * Real.exp (a * L / 2) := by
  have ht0 : t ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) ht)
  apply (norm_source_gaussian_residue_linked ha hL ht0).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ 2 * Real.pi / (4 * N) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) ht
    _ = _ := by ring

/-- The actual large sum forces a large convergent zeta-frequency integral after removing its pole. -/
theorem exists_large_sum_gaussian_frequency_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, x ≤ |t| →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ c * N ∧ ∀ a : ℝ, c * N ^ (6 : ℕ) / Real.log x ≤ a → a ≤ 1 / 2 →
          Integrable (fun ξ : ℝ =>
            (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - (t - t₀) : ℝ) : ℂ) * I) /
              (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
                (Real.exp (-ξ ^ 2 / (2 * (a / Real.log x))) : ℂ)) ∧
          (Real.pi / (2 * N)) * Real.exp (a * Real.log x / 2) ≤
            ‖∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) +
              ((ξ - (t - t₀) : ℝ) : ℂ) * I) /
                (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
                  (Real.exp (-ξ ^ 2 / (2 * (a / Real.log x))) : ℂ)‖ := by
  obtain ⟨c, hc, x₁, hx₁, hlower⟩ := exists_large_sum_gaussian_lower
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (Real.isLittleO_log_id_atTop.bound (by positivity : 0 < 1 / (c + 4)))
  refine ⟨c, hc, max x₁ (max (Real.exp 1) B), hx₁.trans (le_max_left _ _), ?_⟩
  intro x hx₀ t N hxt hN hNtop hsum
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx₀
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hxrest : max (Real.exp 1) B ≤ x := (le_max_right _ _).trans hx₀
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_left _ _).trans hxrest)
    simpa only [Real.log_exp] using h
  have hL : 0 < Real.log x := by linarith
  have hlogsmall := hB x ((le_max_right _ _).trans hxrest)
  simp only [id_eq, Real.norm_of_nonneg hL.le, Real.norm_of_nonneg hx0.le] at hlogsmall
  have hsize : (c + 4) * N ≤ x := by
    have hNL := hNtop.trans (Real.rpow_le_self_of_one_le hL1 (by norm_num))
    have h := (le_div_iff₀ (by positivity : 0 < c + 4)).mp
      (show Real.log x ≤ x / (c + 4) by
        simpa only [one_div, mul_comm x, div_eq_mul_inv, one_mul] using hlogsmall)
    nlinarith
  obtain ⟨t₀, ht₀, hmax, hdisplace, hgauss⟩ := hlower x hxx₁ t N hN hNtop hsum
  have hN0 : 0 < N := by linarith
  have hheight : 4 * N ≤ |t - t₀| := by
    have htri : |t| ≤ |t - t₀| + |t₀| := by simpa using abs_add_le (t - t₀) t₀
    linarith
  refine ⟨t₀, ht₀, hmax, hdisplace, ?_⟩
  intro a halow ha2
  have ha : 0 < a := (div_pos (mul_pos hc (pow_pos hN0 _)) hL).trans_le halow
  have hV : 0 < a / Real.log x := div_pos ha hL
  refine ⟨integrable_source_gaussian_zeta a (t - t₀) (a / Real.log x) ha (by linarith) hV, ?_⟩
  have hg := hgauss a halow ha2
  rw [source_gaussian_identity a (t - t₀) (a / Real.log x) ha ha2 hV] at hg
  have hr := norm_source_gaussian_residue_half ha hL hN0 hheight
  have hn := norm_add_le
    (∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - (t - t₀) : ℝ) : ℂ) * I) /
      (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) *
        (Real.exp (-ξ ^ 2 / (2 * (a / Real.log x))) : ℂ))
    ((2 * Real.pi : ℂ) / (1 + ((t - t₀ : ℝ) : ℂ) * I) *
      Complex.exp (((a : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) ^ 2 /
        (2 * ((a / Real.log x : ℝ) : ℂ))))
  have hfrac : Real.pi / N = 2 * (Real.pi / (2 * N)) := by ring
  rw [hfrac] at hg
  linarith

/-- The source denominator absorbs the frequency growth in the uniform zeta estimate. -/
theorem norm_source_zeta_quotient_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (t ξ : ℝ) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
      (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖ ≤ (24 / a) * (2 + |t|) ^ a := by
  let d := ‖(((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖
  have hdre : 1 - a ≤ d := by
    simpa [d] using Complex.re_le_norm (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)
  have hdim : |ξ| ≤ d := by
    simpa [d] using Complex.abs_im_le_norm (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)
  have hd : 0 < d := by linarith
  have hdsum : 1 + |ξ| ≤ 3 * d := by linarith
  have hbase : 2 + |ξ - t| ≤ (2 + |t|) * (1 + |ξ|) := by
    have h := abs_sub ξ t
    nlinarith [abs_nonneg t, abs_nonneg ξ]
  have hp : (2 + |ξ - t|) ^ a ≤ (2 + |t|) ^ a * (1 + |ξ|) := by
    calc
      _ ≤ ((2 + |t|) * (1 + |ξ|)) ^ a :=
        Real.rpow_le_rpow (by positivity) hbase ha.le
      _ = (2 + |t|) ^ a * (1 + |ξ|) ^ a := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg ξ]) (by linarith))
        (Real.rpow_nonneg (by positivity) _)
  have hz := norm_zeta_left_strip_le a (ξ - t) ha ha2
  rw [norm_div]
  apply (div_le_iff₀ hd).mpr
  have hz' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 / a)
  have hd' := mul_le_mul_of_nonneg_left hdsum
    (by positivity : 0 ≤ (8 / a) * (2 + |t|) ^ a)
  have he : 8 * (2 + |ξ - t|) ^ a / a = (8 / a) * (2 + |ξ - t|) ^ a := by ring
  rw [he] at hz
  simp only [div_eq_mul_inv] at hz hz' hd' ⊢
  nlinarith

/-- Beyond the source frequency radius the Gaussian absorbs the complete height factor. -/
theorem source_gaussian_tail_height_absorption {a L T ξ : ℝ}
    (ha : 0 < a) (hL : 0 < L) (hT : 1 ≤ T)
    (hξ : 2 * a * Real.sqrt (Real.log T / L) ≤ |ξ|) :
    T ^ a * Real.exp (-ξ ^ 2 / (4 * (a / L))) ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have hQ : 0 ≤ Real.log T := Real.log_nonneg hT
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ 2 * a * Real.sqrt (Real.log T / L))
    (abs_nonneg ξ)).mpr hξ
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hQ hL.le)] at hs
  have hbound : a * Real.log T ≤ ξ ^ 2 / (4 * (a / L)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (a / L))).mpr
    convert hs using 1
    ring
  rw [Real.rpow_def_of_pos hT0, ← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  rw [neg_div]
  nlinarith only [hbound]

/-- One uniform estimate covers both source frequency tails, including arbitrarily large frequencies. -/
theorem source_gaussian_weighted_zeta_tail {a L T : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hL : 0 < L) (hT : 1 ≤ T)
    {t ξ : ℝ} (ht : |t| ≤ 3 * T)
    (hξ : 2 * a * Real.sqrt (Real.log T / L) ≤ |ξ|) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
      (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖ *
        Real.exp (-ξ ^ 2 / (4 * (a / L))) ≤ 120 / a := by
  have hT0 : 0 < T := by linarith
  have hh : (2 + |t|) ^ a ≤ 5 * T ^ a := by
    calc
      _ ≤ (5 * T) ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
      _ = (5 : ℝ) ^ a * T ^ a := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by linarith))
        (Real.rpow_nonneg hT0.le _)
  have hq := norm_source_zeta_quotient_le ha ha2 t ξ
  have htail := source_gaussian_tail_height_absorption ha hL hT hξ
  calc
    _ ≤ ((24 / a) * (2 + |t|) ^ a) * Real.exp (-ξ ^ 2 / (4 * (a / L))) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
    _ ≤ ((24 / a) * (5 * T ^ a)) * Real.exp (-ξ ^ 2 / (4 * (a / L))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity))
        (Real.exp_pos _).le
    _ = (120 / a) * (T ^ a * Real.exp (-ξ ^ 2 / (4 * (a / L)))) := by ring
    _ ≤ _ := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 120 / a)

/-- A large actual frequency integral produces a weighted point without assuming maximum attainment. -/
theorem exists_zeta_gaussian_frequency_gt (a t V M : ℝ) (hV : 0 < V)
    (hlarge : M * Real.sqrt (4 * Real.pi * V) <
      ‖∫ ξ : ℝ, (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) * (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ)‖) :
    ∃ ξ : ℝ, M <
      ‖riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
        (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)‖ * Real.exp (-ξ ^ 2 / (4 * V)) := by
  by_contra h
  push Not at h
  have hg : Integrable (fun ξ : ℝ => Real.exp (-ξ ^ 2 / (4 * V))) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * V)) using 1
    ext ξ
    congr 1
    ring
  have hi : (∫ ξ : ℝ, Real.exp (-ξ ^ 2 / (4 * V))) = Real.sqrt (4 * Real.pi * V) := by
    have hf : (fun ξ : ℝ => Real.exp (-ξ ^ 2 / (4 * V))) =
        (fun ξ : ℝ => Real.exp (-(1 / (4 * V)) * ξ ^ 2)) := by
      funext ξ
      congr 1
      ring
    rw [hf, integral_gaussian]
    congr 1
    field_simp
  have hbound := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => (riemannZeta (((1 - a : ℝ) : ℂ) + ((ξ - t : ℝ) : ℂ) * I) /
      (((1 - a : ℝ) : ℂ) + (ξ : ℂ) * I)) * (Real.exp (-ξ ^ 2 / (2 * V)) : ℂ))
    (hg.const_mul M) (ae_of_all _ (fun ξ => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have he : Real.exp (-ξ ^ 2 / (2 * V)) =
          Real.exp (-ξ ^ 2 / (4 * V)) * Real.exp (-ξ ^ 2 / (4 * V)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (h ξ) (Real.exp_pos _).le))
  rw [integral_const_mul, hi] at hbound
  linarith

end
end DongWangWangZhang2026
