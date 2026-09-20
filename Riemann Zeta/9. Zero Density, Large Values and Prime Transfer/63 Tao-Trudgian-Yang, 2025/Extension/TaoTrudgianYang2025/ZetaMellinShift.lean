import TaoTrudgianYang2025.ZetaMellinContour

/-!
# Absolute convergence and the critical-line Mellin shift

The native Abel formula controls zeta, and the genuine compactly supported
cutoff gives rapid Mellin decay. These justify the infinite-height shift;
the moving-pole residue is retained rather than absorbed without a bound.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
open scoped Interval

namespace TaoTrudgianYang2025

theorem norm_zeta_mellin_boundary {c : ℝ} (hc : c = 1 / 2 ∨ c = 3 / 2) (v : ℝ) :
    ‖riemannZeta ((c : ℂ) + (v : ℂ) * I)‖ ≤ 6 * (1 + |v|) := by
  let s : ℂ := (c : ℂ) + (v : ℂ) * I
  have hre : s.re = c := by simp [s]
  have hcpos : 0 < c := by rcases hc with rfl | rfl <;> norm_num
  have hcsmall : |c| ≤ 3 / 2 := by rcases hc with rfl | rfl <;> norm_num
  have hcdiff : |c - 1| = 1 / 2 := by rcases hc with rfl | rfl <;> norm_num
  have hcge : 1 / 2 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    calc
      _ = |(s - 1).re| := by simp only [sub_re, hre, one_re, hcdiff]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hsne : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hden; norm_num at hden
  have hrem : ‖abelZetaRemainder s‖ ≤ 2 := by
    apply (norm_abelZetaRemainder_le (hre.symm ▸ hcpos)).trans
    rw [hre]
    exact (div_le_iff₀ hcpos).2 (by linarith)
  have hnorm : ‖s‖ ≤ 3 / 2 + |v| := by
    apply (Complex.norm_le_abs_re_add_abs_im s).trans
    have hsim : |s.re| + |s.im| = |c| + |v| := by simp [s]
    rw [hsim]
    linarith
  change ‖riemannZeta s‖ ≤ _
  rw [riemannZeta_eq_abel (hre.symm ▸ hcpos) hsne]
  calc
    _ ≤ ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ ≤ 2 * ‖s‖ + ‖s‖ * 2 := by
      rw [norm_div, norm_mul]
      apply add_le_add
      · exact (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).2
          (by nlinarith [norm_nonneg s])
      · exact mul_le_mul_of_nonneg_left hrem (norm_nonneg s)
    _ ≤ _ := by nlinarith [abs_nonneg v]

theorem integrable_zetaMellin_boundary {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {c : ℝ} (hc : c = 1 / 2 ∨ c = 3 / 2) (t : ℝ) :
    Integrable (fun u : ℝ => zetaMellinIntegrand g t ((c : ℂ) + (u : ℂ) * I)) := by
  have hcont : Continuous (fun u : ℝ => zetaMellinIntegrand g t ((c : ℂ) + (u : ℂ) * I)) := by
    apply Continuous.mul
    · rw [continuous_iff_continuousAt]
      intro u
      have hne : ((c : ℂ) + (u : ℂ) * I) + (t : ℂ) * I ≠ 1 := by
        intro h
        have hreal := congrArg Complex.re h
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
          zero_mul, sub_zero, add_zero, one_re] at hreal
        rcases hc with rfl | rfl <;> norm_num at hreal
      exact (differentiableAt_riemannZeta hne).continuousAt.comp
        (f := fun x : ℝ => (c : ℂ) + (x : ℂ) * I + (t : ℂ) * I) (by fun_prop)
    · exact hg.differentiable_mellin.continuous.comp (by fun_prop)
  have hdom := (hg.integrable_sqWeight_norm_mellin c).const_mul (6 * (1 + |t|))
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards with u
  have hz := norm_zeta_mellin_boundary hc (u + t)
  have harg : ((c : ℂ) + (u : ℂ) * I) + (t : ℂ) * I =
      (c : ℂ) + ((u + t : ℝ) : ℂ) * I := by push_cast; ring
  have hu : 0 ≤ |u| := abs_nonneg u
  have ht : 0 ≤ |t| := abs_nonneg t
  have hweight : 1 + |u + t| ≤ (1 + |t|) * (1 + |u|) ^ 2 := by
    have := abs_add_le u t
    nlinarith [sq_nonneg |u|, mul_nonneg ht hu, mul_nonneg ht (sq_nonneg |u|)]
  unfold zetaMellinIntegrand
  rw [norm_mul, harg]
  have hbound := hz.trans (mul_le_mul_of_nonneg_left hweight (by norm_num))
  calc
    _ ≤ (6 * ((1 + |t|) * (1 + |u|) ^ 2)) *
        ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = _ := by ring

/-- Uniform horizontal decay across the whole shift strip, away from the
moving pole. Constants may depend on the actual test function and ordinate. -/
theorem exists_zetaMellin_strip_tail_bound {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 / 2 ≤ c → c ≤ 3 / 2 →
      ∀ u : ℝ, |t| + 1 ≤ |u| →
        ‖zetaMellinIntegrand g t ((c : ℂ) + (u : ℂ) * I)‖ ≤ K / (1 + |u|) ^ 2 := by
  obtain ⟨D, hD, hdecay⟩ := hg.exists_mellin_one_add_abs_pow_shifted_strip_bound 3 0
  refine ⟨5 * (2 + |t|) * D, by positivity, ?_⟩
  intro c hc0 hc1 u hu
  have habs : 1 ≤ |u + t| := by
    have htriangle : |u| ≤ |u + t| + |t| := by
      simpa only [add_sub_cancel_right] using (abs_sub (u + t) t)
    linarith
  have hz := norm_riemannZeta_le_five_mul_norm
    (s := (c : ℂ) + ((u + t : ℝ) : ℂ) * I) (by simpa using (show 1 / 4 ≤ c by linarith))
    (by simpa using habs)
  have hcabs : |c| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hnorm : ‖(c : ℂ) + ((u + t : ℝ) : ℂ) * I‖ ≤ (2 + |t|) * (1 + |u|) := by
    have h := Complex.norm_le_abs_re_add_abs_im ((c : ℂ) + ((u + t : ℝ) : ℂ) * I)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add] at h
    nlinarith [abs_add_le u t, abs_nonneg u, abs_nonneg t, mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  have hM := hdecay c (by norm_num; linarith) (by simpa using hc1) u
  have harg : ((c : ℂ) + (u : ℂ) * I) + (t : ℂ) * I =
      (c : ℂ) + ((u + t : ℝ) : ℂ) * I := by push_cast; ring
  unfold zetaMellinIntegrand
  rw [norm_mul, harg]
  apply (le_div_iff₀ (by positivity : 0 < (1 + |u|) ^ 2)).2
  calc
    _ ≤ (5 * ((2 + |t|) * (1 + |u|))) *
        ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖ * (1 + |u|) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hz.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num)))
        (norm_nonneg _)
    _ = (5 * (2 + |t|)) * ((1 + |u|) ^ 3 * ‖mellin g ((c : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)

/-- Both horizontal sides vanish at infinite height, uniformly across
the full real interval of the contour shift. -/
theorem zetaMellin_horizontal_limits {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    Tendsto (fun R : ℝ => HIntegral (zetaMellinIntegrand g t) (1 / 2) (3 / 2) R)
      atTop (nhds 0) ∧
    Tendsto (fun R : ℝ => HIntegral (zetaMellinIntegrand g t) (1 / 2) (3 / 2) (-R))
      atTop (nhds 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_zetaMellin_strip_tail_bound hg t
  let envelope : ℝ → ℝ := fun R => K / (1 + |R|) ^ 2
  have hzero : Tendsto envelope atTop (nhds 0) := by
    have habs : Tendsto (fun R : ℝ => |R|) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall le_abs_self) tendsto_id
    have hden : Tendsto (fun R : ℝ => (1 + |R|) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_const_nhds.add_atTop habs)
    exact tendsto_const_nhds.div_atTop hden
  have hnorm (R : ℝ) (hR : |t| + 1 ≤ |R|) :
      ‖HIntegral (zetaMellinIntegrand g t) (1 / 2) (3 / 2) R‖ ≤ envelope R := by
    unfold HIntegral
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => zetaMellinIntegrand g t ((x : ℂ) + (R : ℂ) * I))
      (C := envelope R) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] at hx'
        exact hbound x hx'.1 hx'.2 R hR)
    norm_num at h
    exact h
  constructor
  · apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop (|t| + 1)] with R hR
    exact hnorm R (hR.trans (le_abs_self R))
  · apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop (|t| + 1)] with R hR
    have h := hnorm (-R) (by rw [abs_neg]; exact hR.trans (le_abs_self R))
    simpa only [envelope, abs_neg] using h

/-- The full infinite-height critical-line shift, with its moving zeta
residue. No horizontal-tail or vertical-integrability premise remains. -/
theorem zetaMellin_vertical_shift {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    VerticalIntegral' (zetaMellinIntegrand g t) (3 / 2) -
      VerticalIntegral' (zetaMellinIntegrand g t) (1 / 2) = mellin g (1 - (t : ℂ) * I) := by
  let f := zetaMellinIntegrand g t
  let a : ℝ := 1 / 2
  let b : ℝ := 3 / 2
  obtain ⟨htop, hbottom⟩ := zetaMellin_horizontal_limits hg t
  have hleft := integrable_zetaMellin_boundary hg (Or.inl rfl) t
  have hright := integrable_zetaMellin_boundary hg (Or.inr rfl) t
  have hlimit : Tendsto (fun R : ℝ =>
      RectangleIntegral f ((a : ℂ) - I * (R : ℂ)) ((b : ℂ) + I * (R : ℂ))) atTop
      (nhds (VerticalIntegral f b - VerticalIntegral f a)) := by
    simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
      ofReal_im, mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im,
      one_mul, zero_add, zero_sub, add_im]
    apply Tendsto.sub
    · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
      exact (hbottom.sub htop).add
        ((intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I)
    · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I
  have hnormalized := hlimit.const_smul (1 / (2 * Real.pi * I) : ℂ)
  have hlimit' : Tendsto (fun R : ℝ =>
      RectangleIntegral' f ((a : ℂ) - I * (R : ℂ)) ((b : ℂ) + I * (R : ℂ))) atTop
      (nhds (VerticalIntegral' f b - VerticalIntegral' f a)) := by
    simpa only [RectangleIntegral', VerticalIntegral', smul_sub] using hnormalized
  have hfinite : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' f ((a : ℂ) - I * (R : ℂ)) ((b : ℂ) + I * (R : ℂ)) =
        mellin g (1 - (t : ℂ) * I) := by
    filter_upwards [eventually_gt_atTop |t|] with R hR
    simpa [a, b, f, mul_comm] using zetaMellin_finite_rectangle hg t hR
  exact tendsto_nhds_unique hlimit' (tendsto_const_nhds.congr' (hfinite.mono fun _ h => h.symm))

theorem zetaMellin_verticalIntegral_eq (g : ℝ → ℂ) (t c : ℝ) :
    VerticalIntegral' (zetaMellinIntegrand g t) c =
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
          mellin g ((c : ℂ) + (u : ℂ) * I) := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  have hscalar : (1 / (2 * Real.pi * I) : ℂ) * I = 1 / (2 * Real.pi) := by
    field_simp [Real.pi_ne_zero]
  rw [hscalar]
  congr 2
  funext u
  unfold zetaMellinIntegrand
  congr 2
  push_cast
  ring

/-- Exact critical-line formula, with the actual residue term and no
analytic theorem parameters. This is not yet a localized norm estimate. -/
theorem smooth_dirichlet_sum_eq_critical_zeta_mellin {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) :
    (∑' n : ℕ, g n * dirichletPhase n t) = mellin g (1 - (t : ℂ) * I) +
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * I) *
          mellin g (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
  have h := zetaMellin_vertical_shift hg t
  rw [zetaMellin_verticalIntegral_eq, zetaMellin_verticalIntegral_eq] at h
  rw [smooth_dirichlet_sum_eq_zeta_mellin hg (c := 3 / 2) (by norm_num) t]
  linear_combination h

theorem ZetaLargeValuePattern.polynomial_eq_critical_zeta_mellin (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I) +
        (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * I) *
            mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
              (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
  rw [P.polynomial_eq_cutoff_tsum hactive]
  exact smooth_dirichlet_sum_eq_critical_zeta_mellin
    (zetaIntervalCutoffTest a b (P.active_left_pos hactive)) t

/-- Actual-pattern critical-line entry, with one common exact interval
cutoff for all large ordinates and the pole contribution still visible. -/
theorem ZetaLargeValuePattern.exists_critical_zeta_mellin_large (P : ZetaLargeValuePattern) :
    ∃ a b : ℕ, P.active = Finset.Icc a b ∧ 1 ≤ a ∧
      ∀ t ∈ P.ordinates, P.V ≤
        ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I) +
          (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
            riemannZeta (((1 / 2 : ℝ) : ℂ) + ((u + t : ℝ) : ℂ) * I) *
              mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
                (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  refine ⟨a, b, hactive, P.active_left_pos hactive, ?_⟩
  intro t ht
  rw [← P.polynomial_eq_critical_zeta_mellin hactive t]
  exact P.large t ht

end TaoTrudgianYang2025
