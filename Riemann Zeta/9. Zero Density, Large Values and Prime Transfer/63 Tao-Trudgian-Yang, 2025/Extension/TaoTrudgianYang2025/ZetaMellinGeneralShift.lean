import TaoTrudgianYang2025.ZetaMellinGeneralBoundary

/-!
# Exact Mellin shifts to any fixed line in the half-open critical strip

The actual contour crosses the moving pole at 1-it. Its residue is retained.
These identities use no moment or growth hypotheses, and assert no contour
integrability on the line through the pole.
-/

noncomputable section
open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
open scoped Interval
namespace TaoTrudgianYang2025

theorem zetaMellin_general_finite_rectangle {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {c : ℝ} (hc : c < 1) (t : ℝ) {R : ℝ} (hR : |t| < R) :
    RectangleIntegral' (zetaMellinIntegrand g t)
      ((c : ℂ) - (R : ℂ) * I) ((3 / 2 : ℂ) + (R : ℂ) * I) =
        mellin g (1 - (t : ℂ) * I) := by
  let z : ℂ := (c : ℂ) - (R : ℂ) * I
  let w : ℂ := (3 / 2 : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - (t : ℂ) * I
  let F := zetaMellinNumerator g t
  have hRpos : 0 < R := (abs_nonneg t).trans_lt hR
  have hzRe : z.re ≤ w.re := by norm_num [z, w]; linarith
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hp : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · norm_num [p, z, w]
      exact hc
    · norm_num [p, z, w]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hdiff : DifferentiableOn ℂ F (Rectangle z w) :=
    (differentiable_zetaMellinNumerator hg t).differentiableOn
  have hdslope : HolomorphicOn (dslope F p) (Rectangle z w) :=
    (Complex.differentiableOn_dslope hp).2 hdiff
  have hFp : F p = mellin g p := zetaMellinNumerator_at_pole g t
  have hprincipal : Set.EqOn
      (zetaMellinIntegrand g t - fun s => mellin g p / (s - p)) (dslope F p)
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := hs.2
    change zetaMellinIntegrand g t s - mellin g p / (s - p) = dslope F p s
    rw [zetaMellinIntegrand_eq_quotient g t hsp, ← hFp, ← sub_div]
    change (F s - F p) / (s - p) = dslope F p s
    rw [← sub_smul_dslope F p s, smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  exact ResidueTheoremOnRectangleWithSimplePole hzRe hzIm hp hdslope hprincipal

theorem zetaMellin_general_horizontal_limits {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    Tendsto (fun R : ℝ => HIntegral (zetaMellinIntegrand g t) c (3 / 2) R)
      atTop (nhds 0) ∧
    Tendsto (fun R : ℝ => HIntegral (zetaMellinIntegrand g t) c (3 / 2) (-R))
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
      ‖HIntegral (zetaMellinIntegrand g t) c (3 / 2) R‖ ≤ envelope R := by
    unfold HIntegral
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => zetaMellinIntegrand g t ((x : ℂ) + (R : ℂ) * I))
      (C := envelope R) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by linarith : c ≤ 3 / 2)] at hx'
        exact hbound x (hc.trans hx'.1) hx'.2 R hR)
    apply h.trans
    have hlen : |(3 / 2 : ℝ) - c| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlen (by dsimp [envelope]; positivity)
  constructor
  · apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop (|t| + 1)] with R hR
    exact hnorm R (hR.trans (le_abs_self R))
  · apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop (|t| + 1)] with R hR
    have h := hnorm (-R) (by rw [abs_neg]; exact hR.trans (le_abs_self R))
    simpa only [envelope, abs_neg] using h


theorem zetaMellin_general_vertical_shift {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    VerticalIntegral' (zetaMellinIntegrand g t) (3 / 2) -
      VerticalIntegral' (zetaMellinIntegrand g t) c = mellin g (1 - (t : ℂ) * I) := by
  let f := zetaMellinIntegrand g t
  let a : ℝ := c
  let b : ℝ := 3 / 2
  obtain ⟨htop, hbottom⟩ := zetaMellin_general_horizontal_limits hg hc hc1 t
  have hleft := integrable_zetaMellin_left_boundary hg hc hc1 t
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
    simpa [a, b, f, mul_comm] using zetaMellin_general_finite_rectangle hg hc1 t hR
  exact tendsto_nhds_unique hlimit' (tendsto_const_nhds.congr' (hfinite.mono fun _ h => h.symm))


/-- Exact arbitrary-line formula, retaining the pole contribution. -/
theorem smooth_dirichlet_sum_eq_general_zeta_mellin {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) {c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    (∑' n : ℕ, g n * dirichletPhase n t) = mellin g (1 - (t : ℂ) * I) +
      (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
        riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
          mellin g ((c : ℂ) + (u : ℂ) * I) := by
  have h := zetaMellin_general_vertical_shift hg hc hc1 t
  rw [zetaMellin_verticalIntegral_eq, zetaMellin_verticalIntegral_eq] at h
  rw [smooth_dirichlet_sum_eq_zeta_mellin hg (c := 3 / 2) (by norm_num) t]
  linear_combination h

theorem ZetaLargeValuePattern.polynomial_eq_general_zeta_mellin (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b)
    {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1) (t : ℝ) :
    (∑ n ∈ P.indices, P.coeff n * dirichletPhase n t) =
      mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I) +
        (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
            mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
              ((c : ℂ) + (u : ℂ) * I) := by
  rw [P.polynomial_eq_cutoff_tsum hactive]
  exact smooth_dirichlet_sum_eq_general_zeta_mellin
    (zetaIntervalCutoffTest a b (P.active_left_pos hactive)) hc hc1 t

/-- Actual-pattern arbitrary-line entry, with one common exact interval
cutoff for all large ordinates and the pole contribution still visible. -/
theorem ZetaLargeValuePattern.exists_general_zeta_mellin_large (P : ZetaLargeValuePattern)
    {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1) :
    ∃ a b : ℕ, P.active = Finset.Icc a b ∧ 1 ≤ a ∧
      ∀ t ∈ P.ordinates, P.V ≤
        ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I) +
          (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
            riemannZeta ((c : ℂ) + ((u + t : ℝ) : ℂ) * I) *
              mellin (fun x => (zetaIntervalCutoff a b x : ℂ))
                ((c : ℂ) + (u : ℂ) * I)‖ := by
  obtain ⟨a, b, hactive⟩ := P.active_isInterval
  refine ⟨a, b, hactive, P.active_left_pos hactive, ?_⟩
  intro t ht
  rw [← P.polynomial_eq_general_zeta_mellin hactive hc hc1 t]
  exact P.large t ht


end TaoTrudgianYang2025

