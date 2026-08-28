import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RiemannZeta.GuthMaynard.LargeValuesAffineHeight

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Section 10: the refined three-frequency estimate

This module joins the literal localized `S₃` object from Proposition 7.2
to the finite affine functional from Proposition 9.1.  In particular, the
functions passed to the affine theorem below are constructed from the
actual smoothed `R`-square rather than introduced as independent inputs.
-/

/-! ## The actual smoothed `R`-square as a Schwartz function -/

/-- The additive-coordinate exponential sum is smooth to every order. -/
theorem contDiff_gmRPhase (W : Finset ℝ) :
    ContDiff ℝ ∞ (gmRPhase W) := by
  unfold gmRPhase
  apply ContDiff.sum
  intro t ht
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)).mul contDiff_const)

/-- The compactly supported source density convolved in equation (7.5).
Writing `gmR` through `gmRPhase` removes its irrelevant value at zero and
makes the removable singularity in the logarithm explicit. -/
noncomputable def gmCubicRWeightFunction (W : Finset ℝ) (u : ℝ) : ℝ :=
  gmCubicRatioBump u * ‖gmRPhase W (Real.log u)‖ ^ 2

theorem gmCubicRWeightFunction_eq
    (W : Finset ℝ) {u : ℝ} (hu : 0 < u) :
    gmCubicRWeightFunction W u = gmCubicRatioBump u * ‖gmR W u‖ ^ 2 := by
  unfold gmCubicRWeightFunction
  rw [gmR_eq_gmRPhase_log hu.ne']
  rw [abs_of_pos hu]

theorem contDiff_gmCubicRWeightFunction (W : Finset ℝ) :
    ContDiff ℝ ∞ (gmCubicRWeightFunction W) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    have hzero : gmCubicRWeightFunction W =ᶠ[nhds 0] 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)] with x hx
      have hnot : x ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
        intro hmem
        exact (not_le_of_gt hx) hmem.1
      simp [gmCubicRWeightFunction,
        gmCubicRatioBump_eq_zero_of_not_mem_Icc hnot]
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hlog : ContDiffAt ℝ ∞ Real.log u := Real.contDiffAt_log.2 hu
    have hphase : ContDiffAt ℝ ∞ (fun x : ℝ => gmRPhase W (Real.log x)) u :=
      (contDiff_gmRPhase W).contDiffAt.comp u hlog
    exact gmCubicRatioBump.contDiff.contDiffAt.mul (hphase.norm_sq ℂ)

theorem hasCompactSupport_gmCubicRWeightFunction (W : Finset ℝ) :
    HasCompactSupport (gmCubicRWeightFunction W) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 8 : ℝ) (33 / 8)))
  intro u hu
  simp only [gmCubicRWeightFunction,
    gmCubicRatioBump_eq_zero_of_not_mem_Icc hu, zero_mul]

/-- Schwartz realization of the compact source density in (7.5). -/
noncomputable def gmCubicRWeightSchwartz (W : Finset ℝ) : SchwartzMap ℝ ℝ :=
  (hasCompactSupport_gmCubicRWeightFunction W).toSchwartzMap
    (contDiff_gmCubicRWeightFunction W)

@[simp]
theorem gmCubicRWeightSchwartz_apply (W : Finset ℝ) (u : ℝ) :
    gmCubicRWeightSchwartz W u = gmCubicRWeightFunction W u := rfl

theorem gmCubicRWeightSchwartz_nonneg (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicRWeightSchwartz W u := by
  rw [gmCubicRWeightSchwartz_apply]
  unfold gmCubicRWeightFunction
  exact mul_nonneg (gmCubicRatioBump_nonneg u) (sq_nonneg _)

/-- The literal equation-(7.5) smoother, now retained as a real Schwartz
map.  Its convolution scale is the physical `NM/(2T^η)` scale. -/
noncomputable def gmCubicSmoothedRSqSchwartz
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) : SchwartzMap ℝ ℝ :=
  gmAffineTildeSchwartz (gmCubicSmoothingScale η T N M) hB
    (gmCubicRWeightSchwartz W)

theorem gmCubicSmoothedRSqSchwartz_apply
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (v : ℝ) :
    gmCubicSmoothedRSqSchwartz η T N M W hB v =
      gmCubicSmoothedRSq η T N M W v := by
  rw [gmCubicSmoothedRSqSchwartz, gmAffineTildeSchwartz_apply_sub]
  unfold gmCubicSmoothedRSq gmCubicSmoothedRIntegrand
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
  · have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
    rw [gmCubicRWeightSchwartz_apply, gmCubicRWeightFunction_eq W hupos]
    ring
  · rw [gmCubicRWeightSchwartz_apply]
    simp only [gmCubicRWeightFunction,
      gmCubicRatioBump_eq_zero_of_not_mem_Icc hu, zero_mul, mul_zero]

theorem gmCubicSmoothedRSqSchwartz_nonneg
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (v : ℝ) :
    0 ≤ gmCubicSmoothedRSqSchwartz η T N M W hB v := by
  rw [gmCubicSmoothedRSqSchwartz_apply]
  exact gmCubicSmoothedRSq_nonneg W v hB.le

/-! ## The source-facing compact window from Proposition 10.1 -/

/-- A fixed cutoff equal to one on the complete `v₁ ∈ [1/2,2]`
integration range and supported in `(1/4,9/4)`.  The wider outer support
is forced by smoothness; using `[1/2,2]` itself as the support envelope
would silently discard endpoint neighbourhoods. -/
noncomputable def gmCubicAffineWindow : ContDiffBump (5 / 4 : ℝ) :=
  ⟨3 / 4, 1, by norm_num, by norm_num⟩

theorem gmCubicAffineWindow_one {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    gmCubicAffineWindow u = 1 := by
  apply gmCubicAffineWindow.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |u - 5 / 4| ≤ 3 / 4
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

theorem gmCubicAffineWindow_nonneg (u : ℝ) :
    0 ≤ gmCubicAffineWindow u := gmCubicAffineWindow.nonneg

theorem gmCubicAffineWindow_eq_zero_of_not_mem_Icc
    {u : ℝ} (hu : u ∉ Set.Icc (1 / 4 : ℝ) (9 / 4)) :
    gmCubicAffineWindow u = 0 := by
  by_contra hne
  have hsupp : u ∈ Function.support gmCubicAffineWindow := hne
  rw [gmCubicAffineWindow.support_eq, Metric.mem_ball, Real.dist_eq] at hsupp
  change |u - 5 / 4| < 1 at hsupp
  apply hu
  rw [Set.mem_Icc]
  rcases abs_lt.mp hsupp with ⟨hleft, hright⟩
  constructor <;> linarith

/-- The actual Proposition 10.1 affine input
`ψ₁(v) |R_tilde(v)|²`, constructed from the literal equation-(7.5)
smoother. -/
noncomputable def gmCubicAffineSourceFunction
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (u : ℝ) : ℝ :=
  gmCubicAffineWindow u * gmCubicSmoothedRSqSchwartz η T N M W hB u

theorem contDiff_gmCubicAffineSourceFunction
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    ContDiff ℝ ∞ (gmCubicAffineSourceFunction η T N M W hB) := by
  exact gmCubicAffineWindow.contDiff.mul
    ((gmCubicSmoothedRSqSchwartz η T N M W hB).smooth ⊤)

theorem hasCompactSupport_gmCubicAffineSourceFunction
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    HasCompactSupport (gmCubicAffineSourceFunction η T N M W hB) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 4 : ℝ) (9 / 4)))
  intro u hu
  simp only [gmCubicAffineSourceFunction,
    gmCubicAffineWindow_eq_zero_of_not_mem_Icc hu, zero_mul]

/-- Schwartz realization of the exact Section 10 affine input. -/
noncomputable def gmCubicAffineSourceSchwartz
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) : SchwartzMap ℝ ℝ :=
  (hasCompactSupport_gmCubicAffineSourceFunction η T N M W hB).toSchwartzMap
    (contDiff_gmCubicAffineSourceFunction η T N M W hB)

@[simp]
theorem gmCubicAffineSourceSchwartz_apply
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (u : ℝ) :
    gmCubicAffineSourceSchwartz η T N M W hB u =
      gmCubicAffineWindow u * gmCubicSmoothedRSq η T N M W u := by
  change gmCubicAffineSourceFunction η T N M W hB u = _
  rw [gmCubicAffineSourceFunction, gmCubicSmoothedRSqSchwartz_apply]

theorem gmCubicAffineSourceSchwartz_nonneg
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (u : ℝ) :
    0 ≤ gmCubicAffineSourceSchwartz η T N M W hB u := by
  rw [gmCubicAffineSourceSchwartz_apply]
  exact mul_nonneg (gmCubicAffineWindow_nonneg u)
    (gmCubicSmoothedRSq_nonneg W u hB.le)

theorem gmCubicSmoothedRSq_le_affineSource_on_sourceInterval
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M)
    {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    gmCubicSmoothedRSq η T N M W u ≤
      gmCubicAffineSourceSchwartz η T N M W hB u := by
  rw [gmCubicAffineSourceSchwartz_apply, gmCubicAffineWindow_one hu, one_mul]

theorem gmCubicAffineSourceSchwartz_supportedOn
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4)
      (gmCubicAffineSourceSchwartz η T N M W hB) := by
  intro u hu
  rw [gmCubicAffineSourceSchwartz_apply,
    gmCubicAffineWindow_eq_zero_of_not_mem_Icc hu, zero_mul]

/-! ## The height-uniform Lemma 8.4 profile -/

/-- On the physical interval `[0,T]`, the additive exponential sum stays
close to its value at the origin on a `1/T` neighbourhood.  This is the
elementary coherence estimate used for the positive source-mass lower
bound in Lemma 8.4. -/
theorem norm_gmRPhase_sub_card_le
    {T : ℝ} {W : Finset ℝ} (hW : InBaseInterval T W) (x : ℝ) :
    ‖gmRPhase W x - (W.card : ℂ)‖ ≤ (W.card : ℝ) * T * |x| := by
  unfold gmRPhase
  rw [show (W.card : ℂ) = ∑ _t ∈ W, (1 : ℂ) by simp]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ t ∈ W,
        (Complex.exp (((t * x : ℝ) : ℂ) * I) - 1)‖ ≤
      ∑ t ∈ W, ‖Complex.exp (((t * x : ℝ) : ℂ) * I) - 1‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _t ∈ W, T * |x| := by
      apply Finset.sum_le_sum
      intro t ht
      have htI := hW t ht
      have hphase :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * I) - 1‖ ≤ |t * x| := by
        have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
        simpa [mul_comm] using h
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * I) - 1‖ ≤ |t * x| := hphase
        _ = |t| * |x| := abs_mul t x
        _ ≤ T * |x| := by
          rw [abs_of_nonneg htI.1]
          exact mul_le_mul_of_nonneg_right htI.2 (abs_nonneg x)
    _ = (W.card : ℝ) * T * |x| := by simp [mul_assoc]

theorem three_fourths_card_le_norm_gmRPhase
    {T : ℝ} {W : Finset ℝ} (hW : InBaseInterval T W) {x : ℝ}
    (hx : T * |x| ≤ 1 / 4) :
    (3 / 4 : ℝ) * W.card ≤ ‖gmRPhase W x‖ := by
  have herr := norm_gmRPhase_sub_card_le hW x
  have htri :
      ‖(W.card : ℂ)‖ ≤
        ‖gmRPhase W x - (W.card : ℂ)‖ + ‖gmRPhase W x‖ := by
    calc
      ‖(W.card : ℂ)‖ =
          ‖((W.card : ℂ) - gmRPhase W x) + gmRPhase W x‖ := by
            congr 1
            ring
      _ ≤ _ := norm_add_le _ _
      _ = ‖gmRPhase W x - (W.card : ℂ)‖ + ‖gmRPhase W x‖ := by
        rw [show (W.card : ℂ) - gmRPhase W x =
          -(gmRPhase W x - (W.card : ℂ)) by ring, norm_neg]
  have hcard : 0 ≤ (W.card : ℝ) := by positivity
  have herr' :
      ‖gmRPhase W x - (W.card : ℂ)‖ ≤ (W.card : ℝ) / 4 := by
    calc
      _ ≤ (W.card : ℝ) * T * |x| := herr
      _ ≤ (W.card : ℝ) * (1 / 4) :=
        by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hx hcard
      _ = (W.card : ℝ) / 4 := by ring
  rw [Complex.norm_natCast] at htri
  linarith

/-- A real logarithm is Lipschitz with constant two on `[1/2,3/2]`.
The explicit elementary form is convenient for the source mass interval. -/
theorem abs_log_le_two_mul_abs_sub_one
    {u : ℝ} (huLower : 1 / 2 ≤ u) :
    |Real.log u| ≤ 2 * |u - 1| := by
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huLower
  by_cases huOne : 1 ≤ u
  · rw [abs_of_nonneg (Real.log_nonneg huOne), abs_of_nonneg (sub_nonneg.mpr huOne)]
    have hlog := Real.log_le_sub_one_of_pos huPos
    linarith
  · have huLe : u ≤ 1 := le_of_not_ge huOne
    rw [abs_of_nonpos (Real.log_nonpos huPos.le huLe),
      abs_of_nonpos (sub_nonpos.mpr huLe)]
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr huPos)
    rw [Real.log_inv] at hlogInv
    have huInv : u⁻¹ - 1 = (1 - u) / u := by field_simp [huPos.ne']
    rw [huInv] at hlogInv
    have hdiv : (1 - u) / u ≤ 2 * (1 - u) := by
      rw [div_le_iff₀ huPos]
      nlinarith
    linarith

noncomputable def gmCubicCoherenceRadius (T : ℝ) : ℝ := 1 / (16 * T)

theorem gmCubicCoherenceRadius_pos {T : ℝ} (hT : 0 < T) :
    0 < gmCubicCoherenceRadius T := by
  unfold gmCubicCoherenceRadius
  positivity

theorem norm_gmR_ge_three_fourths_card_on_coherenceInterval
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W)
    {u : ℝ}
    (hu : u ∈ Set.Icc (1 - gmCubicCoherenceRadius T)
      (1 + gmCubicCoherenceRadius T)) :
    (3 / 4 : ℝ) * W.card ≤ ‖gmR W u‖ := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hrPos : 0 < gmCubicCoherenceRadius T :=
    gmCubicCoherenceRadius_pos hTpos
  have hrUpper : gmCubicCoherenceRadius T ≤ 1 / 16 := by
    unfold gmCubicCoherenceRadius
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * T)]
    nlinarith
  have huLower : 1 / 2 ≤ u := by linarith [hu.1]
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huLower
  have huDist : |u - 1| ≤ gmCubicCoherenceRadius T := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hlog := abs_log_le_two_mul_abs_sub_one huLower
  have hscale : T * |Real.log u| ≤ 1 / 4 := by
    calc
      T * |Real.log u| ≤ T * (2 * |u - 1|) :=
        mul_le_mul_of_nonneg_left hlog hTpos.le
      _ ≤ T * (2 * gmCubicCoherenceRadius T) := by gcongr
      _ = 1 / 8 := by
        unfold gmCubicCoherenceRadius
        field_simp [hTpos.ne']
        norm_num
      _ ≤ 1 / 4 := by norm_num
  rw [gmR_eq_gmRPhase_log huPos.ne', abs_of_pos huPos]
  exact three_fourths_card_le_norm_gmRPhase hW hscale

theorem gmCubicRWeightSchwartz_ge_card_sq_half_on_coherenceInterval
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W)
    {u : ℝ}
    (hu : u ∈ Set.Icc (1 - gmCubicCoherenceRadius T)
      (1 + gmCubicCoherenceRadius T)) :
    (W.card : ℝ) ^ 2 / 2 ≤ gmCubicRWeightSchwartz W u := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hrUpper : gmCubicCoherenceRadius T ≤ 1 / 16 := by
    unfold gmCubicCoherenceRadius
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * T)]
    nlinarith
  have huRatio : u ∈ Set.Icc (1 / 4 : ℝ) 4 := by
    constructor <;> linarith [hu.1, hu.2]
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huRatio.1
  have hnorm :=
    norm_gmR_ge_three_fourths_card_on_coherenceInterval hT hW hu
  rw [gmCubicRWeightSchwartz_apply, gmCubicRWeightFunction_eq W huPos,
    gmCubicRatioBump_one huRatio, one_mul]
  have hcard : 0 ≤ (W.card : ℝ) := by positivity
  have hsquare := pow_le_pow_left₀ (mul_nonneg (by norm_num) hcard) hnorm 2
  nlinarith [sq_nonneg ((W.card : ℝ) / 4)]

/-- Quantitative positivity in Lemma 8.4.  The compact Mellin source has
mass at least `|W|²/(16T)`, uniformly in the separated set. -/
theorem card_sq_div_sixteen_mul_le_integral_gmCubicRWeightSchwartz
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 / (16 * T) ≤
      ∫ u : ℝ, gmCubicRWeightSchwartz W u := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let I : Set ℝ := Set.Icc (1 - gmCubicCoherenceRadius T)
    (1 + gmCubicCoherenceRadius T)
  have hconstInt : IntegrableOn (fun _u : ℝ => (W.card : ℝ) ^ 2 / 2) I :=
    MeasureTheory.integrableOn_const
      (hs := ne_of_lt (isCompact_Icc.measure_lt_top))
  have hsourceInt : IntegrableOn (fun u : ℝ => gmCubicRWeightSchwartz W u) I :=
    (gmCubicRWeightSchwartz W).integrable.integrableOn
  have hmono :
      (∫ _u : ℝ in I, (W.card : ℝ) ^ 2 / 2) ≤
        ∫ u : ℝ in I, gmCubicRWeightSchwartz W u := by
    apply MeasureTheory.integral_mono_ae hconstInt hsourceInt
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact gmCubicRWeightSchwartz_ge_card_sq_half_on_coherenceInterval hT hW hu
  have hrestrict :
      (∫ u : ℝ in I, gmCubicRWeightSchwartz W u) ≤
        ∫ u : ℝ, gmCubicRWeightSchwartz W u := by
    exact setIntegral_le_integral_of_nonneg _
      (gmCubicRWeightSchwartz W).integrable
      (gmCubicRWeightSchwartz_nonneg W) I
  calc
    (W.card : ℝ) ^ 2 / (16 * T) =
        ∫ _u : ℝ in I, (W.card : ℝ) ^ 2 / 2 := by
      rw [MeasureTheory.setIntegral_const]
      change (W.card : ℝ) ^ 2 / (16 * T) =
        volume.real I * ((W.card : ℝ) ^ 2 / 2)
      rw [show volume.real I = 2 * gmCubicCoherenceRadius T by
        dsimp only [I]
        rw [Real.volume_real_Icc_of_le (by
          linarith [gmCubicCoherenceRadius_pos hTpos])]
        ring]
      unfold gmCubicCoherenceRadius
      field_simp [hTpos.ne']
    _ ≤ ∫ u : ℝ in I, gmCubicRWeightSchwartz W u := hmono
    _ ≤ ∫ u : ℝ, gmCubicRWeightSchwartz W u := hrestrict

/-! ### Uniform derivatives of the compact Mellin source -/

noncomputable def gmCubicRatioBumpComplexFunction (u : ℝ) : ℂ :=
  gmCubicRatioBump u

theorem contDiff_gmCubicRatioBumpComplexFunction :
    ContDiff ℝ ∞ gmCubicRatioBumpComplexFunction := by
  exact Complex.ofRealCLM.contDiff.comp gmCubicRatioBump.contDiff

theorem hasCompactSupport_gmCubicRatioBumpComplexFunction :
    HasCompactSupport gmCubicRatioBumpComplexFunction := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 8 : ℝ) (33 / 8)))
  intro u hu
  simp [gmCubicRatioBumpComplexFunction,
    gmCubicRatioBump_eq_zero_of_not_mem_Icc hu]

noncomputable def gmCubicRatioBumpComplexSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_gmCubicRatioBumpComplexFunction.toSchwartzMap
    contDiff_gmCubicRatioBumpComplexFunction

@[simp]
theorem gmCubicRatioBumpComplexSchwartz_apply (u : ℝ) :
    gmCubicRatioBumpComplexSchwartz u = gmCubicRatioBump u := rfl

noncomputable def gmCubicPairMellinAtom (d u : ℝ) : ℂ :=
  gmCubicRatioBumpComplexFunction u * (u : ℂ) ^ ((d : ℂ) * I)

theorem contDiffAt_ofReal_cpow_mul_I_public
    (d : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) =ᶠ[nhds u]
        fun y : ℝ => Complex.exp ((((d * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hu] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [← Complex.ofReal_log hy.le]
    congr 1
    push_cast
    ring
  have hExp : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((((d * Real.log y : ℝ) : ℂ) * I))) u := by
    have hReal : ContDiffAt ℝ n (fun y : ℝ => d * Real.log y) u :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hu.ne')
    have hComplex : ContDiffAt ℝ n
        (fun y : ℝ => ((d * Real.log y : ℝ) : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u hReal
    exact (hComplex.mul contDiffAt_const).cexp
  exact hExp.congr_of_eventuallyEq hEq

theorem contDiff_gmCubicPairMellinAtom (d : ℝ) :
    ContDiff ℝ ∞ (gmCubicPairMellinAtom d) := by
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : 0 < u
  · exact
      (contDiff_gmCubicRatioBumpComplexFunction.of_le
        (by exact_mod_cast le_top)).contDiffAt.mul
        (contDiffAt_ofReal_cpow_mul_I_public d n hu)
  · have hzero : gmCubicPairMellinAtom d =ᶠ[nhds u] 0 := by
      have hu' : u < 1 / 8 := (le_of_not_gt hu).trans_lt (by norm_num)
      filter_upwards [Iio_mem_nhds hu'] with y hy
      have hnot : y ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
        intro hmem
        exact (not_lt_of_ge hmem.1) hy
      simp [gmCubicPairMellinAtom, gmCubicRatioBumpComplexFunction,
        gmCubicRatioBump_eq_zero_of_not_mem_Icc hnot]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem norm_iteratedDeriv_ofReal_cpow_mul_I_le_eight
    (d : ℝ) (n : ℕ) {u : ℝ} (hu : 1 / 8 ≤ u) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u‖ ≤
      8 ^ n * (|d| + n) ^ n := by
  have huPos : 0 < u := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hu
  rw [iteratedDeriv_ofReal_cpow ((d : ℂ) * I) n huPos, norm_mul]
  have hcoeff := norm_gmCpowDerivativeCoeff_le ((d : ℂ) * I) n
  have hpow : ‖(u : ℂ) ^ ((d : ℂ) * I - n)‖ ≤ 8 ^ n := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos]
    have hre : (((d : ℂ) * I - n).re) = -(n : ℝ) := by simp
    rw [hre]
    have hmono : u ^ (-(n : ℝ)) ≤ (1 / 8 : ℝ) ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hu
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    calc
      u ^ (-(n : ℝ)) ≤ (1 / 8 : ℝ) ^ (-(n : ℝ)) := hmono
      _ = 8 ^ n := by
        rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
        norm_num
  calc
    ‖gmCpowDerivativeCoeff ((d : ℂ) * I) n‖ *
          ‖(u : ℂ) ^ ((d : ℂ) * I - n)‖ ≤
        (‖((d : ℂ) * I)‖ + n) ^ n * 8 ^ n :=
      mul_le_mul hcoeff hpow (norm_nonneg _) (by positivity)
    _ = 8 ^ n * (|d| + n) ^ n := by
      simp [Real.norm_eq_abs]
      ring

theorem gmCubicMellinDerivativePower_le
    (d : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|d| + k) ^ k ≤
      (n + 1 : ℝ) ^ n * (1 + |d|) ^ n := by
  let B : ℝ := (n + 1) * (1 + |d|)
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    nlinarith [abs_nonneg d, (show (0 : ℝ) ≤ n by positivity)]
  have hbase : |d| + k ≤ B := by
    dsimp only [B]
    have hkReal : (k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith [abs_nonneg d, (show (0 : ℝ) ≤ n by positivity)]
  calc
    (|d| + k) ^ k ≤ B ^ k := pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ B ^ n := pow_le_pow_right₀ hBOne hkn
    _ = (n + 1 : ℝ) ^ n * (1 + |d|) ^ n := by
      dsimp only [B]
      rw [mul_pow]

noncomputable def gmCubicPairMellinDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i gmCubicRatioBumpComplexSchwartz *
      8 ^ (n - i) * (n + 1 : ℝ) ^ n

theorem gmCubicPairMellinDerivativeConstant_nonneg (n : ℕ) :
    0 ≤ gmCubicPairMellinDerivativeConstant n := by
  unfold gmCubicPairMellinDerivativeConstant
  positivity

theorem norm_iteratedDeriv_gmCubicPairMellinAtom_le
    (n : ℕ) (d u : ℝ) :
    ‖iteratedDeriv n (gmCubicPairMellinAtom d) u‖ ≤
      gmCubicPairMellinDerivativeConstant n * (1 + |d|) ^ n := by
  by_cases huLow : u < 1 / 8
  · have hzero : gmCubicPairMellinAtom d =ᶠ[nhds u] 0 := by
      filter_upwards [Iio_mem_nhds huLow] with y hy
      have hnot : y ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
        intro hmem
        exact (not_lt_of_ge hmem.1) hy
      simp [gmCubicPairMellinAtom, gmCubicRatioBumpComplexFunction,
        gmCubicRatioBump_eq_zero_of_not_mem_Icc hnot]
    rw [hzero.iteratedDeriv_eq]
    simpa using mul_nonneg (gmCubicPairMellinDerivativeConstant_nonneg n)
      (by positivity : 0 ≤ (1 + |d|) ^ n)
  by_cases huHigh : 33 / 8 < u
  · have hzero : gmCubicPairMellinAtom d =ᶠ[nhds u] 0 := by
      filter_upwards [Ioi_mem_nhds huHigh] with y hy
      have hnot : y ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
        intro hmem
        exact (not_lt_of_ge hmem.2) hy
      simp [gmCubicPairMellinAtom, gmCubicRatioBumpComplexFunction,
        gmCubicRatioBump_eq_zero_of_not_mem_Icc hnot]
    rw [hzero.iteratedDeriv_eq]
    simpa using mul_nonneg (gmCubicPairMellinDerivativeConstant_nonneg n)
      (by positivity : 0 ≤ (1 + |d|) ^ n)
  have huIcc : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8) :=
    ⟨le_of_not_gt huLow, le_of_not_gt huHigh⟩
  have huPos : 0 < u := (by norm_num : (0 : ℝ) < 1 / 8).trans_le huIcc.1
  have hbumpSmooth : ContDiffAt ℝ n gmCubicRatioBumpComplexFunction u :=
    contDiff_gmCubicRatioBumpComplexFunction.contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hphaseSmooth := contDiffAt_ofReal_cpow_mul_I_public d n huPos
  unfold gmCubicPairMellinAtom
  change ‖iteratedDeriv n
      (gmCubicRatioBumpComplexFunction *
        fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u‖ ≤ _
  rw [iteratedDeriv_mul hbumpSmooth hphaseSmooth]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) *
          iteratedDeriv i gmCubicRatioBumpComplexFunction u *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) *
          iteratedDeriv i gmCubicRatioBumpComplexFunction u *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i gmCubicRatioBumpComplexSchwartz *
          8 ^ (n - i) * (n + 1 : ℝ) ^ n) *
          (1 + |d|) ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hbump := SchwartzMap.le_seminorm' ℝ 0 i
        gmCubicRatioBumpComplexSchwartz u
      simp only [pow_zero, one_mul] at hbump
      change ‖iteratedDeriv i gmCubicRatioBumpComplexFunction u‖ ≤ _ at hbump
      have hphase := norm_iteratedDeriv_ofReal_cpow_mul_I_le_eight
        d (n - i) huIcc.1
      have hpower := gmCubicMellinDerivativePower_le d (Nat.sub_le n i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (n.choose i : ℝ) * ‖iteratedDeriv i gmCubicRatioBumpComplexFunction u‖ *
            ‖iteratedDeriv (n - i)
              (fun y : ℝ => (y : ℂ) ^ ((d : ℂ) * I)) u‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i gmCubicRatioBumpComplexSchwartz *
              (8 ^ (n - i) * (|d| + (n - i : ℕ)) ^ (n - i)) := by
            gcongr
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i gmCubicRatioBumpComplexSchwartz *
              (8 ^ (n - i) *
                ((n + 1 : ℝ) ^ n * (1 + |d|) ^ n)) := by
            gcongr
        _ = ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i gmCubicRatioBumpComplexSchwartz *
            8 ^ (n - i) * (n + 1 : ℝ) ^ n) *
              (1 + |d|) ^ n := by ring
    _ = gmCubicPairMellinDerivativeConstant n * (1 + |d|) ^ n := by
      unfold gmCubicPairMellinDerivativeConstant
      rw [Finset.sum_mul]

theorem gmCubicPairMellinAtom_eq_exp
    (d : ℝ) {u : ℝ} (hu : 0 < u) :
    gmCubicPairMellinAtom d u =
      gmCubicRatioBump u *
        Complex.exp ((((d * Real.log u : ℝ) : ℂ) * I)) := by
  unfold gmCubicPairMellinAtom gmCubicRatioBumpComplexFunction
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  rw [← Complex.ofReal_log hu.le]
  congr 2
  push_cast
  ring

/-- The actual compact source in Section 10 is the finite ordered-pair
Mellin sum to which the uniform derivative estimate is applied. -/
theorem gmAffineComplexify_cubicRWeight_eq_pair_sum
    (W : Finset ℝ) :
    (gmAffineComplexify (gmCubicRWeightSchwartz W) : ℝ → ℂ) =
      fun u => ∑ t ∈ W, ∑ s ∈ W, gmCubicPairMellinAtom (t - s) u := by
  funext u
  by_cases hu : 0 < u
  · rw [gmAffineComplexify_apply, gmCubicRWeightSchwartz_apply]
    unfold gmCubicRWeightFunction
    simp_rw [gmCubicPairMellinAtom_eq_exp (hu := hu)]
    change (((gmCubicRatioBump u * ‖gmRPhase W (Real.log u)‖ ^ 2 : ℝ) : ℂ)) = _
    calc
      (((gmCubicRatioBump u * ‖gmRPhase W (Real.log u)‖ ^ 2 : ℝ) : ℂ)) =
          (gmCubicRatioBump u : ℂ) *
            ((‖gmRPhase W (Real.log u)‖ ^ 2 : ℝ) : ℂ) := by
              push_cast
              rfl
      _ = (gmCubicRatioBump u : ℂ) *
            (∑ t ∈ W, ∑ s ∈ W,
              Complex.exp (((((t - s) * Real.log u : ℝ) : ℂ) * I))) := by
          rw [norm_gmRPhase_sq_expand]
      _ = ∑ t ∈ W, ∑ s ∈ W,
            (gmCubicRatioBump u : ℂ) *
              Complex.exp (((((t - s) * Real.log u : ℝ) : ℂ) * I)) := by
          simp only [Finset.mul_sum]
  · have huLow : u < 1 / 8 := (le_of_not_gt hu).trans_lt (by norm_num)
    have hnot : u ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
      intro hmem
      exact (not_lt_of_ge hmem.1) huLow
    rw [gmAffineComplexify_apply, gmCubicRWeightSchwartz_apply]
    simp [gmCubicRWeightFunction, gmCubicPairMellinAtom,
      gmCubicRatioBumpComplexFunction,
      gmCubicRatioBump_eq_zero_of_not_mem_Icc hnot]

theorem norm_iteratedDeriv_gmAffineComplexify_cubicRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ ≤
      gmCubicPairMellinDerivativeConstant n * (2 * T) ^ n * W.card ^ 2 := by
  have hsmoothInner (t : ℝ) :
      ContDiff ℝ ∞ (fun y : ℝ => ∑ s ∈ W,
        gmCubicPairMellinAtom (t - s) y) := by
    apply ContDiff.sum
    intro s hs
    exact contDiff_gmCubicPairMellinAtom (t - s)
  have hderiv :
      iteratedDeriv n (gmAffineComplexify (gmCubicRWeightSchwartz W)) u =
        ∑ t ∈ W, ∑ s ∈ W,
          iteratedDeriv n (gmCubicPairMellinAtom (t - s)) u := by
    rw [gmAffineComplexify_cubicRWeight_eq_pair_sum]
    rw [iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [iteratedDeriv_fun_sum]
      intro s hs
      exact (contDiff_gmCubicPairMellinAtom (t - s)).contDiffAt.of_le
        (by exact_mod_cast le_top)
    · intro t ht
      exact (hsmoothInner t).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [hderiv]
  calc
    ‖∑ t ∈ W, ∑ s ∈ W,
        iteratedDeriv n (gmCubicPairMellinAtom (t - s)) u‖ ≤
        ∑ t ∈ W, ∑ s ∈ W,
          ‖iteratedDeriv n (gmCubicPairMellinAtom (t - s)) u‖ := by
      exact norm_sum_le_of_le W
        (fun t _ => norm_sum_le_of_le W (fun s _ => le_rfl))
    _ ≤ ∑ _t ∈ W, ∑ _s ∈ W,
        gmCubicPairMellinDerivativeConstant n * (2 * T) ^ n := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro s hs
      have htBounds := hW t ht
      have hsBounds := hW s hs
      have hd : |t - s| ≤ T := by
        rw [abs_le]
        constructor <;> linarith [htBounds.1, htBounds.2, hsBounds.1, hsBounds.2]
      have hone : 1 + |t - s| ≤ 2 * T := by linarith
      calc
        ‖iteratedDeriv n (gmCubicPairMellinAtom (t - s)) u‖ ≤
            gmCubicPairMellinDerivativeConstant n * (1 + |t - s|) ^ n :=
          norm_iteratedDeriv_gmCubicPairMellinAtom_le n (t - s) u
        _ ≤ gmCubicPairMellinDerivativeConstant n * (2 * T) ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hone n)
            (gmCubicPairMellinDerivativeConstant_nonneg n)
    _ = gmCubicPairMellinDerivativeConstant n * (2 * T) ^ n * W.card ^ 2 := by
      simp
      ring

theorem integral_norm_iteratedFDeriv_gmAffineComplexify_cubicRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (p : ℕ) :
    (∫ u : ℝ, ‖iteratedFDeriv ℝ p
        (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖) ≤
      4 * (gmCubicPairMellinDerivativeConstant p *
        (2 * T) ^ p * W.card ^ 2) := by
  let f : ℝ → ℝ := fun u => ‖iteratedFDeriv ℝ p
    (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖
  have hfInt : Integrable f := by
    simpa only [f, pow_zero, one_mul] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmAffineComplexify (gmCubicRWeightSchwartz W)) 0 p)
  have hsupport : Function.support f ⊆ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
    intro u hu
    by_contra hnot
    have hout : u < 1 / 8 ∨ 33 / 8 < u := by
      by_cases hlow : u < 1 / 8
      · exact Or.inl hlow
      · exact Or.inr (lt_of_not_ge fun hupp =>
          hnot ⟨le_of_not_gt hlow, hupp⟩)
    have hzero :
        (gmAffineComplexify (gmCubicRWeightSchwartz W) : ℝ → ℂ) =ᶠ[nhds u] 0 := by
      rcases hout with hlow | hhigh
      · filter_upwards [Iio_mem_nhds hlow] with y hy
        have hmem : y ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
          intro hiy
          exact (not_lt_of_ge hiy.1) hy
        simp [gmAffineComplexify_apply, gmCubicRWeightSchwartz_apply,
          gmCubicRWeightFunction,
          gmCubicRatioBump_eq_zero_of_not_mem_Icc hmem]
      · filter_upwards [Ioi_mem_nhds hhigh] with y hy
        have hmem : y ∉ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
          intro hiy
          exact (not_lt_of_ge hiy.2) hy
        simp [gmAffineComplexify_apply, gmCubicRWeightSchwartz_apply,
          gmCubicRWeightFunction,
          gmCubicRatioBump_eq_zero_of_not_mem_Icc hmem]
    apply hu
    dsimp only [f]
    rw [(hzero.iteratedFDeriv ℝ p).eq_of_nhds]
    simp
  have hEq : f = Set.indicator (Set.Icc (1 / 8 : ℝ) (33 / 8)) f := by
    funext u
    by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
    · rw [Set.indicator_of_mem hu]
    · have : f u = 0 := not_ne_iff.mp fun hne => hu (hsupport hne)
      rw [Set.indicator_of_notMem hu, this]
  rw [show (∫ u : ℝ, ‖iteratedFDeriv ℝ p
      (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖) =
      ∫ u : ℝ, f u by rfl]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ u : ℝ in Set.Icc (1 / 8 : ℝ) (33 / 8), f u) ≤
        ∫ _u : ℝ in Set.Icc (1 / 8 : ℝ) (33 / 8),
          gmCubicPairMellinDerivativeConstant p *
            (2 * T) ^ p * W.card ^ 2 := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top :
              volume (Set.Icc (1 / 8 : ℝ) (33 / 8)) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro u hu
        dsimp only [f]
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_gmAffineComplexify_cubicRWeight_le hT hW p u
    _ = 4 * (gmCubicPairMellinDerivativeConstant p *
          (2 * T) ^ p * W.card ^ 2) := by
      norm_num [max_eq_left]

noncomputable def gmCubicRWeightFourierConstant (n : ℕ) : ℝ :=
  2 ^ n * ∑ p ∈ Finset.range (n + 1),
    4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p

theorem gmCubicRWeightFourierConstant_nonneg (n : ℕ) :
    0 ≤ gmCubicRWeightFourierConstant n := by
  unfold gmCubicRWeightFourierConstant
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (by norm_num)
      (gmCubicPairMellinDerivativeConstant_nonneg p)) (by positivity))

theorem pow_mul_norm_fourier_gmCubicRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) (xi : ℝ) :
    |xi| ^ n *
        ‖fourier (gmAffineComplexify (gmCubicRWeightSchwartz W)) xi‖ ≤
      gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun u : ℝ => ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ p
          (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖) := by
    intro k p _hk _hp
    exact SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
      (gmAffineComplexify (gmCubicRWeightSchwartz W)) k p
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := (gmAffineComplexify (gmCubicRWeightSchwartz W) : ℝ → ℂ))
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    ((gmAffineComplexify (gmCubicRWeightSchwartz W)).smooth ⊤) hIntegrable
    (k := 0) (n := n) (by norm_num) (by simp) xi
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero] at hFourier
  have hFourier' :
      |xi| ^ n *
          ‖fourier (gmAffineComplexify (gmCubicRWeightSchwartz W)) xi‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ u : ℝ, ‖iteratedFDeriv ℝ p
            (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ := by
    simpa [Real.norm_eq_abs, SchwartzMap.fourier_coe] using hFourier
  calc
    |xi| ^ n *
        ‖fourier (gmAffineComplexify (gmCubicRWeightSchwartz W)) xi‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ u : ℝ, ‖iteratedFDeriv ℝ p
          (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        (4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
          T ^ n * W.card ^ 2 := by
      gcongr with p hp
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hTpow : T ^ p ≤ T ^ n := pow_le_pow_right₀ hT hpn
      calc
        (∫ u : ℝ, ‖iteratedFDeriv ℝ p
            (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖) ≤
            4 * (gmCubicPairMellinDerivativeConstant p *
              (2 * T) ^ p * W.card ^ 2) :=
          integral_norm_iteratedFDeriv_gmAffineComplexify_cubicRWeight_le
            hT hW p
        _ ≤ (4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
              T ^ n * W.card ^ 2 := by
          have hpow : (2 * T) ^ p ≤ 2 ^ p * T ^ n := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hTpow (by positivity)
          have hcoef : 0 ≤ 4 * gmCubicPairMellinDerivativeConstant p :=
            mul_nonneg (by norm_num)
              (gmCubicPairMellinDerivativeConstant_nonneg p)
          have hcard : 0 ≤ (W.card : ℝ) ^ 2 := by positivity
          calc
            4 * (gmCubicPairMellinDerivativeConstant p *
                (2 * T) ^ p * W.card ^ 2) =
                (4 * gmCubicPairMellinDerivativeConstant p) *
                  (2 * T) ^ p * W.card ^ 2 := by ring
            _ ≤ (4 * gmCubicPairMellinDerivativeConstant p) *
                  (2 ^ p * T ^ n) * W.card ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hcoef) hcard
            _ = (4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
                  T ^ n * W.card ^ 2 := by ring
    _ = gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
      unfold gmCubicRWeightFourierConstant
      calc
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
            (4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
              T ^ n * W.card ^ 2 =
          2 ^ n * ∑ p ∈ Finset.range (n + 1),
            (4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
              (T ^ n * W.card ^ 2) := by
                congr 2
                funext p
                ring
        _ = 2 ^ n *
            ((∑ p ∈ Finset.range (n + 1),
              4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
                (T ^ n * W.card ^ 2)) := by
              rw [Finset.sum_mul]
        _ = (2 ^ n * ∑ p ∈ Finset.range (n + 1),
              4 * gmCubicPairMellinDerivativeConstant p * 2 ^ p) *
                T ^ n * W.card ^ 2 := by ring

theorem seminorm_fourier_gmCubicRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) :
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify (gmCubicRWeightSchwartz W))) ≤
      gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  apply SchwartzMap.seminorm_le_bound' ℝ n 0 _
  · exact mul_nonneg
      (mul_nonneg (gmCubicRWeightFourierConstant_nonneg n) (by positivity))
      (by positivity)
  · intro xi
    rw [iteratedDeriv_zero]
    exact pow_mul_norm_fourier_gmCubicRWeight_le hT hW n xi

theorem card_sq_le_sixteen_mul_T_mul_integral_gmCubicRWeightSchwartz
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 ≤
      16 * T * ∫ u : ℝ, gmCubicRWeightSchwartz W u := by
  have hden : 0 < 16 * T := by positivity
  have hmass :=
    card_sq_div_sixteen_mul_le_integral_gmCubicRWeightSchwartz hT hW
  rw [div_le_iff₀ hden] at hmass
  calc
    (W.card : ℝ) ^ 2 ≤
        (∫ u : ℝ, gmCubicRWeightSchwartz W u) * (16 * T) := hmass
    _ = 16 * T * ∫ u : ℝ, gmCubicRWeightSchwartz W u := by ring

/-! ### The source-faithful pre-smoothing support truncation -/

/-- Fixed Section 10 truncation.  It equals one on `[13/32,67/32]`
and is supported on `[3/8,17/8]`, leaving a `1/16` convolution margin
inside Proposition 9.1's admissible interval `[1/4,9/4]`. -/
noncomputable def gmCubicPreSmoothingWindow : ContDiffBump (5 / 4 : ℝ) :=
  ⟨27 / 32, 7 / 8, by norm_num, by norm_num⟩

theorem gmCubicPreSmoothingWindow_one_wide {u : ℝ}
    (hu : u ∈ Set.Icc (13 / 32 : ℝ) (67 / 32)) :
    gmCubicPreSmoothingWindow u = 1 := by
  apply gmCubicPreSmoothingWindow.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |u - 5 / 4| ≤ 27 / 32
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

theorem gmCubicPreSmoothingWindow_one {u : ℝ}
    (hu : u ∈ Set.Icc (7 / 16 : ℝ) (33 / 16)) :
    gmCubicPreSmoothingWindow u = 1 := by
  apply gmCubicPreSmoothingWindow_one_wide
  constructor <;> linarith [hu.1, hu.2]

theorem gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc
    {u : ℝ} (hu : u ∉ Set.Icc (3 / 8 : ℝ) (17 / 8)) :
    gmCubicPreSmoothingWindow u = 0 := by
  by_contra hne
  have hsupp : u ∈ Function.support gmCubicPreSmoothingWindow := hne
  rw [gmCubicPreSmoothingWindow.support_eq, Metric.mem_ball,
    Real.dist_eq] at hsupp
  change |u - 5 / 4| < 7 / 8 at hsupp
  apply hu
  rw [Set.mem_Icc]
  rcases abs_lt.mp hsupp with ⟨hleft, hright⟩
  constructor <;> linarith

noncomputable def gmCubicPreSmoothingWindowComplexFunction (u : ℝ) : ℂ :=
  gmCubicPreSmoothingWindow u

theorem contDiff_gmCubicPreSmoothingWindowComplexFunction :
    ContDiff ℝ ∞ gmCubicPreSmoothingWindowComplexFunction := by
  exact Complex.ofRealCLM.contDiff.comp gmCubicPreSmoothingWindow.contDiff

theorem hasCompactSupport_gmCubicPreSmoothingWindowComplexFunction :
    HasCompactSupport gmCubicPreSmoothingWindowComplexFunction := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (3 / 8 : ℝ) (17 / 8)))
  intro u hu
  simp [gmCubicPreSmoothingWindowComplexFunction,
    gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc hu]

noncomputable def gmCubicPreSmoothingWindowComplexSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_gmCubicPreSmoothingWindowComplexFunction.toSchwartzMap
    contDiff_gmCubicPreSmoothingWindowComplexFunction

@[simp]
theorem gmCubicPreSmoothingWindowComplexSchwartz_apply (u : ℝ) :
    gmCubicPreSmoothingWindowComplexSchwartz u =
      gmCubicPreSmoothingWindow u := rfl

noncomputable def gmCubicTruncatedRWeightFunction
    (W : Finset ℝ) (u : ℝ) : ℝ :=
  gmCubicPreSmoothingWindow u * gmCubicRWeightSchwartz W u

theorem contDiff_gmCubicTruncatedRWeightFunction (W : Finset ℝ) :
    ContDiff ℝ ∞ (gmCubicTruncatedRWeightFunction W) := by
  exact gmCubicPreSmoothingWindow.contDiff.mul
    ((gmCubicRWeightSchwartz W).smooth ⊤)

theorem hasCompactSupport_gmCubicTruncatedRWeightFunction (W : Finset ℝ) :
    HasCompactSupport (gmCubicTruncatedRWeightFunction W) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (3 / 8 : ℝ) (17 / 8)))
  intro u hu
  simp [gmCubicTruncatedRWeightFunction,
    gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc hu]

noncomputable def gmCubicTruncatedRWeightSchwartz
    (W : Finset ℝ) : SchwartzMap ℝ ℝ :=
  (hasCompactSupport_gmCubicTruncatedRWeightFunction W).toSchwartzMap
    (contDiff_gmCubicTruncatedRWeightFunction W)

@[simp]
theorem gmCubicTruncatedRWeightSchwartz_apply (W : Finset ℝ) (u : ℝ) :
    gmCubicTruncatedRWeightSchwartz W u =
      gmCubicPreSmoothingWindow u * gmCubicRWeightSchwartz W u := rfl

theorem gmCubicTruncatedRWeightSchwartz_nonneg (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicTruncatedRWeightSchwartz W u := by
  rw [gmCubicTruncatedRWeightSchwartz_apply]
  exact mul_nonneg gmCubicPreSmoothingWindow.nonneg
    (gmCubicRWeightSchwartz_nonneg W u)

theorem gmAffineComplexify_truncatedRWeight_eq_mul (W : Finset ℝ) :
    (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W) : ℝ → ℂ) =
      gmCubicPreSmoothingWindowComplexFunction *
        (gmAffineComplexify (gmCubicRWeightSchwartz W) : ℝ → ℂ) := by
  funext u
  rw [gmAffineComplexify_apply, gmCubicTruncatedRWeightSchwartz_apply,
    Pi.mul_apply, gmAffineComplexify_apply]
  unfold gmCubicPreSmoothingWindowComplexFunction
  push_cast
  rfl

noncomputable def gmCubicTruncatedRWeightDerivativeConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i gmCubicPreSmoothingWindowComplexSchwartz *
      gmCubicPairMellinDerivativeConstant (n - i)

theorem gmCubicTruncatedRWeightDerivativeConstant_nonneg (n : ℕ) :
    0 ≤ gmCubicTruncatedRWeightDerivativeConstant n := by
  unfold gmCubicTruncatedRWeightDerivativeConstant
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (gmCubicPairMellinDerivativeConstant_nonneg (n - i))

theorem norm_iteratedDeriv_gmAffineComplexify_truncatedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n
        (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖ ≤
      gmCubicTruncatedRWeightDerivativeConstant n *
        (2 * T) ^ n * W.card ^ 2 := by
  rw [gmAffineComplexify_truncatedRWeight_eq_mul]
  rw [iteratedDeriv_mul
    (contDiff_gmCubicPreSmoothingWindowComplexFunction.contDiffAt.of_le
      (by exact_mod_cast le_top))
    ((gmAffineComplexify (gmCubicRWeightSchwartz W)).smooth ⊤ |>.contDiffAt.of_le
      (by exact_mod_cast le_top))]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) *
          iteratedDeriv i gmCubicPreSmoothingWindowComplexFunction u *
          iteratedDeriv (n - i)
            (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) *
          iteratedDeriv i gmCubicPreSmoothingWindowComplexFunction u *
          iteratedDeriv (n - i)
            (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i
            gmCubicPreSmoothingWindowComplexSchwartz *
          gmCubicPairMellinDerivativeConstant (n - i)) *
            (2 * T) ^ n * W.card ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hwindow := SchwartzMap.le_seminorm' ℝ 0 i
        gmCubicPreSmoothingWindowComplexSchwartz u
      simp only [pow_zero, one_mul] at hwindow
      change ‖iteratedDeriv i gmCubicPreSmoothingWindowComplexFunction u‖ ≤ _
        at hwindow
      have hsource :=
        norm_iteratedDeriv_gmAffineComplexify_cubicRWeight_le
          hT hW (n - i) u
      have hbase : 1 ≤ 2 * T := by linarith
      have hpow : (2 * T) ^ (n - i) ≤ (2 * T) ^ n :=
        pow_le_pow_right₀ hbase (Nat.sub_le n i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (n.choose i : ℝ) *
            ‖iteratedDeriv i gmCubicPreSmoothingWindowComplexFunction u‖ *
            ‖iteratedDeriv (n - i)
              (gmAffineComplexify (gmCubicRWeightSchwartz W)) u‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i
              gmCubicPreSmoothingWindowComplexSchwartz *
            (gmCubicPairMellinDerivativeConstant (n - i) *
              (2 * T) ^ (n - i) * W.card ^ 2) := by gcongr
        _ ≤ ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i
              gmCubicPreSmoothingWindowComplexSchwartz *
            gmCubicPairMellinDerivativeConstant (n - i)) *
              (2 * T) ^ n * W.card ^ 2 := by
          have hcoef : 0 ≤ (n.choose i : ℝ) *
              SchwartzMap.seminorm ℝ 0 i
                gmCubicPreSmoothingWindowComplexSchwartz *
              gmCubicPairMellinDerivativeConstant (n - i) := by
            exact mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (gmCubicPairMellinDerivativeConstant_nonneg (n - i))
          have hcard : 0 ≤ (W.card : ℝ) ^ 2 := by positivity
          calc
            _ = ((n.choose i : ℝ) *
                SchwartzMap.seminorm ℝ 0 i
                  gmCubicPreSmoothingWindowComplexSchwartz *
                gmCubicPairMellinDerivativeConstant (n - i)) *
                  (2 * T) ^ (n - i) * W.card ^ 2 := by ring
            _ ≤ ((n.choose i : ℝ) *
                SchwartzMap.seminorm ℝ 0 i
                  gmCubicPreSmoothingWindowComplexSchwartz *
                gmCubicPairMellinDerivativeConstant (n - i)) *
                  (2 * T) ^ n * W.card ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hcoef) hcard
    _ = gmCubicTruncatedRWeightDerivativeConstant n *
          (2 * T) ^ n * W.card ^ 2 := by
      unfold gmCubicTruncatedRWeightDerivativeConstant
      rw [Finset.sum_mul, Finset.sum_mul]

theorem gmCubicTruncatedRWeightSchwartz_ge_card_sq_half_on_coherenceInterval
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W)
    {u : ℝ}
    (hu : u ∈ Set.Icc (1 - gmCubicCoherenceRadius T)
      (1 + gmCubicCoherenceRadius T)) :
    (W.card : ℝ) ^ 2 / 2 ≤ gmCubicTruncatedRWeightSchwartz W u := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hrUpper : gmCubicCoherenceRadius T ≤ 1 / 16 := by
    unfold gmCubicCoherenceRadius
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * T)]
    nlinarith
  have huInner : u ∈ Set.Icc (7 / 16 : ℝ) (33 / 16) := by
    constructor <;> linarith [hu.1, hu.2]
  rw [gmCubicTruncatedRWeightSchwartz_apply,
    gmCubicPreSmoothingWindow_one huInner, one_mul]
  exact gmCubicRWeightSchwartz_ge_card_sq_half_on_coherenceInterval hT hW hu

theorem card_sq_div_sixteen_mul_le_integral_gmCubicTruncatedRWeightSchwartz
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 / (16 * T) ≤
      ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let I : Set ℝ := Set.Icc (1 - gmCubicCoherenceRadius T)
    (1 + gmCubicCoherenceRadius T)
  have hconstInt : IntegrableOn (fun _u : ℝ => (W.card : ℝ) ^ 2 / 2) I :=
    MeasureTheory.integrableOn_const
      (hs := ne_of_lt (isCompact_Icc.measure_lt_top))
  have hsourceInt :
      IntegrableOn (fun u : ℝ => gmCubicTruncatedRWeightSchwartz W u) I :=
    (gmCubicTruncatedRWeightSchwartz W).integrable.integrableOn
  have hmono :
      (∫ _u : ℝ in I, (W.card : ℝ) ^ 2 / 2) ≤
        ∫ u : ℝ in I, gmCubicTruncatedRWeightSchwartz W u := by
    apply MeasureTheory.integral_mono_ae hconstInt hsourceInt
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact
      gmCubicTruncatedRWeightSchwartz_ge_card_sq_half_on_coherenceInterval
        hT hW hu
  have hrestrict :
      (∫ u : ℝ in I, gmCubicTruncatedRWeightSchwartz W u) ≤
        ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := by
    exact setIntegral_le_integral_of_nonneg _
      (gmCubicTruncatedRWeightSchwartz W).integrable
      (gmCubicTruncatedRWeightSchwartz_nonneg W) I
  calc
    (W.card : ℝ) ^ 2 / (16 * T) =
        ∫ _u : ℝ in I, (W.card : ℝ) ^ 2 / 2 := by
      rw [MeasureTheory.setIntegral_const]
      change (W.card : ℝ) ^ 2 / (16 * T) =
        volume.real I * ((W.card : ℝ) ^ 2 / 2)
      rw [show volume.real I = 2 * gmCubicCoherenceRadius T by
        dsimp only [I]
        rw [Real.volume_real_Icc_of_le (by
          linarith [gmCubicCoherenceRadius_pos hTpos])]
        ring]
      unfold gmCubicCoherenceRadius
      field_simp [hTpos.ne']
    _ ≤ ∫ u : ℝ in I, gmCubicTruncatedRWeightSchwartz W u := hmono
    _ ≤ ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := hrestrict

theorem integral_norm_iteratedFDeriv_gmAffineComplexify_truncatedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (p : ℕ) :
    (∫ u : ℝ, ‖iteratedFDeriv ℝ p
        (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖) ≤
      2 * (gmCubicTruncatedRWeightDerivativeConstant p *
        (2 * T) ^ p * W.card ^ 2) := by
  let f : ℝ → ℝ := fun u => ‖iteratedFDeriv ℝ p
    (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖
  have hfInt : Integrable f := by
    simpa only [f, pow_zero, one_mul] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) 0 p)
  have hsupport : Function.support f ⊆ Set.Icc (3 / 8 : ℝ) (17 / 8) := by
    intro u hu
    by_contra hnot
    have hout : u < 3 / 8 ∨ 17 / 8 < u := by
      by_cases hlow : u < 3 / 8
      · exact Or.inl hlow
      · exact Or.inr (lt_of_not_ge fun hupp =>
          hnot ⟨le_of_not_gt hlow, hupp⟩)
    have hzero :
        (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W) : ℝ → ℂ)
          =ᶠ[nhds u] 0 := by
      rcases hout with hlow | hhigh
      · filter_upwards [Iio_mem_nhds hlow] with y hy
        have hmem : y ∉ Set.Icc (3 / 8 : ℝ) (17 / 8) := by
          intro hiy
          exact (not_lt_of_ge hiy.1) hy
        simp [gmAffineComplexify_apply, gmCubicTruncatedRWeightSchwartz_apply,
          gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc hmem]
      · filter_upwards [Ioi_mem_nhds hhigh] with y hy
        have hmem : y ∉ Set.Icc (3 / 8 : ℝ) (17 / 8) := by
          intro hiy
          exact (not_lt_of_ge hiy.2) hy
        simp [gmAffineComplexify_apply, gmCubicTruncatedRWeightSchwartz_apply,
          gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc hmem]
    apply hu
    dsimp only [f]
    rw [(hzero.iteratedFDeriv ℝ p).eq_of_nhds]
    simp
  have hEq : f = Set.indicator (Set.Icc (3 / 8 : ℝ) (17 / 8)) f := by
    funext u
    by_cases hu : u ∈ Set.Icc (3 / 8 : ℝ) (17 / 8)
    · rw [Set.indicator_of_mem hu]
    · have : f u = 0 := not_ne_iff.mp fun hne => hu (hsupport hne)
      rw [Set.indicator_of_notMem hu, this]
  rw [show (∫ u : ℝ, ‖iteratedFDeriv ℝ p
      (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖) =
      ∫ u : ℝ, f u by rfl]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ u : ℝ in Set.Icc (3 / 8 : ℝ) (17 / 8), f u) ≤
        ∫ _u : ℝ in Set.Icc (3 / 8 : ℝ) (17 / 8),
          gmCubicTruncatedRWeightDerivativeConstant p *
            (2 * T) ^ p * W.card ^ 2 := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top :
              volume (Set.Icc (3 / 8 : ℝ) (17 / 8)) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro u hu
        dsimp only [f]
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_gmAffineComplexify_truncatedRWeight_le
          hT hW p u
    _ = (7 / 4 : ℝ) *
          (gmCubicTruncatedRWeightDerivativeConstant p *
            (2 * T) ^ p * W.card ^ 2) := by
      norm_num [max_eq_left]
    _ ≤ 2 * (gmCubicTruncatedRWeightDerivativeConstant p *
          (2 * T) ^ p * W.card ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (mul_nonneg
          (mul_nonneg
            (gmCubicTruncatedRWeightDerivativeConstant_nonneg p)
            (pow_nonneg (by linarith) p))
          (sq_nonneg (W.card : ℝ)))

noncomputable def gmCubicTruncatedRWeightFourierConstant (n : ℕ) : ℝ :=
  2 ^ n * ∑ p ∈ Finset.range (n + 1),
    2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p

theorem gmCubicTruncatedRWeightFourierConstant_nonneg (n : ℕ) :
    0 ≤ gmCubicTruncatedRWeightFourierConstant n := by
  unfold gmCubicTruncatedRWeightFourierConstant
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (by norm_num)
      (gmCubicTruncatedRWeightDerivativeConstant_nonneg p)) (by positivity))

theorem pow_mul_norm_fourier_gmCubicTruncatedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) (xi : ℝ) :
    |xi| ^ n *
        ‖fourier (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) xi‖ ≤
      gmCubicTruncatedRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun u : ℝ => ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ p
          (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖) := by
    intro k p _hk _hp
    exact SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
      (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) k p
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W) : ℝ → ℂ))
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    ((gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)).smooth ⊤)
    hIntegrable (k := 0) (n := n) (by norm_num) (by simp) xi
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero] at hFourier
  have hFourier' :
      |xi| ^ n *
          ‖fourier (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) xi‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ u : ℝ, ‖iteratedFDeriv ℝ p
            (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖ := by
    simpa [Real.norm_eq_abs, SchwartzMap.fourier_coe] using hFourier
  calc
    |xi| ^ n *
        ‖fourier (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) xi‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ u : ℝ, ‖iteratedFDeriv ℝ p
          (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        (2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
          T ^ n * W.card ^ 2 := by
      gcongr with p hp
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hTpow : T ^ p ≤ T ^ n := pow_le_pow_right₀ hT hpn
      calc
        (∫ u : ℝ, ‖iteratedFDeriv ℝ p
            (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W)) u‖) ≤
            2 * (gmCubicTruncatedRWeightDerivativeConstant p *
              (2 * T) ^ p * W.card ^ 2) :=
          integral_norm_iteratedFDeriv_gmAffineComplexify_truncatedRWeight_le
            hT hW p
        _ ≤ (2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
              T ^ n * W.card ^ 2 := by
          have hpow : (2 * T) ^ p ≤ 2 ^ p * T ^ n := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hTpow (by positivity)
          have hcoef : 0 ≤ 2 * gmCubicTruncatedRWeightDerivativeConstant p :=
            mul_nonneg (by norm_num)
              (gmCubicTruncatedRWeightDerivativeConstant_nonneg p)
          have hcard : 0 ≤ (W.card : ℝ) ^ 2 := by positivity
          calc
            2 * (gmCubicTruncatedRWeightDerivativeConstant p *
                (2 * T) ^ p * W.card ^ 2) =
                (2 * gmCubicTruncatedRWeightDerivativeConstant p) *
                  (2 * T) ^ p * W.card ^ 2 := by ring
            _ ≤ (2 * gmCubicTruncatedRWeightDerivativeConstant p) *
                  (2 ^ p * T ^ n) * W.card ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hcoef) hcard
            _ = (2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
                  T ^ n * W.card ^ 2 := by ring
    _ = gmCubicTruncatedRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
      unfold gmCubicTruncatedRWeightFourierConstant
      calc
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
            (2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
              T ^ n * W.card ^ 2 =
          2 ^ n * ∑ p ∈ Finset.range (n + 1),
            (2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
              (T ^ n * W.card ^ 2) := by
                congr 2
                funext p
                ring
        _ = 2 ^ n *
            ((∑ p ∈ Finset.range (n + 1),
              2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
                (T ^ n * W.card ^ 2)) := by
              rw [Finset.sum_mul]
        _ = (2 ^ n * ∑ p ∈ Finset.range (n + 1),
              2 * gmCubicTruncatedRWeightDerivativeConstant p * 2 ^ p) *
                T ^ n * W.card ^ 2 := by ring

theorem seminorm_fourier_gmCubicTruncatedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) :
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W))) ≤
      gmCubicTruncatedRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  apply SchwartzMap.seminorm_le_bound' ℝ n 0 _
  · exact mul_nonneg
      (mul_nonneg (gmCubicTruncatedRWeightFourierConstant_nonneg n)
        (pow_nonneg (zero_le_one.trans hT) n))
      (sq_nonneg (W.card : ℝ))
  · intro xi
    rw [iteratedDeriv_zero]
    exact pow_mul_norm_fourier_gmCubicTruncatedRWeight_le hT hW n xi

theorem card_sq_le_sixteen_mul_T_mul_integral_gmCubicTruncatedRWeightSchwartz
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 ≤
      16 * T * ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := by
  have hden : 0 < 16 * T := by positivity
  have hmass :=
    card_sq_div_sixteen_mul_le_integral_gmCubicTruncatedRWeightSchwartz hT hW
  rw [div_le_iff₀ hden] at hmass
  calc
    (W.card : ℝ) ^ 2 ≤
        (∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u) * (16 * T) := hmass
    _ = 16 * T * ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := by ring

noncomputable def gmCubicTruncatedHeightProfileConstant
    (_epsilon : ℝ) (n : ℕ) : ℝ :=
  16 * gmCubicTruncatedRWeightFourierConstant n

theorem gmCubicTruncatedHeightProfileConstant_nonneg (epsilon : ℝ) (n : ℕ) :
    0 ≤ gmCubicTruncatedHeightProfileConstant epsilon n := by
  unfold gmCubicTruncatedHeightProfileConstant
  exact mul_nonneg (by norm_num)
    (gmCubicTruncatedRWeightFourierConstant_nonneg n)

theorem gmCubicTruncatedRWeight_heightFourierMassFamilyAtDepth_zero
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W) :
    GMAffineHeightFourierMassFamilyAtDepth T
      gmCubicTruncatedHeightProfileConstant 0
      (gmCubicTruncatedRWeightSchwartz W) := by
  intro epsilon hepsilon n
  unfold GMAffineHeightFourierMassBound
  simp only [pow_zero, one_mul]
  let mass : ℝ := ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u
  have hmass : 0 ≤ mass := by
    dsimp only [mass]
    exact integral_nonneg (gmCubicTruncatedRWeightSchwartz_nonneg W)
  have hcard :=
    card_sq_le_sixteen_mul_T_mul_integral_gmCubicTruncatedRWeightSchwartz
      hT hW
  have hcoef : 0 ≤ gmCubicTruncatedRWeightFourierConstant n * T ^ n :=
    mul_nonneg (gmCubicTruncatedRWeightFourierConstant_nonneg n)
      (pow_nonneg (zero_le_one.trans hT) n)
  have hepsPow : 1 ≤ T ^ epsilon :=
    Real.one_le_rpow hT (le_of_lt hepsilon)
  have hscale : T ^ n * T ≤ T ^ epsilon * T ^ (n + 2) := by
    calc
      T ^ n * T = T ^ (n + 1) := by rw [pow_succ]
      _ ≤ T ^ (n + 2) :=
        pow_le_pow_right₀ hT (Nat.le_succ (n + 1))
      _ ≤ T ^ epsilon * T ^ (n + 2) := by
        exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hT) (n + 2))
          hepsPow
  calc
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify (gmCubicTruncatedRWeightSchwartz W))) ≤
      gmCubicTruncatedRWeightFourierConstant n * T ^ n * W.card ^ 2 :=
        seminorm_fourier_gmCubicTruncatedRWeight_le hT hW n
    _ ≤ gmCubicTruncatedRWeightFourierConstant n * T ^ n *
        (16 * T * mass) := mul_le_mul_of_nonneg_left hcard hcoef
    _ = (16 * gmCubicTruncatedRWeightFourierConstant n) *
        (T ^ n * T) * mass := by ring
    _ ≤ (16 * gmCubicTruncatedRWeightFourierConstant n) *
        (T ^ epsilon * T ^ (n + 2)) * mass := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale
          (mul_nonneg (by norm_num)
            (gmCubicTruncatedRWeightFourierConstant_nonneg n))) hmass
    _ = gmCubicTruncatedHeightProfileConstant epsilon n *
        T ^ epsilon * T ^ (n + 2) *
          ∫ u : ℝ, gmCubicTruncatedRWeightSchwartz W u := by
      unfold gmCubicTruncatedHeightProfileConstant
      dsimp only [mass]
      ring

theorem gmCubicTruncatedRWeight_supportedOn (W : Finset ℝ) :
    GMAffineSupportedOn (3 / 8 : ℝ) (17 / 8)
      (gmCubicTruncatedRWeightSchwartz W) := by
  intro u hu
  rw [gmCubicTruncatedRWeightSchwartz_apply,
    gmCubicPreSmoothingWindow_eq_zero_of_not_mem_Icc hu, zero_mul]

/-- The actual one-time Section 7 smoother applied to the faithfully
truncated source.  Proposition 9.1 treats this as its depth-zero input;
its later adaptive smoothings are tracked separately. -/
noncomputable def gmCubicNativeAffineSourceSchwartz
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) : SchwartzMap ℝ ℝ :=
  gmAffineTildeSchwartz B hB (gmCubicTruncatedRWeightSchwartz W)

theorem gmCubicNativeAffineSourceSchwartz_nonneg
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicNativeAffineSourceSchwartz B hB W u := by
  exact gmAffineTildeSchwartz_nonneg B hB
    (gmCubicTruncatedRWeightSchwartz W)
    (gmCubicTruncatedRWeightSchwartz_nonneg W) u

noncomputable def gmCubicNativeHeightProfileConstant
    (_epsilon : ℝ) (n : ℕ) : ℝ :=
  32 * gmCubicTruncatedRWeightFourierConstant n

theorem gmCubicNativeHeightProfileConstant_nonneg (epsilon : ℝ) (n : ℕ) :
    0 ≤ gmCubicNativeHeightProfileConstant epsilon n := by
  unfold gmCubicNativeHeightProfileConstant
  exact mul_nonneg (by norm_num)
    (gmCubicTruncatedRWeightFourierConstant_nonneg n)

theorem gmCubicNativeAffineSource_heightFourierMassFamilyAtDepth_zero
    {T B : ℝ} (hT : 1 ≤ T) (hB : 0 < B)
    {W : Finset ℝ} (hW : InBaseInterval T W) :
    GMAffineHeightFourierMassFamilyAtDepth T
      gmCubicNativeHeightProfileConstant 0
      (gmCubicNativeAffineSourceSchwartz B hB W) := by
  intro epsilon hepsilon n
  have hbase :=
    gmCubicTruncatedRWeight_heightFourierMassFamilyAtDepth_zero
      hT hW epsilon hepsilon n
  simp only [pow_zero, one_mul] at hbase ⊢
  have hsmooth := gmAffineTildeSchwartz_heightFourierMassBound
    (show 0 ≤ T from zero_le_one.trans hT) hB
    (gmCubicTruncatedHeightProfileConstant_nonneg epsilon n) n
    (gmCubicTruncatedRWeightSchwartz W)
    (gmCubicTruncatedRWeightSchwartz_nonneg W) hbase
  unfold gmCubicNativeAffineSourceSchwartz
  convert hsmooth using 1
  unfold gmCubicNativeHeightProfileConstant
    gmCubicTruncatedHeightProfileConstant
  ring

theorem gmCubicNativeAffineSource_supportedOn
    {B : ℝ} (hB : 0 < B) (hB32 : 32 ≤ B) (W : Finset ℝ) :
    GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4)
      (gmCubicNativeAffineSourceSchwartz B hB W) := by
  have hradius : 2 / B ≤ 1 / 16 := by
    rw [div_le_iff₀ hB]
    linarith
  have hsupp := gmAffineTildeSchwartz_supportedOn hB
    (gmCubicTruncatedRWeightSchwartz W)
    (gmCubicTruncatedRWeight_supportedOn (W := W))
  unfold gmCubicNativeAffineSourceSchwartz
  exact hsupp.mono (by linarith) (by linarith)

/-- On the enlarged active-cancellation interval `[15/32,65/32]`, a
smoothing scale at least `32` cannot see the pre-smoothing cutoff boundary.
This is the interval forced by a nonempty Section 7 cancellation slice. -/
theorem gmCubicNativeAffineSource_eq_original_on_activeInterval
    {B : ℝ} (hB : 0 < B) (hB32 : 32 ≤ B) (W : Finset ℝ)
    {u : ℝ} (hu : u ∈ Set.Icc (15 / 32 : ℝ) (65 / 32)) :
    gmCubicNativeAffineSourceSchwartz B hB W u =
      gmAffineTildeSchwartz B hB (gmCubicRWeightSchwartz W) u := by
  unfold gmCubicNativeAffineSourceSchwartz
  rw [gmAffineTildeSchwartz_apply_sub,
    gmAffineTildeSchwartz_apply_sub]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hbump : gmCubicLocalBump (B * (u - v)) = 0
  · simp [hbump]
  · have hBdist : |B * (u - v)| < 2 := by
      exact lt_of_not_ge fun hge =>
        hbump (gmCubicLocalBump_eq_zero_of_two_le_abs hge)
    have hdist : |u - v| < 2 / B := by
      rw [abs_mul, abs_of_pos hB] at hBdist
      exact (lt_div_iff₀ hB).mpr (by simpa only [mul_comm] using hBdist)
    have hradius : 2 / B ≤ 1 / 16 := by
      rw [div_le_iff₀ hB]
      linarith
    have hvInner : v ∈ Set.Icc (13 / 32 : ℝ) (67 / 32) := by
      rw [abs_lt] at hdist
      constructor <;> linarith [hu.1, hu.2]
    rw [gmCubicTruncatedRWeightSchwartz_apply,
      gmCubicPreSmoothingWindow_one_wide hvInner, one_mul]

/-- Source-interval specialization of the active-cancellation identity. -/
theorem gmCubicNativeAffineSource_eq_original_on_sourceInterval
    {B : ℝ} (hB : 0 < B) (hB32 : 32 ≤ B) (W : Finset ℝ)
    {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    gmCubicNativeAffineSourceSchwartz B hB W u =
      gmAffineTildeSchwartz B hB (gmCubicRWeightSchwartz W) u := by
  apply gmCubicNativeAffineSource_eq_original_on_activeInterval hB hB32 W
  constructor <;> linarith [hu.1, hu.2]

/-! ### A source normalization covering the complete ratio range -/

/-- The affine normalization `x = 3u - 11/16` maps the complete compact
ratio support `[1/8,33/8]` into `[13/48,77/48]`.  Unlike a truncation, this
retains every reflected ratio in Proposition 10.1. -/
noncomputable def gmCubicNormalizedRWeightSchwartz
    (W : Finset ℝ) : SchwartzMap ℝ ℝ := by
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (3 : ℝ) (by norm_num))
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e
    ((gmCubicRWeightSchwartz W).compSubConstCLM ℝ (11 / 16))

@[simp]
theorem gmCubicNormalizedRWeightSchwartz_apply
    (W : Finset ℝ) (u : ℝ) :
    gmCubicNormalizedRWeightSchwartz W u =
      gmCubicRWeightSchwartz W (3 * u - 11 / 16) := by
  dsimp only [gmCubicNormalizedRWeightSchwartz]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, SchwartzMap.compSubConstCLM_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_mk0, smul_eq_mul]

theorem gmCubicNormalizedRWeightSchwartz_nonneg
    (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicNormalizedRWeightSchwartz W u := by
  rw [gmCubicNormalizedRWeightSchwartz_apply]
  exact gmCubicRWeightSchwartz_nonneg W _

theorem gmCubicNormalizedRWeight_supportedOn (W : Finset ℝ) :
    GMAffineSupportedOn (13 / 48 : ℝ) (77 / 48)
      (gmCubicNormalizedRWeightSchwartz W) := by
  intro u hu
  rw [gmCubicNormalizedRWeightSchwartz_apply,
    gmCubicRWeightSchwartz_apply]
  unfold gmCubicRWeightFunction
  rw [gmCubicRatioBump_eq_zero_of_not_mem_Icc]
  · simp
  · intro hx
    apply hu
    constructor <;> linarith [hx.1, hx.2]

/-- The normalization `u ↦ 3u - 11/16` is exactly the integer affine
pullback `(48u-11)/16`.  Writing it in this form lets us use the proved
Fourier covariance theorem without introducing a new analytic axiom. -/
theorem gmAffineComplexify_normalizedRWeight_eq_affineTerm
    (W : Finset ℝ) :
    gmAffineComplexify (gmCubicNormalizedRWeightSchwartz W) =
      gmAffineTermSchwartz
        (gmAffineComplexify (gmCubicRWeightSchwartz W)) 48 16 (-11)
          (by norm_num) (by norm_num) := by
  ext u
  rw [gmAffineComplexify_apply, gmAffineTermSchwartz_apply,
    gmAffineComplexify_apply, gmCubicNormalizedRWeightSchwartz_apply]
  congr 2
  norm_num
  ring

/-- Exact Fourier covariance of the complete, untruncated Section 10
source under the support-normalizing affine map. -/
theorem fourier_gmAffineComplexify_normalizedRWeight
    (W : Finset ℝ) (xi : ℝ) :
    𝓕 (gmAffineComplexify (gmCubicNormalizedRWeightSchwartz W)) xi =
      ((1 / 3 : ℝ) : ℂ) *
        Complex.exp (((-(11 : ℝ) * Real.pi * xi / 24 : ℝ) : ℂ) * I) *
          𝓕 (gmAffineComplexify (gmCubicRWeightSchwartz W)) (xi / 3) := by
  rw [gmAffineComplexify_normalizedRWeight_eq_affineTerm]
  rw [gmAffineTermSchwartz_fourier]
  norm_num [abs_of_nonneg]
  ring_nf

theorem norm_fourier_gmAffineComplexify_normalizedRWeight
    (W : Finset ℝ) (xi : ℝ) :
    ‖𝓕 (gmAffineComplexify (gmCubicNormalizedRWeightSchwartz W)) xi‖ =
      (1 / 3 : ℝ) *
        ‖𝓕 (gmAffineComplexify (gmCubicRWeightSchwartz W)) (xi / 3)‖ := by
  rw [fourier_gmAffineComplexify_normalizedRWeight, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_exp]
  norm_num

theorem integral_gmCubicNormalizedRWeightSchwartz
    (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u) =
      (1 / 3 : ℝ) * ∫ x : ℝ, gmCubicRWeightSchwartz W x := by
  simp_rw [gmCubicNormalizedRWeightSchwartz_apply]
  calc
    (∫ u : ℝ, gmCubicRWeightSchwartz W (3 * u - 11 / 16)) =
        |(3 : ℝ)⁻¹| *
          ∫ y : ℝ, gmCubicRWeightSchwartz W (y - 11 / 16) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.integral_comp_mul_left
          (fun y : ℝ => gmCubicRWeightSchwartz W (y - 11 / 16)) (3 : ℝ))
    _ = |(3 : ℝ)⁻¹| * ∫ x : ℝ, gmCubicRWeightSchwartz W x := by
      rw [integral_sub_right_eq_self]
    _ = (1 / 3 : ℝ) * ∫ x : ℝ, gmCubicRWeightSchwartz W x := by
      norm_num

theorem integral_sq_gmCubicNormalizedRWeightSchwartz
    (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u ^ 2) =
      (1 / 3 : ℝ) * ∫ x : ℝ, gmCubicRWeightSchwartz W x ^ 2 := by
  simp_rw [gmCubicNormalizedRWeightSchwartz_apply]
  calc
    (∫ u : ℝ, gmCubicRWeightSchwartz W (3 * u - 11 / 16) ^ 2) =
        |(3 : ℝ)⁻¹| *
          ∫ y : ℝ, gmCubicRWeightSchwartz W (y - 11 / 16) ^ 2 := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.integral_comp_mul_left
          (fun y : ℝ => gmCubicRWeightSchwartz W (y - 11 / 16) ^ 2)
          (3 : ℝ))
    _ = |(3 : ℝ)⁻¹| * ∫ x : ℝ, gmCubicRWeightSchwartz W x ^ 2 := by
      rw [integral_sub_right_eq_self
        (fun x : ℝ => gmCubicRWeightSchwartz W x ^ 2) (11 / 16 : ℝ)]
    _ = (1 / 3 : ℝ) * ∫ x : ℝ, gmCubicRWeightSchwartz W x ^ 2 := by
      norm_num

/-- The complete Section 10 source mass is bounded by the literal
second moment of the exponential sum on the fixed ratio interval. -/
theorem integral_gmCubicRWeightSchwartz_le_secondMoment
    (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicRWeightSchwartz W u) ≤
      ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2 := by
  have hzero : ∀ u ∉ Set.Icc (1 / 8 : ℝ) (33 / 8),
      gmCubicRWeightSchwartz W u = 0 := by
    intro u hu
    rw [gmCubicRWeightSchwartz_apply]
    simp [gmCubicRWeightFunction,
      gmCubicRatioBump_eq_zero_of_not_mem_Icc hu]
  have hrestrict :
      (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8),
          gmCubicRWeightSchwartz W u) =
        ∫ u : ℝ, gmCubicRWeightSchwartz W u :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [← hrestrict]
  apply MeasureTheory.integral_mono
  · exact (gmCubicRWeightSchwartz W).integrable.integrableOn
  · apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_gmR W).norm.pow_const 2).aestronglyMeasurable.restrict
      ((W.card : ℝ) ^ 2)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W u) 2
  · intro u
    rw [gmCubicRWeightSchwartz_apply]
    by_cases hu : 0 < u
    · rw [gmCubicRWeightFunction_eq W hu]
      have hb0 := gmCubicRatioBump_nonneg u
      have hb1 := gmCubicRatioBump_le_one u
      nlinarith [sq_nonneg ‖gmR W u‖]
    · have hle : u ≤ 0 := le_of_not_gt hu
      have hbump : gmCubicRatioBump u = 0 := by
        apply gmCubicRatioBump_eq_zero_of_not_mem_Icc
        intro hmem
        linarith [hmem.1]
      simp [gmCubicRWeightFunction, hbump]

/-- The square of the complete Section 10 source is bounded by the
literal fourth moment on the same fixed ratio interval. -/
theorem integral_sq_gmCubicRWeightSchwartz_le_fourthMoment
    (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicRWeightSchwartz W u ^ 2) ≤
      ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
  have hzero : ∀ u ∉ Set.Icc (1 / 8 : ℝ) (33 / 8),
      gmCubicRWeightSchwartz W u ^ 2 = 0 := by
    intro u hu
    rw [gmCubicRWeightSchwartz_apply]
    simp [gmCubicRWeightFunction,
      gmCubicRatioBump_eq_zero_of_not_mem_Icc hu]
  have hrestrict :
      (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8),
          gmCubicRWeightSchwartz W u ^ 2) =
        ∫ u : ℝ, gmCubicRWeightSchwartz W u ^ 2 :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  rw [← hrestrict]
  apply MeasureTheory.integral_mono
  · have hmeas : AEStronglyMeasurable
        (fun u : ℝ => gmCubicRWeightSchwartz W u ^ 2)
        (volume.restrict (Set.Icc (1 / 8 : ℝ) (33 / 8))) :=
        ((gmCubicRWeightSchwartz W).continuous.measurable.pow_const 2).aestronglyMeasurable.restrict
    apply IntegrableOn.of_bound measure_Icc_lt_top hmeas
      ((W.card : ℝ) ^ 4)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg
      (by positivity : 0 ≤ gmCubicRWeightSchwartz W u ^ 2)]
    have hsource : gmCubicRWeightSchwartz W u ≤ (W.card : ℝ) ^ 2 := by
      rw [gmCubicRWeightSchwartz_apply]
      by_cases hu : 0 < u
      · rw [gmCubicRWeightFunction_eq W hu]
        have hb0 := gmCubicRatioBump_nonneg u
        have hb1 := gmCubicRatioBump_le_one u
        have hR := norm_gmR_le_card_all W u
        have hR2 : ‖gmR W u‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hR 2
        calc
          (gmCubicRatioBump u : ℝ) * ‖gmR W u‖ ^ 2 ≤
              1 * ‖gmR W u‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hb1 (sq_nonneg _)
          _ ≤ 1 * (W.card : ℝ) ^ 2 := by gcongr
          _ = (W.card : ℝ) ^ 2 := one_mul _
      · have hbump : gmCubicRatioBump u = 0 := by
          apply gmCubicRatioBump_eq_zero_of_not_mem_Icc
          intro hmem
          linarith [hmem.1]
        unfold gmCubicRWeightFunction
        rw [hbump, zero_mul]
        positivity
    nlinarith [gmCubicRWeightSchwartz_nonneg W u,
      sq_nonneg ((W.card : ℝ) ^ 2 - gmCubicRWeightSchwartz W u)]
  · apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_gmR W).norm.pow_const 4).aestronglyMeasurable.restrict
      ((W.card : ℝ) ^ 4)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖gmR W u‖ ^ 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W u) 4
  · intro u
    change gmCubicRWeightSchwartz W u ^ 2 ≤ ‖gmR W u‖ ^ 4
    rw [gmCubicRWeightSchwartz_apply]
    by_cases hu : 0 < u
    · rw [gmCubicRWeightFunction_eq W hu]
      have hb0 := gmCubicRatioBump_nonneg u
      have hb1 := gmCubicRatioBump_le_one u
      have hbSq : (gmCubicRatioBump u : ℝ) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (1 - (gmCubicRatioBump u : ℝ))]
      calc
        ((gmCubicRatioBump u : ℝ) * ‖gmR W u‖ ^ 2) ^ 2 =
            (gmCubicRatioBump u : ℝ) ^ 2 * ‖gmR W u‖ ^ 4 := by ring
        _ ≤ 1 * ‖gmR W u‖ ^ 4 := by
          exact mul_le_mul_of_nonneg_right hbSq (by positivity)
        _ = ‖gmR W u‖ ^ 4 := one_mul _
    · have hle : u ≤ 0 := le_of_not_gt hu
      have hbump : gmCubicRatioBump u = 0 := by
        apply gmCubicRatioBump_eq_zero_of_not_mem_Icc
        intro hmem
        linarith [hmem.1]
      simp [gmCubicRWeightFunction, hbump]

/-- Exact logarithmic change of variables for the wide second moment
which controls the complete Section 10 affine source. -/
theorem setIntegral_norm_gmR_sq_wide_eq_logWeighted (W : Finset ℝ) :
    (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2) =
      ∫ x in Real.log (1 / 8 : ℝ)..Real.log (33 / 8 : ℝ),
        ‖gmRPhase W x‖ ^ 2 * Real.exp x := by
  let a : ℝ := Real.log (1 / 8 : ℝ)
  let b : ℝ := Real.log (33 / 8 : ℝ)
  let g : ℝ → ℝ := fun u => ‖gmR W u‖ ^ 2
  have ha0 : (0 : ℝ) < 1 / 8 := by norm_num
  have hb0 : (0 : ℝ) < 33 / 8 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr ha0)
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hgCont : ContinuousOn g (Real.exp '' Set.uIcc a b) := by
    rintro u ⟨x, hx, rfl⟩
    exact ((continuousAt_gmR W (Real.exp_ne_zero x)).norm.pow 2).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := Real.exp) (f' := Real.exp) (g := g)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hgCont
  have hsub' :
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) =
        ∫ u in (1 / 8 : ℝ)..(33 / 8 : ℝ), ‖gmR W u‖ ^ 2 := by
    calc
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) =
          ∫ x in a..b, (g ∘ Real.exp) x * Real.exp x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [Function.comp_apply, g, gmR_exp_eq_gmRPhase]
      _ = ∫ u in Real.exp a..Real.exp b, g u := hsub
      _ = ∫ u in (1 / 8 : ℝ)..(33 / 8 : ℝ), ‖gmR W u‖ ^ 2 := by
        dsimp only [a, b, g]
        rw [Real.exp_log ha0, Real.exp_log hb0]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 8 : ℝ) ≤ 33 / 8)]
  simpa only [a, b] using hsub'.symm

noncomputable def gmCubicWideL2Constant (ε : ℝ) : ℝ :=
  (33 / 8) *
    (|Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
      4 * (1 + ε⁻¹) * 2 ^ ε)

theorem gmCubicWideL2Constant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmCubicWideL2Constant ε := by
  unfold gmCubicWideL2Constant
  positivity

/-- Uniform epsilon-budget form of the wide second moment. -/
theorem setIntegral_norm_gmR_sq_wide_le_epsilon_budget
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2) ≤
      gmCubicWideL2Constant ε * T ^ ε * (W.card : ℝ) := by
  let a : ℝ := Real.log (1 / 8 : ℝ)
  let b : ℝ := Real.log (33 / 8 : ℝ)
  let A : ℝ := |b - a|
  let D : ℝ := 4 * (1 + ε⁻¹) * 2 ^ ε
  let X : ℝ := T ^ ε
  have hb0 : (0 : ℝ) < 33 / 8 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1 / 8))
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hphase := intervalIntegral_norm_gmRPhase_sq_le_epsilon
    hε hT hSep hBase a b hab
  have hweighted :
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) ≤
        (33 / 8 : ℝ) * ∫ x in a..b, ‖gmRPhase W x‖ ^ 2 := by
    calc
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) ≤
          ∫ x in a..b, (33 / 8 : ℝ) * ‖gmRPhase W x‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hab
        · exact (continuous_norm_gmRPhase_pow W 2).mul
            Real.continuous_exp |>.intervalIntegrable a b
        · exact (continuous_const.mul
            (continuous_norm_gmRPhase_pow W 2)).intervalIntegrable a b
        · intro x hx
          have hexp : Real.exp x ≤ (33 / 8 : ℝ) := by
            rw [← Real.exp_log hb0]
            exact Real.exp_le_exp.mpr hx.2
          have hq0 : 0 ≤ ‖gmRPhase W x‖ ^ 2 := sq_nonneg _
          nlinarith
      _ = (33 / 8 : ℝ) * ∫ x in a..b, ‖gmRPhase W x‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  have hX : 1 ≤ X := by
    dsimp only [X]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hε.le
  have hA : 0 ≤ A := abs_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  rw [setIntegral_norm_gmR_sq_wide_eq_logWeighted W]
  calc
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) ≤
        (33 / 8 : ℝ) * ∫ x in a..b, ‖gmRPhase W x‖ ^ 2 := hweighted
    _ ≤ (33 / 8 : ℝ) * ((A + D * X) * (W.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [A, D, X] using hphase) (by norm_num)
    _ ≤ (33 / 8 : ℝ) * (((A + D) * X) * (W.card : ℝ)) := by
      gcongr
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hX)]
    _ = gmCubicWideL2Constant ε * T ^ ε * (W.card : ℝ) := by
      dsimp only [gmCubicWideL2Constant, A, D, X, a, b]
      ring

noncomputable def gmCubicWideFourthConstant (ε : ℝ) : ℝ :=
  (33 / 8) *
    (4 * |Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
      8 * (1 + ε⁻¹) * 3 ^ ε)

theorem gmCubicWideFourthConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmCubicWideFourthConstant ε := by
  unfold gmCubicWideFourthConstant
  positivity

theorem setIntegral_norm_gmR_fourth_wide_le_epsilon_budget
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hBase : InBaseInterval T W) :
    (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4) ≤
      gmCubicWideFourthConstant ε * T ^ ε *
        (ApproxAddEnergy 1 W : ℝ) := by
  simpa only [gmCubicWideFourthConstant] using
    setIntegral_norm_gmR_fourth_le_energy_epsilon hε hT hBase

theorem pow_mul_norm_fourier_gmCubicNormalizedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) (xi : ℝ) :
    |xi| ^ n *
        ‖fourier (gmAffineComplexify
          (gmCubicNormalizedRWeightSchwartz W)) xi‖ ≤
      3 ^ n * gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  rw [norm_fourier_gmAffineComplexify_normalizedRWeight]
  have hbase := pow_mul_norm_fourier_gmCubicRWeight_le
    hT hW n (xi / 3)
  have habs : |xi| = 3 * |xi / 3| := by
    rw [abs_div]
    norm_num
    ring
  rw [habs, mul_pow]
  calc
    (3 ^ n * |xi / 3| ^ n) *
          ((1 / 3 : ℝ) *
            ‖fourier (gmAffineComplexify
              (gmCubicRWeightSchwartz W)) (xi / 3)‖) =
        ((1 / 3 : ℝ) * 3 ^ n) *
          (|xi / 3| ^ n *
            ‖fourier (gmAffineComplexify
              (gmCubicRWeightSchwartz W)) (xi / 3)‖) := by ring
    _ ≤ ((1 / 3 : ℝ) * 3 ^ n) *
          (gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ 3 ^ n * gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
      have hnonneg :
          0 ≤ 3 ^ n * gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity)
              (gmCubicRWeightFourierConstant_nonneg n))
            (pow_nonneg (zero_le_one.trans hT) n))
          (sq_nonneg (W.card : ℝ))
      nlinarith

theorem seminorm_fourier_gmCubicNormalizedRWeight_le
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W)
    (n : ℕ) :
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify
          (gmCubicNormalizedRWeightSchwartz W))) ≤
      3 ^ n * gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 := by
  apply SchwartzMap.seminorm_le_bound' ℝ n 0 _
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (gmCubicRWeightFourierConstant_nonneg n))
        (pow_nonneg (zero_le_one.trans hT) n))
      (sq_nonneg (W.card : ℝ))
  · intro xi
    rw [iteratedDeriv_zero]
    exact pow_mul_norm_fourier_gmCubicNormalizedRWeight_le hT hW n xi

theorem card_sq_le_fortyeight_mul_T_mul_integral_normalizedRWeight
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (hW : InBaseInterval T W) :
    (W.card : ℝ) ^ 2 ≤
      48 * T * ∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u := by
  rw [integral_gmCubicNormalizedRWeightSchwartz]
  have hbase :=
    card_sq_le_sixteen_mul_T_mul_integral_gmCubicRWeightSchwartz hT hW
  convert hbase using 1
  ring

noncomputable def gmCubicNormalizedHeightProfileConstant
    (_epsilon : ℝ) (n : ℕ) : ℝ :=
  48 * 3 ^ n * gmCubicRWeightFourierConstant n

theorem gmCubicNormalizedHeightProfileConstant_nonneg
    (epsilon : ℝ) (n : ℕ) :
    0 ≤ gmCubicNormalizedHeightProfileConstant epsilon n := by
  unfold gmCubicNormalizedHeightProfileConstant
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (gmCubicRWeightFourierConstant_nonneg n)

theorem gmCubicNormalizedRWeight_heightFourierMassFamilyAtDepth_zero
    {T : ℝ} (hT : 1 ≤ T) {W : Finset ℝ} (hW : InBaseInterval T W) :
    GMAffineHeightFourierMassFamilyAtDepth T
      gmCubicNormalizedHeightProfileConstant 0
      (gmCubicNormalizedRWeightSchwartz W) := by
  intro epsilon hepsilon n
  unfold GMAffineHeightFourierMassBound
  simp only [pow_zero, one_mul]
  let mass : ℝ := ∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u
  have hmass : 0 ≤ mass := by
    dsimp only [mass]
    exact integral_nonneg (gmCubicNormalizedRWeightSchwartz_nonneg W)
  have hcard :=
    card_sq_le_fortyeight_mul_T_mul_integral_normalizedRWeight hT hW
  have hcoef :
      0 ≤ 3 ^ n * gmCubicRWeightFourierConstant n * T ^ n := by
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (gmCubicRWeightFourierConstant_nonneg n))
      (pow_nonneg (zero_le_one.trans hT) n)
  have hepsPow : 1 ≤ T ^ epsilon :=
    Real.one_le_rpow hT (le_of_lt hepsilon)
  have hscale : T ^ n * T ≤ T ^ epsilon * T ^ (n + 2) := by
    calc
      T ^ n * T = T ^ (n + 1) := by rw [pow_succ]
      _ ≤ T ^ (n + 2) :=
        pow_le_pow_right₀ hT (Nat.le_succ (n + 1))
      _ ≤ T ^ epsilon * T ^ (n + 2) := by
        exact le_mul_of_one_le_left
          (pow_nonneg (zero_le_one.trans hT) (n + 2)) hepsPow
  calc
    SchwartzMap.seminorm ℝ n 0
        (fourier (gmAffineComplexify
          (gmCubicNormalizedRWeightSchwartz W))) ≤
      3 ^ n * gmCubicRWeightFourierConstant n * T ^ n * W.card ^ 2 :=
        seminorm_fourier_gmCubicNormalizedRWeight_le hT hW n
    _ ≤ (3 ^ n * gmCubicRWeightFourierConstant n * T ^ n) *
        (48 * T * mass) := mul_le_mul_of_nonneg_left hcard hcoef
    _ = (48 * 3 ^ n * gmCubicRWeightFourierConstant n) *
        (T ^ n * T) * mass := by ring
    _ ≤ (48 * 3 ^ n * gmCubicRWeightFourierConstant n) *
        (T ^ epsilon * T ^ (n + 2)) * mass := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale
          (mul_nonneg (mul_nonneg (by positivity) (by positivity))
            (gmCubicRWeightFourierConstant_nonneg n))) hmass
    _ = gmCubicNormalizedHeightProfileConstant epsilon n *
        T ^ epsilon * T ^ (n + 2) *
          ∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u := by
      unfold gmCubicNormalizedHeightProfileConstant
      dsimp only [mass]
      ring

/-- The normalized complete Section 10 source.  Its physical convolution
scale is `3B`, exactly as dictated by the affine change of variables. -/
noncomputable def gmCubicNormalizedAffineSourceSchwartz
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) : SchwartzMap ℝ ℝ :=
  gmAffineTildeSchwartz (3 * B) (mul_pos (by norm_num) hB)
    (gmCubicNormalizedRWeightSchwartz W)

theorem gmCubicNormalizedAffineSourceSchwartz_nonneg
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicNormalizedAffineSourceSchwartz B hB W u := by
  exact gmAffineTildeSchwartz_nonneg (3 * B) (mul_pos (by norm_num) hB)
    (gmCubicNormalizedRWeightSchwartz W)
    (gmCubicNormalizedRWeightSchwartz_nonneg W) u

/-- The `L¹` mass entering Proposition 9.1 is controlled by the actual
second moment of `R`; both affine normalizations and the smoothing-kernel
mass are accounted for explicitly. -/
theorem integral_gmCubicNormalizedAffineSource_le_two_secondMoment
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz B hB W u) ≤
      2 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2 := by
  have hsmooth := integral_gmAffineTildeSchwartz_le
    (3 * B) (mul_pos (by norm_num) hB)
    (gmCubicNormalizedRWeightSchwartz W)
    (gmCubicNormalizedRWeightSchwartz_nonneg W)
  have hsource := integral_gmCubicRWeightSchwartz_le_secondMoment W
  have hmass0 : 0 ≤ ∫ u : ℝ, gmCubicRWeightSchwartz W u :=
    integral_nonneg (gmCubicRWeightSchwartz_nonneg W)
  have hmoment0 : 0 ≤
      ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  calc
    (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz B hB W u) ≤
        4 * ∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u := hsmooth
    _ = (4 / 3 : ℝ) * ∫ u : ℝ, gmCubicRWeightSchwartz W u := by
      rw [integral_gmCubicNormalizedRWeightSchwartz]
      ring
    _ ≤ 2 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2 := by
      nlinarith

/-- The `L²` mass entering Proposition 9.1 is controlled by the actual
fourth moment of `R`, with the normalization and smoothing losses kept
as the explicit constant six. -/
theorem integral_sq_gmCubicNormalizedAffineSource_le_six_fourthMoment
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz B hB W u ^ 2) ≤
      6 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
  have hsmooth := integral_gmAffineTildeSchwartz_sq_le
    (3 * B) (mul_pos (by norm_num) hB)
    (gmCubicNormalizedRWeightSchwartz W)
  have hsource := integral_sq_gmCubicRWeightSchwartz_le_fourthMoment W
  have hmass0 : 0 ≤ ∫ u : ℝ, gmCubicRWeightSchwartz W u ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hmoment0 : 0 ≤
      ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
  calc
    (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz B hB W u ^ 2) ≤
        16 * ∫ u : ℝ, gmCubicNormalizedRWeightSchwartz W u ^ 2 := hsmooth
    _ = (16 / 3 : ℝ) * ∫ u : ℝ, gmCubicRWeightSchwartz W u ^ 2 := by
      rw [integral_sq_gmCubicNormalizedRWeightSchwartz]
      ring
    _ ≤ 6 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
      nlinarith

theorem gmCubicNormalizedAffineSource_supportedOn
    {B : ℝ} (hB : 0 < B) (hB32 : 32 ≤ B) (W : Finset ℝ) :
    GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4)
      (gmCubicNormalizedAffineSourceSchwartz B hB W) := by
  have hradius : 2 / (3 * B) ≤ 1 / 48 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hB)]
    nlinarith
  have h3B : 0 < 3 * B := mul_pos (by norm_num) hB
  have hsupp := gmAffineTildeSchwartz_supportedOn h3B
    (gmCubicNormalizedRWeightSchwartz W)
    (gmCubicNormalizedRWeight_supportedOn W)
  have hout : GMAffineSupportedOn (1 / 4 : ℝ) (9 / 4)
      (gmAffineTildeSchwartz (3 * B) h3B
        (gmCubicNormalizedRWeightSchwartz W)) :=
    hsupp.mono (by linarith) (by linarith)
  simpa only [gmCubicNormalizedAffineSourceSchwartz] using hout

/-- Exact covariance of the physical equation-(7.5) smoother under the
normalization `x = 3u - 11/16`. -/
theorem gmCubicNormalizedAffineSource_eq_original
    (B : ℝ) (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    gmCubicNormalizedAffineSourceSchwartz B hB W u =
      gmAffineTildeSchwartz B hB (gmCubicRWeightSchwartz W)
        (3 * u - 11 / 16) := by
  rw [gmCubicNormalizedAffineSourceSchwartz,
    gmAffineTildeSchwartz_apply_sub,
    gmAffineTildeSchwartz_apply_sub]
  simp only [gmCubicNormalizedRWeightSchwartz_apply]
  let q : ℝ → ℝ := fun x =>
    B * gmCubicLocalBump (B * ((3 * u - 11 / 16) - x)) *
      gmCubicRWeightSchwartz W x
  have hpoint : ∀ z : ℝ,
      (3 * B) * gmCubicLocalBump ((3 * B) * (u - z)) *
          gmCubicRWeightSchwartz W (3 * z - 11 / 16) =
        3 * q (3 * z - 11 / 16) := by
    intro z
    dsimp only [q]
    have harg : (3 * B) * (u - z) =
        B * ((3 * u - 11 / 16) - (3 * z - 11 / 16)) := by ring
    rw [harg]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  have hchange : (∫ z : ℝ, q (3 * z - 11 / 16)) =
      (1 / 3 : ℝ) * ∫ x : ℝ, q x := by
    calc
      (∫ z : ℝ, q (3 * z - 11 / 16)) =
          |(3 : ℝ)⁻¹| * ∫ y : ℝ, q (y - 11 / 16) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.integral_comp_mul_left
            (fun y : ℝ => q (y - 11 / 16)) (3 : ℝ))
      _ = |(3 : ℝ)⁻¹| * ∫ x : ℝ, q x := by
        rw [integral_sub_right_eq_self]
      _ = (1 / 3 : ℝ) * ∫ x : ℝ, q x := by norm_num
  rw [hchange]
  change 3 * ((1 / 3 : ℝ) * ∫ x : ℝ, q x) = ∫ x : ℝ, q x
  ring

noncomputable def gmCubicNormalizedNativeHeightProfileConstant
    (_epsilon : ℝ) (n : ℕ) : ℝ :=
  96 * 3 ^ n * gmCubicRWeightFourierConstant n

theorem gmCubicNormalizedNativeHeightProfileConstant_nonneg
    (epsilon : ℝ) (n : ℕ) :
    0 ≤ gmCubicNormalizedNativeHeightProfileConstant epsilon n := by
  unfold gmCubicNormalizedNativeHeightProfileConstant
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (gmCubicRWeightFourierConstant_nonneg n)

theorem gmCubicNormalizedAffineSource_heightFourierMassFamilyAtDepth_zero
    {T B : ℝ} (hT : 1 ≤ T) (hB : 0 < B)
    {W : Finset ℝ} (hW : InBaseInterval T W) :
    GMAffineHeightFourierMassFamilyAtDepth T
      gmCubicNormalizedNativeHeightProfileConstant 0
      (gmCubicNormalizedAffineSourceSchwartz B hB W) := by
  intro epsilon hepsilon n
  have hbase :=
    gmCubicNormalizedRWeight_heightFourierMassFamilyAtDepth_zero
      hT hW epsilon hepsilon n
  simp only [pow_zero, one_mul] at hbase ⊢
  have h3B : 0 < 3 * B := mul_pos (by norm_num) hB
  have hsmooth := gmAffineTildeSchwartz_heightFourierMassBound
    (show 0 ≤ T from zero_le_one.trans hT) h3B
    (gmCubicNormalizedHeightProfileConstant_nonneg epsilon n) n
    (gmCubicNormalizedRWeightSchwartz W)
    (gmCubicNormalizedRWeightSchwartz_nonneg W) hbase
  unfold gmCubicNormalizedAffineSourceSchwartz
  convert hsmooth using 1
  unfold gmCubicNormalizedNativeHeightProfileConstant
    gmCubicNormalizedHeightProfileConstant
  ring

/-- Proposition 9.1 for the complete normalized equation-(7.5) source.
Unlike the earlier cutoff specialization, this theorem retains every
ratio in the Section 10 reflected sum. -/
theorem gmCubicNormalizedAffineSource_proposition9_1
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ {T B : ℝ}, T₀ ≤ T → ∀ (hB : 0 < B), 32 ≤ B →
      ∀ {W : Finset ℝ}, InBaseInterval T W →
      ∀ {M : ℕ}, 0 < M → (M : ℝ) ≤ T ^ 4 →
        gmAffineJ (gmCubicNormalizedAffineSourceSchwartz B hB W) M ≤
          C * T ^ epsilon *
            ((M : ℝ) ^ 6 *
                (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz B
                  hB W u) ^ 2 +
              (M : ℝ) ^ 4 *
                ∫ u : ℝ,
                  gmCubicNormalizedAffineSourceSchwartz B hB W u ^ 2) := by
  obtain ⟨C, T₀, hC, hT₀, hprop⟩ :=
    gmAffine_proposition9_1_height_family_native
      gmCubicNormalizedNativeHeightProfileConstant
      gmCubicNormalizedNativeHeightProfileConstant_nonneg hepsilon
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T B hT hB hB32 W hW M hM hMT
  exact hprop hT (gmCubicNormalizedAffineSourceSchwartz B hB W)
    (gmCubicNormalizedAffineSourceSchwartz_nonneg B hB W)
    (gmCubicNormalizedAffineSource_supportedOn hB hB32 W)
    (gmCubicNormalizedAffineSource_heightFourierMassFamilyAtDepth_zero
      (one_le_two.trans (hT₀.trans hT)) hB hW) hM hMT

/-! ## Exact integer reindexing of the two Section 10 centers -/

/-- Integer coefficients for the normalized direct cancellation center.
Multiplication by `sign b` makes the denominator positive while preserving
the underlying rational affine map. -/
def gmCubicNormalizedDirectTriple
    (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) :=
  let e := Int.sign m.2.1
  (-16 * e * m.1,
    (48 * (m.2.1.natAbs : ℤ), e * (-16 * m.2.2 + 11 * m.2.1)))

/-- Integer coefficients for the normalized reflected center after the
reciprocal substitution `u = 1/v`; this exchanges the first and third
source frequencies exactly as in Guth--Maynard Section 10. -/
def gmCubicNormalizedReflectedTriple
    (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) :=
  let e := Int.sign m.2.1
  (-16 * e * m.2.2,
    (48 * (m.2.1.natAbs : ℤ), e * (-16 * m.1 + 11 * m.2.1)))

theorem gmCubicNormalizedDirectTriple_affine
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) (v : ℝ) :
    (((gmCubicNormalizedDirectTriple m).1 : ℝ) * v +
          ((gmCubicNormalizedDirectTriple m).2.2 : ℝ)) /
        ((gmCubicNormalizedDirectTriple m).2.1 : ℝ) =
      gmCubicCancellationCenter m v / 3 + 11 / 48 := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hbnegR : (m.2.1 : ℝ) < 0 := by exact_mod_cast hbneg
    simp [gmCubicNormalizedDirectTriple,
      Int.sign_eq_neg_one_of_neg hbneg, Nat.cast_natAbs,
      Int.cast_abs, abs_of_neg hbnegR]
    have hbR : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hb
    unfold gmCubicCancellationCenter
    field_simp [hbR]
    ring
  · simp [gmCubicNormalizedDirectTriple,
      Int.sign_eq_one_of_pos hbpos, Int.natAbs_of_nonneg hbpos.le]
    have hbR : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hb
    unfold gmCubicCancellationCenter
    field_simp [hbR]
    ring

theorem gmCubicNormalizedReflectedTriple_affine
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) (u : ℝ) :
    (((gmCubicNormalizedReflectedTriple m).1 : ℝ) * u +
          ((gmCubicNormalizedReflectedTriple m).2.2 : ℝ)) /
        ((gmCubicNormalizedReflectedTriple m).2.1 : ℝ) =
      (-((m.2.2 : ℝ) * u + (m.1 : ℝ)) / (m.2.1 : ℝ)) / 3 +
        11 / 48 := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hbnegR : (m.2.1 : ℝ) < 0 := by exact_mod_cast hbneg
    simp [gmCubicNormalizedReflectedTriple,
      Int.sign_eq_neg_one_of_neg hbneg, Nat.cast_natAbs,
      Int.cast_abs, abs_of_neg hbnegR]
    have hbR : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp [hbR]
    ring
  · simp [gmCubicNormalizedReflectedTriple,
      Int.sign_eq_one_of_pos hbpos, Int.natAbs_of_nonneg hbpos.le]
    have hbR : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp [hbR]
    ring

theorem gmCubicNormalizedAffineSource_directTriple
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) (v : ℝ) :
    gmAffineTerm (gmCubicNormalizedAffineSourceSchwartz B hB W)
        (gmCubicNormalizedDirectTriple m).1
        (gmCubicNormalizedDirectTriple m).2.1
        (gmCubicNormalizedDirectTriple m).2.2 v =
      gmAffineTildeSchwartz B hB (gmCubicRWeightSchwartz W)
        (gmCubicCancellationCenter m v) := by
  unfold gmAffineTerm
  rw [gmCubicNormalizedDirectTriple_affine hb,
    gmCubicNormalizedAffineSource_eq_original]
  congr 2
  ring

theorem gmCubicNormalizedAffineSource_reflectedTriple
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) (u : ℝ) :
    gmAffineTerm (gmCubicNormalizedAffineSourceSchwartz B hB W)
        (gmCubicNormalizedReflectedTriple m).1
        (gmCubicNormalizedReflectedTriple m).2.1
        (gmCubicNormalizedReflectedTriple m).2.2 u =
      gmAffineTildeSchwartz B hB (gmCubicRWeightSchwartz W)
        (-((m.2.2 : ℝ) * u + (m.1 : ℝ)) / (m.2.1 : ℝ)) := by
  unfold gmAffineTerm
  rw [gmCubicNormalizedReflectedTriple_affine hb,
    gmCubicNormalizedAffineSource_eq_original]
  congr 2
  ring

theorem mem_gmAffineSignedShell_of_abs_bounds
    {M : ℕ} {z : ℤ}
    (hLower : (M : ℝ) ≤ |(z : ℝ)|)
    (hUpper : |(z : ℝ)| ≤ (2 * M : ℕ)) :
    z ∈ gmAffineSignedShell M := by
  rw [mem_gmAffineSignedShell]
  by_cases hz : (z : ℝ) ≤ 0
  · left
    rw [abs_of_nonpos hz] at hLower hUpper
    constructor
    · have h : (-(2 * M : ℕ) : ℝ) ≤ (z : ℝ) := by linarith
      exact_mod_cast h
    · have h : (z : ℝ) ≤ -(M : ℕ) := by linarith
      exact_mod_cast h
  · right
    have hz0 : 0 ≤ (z : ℝ) := le_of_not_ge hz
    rw [abs_of_nonneg hz0] at hLower hUpper
    constructor
    · exact_mod_cast hLower
    · exact_mod_cast hUpper

theorem mem_gmAffineCentralShell_of_abs_bound
    {M : ℕ} {z : ℤ} (hz : |(z : ℝ)| ≤ (8 * M : ℕ)) :
    z ∈ gmAffineCentralShell M := by
  rw [mem_gmAffineCentralShell]
  rw [abs_le] at hz
  constructor
  · exact_mod_cast hz.1
  · exact_mod_cast hz.2

theorem abs_directTriple_first
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) :
    |((gmCubicNormalizedDirectTriple m).1 : ℝ)| =
      16 * |(m.1 : ℝ)| := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · simp [gmCubicNormalizedDirectTriple,
      Int.sign_eq_neg_one_of_neg hbneg, abs_mul]
  · simp [gmCubicNormalizedDirectTriple,
      Int.sign_eq_one_of_pos hbpos, abs_mul]

theorem abs_reflectedTriple_first
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) :
    |((gmCubicNormalizedReflectedTriple m).1 : ℝ)| =
      16 * |(m.2.2 : ℝ)| := by
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · simp [gmCubicNormalizedReflectedTriple,
      Int.sign_eq_neg_one_of_neg hbneg, abs_mul]
  · simp [gmCubicNormalizedReflectedTriple,
      Int.sign_eq_one_of_pos hbpos, abs_mul]

theorem abs_directTriple_central_le
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) :
    |((gmCubicNormalizedDirectTriple m).2.2 : ℝ)| ≤
      16 * |(m.2.2 : ℝ)| + 11 * |(m.2.1 : ℝ)| := by
  have hsign : |(Int.sign m.2.1 : ℝ)| = 1 := by
    rcases lt_or_gt_of_ne hb with hbneg | hbpos
    · simp [Int.sign_eq_neg_one_of_neg hbneg]
    · simp [Int.sign_eq_one_of_pos hbpos]
  rw [show ((gmCubicNormalizedDirectTriple m).2.2 : ℝ) =
      (Int.sign m.2.1 : ℝ) *
        (-16 * (m.2.2 : ℝ) + 11 * (m.2.1 : ℝ)) by
    simp [gmCubicNormalizedDirectTriple]]
  rw [abs_mul, hsign, one_mul]
  calc
    |-16 * (m.2.2 : ℝ) + 11 * (m.2.1 : ℝ)| ≤
        |-16 * (m.2.2 : ℝ)| + |11 * (m.2.1 : ℝ)| := abs_add_le _ _
    _ = 16 * |(m.2.2 : ℝ)| + 11 * |(m.2.1 : ℝ)| := by
      simp [abs_mul]

theorem abs_reflectedTriple_central_le
    {m : ℤ × (ℤ × ℤ)} (hb : m.2.1 ≠ 0) :
    |((gmCubicNormalizedReflectedTriple m).2.2 : ℝ)| ≤
      16 * |(m.1 : ℝ)| + 11 * |(m.2.1 : ℝ)| := by
  have hsign : |(Int.sign m.2.1 : ℝ)| = 1 := by
    rcases lt_or_gt_of_ne hb with hbneg | hbpos
    · simp [Int.sign_eq_neg_one_of_neg hbneg]
    · simp [Int.sign_eq_one_of_pos hbpos]
  rw [show ((gmCubicNormalizedReflectedTriple m).2.2 : ℝ) =
      (Int.sign m.2.1 : ℝ) *
        (-16 * (m.1 : ℝ) + 11 * (m.2.1 : ℝ)) by
    simp [gmCubicNormalizedReflectedTriple]]
  rw [abs_mul, hsign, one_mul]
  calc
    |-16 * (m.1 : ℝ) + 11 * (m.2.1 : ℝ)| ≤
        |-16 * (m.1 : ℝ)| + |11 * (m.2.1 : ℝ)| := abs_add_le _ _
    _ = 16 * |(m.1 : ℝ)| + 11 * |(m.2.1 : ℝ)| := by
      simp [abs_mul]

def gmCubicDirectAffineScales (r s : ℕ) : ℕ × (ℕ × ℕ) :=
  (16 * 2 ^ r, 48 * 2 ^ s, 24 * 2 ^ s)

def gmCubicReflectedAffineScales
    (m : ℤ × (ℤ × ℤ)) (s : ℕ) : ℕ × (ℕ × ℕ) :=
  (16 * 2 ^ (Nat.log 2 m.2.2.natAbs), 48 * 2 ^ s, 24 * 2 ^ s)

def gmCubicAffineTerminalScale (s : ℕ) : ℕ := 128 * 2 ^ s

theorem gmCubicNormalizedDirectTriple_mem_indexSet
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicDyadicFrequencyBlock H r s) :
    gmCubicNormalizedDirectTriple m ∈
      gmAffineIndexSet (gmCubicDirectAffineScales r s).1
        (gmCubicDirectAffineScales r s).2.1
        (gmCubicDirectAffineScales r s).2.2 := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmOrdered := mem_gmCubicOrderedFrequencyBox.mp hmBalanced.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmOrdered.1
  have hb := hmNZ.2.2.1
  have haLower : ((2 ^ r : ℕ) : ℝ) ≤ |(m.1 : ℝ)| := by
    rw [show |(m.1 : ℝ)| = (m.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hmBlock.2.1
  have haUpper : |(m.1 : ℝ)| ≤ ((2 ^ (r + 1) : ℕ) : ℝ) := by
    rw [show |(m.1 : ℝ)| = (m.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast (Nat.le_of_lt hmBlock.2.2.1)
  have hbLower : ((2 ^ s : ℕ) : ℝ) ≤ |(m.2.1 : ℝ)| := by
    rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hmBlock.2.2.2.1
  have hbUpper : |(m.2.1 : ℝ)| ≤ ((2 ^ (s + 1) : ℕ) : ℝ) := by
    rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast (Nat.le_of_lt hmBlock.2.2.2.2)
  rw [mem_gmAffineIndexSet]
  refine ⟨?_, ?_, ?_⟩
  · apply mem_gmAffineSignedShell_of_abs_bounds
    · rw [abs_directTriple_first hb]
      dsimp only [gmCubicDirectAffineScales]
      rw [show |(m.1 : ℝ)| = (m.1.natAbs : ℝ) by
        simp only [Nat.cast_natAbs, Int.cast_abs]]
      exact_mod_cast Nat.mul_le_mul_left 16 hmBlock.2.1
    · rw [abs_directTriple_first hb]
      dsimp only [gmCubicDirectAffineScales]
      push_cast
      rw [pow_succ'] at haUpper
      norm_num at haUpper ⊢
      nlinarith
  · rw [mem_gmAffinePositiveShell]
    dsimp only [gmCubicDirectAffineScales,
      gmCubicNormalizedDirectTriple]
    constructor
    · exact_mod_cast Nat.mul_le_mul_left 48 hmBlock.2.2.2.1
    · have hmul := Nat.mul_le_mul_left 48
          (Nat.le_of_lt hmBlock.2.2.2.2)
      have heq : 48 * 2 ^ (s + 1) = 2 * (48 * 2 ^ s) := by
        rw [pow_succ']
        ring
      exact_mod_cast hmul.trans_eq heq
  · apply mem_gmAffineCentralShell_of_abs_bound
    have hcentral := abs_directTriple_central_le hb
    have hcUpper := hmBalanced.2
    dsimp only [gmCubicDirectAffineScales]
    push_cast
    rw [pow_succ'] at hbUpper
    norm_num at hbUpper ⊢
    nlinarith

theorem gmCubicDirectAffineScales_mem_terminal
    {r s : ℕ} (hrs : r ≤ s) :
    gmCubicDirectAffineScales r s ∈
      gmAffineScaleTriples (gmCubicAffineTerminalScale s) := by
  rw [mem_gmAffineScaleTriples]
  dsimp only [gmCubicDirectAffineScales, gmCubicAffineTerminalScale]
  have hp : 2 ^ r ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hrs
  have hpos : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) _
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  · calc
      16 * 2 ^ r ≤ 16 * 2 ^ s := Nat.mul_le_mul_left 16 hp
      _ ≤ 128 * 2 ^ s := by omega
  · omega
  · omega

theorem gmCubicNormalizedReflectedTriple_mem_indexSet
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicDyadicFrequencyBlock H r s) :
    gmCubicNormalizedReflectedTriple m ∈
      gmAffineIndexSet (gmCubicReflectedAffineScales m s).1
        (gmCubicReflectedAffineScales m s).2.1
        (gmCubicReflectedAffineScales m s).2.2 := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmOrdered := mem_gmCubicOrderedFrequencyBox.mp hmBalanced.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmOrdered.1
  have hb := hmNZ.2.2.1
  have hc := hmNZ.2.2.2
  have hcAbs : m.2.2.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  let q := Nat.log 2 m.2.2.natAbs
  have hcLowerNat : 2 ^ q ≤ m.2.2.natAbs := by
    exact Nat.pow_log_le_self 2 hcAbs
  have hcUpperNat : m.2.2.natAbs ≤ 2 ^ (q + 1) := by
    exact Nat.le_of_lt
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) m.2.2.natAbs)
  have hcLower : ((2 ^ q : ℕ) : ℝ) ≤ |(m.2.2 : ℝ)| := by
    rw [show |(m.2.2 : ℝ)| = (m.2.2.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hcLowerNat
  have hcUpper : |(m.2.2 : ℝ)| ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by
    rw [show |(m.2.2 : ℝ)| = (m.2.2.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hcUpperNat
  have hbUpper : |(m.2.1 : ℝ)| ≤ ((2 ^ (s + 1) : ℕ) : ℝ) := by
    rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast (Nat.le_of_lt hmBlock.2.2.2.2)
  rw [mem_gmAffineIndexSet]
  refine ⟨?_, ?_, ?_⟩
  · apply mem_gmAffineSignedShell_of_abs_bounds
    · rw [abs_reflectedTriple_first hb]
      dsimp only [gmCubicReflectedAffineScales]
      rw [show |(m.2.2 : ℝ)| = (m.2.2.natAbs : ℝ) by
        simp only [Nat.cast_natAbs, Int.cast_abs]]
      exact_mod_cast Nat.mul_le_mul_left 16 hcLowerNat
    · rw [abs_reflectedTriple_first hb]
      dsimp only [gmCubicReflectedAffineScales]
      rw [show |(m.2.2 : ℝ)| = (m.2.2.natAbs : ℝ) by
        simp only [Nat.cast_natAbs, Int.cast_abs]]
      have hmul := Nat.mul_le_mul_left 16 hcUpperNat
      have heq : 16 * 2 ^ (q + 1) = 2 * (16 * 2 ^ q) := by
        rw [pow_succ']
        ring
      exact_mod_cast hmul.trans_eq heq
  · rw [mem_gmAffinePositiveShell]
    dsimp only [gmCubicReflectedAffineScales,
      gmCubicNormalizedReflectedTriple]
    constructor
    · exact_mod_cast Nat.mul_le_mul_left 48 hmBlock.2.2.2.1
    · have hmul := Nat.mul_le_mul_left 48
          (Nat.le_of_lt hmBlock.2.2.2.2)
      have heq : 48 * 2 ^ (s + 1) = 2 * (48 * 2 ^ s) := by
        rw [pow_succ']
        ring
      exact_mod_cast hmul.trans_eq heq
  · apply mem_gmAffineCentralShell_of_abs_bound
    have hcentral := abs_reflectedTriple_central_le hb
    have haLe := hmOrdered.2.1
    dsimp only [gmCubicReflectedAffineScales]
    push_cast
    rw [pow_succ'] at hbUpper
    norm_num at hbUpper ⊢
    nlinarith

theorem gmCubicReflectedAffineScales_mem_terminal
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicDyadicFrequencyBlock H r s) :
    gmCubicReflectedAffineScales m s ∈
      gmAffineScaleTriples (gmCubicAffineTerminalScale s) := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmOrdered := mem_gmCubicOrderedFrequencyBox.mp hmBalanced.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmOrdered.1
  have hcAbs : m.2.2.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hmNZ.2.2.2
  let q := Nat.log 2 m.2.2.natAbs
  have hqLower : 2 ^ q ≤ m.2.2.natAbs :=
    Nat.pow_log_le_self 2 hcAbs
  have hbalancedNat : m.2.2.natAbs ≤ 5 * m.2.1.natAbs := by
    have hcast : (m.2.2.natAbs : ℝ) ≤ 5 * (m.2.1.natAbs : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hmBalanced.2
    exact_mod_cast hcast
  have hcLt : m.2.2.natAbs < 2 ^ (s + 4) := by
    calc
      m.2.2.natAbs ≤ 5 * m.2.1.natAbs := hbalancedNat
      _ < 5 * 2 ^ (s + 1) :=
        Nat.mul_lt_mul_of_pos_left hmBlock.2.2.2.2 (by omega)
      _ < 2 ^ (s + 4) := by
        have heq : 2 ^ (s + 4) = 8 * 2 ^ (s + 1) := by
          rw [show s + 4 = 3 + (s + 1) by omega, pow_add]
          norm_num
        rw [heq]
        exact Nat.mul_lt_mul_of_pos_right (by omega)
          (pow_pos (by omega) _)
  have hpowLt : 2 ^ q < 2 ^ (s + 4) := hqLower.trans_lt hcLt
  have hq : q ≤ s + 3 := by
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hpowLt
    omega
  rw [mem_gmAffineScaleTriples]
  dsimp only [gmCubicReflectedAffineScales, gmCubicAffineTerminalScale]
  have hqPow : 2 ^ q ≤ 2 ^ (s + 3) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hq
  have hsPos : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) _
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  · calc
      16 * 2 ^ q ≤ 16 * 2 ^ (s + 3) := Nat.mul_le_mul_left 16 hqPow
      _ = 128 * 2 ^ s := by rw [pow_add]; norm_num; ring
  · omega
  · omega

/-! ## Two-sign injective reindexing of a selected frequency block -/

noncomputable def gmCubicPositiveDenominatorBlock (H r s : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicDyadicFrequencyBlock H r s).filter fun m => 0 < m.2.1

noncomputable def gmCubicNegativeDenominatorBlock (H r s : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicDyadicFrequencyBlock H r s).filter fun m => m.2.1 < 0

@[simp] theorem mem_gmCubicPositiveDenominatorBlock
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicPositiveDenominatorBlock H r s ↔
      m ∈ gmCubicDyadicFrequencyBlock H r s ∧ 0 < m.2.1 := by
  simp [gmCubicPositiveDenominatorBlock]

@[simp] theorem mem_gmCubicNegativeDenominatorBlock
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicNegativeDenominatorBlock H r s ↔
      m ∈ gmCubicDyadicFrequencyBlock H r s ∧ m.2.1 < 0 := by
  simp [gmCubicNegativeDenominatorBlock]

theorem gmCubicNormalizedDirectTriple_injective_of_denominator_pos
    {x y : ℤ × (ℤ × ℤ)} (hx : 0 < x.2.1) (hy : 0 < y.2.1)
    (hxy : gmCubicNormalizedDirectTriple x =
      gmCubicNormalizedDirectTriple y) : x = y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨a', b', c'⟩
  simp only at hx hy
  have hden := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hxy
  change 48 * (b.natAbs : ℤ) = 48 * (b'.natAbs : ℤ) at hden
  have habs : b.natAbs = b'.natAbs := by exact_mod_cast (by omega :
    (b.natAbs : ℤ) = (b'.natAbs : ℤ))
  rcases Int.natAbs_eq_natAbs_iff.mp habs with hbb | hbb
  · subst b'
    have hfirst := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hxy
    have hcentral := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hxy
    dsimp only [gmCubicNormalizedDirectTriple] at hfirst hcentral
    rw [Int.sign_eq_one_of_pos hx] at hfirst hcentral
    have ha : a = a' := by omega
    have hc : c = c' := by omega
    subst a'; subst c'; rfl
  · omega

theorem gmCubicNormalizedDirectTriple_injective_of_denominator_neg
    {x y : ℤ × (ℤ × ℤ)} (hx : x.2.1 < 0) (hy : y.2.1 < 0)
    (hxy : gmCubicNormalizedDirectTriple x =
      gmCubicNormalizedDirectTriple y) : x = y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨a', b', c'⟩
  simp only at hx hy
  have hden := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hxy
  change 48 * (b.natAbs : ℤ) = 48 * (b'.natAbs : ℤ) at hden
  have habs : b.natAbs = b'.natAbs := by exact_mod_cast (by omega :
    (b.natAbs : ℤ) = (b'.natAbs : ℤ))
  rcases Int.natAbs_eq_natAbs_iff.mp habs with hbb | hbb
  · subst b'
    have hfirst := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hxy
    have hcentral := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hxy
    dsimp only [gmCubicNormalizedDirectTriple] at hfirst hcentral
    rw [Int.sign_eq_neg_one_of_neg hx] at hfirst hcentral
    have ha : a = a' := by omega
    have hc : c = c' := by omega
    subst a'; subst c'; rfl
  · omega

theorem gmCubicNormalizedReflectedTriple_injective_of_denominator_pos
    {x y : ℤ × (ℤ × ℤ)} (hx : 0 < x.2.1) (hy : 0 < y.2.1)
    (hxy : gmCubicNormalizedReflectedTriple x =
      gmCubicNormalizedReflectedTriple y) : x = y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨a', b', c'⟩
  simp only at hx hy
  have hden := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hxy
  change 48 * (b.natAbs : ℤ) = 48 * (b'.natAbs : ℤ) at hden
  have habs : b.natAbs = b'.natAbs := by exact_mod_cast (by omega :
    (b.natAbs : ℤ) = (b'.natAbs : ℤ))
  rcases Int.natAbs_eq_natAbs_iff.mp habs with hbb | hbb
  · subst b'
    have hfirst := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hxy
    have hcentral := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hxy
    dsimp only [gmCubicNormalizedReflectedTriple] at hfirst hcentral
    rw [Int.sign_eq_one_of_pos hx] at hfirst hcentral
    have hc : c = c' := by omega
    have ha : a = a' := by omega
    subst a'; subst c'; rfl
  · omega

theorem gmCubicNormalizedReflectedTriple_injective_of_denominator_neg
    {x y : ℤ × (ℤ × ℤ)} (hx : x.2.1 < 0) (hy : y.2.1 < 0)
    (hxy : gmCubicNormalizedReflectedTriple x =
      gmCubicNormalizedReflectedTriple y) : x = y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨a', b', c'⟩
  simp only at hx hy
  have hden := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.1) hxy
  change 48 * (b.natAbs : ℤ) = 48 * (b'.natAbs : ℤ) at hden
  have habs : b.natAbs = b'.natAbs := by exact_mod_cast (by omega :
    (b.natAbs : ℤ) = (b'.natAbs : ℤ))
  rcases Int.natAbs_eq_natAbs_iff.mp habs with hbb | hbb
  · subst b'
    have hfirst := congrArg (fun p : ℤ × (ℤ × ℤ) => p.1) hxy
    have hcentral := congrArg (fun p : ℤ × (ℤ × ℤ) => p.2.2) hxy
    dsimp only [gmCubicNormalizedReflectedTriple] at hfirst hcentral
    rw [Int.sign_eq_neg_one_of_neg hx] at hfirst hcentral
    have hc : c = c' := by omega
    have ha : a = a' := by omega
    subst a'; subst c'; rfl
  · omega

theorem finset_sum_comp_le_sum_of_injOn
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (U : Finset β) (g : α → β) (F : β → ℝ)
    (hg : Set.InjOn g S) (hmap : ∀ x ∈ S, g x ∈ U)
    (hF : ∀ y, 0 ≤ F y) :
    (∑ x ∈ S, F (g x)) ≤ ∑ y ∈ U, F y := by
  calc
    (∑ x ∈ S, F (g x)) = ∑ y ∈ S.image g, F y := by
      rw [Finset.sum_image hg]
    _ ≤ ∑ y ∈ U, F y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hmap x hx
      · intro y hyU hyImage
        exact hF y

theorem gmCubicDyadicFrequencyBlock_denominator_split
    (F : ℤ × (ℤ × ℤ) → ℝ) (H r s : ℕ) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s, F m) =
      (∑ m ∈ gmCubicPositiveDenominatorBlock H r s, F m) +
      ∑ m ∈ gmCubicNegativeDenominatorBlock H r s, F m := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := gmCubicDyadicFrequencyBlock H r s)
    (p := fun m : ℤ × (ℤ × ℤ) => 0 < m.2.1) F
  change (∑ m ∈ gmCubicDyadicFrequencyBlock H r s, F m) =
    (∑ m ∈ (gmCubicDyadicFrequencyBlock H r s).filter
      (fun m => 0 < m.2.1), F m) +
    ∑ m ∈ (gmCubicDyadicFrequencyBlock H r s).filter
      (fun m => m.2.1 < 0), F m
  calc
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s, F m) =
        (∑ m ∈ (gmCubicDyadicFrequencyBlock H r s).filter
          (fun m => 0 < m.2.1), F m) +
        ∑ m ∈ (gmCubicDyadicFrequencyBlock H r s).filter
          (fun m => ¬ 0 < m.2.1), F m := hsplit.symm
    _ = _ := by
      congr 1
      apply Finset.sum_congr
      · ext m
        by_cases hm : m ∈ gmCubicDyadicFrequencyBlock H r s
        · have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
          have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp
            (mem_gmCubicOrderedFrequencyBox.mp
              (mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1).1).1
          have hb := hmNZ.2.2.1
          simp only [Finset.mem_filter, hm, true_and]
          omega
        · simp [hm]
      · intro m hm
        rfl

theorem sum_gmCubicDirectAffineSource_le_two_transform
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    {H r s : ℕ} (u : ℝ) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmAffineTerm (gmCubicNormalizedAffineSourceSchwartz B hB W)
          (gmCubicNormalizedDirectTriple m).1
          (gmCubicNormalizedDirectTriple m).2.1
          (gmCubicNormalizedDirectTriple m).2.2 u) ≤
      2 * gmAffineTransformSum
        (gmCubicNormalizedAffineSourceSchwartz B hB W)
        (gmCubicDirectAffineScales r s).1
        (gmCubicDirectAffineScales r s).2.1
        (gmCubicDirectAffineScales r s).2.2 u := by
  let f := gmCubicNormalizedAffineSourceSchwartz B hB W
  let G := gmCubicNormalizedDirectTriple
  let U := gmAffineIndexSet (gmCubicDirectAffineScales r s).1
    (gmCubicDirectAffineScales r s).2.1
    (gmCubicDirectAffineScales r s).2.2
  let F : ℤ × (ℤ × ℤ) → ℝ := fun p =>
    gmAffineTerm f p.1 p.2.1 p.2.2 u
  have hpos : (∑ m ∈ gmCubicPositiveDenominatorBlock H r s, F (G m)) ≤
      ∑ p ∈ U, F p := by
    apply finset_sum_comp_le_sum_of_injOn
    · intro x hx y hy hxy
      exact gmCubicNormalizedDirectTriple_injective_of_denominator_pos
        (mem_gmCubicPositiveDenominatorBlock.mp hx).2
        (mem_gmCubicPositiveDenominatorBlock.mp hy).2 hxy
    · intro m hm
      exact gmCubicNormalizedDirectTriple_mem_indexSet
        (mem_gmCubicPositiveDenominatorBlock.mp hm).1
    · intro p
      unfold F gmAffineTerm f
      exact gmCubicNormalizedAffineSourceSchwartz_nonneg B hB W _
  have hneg : (∑ m ∈ gmCubicNegativeDenominatorBlock H r s, F (G m)) ≤
      ∑ p ∈ U, F p := by
    apply finset_sum_comp_le_sum_of_injOn
    · intro x hx y hy hxy
      exact gmCubicNormalizedDirectTriple_injective_of_denominator_neg
        (mem_gmCubicNegativeDenominatorBlock.mp hx).2
        (mem_gmCubicNegativeDenominatorBlock.mp hy).2 hxy
    · intro m hm
      exact gmCubicNormalizedDirectTriple_mem_indexSet
        (mem_gmCubicNegativeDenominatorBlock.mp hm).1
    · intro p
      unfold F gmAffineTerm f
      exact gmCubicNormalizedAffineSourceSchwartz_nonneg B hB W _
  rw [gmCubicDyadicFrequencyBlock_denominator_split]
  rw [gmAffineTransformSum_eq_indexSum]
  change (∑ m ∈ gmCubicPositiveDenominatorBlock H r s, F (G m)) +
      (∑ m ∈ gmCubicNegativeDenominatorBlock H r s, F (G m)) ≤
    2 * ∑ p ∈ U, F p
  linarith

theorem log_natAbs_third_mem_Icc_of_mem_dyadicBlock
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicDyadicFrequencyBlock H r s) :
    Nat.log 2 m.2.2.natAbs ∈ Finset.Icc s (s + 3) := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmOrdered := mem_gmCubicOrderedFrequencyBox.mp hmBalanced.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmOrdered.1
  have hcAbs : m.2.2.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hmNZ.2.2.2
  let q := Nat.log 2 m.2.2.natAbs
  have hqLower : 2 ^ q ≤ m.2.2.natAbs :=
    Nat.pow_log_le_self 2 hcAbs
  have hqUpper : m.2.2.natAbs < 2 ^ (q + 1) :=
    Nat.lt_pow_succ_log_self (by omega : 1 < 2) m.2.2.natAbs
  have hbcNat : m.2.1.natAbs ≤ m.2.2.natAbs := by
    have hcast : (m.2.1.natAbs : ℝ) ≤ (m.2.2.natAbs : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hmOrdered.2.2
    exact_mod_cast hcast
  have hsLower : s ≤ q := by
    by_contra hnot
    have hqs : q + 1 ≤ s := by omega
    have hp : 2 ^ (q + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hqs
    omega
  have hbalancedNat : m.2.2.natAbs ≤ 5 * m.2.1.natAbs := by
    have hcast : (m.2.2.natAbs : ℝ) ≤ 5 * (m.2.1.natAbs : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hmBalanced.2
    exact_mod_cast hcast
  have hcLt : m.2.2.natAbs < 2 ^ (s + 4) := by
    calc
      m.2.2.natAbs ≤ 5 * m.2.1.natAbs := hbalancedNat
      _ < 5 * 2 ^ (s + 1) :=
        Nat.mul_lt_mul_of_pos_left hmBlock.2.2.2.2 (by omega)
      _ < 2 ^ (s + 4) := by
        have heq : 2 ^ (s + 4) = 8 * 2 ^ (s + 1) := by
          rw [show s + 4 = 3 + (s + 1) by omega, pow_add]
          norm_num
        rw [heq]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) _)
  have hpowLt : 2 ^ q < 2 ^ (s + 4) := hqLower.trans_lt hcLt
  have hsUpper : q ≤ s + 3 := by
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hpowLt
    omega
  exact Finset.mem_Icc.mpr ⟨hsLower, hsUpper⟩

noncomputable def gmCubicReflectedAffineIndexSet (s : ℕ) :
    Finset (ℕ × (ℤ × (ℤ × ℤ))) :=
  (Finset.Icc s (s + 3)).biUnion fun q =>
    (gmAffineIndexSet (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s)).image
      fun p => (q, p)

noncomputable def gmCubicReflectedAffineAggregate
    (f : ℝ → ℝ) (s : ℕ) (u : ℝ) : ℝ :=
  ∑ qp ∈ gmCubicReflectedAffineIndexSet s,
    gmAffineTerm f qp.2.1 qp.2.2.1 qp.2.2.2 u

theorem mem_gmCubicReflectedAffineIndexSet
    {s q : ℕ} {p : ℤ × (ℤ × ℤ)}
    (hq : q ∈ Finset.Icc s (s + 3))
    (hp : p ∈ gmAffineIndexSet (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s)) :
    (q, p) ∈ gmCubicReflectedAffineIndexSet s := by
  unfold gmCubicReflectedAffineIndexSet
  apply Finset.mem_biUnion.mpr
  refine ⟨q, hq, ?_⟩
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem sum_gmCubicReflectedAffineSource_le_two_aggregate
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    {H r s : ℕ} (u : ℝ) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmAffineTerm (gmCubicNormalizedAffineSourceSchwartz B hB W)
          (gmCubicNormalizedReflectedTriple m).1
          (gmCubicNormalizedReflectedTriple m).2.1
          (gmCubicNormalizedReflectedTriple m).2.2 u) ≤
      2 * gmCubicReflectedAffineAggregate
        (gmCubicNormalizedAffineSourceSchwartz B hB W) s u := by
  let f := gmCubicNormalizedAffineSourceSchwartz B hB W
  let G : ℤ × (ℤ × ℤ) → ℕ × (ℤ × (ℤ × ℤ)) := fun m =>
    (Nat.log 2 m.2.2.natAbs, gmCubicNormalizedReflectedTriple m)
  let U := gmCubicReflectedAffineIndexSet s
  let F : ℕ × (ℤ × (ℤ × ℤ)) → ℝ := fun qp =>
    gmAffineTerm f qp.2.1 qp.2.2.1 qp.2.2.2 u
  have hmap (m : ℤ × (ℤ × ℤ))
      (hm : m ∈ gmCubicDyadicFrequencyBlock H r s) : G m ∈ U := by
    apply mem_gmCubicReflectedAffineIndexSet
    · exact log_natAbs_third_mem_Icc_of_mem_dyadicBlock hm
    · simpa only [gmCubicReflectedAffineScales] using
        gmCubicNormalizedReflectedTriple_mem_indexSet hm
  have hpos : (∑ m ∈ gmCubicPositiveDenominatorBlock H r s, F (G m)) ≤
      ∑ qp ∈ U, F qp := by
    apply finset_sum_comp_le_sum_of_injOn
    · intro x hx y hy hxy
      exact gmCubicNormalizedReflectedTriple_injective_of_denominator_pos
        (mem_gmCubicPositiveDenominatorBlock.mp hx).2
        (mem_gmCubicPositiveDenominatorBlock.mp hy).2
        (congrArg Prod.snd hxy)
    · intro m hm
      exact hmap m (mem_gmCubicPositiveDenominatorBlock.mp hm).1
    · intro qp
      unfold F gmAffineTerm f
      exact gmCubicNormalizedAffineSourceSchwartz_nonneg B hB W _
  have hneg : (∑ m ∈ gmCubicNegativeDenominatorBlock H r s, F (G m)) ≤
      ∑ qp ∈ U, F qp := by
    apply finset_sum_comp_le_sum_of_injOn
    · intro x hx y hy hxy
      exact gmCubicNormalizedReflectedTriple_injective_of_denominator_neg
        (mem_gmCubicNegativeDenominatorBlock.mp hx).2
        (mem_gmCubicNegativeDenominatorBlock.mp hy).2
        (congrArg Prod.snd hxy)
    · intro m hm
      exact hmap m (mem_gmCubicNegativeDenominatorBlock.mp hm).1
    · intro qp
      unfold F gmAffineTerm f
      exact gmCubicNormalizedAffineSourceSchwartz_nonneg B hB W _
  rw [gmCubicDyadicFrequencyBlock_denominator_split]
  change (∑ m ∈ gmCubicPositiveDenominatorBlock H r s, F (G m)) +
      (∑ m ∈ gmCubicNegativeDenominatorBlock H r s, F (G m)) ≤
    2 * ∑ qp ∈ U, F qp
  linarith

theorem gmCubicReflectedAffineAggregate_eq_scaleSum
    (f : ℝ → ℝ) (s : ℕ) (u : ℝ) :
    gmCubicReflectedAffineAggregate f s u =
      ∑ q ∈ Finset.Icc s (s + 3),
        gmAffineTransformSum f (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s) u := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(Finset.Icc s (s + 3)))
      (fun q : ℕ =>
        (gmAffineIndexSet (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s)).image
          fun p => (q, p)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffineIndexSet (16 * 2 ^ a) (48 * 2 ^ s) (24 * 2 ^ s)).image
        fun p => (a, p))
      ((gmAffineIndexSet (16 * 2 ^ b) (48 * 2 ^ s) (24 * 2 ^ s)).image
        fun p => (b, p))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨pa, hpaMem, hpaEq⟩ := Finset.mem_image.mp hpa
    obtain ⟨pb, hpbMem, hpbEq⟩ := Finset.mem_image.mp hpb
    apply hab
    have hfirst : (a, pa).1 = (b, pb).1 := by rw [hpaEq, hpbEq]
    simpa using hfirst
  unfold gmCubicReflectedAffineAggregate gmCubicReflectedAffineIndexSet
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_image]
  · symm
    exact gmAffineTransformSum_eq_indexSum f
      (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s) u
  · intro a ha b hb hab
    exact congrArg Prod.snd hab

theorem integrable_gmAffineTransformSum_sq_native
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    Integrable (fun u : ℝ => gmAffineTransformSum f M₁ M₂ M₃ u ^ 2) := by
  let S := gmAffineIndexSet M₁ M₂ M₃
  let G : ℝ → ℝ := fun u =>
    (S.card : ℝ) * ∑ p ∈ S, gmAffineTerm f p.1 p.2.1 p.2.2 u ^ 2
  have hG : Integrable G := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro p hp
    exact integrable_gmAffineTerm_sq ((f.memLp (2 : ENNReal)).integrable_sq)
      (gmAffineSignedShell_ne_zero hM₁ (mem_gmAffineIndexSet.mp hp).1)
      (gmAffinePositiveShell_ne_zero hM₂ (mem_gmAffineIndexSet.mp hp).2.1)
  apply hG.mono'
    ((continuous_gmAffineTransformSum f.continuous M₁ M₂ M₃).pow 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact gmAffineTransformSum_sq_le f M₁ M₂ M₃ u

theorem integral_sq_gmCubicReflectedAffineAggregate_le_sixteen_J
    (f : SchwartzMap ℝ ℝ) {s : ℕ} :
    (∫ u : ℝ, gmCubicReflectedAffineAggregate f s u ^ 2) ≤
      16 * gmAffineJ f (gmCubicAffineTerminalScale s) := by
  let Q := Finset.Icc s (s + 3)
  let A : ℕ → ℝ → ℝ := fun q u =>
    gmAffineTransformSum f (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s) u
  have hQcard : Q.card = 4 := by
    simp [Q]
    omega
  have hAInt (q : ℕ) : Integrable (fun u : ℝ => A q u ^ 2) := by
    apply integrable_gmAffineTransformSum_sq_native
    · positivity
    · positivity
  have hmajorInt : Integrable (fun u : ℝ =>
      (Q.card : ℝ) * ∑ q ∈ Q, A q u ^ 2) := by
    apply Integrable.const_mul
    exact integrable_finsetSum Q (fun q _ => hAInt q)
  have hpoint (u : ℝ) :
      gmCubicReflectedAffineAggregate f s u ^ 2 ≤
        (Q.card : ℝ) * ∑ q ∈ Q, A q u ^ 2 := by
    rw [gmCubicReflectedAffineAggregate_eq_scaleSum]
    exact sq_sum_le_card_mul_sum_sq
  have hint : (∫ u : ℝ, gmCubicReflectedAffineAggregate f s u ^ 2) ≤
      (Q.card : ℝ) * ∑ q ∈ Q, ∫ u : ℝ, A q u ^ 2 := by
    calc
      (∫ u : ℝ, gmCubicReflectedAffineAggregate f s u ^ 2) ≤
          ∫ u : ℝ, (Q.card : ℝ) * ∑ q ∈ Q, A q u ^ 2 := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          hmajorInt
          (Filter.Eventually.of_forall hpoint)
      _ = (Q.card : ℝ) * ∑ q ∈ Q, ∫ u : ℝ, A q u ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact MeasureTheory.integral_finsetSum Q (fun q _ => hAInt q)
  calc
    (∫ u : ℝ, gmCubicReflectedAffineAggregate f s u ^ 2) ≤
        (Q.card : ℝ) * ∑ q ∈ Q, ∫ u : ℝ, A q u ^ 2 := hint
    _ ≤ (Q.card : ℝ) * ∑ _q ∈ Q,
        gmAffineJ f (gmCubicAffineTerminalScale s) := by
      gcongr with q hq
      exact gmAffineTransformIntegral_le_J f
        (show 0 < gmCubicAffineTerminalScale s by
          unfold gmCubicAffineTerminalScale
          positivity)
        (by
          rw [mem_gmAffineScaleTriples]
          have hqMem := Finset.mem_Icc.mp hq
          have hqPow : 2 ^ q ≤ 2 ^ (s + 3) :=
            Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hqMem.2
          unfold gmCubicAffineTerminalScale
          have hsPos : 0 < 2 ^ s := pow_pos (by norm_num : 0 < (2 : ℕ)) s
          refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
            Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
            Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
          · calc
              16 * 2 ^ q ≤ 16 * 2 ^ (s + 3) := Nat.mul_le_mul_left 16 hqPow
              _ = 128 * 2 ^ s := by rw [pow_add]; norm_num; ring
          · omega
          · omega)
    _ = 16 * gmAffineJ f (gmCubicAffineTerminalScale s) := by
      norm_num [hQcard]
      ring

theorem gmCubicReflectedAffineAggregate_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (s : ℕ) (u : ℝ) :
    0 ≤ gmCubicReflectedAffineAggregate f s u := by
  unfold gmCubicReflectedAffineAggregate gmAffineTerm
  exact Finset.sum_nonneg fun qp _ => hf _

theorem integrable_sq_gmCubicReflectedAffineAggregate
    (f : SchwartzMap ℝ ℝ) (s : ℕ) :
    Integrable (fun u : ℝ => gmCubicReflectedAffineAggregate f s u ^ 2) := by
  let Q := Finset.Icc s (s + 3)
  let A : ℕ → ℝ → ℝ := fun q u =>
    gmAffineTransformSum f (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s) u
  have hAInt (q : ℕ) : Integrable (fun u : ℝ => A q u ^ 2) :=
    integrable_gmAffineTransformSum_sq_native f (by positivity) (by positivity)
  have hmajorInt : Integrable (fun u : ℝ =>
      (Q.card : ℝ) * ∑ q ∈ Q, A q u ^ 2) := by
    apply Integrable.const_mul
    exact integrable_finsetSum Q (fun q _ => hAInt q)
  have hcont : Continuous (gmCubicReflectedAffineAggregate f s) := by
    rw [funext (gmCubicReflectedAffineAggregate_eq_scaleSum f s)]
    apply continuous_finsetSum
    intro q hq
    exact continuous_gmAffineTransformSum f.continuous
      (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s)
  apply hmajorInt.mono' (hcont.pow 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [gmCubicReflectedAffineAggregate_eq_scaleSum]
  exact sq_sum_le_card_mul_sum_sq

theorem continuous_gmCubicReflectedAffineAggregate
    (f : SchwartzMap ℝ ℝ) (s : ℕ) :
    Continuous (gmCubicReflectedAffineAggregate f s) := by
  rw [funext (gmCubicReflectedAffineAggregate_eq_scaleSum f s)]
  apply continuous_finsetSum
  intro q hq
  exact continuous_gmAffineTransformSum f.continuous
    (16 * 2 ^ q) (48 * 2 ^ s) (24 * 2 ^ s)

theorem setIntegral_sq_gmCubicDirectAffineTransform_le_J
    (f : SchwartzMap ℝ ℝ) {r s : ℕ} (hrs : r ≤ s) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmAffineTransformSum f
          (gmCubicDirectAffineScales r s).1
          (gmCubicDirectAffineScales r s).2.1
          (gmCubicDirectAffineScales r s).2.2 u ^ 2) ≤
      gmAffineJ f (gmCubicAffineTerminalScale s) := by
  let D : ℝ → ℝ := fun u =>
    gmAffineTransformSum f
      (gmCubicDirectAffineScales r s).1
      (gmCubicDirectAffineScales r s).2.1
      (gmCubicDirectAffineScales r s).2.2 u ^ 2
  have hDInt : Integrable D := by
    apply integrable_gmAffineTransformSum_sq_native
    · unfold gmCubicDirectAffineScales
      positivity
    · unfold gmCubicDirectAffineScales
      positivity
  calc
    (∫ u in Set.Icc (1 / 2 : ℝ) 2, D u) ≤ ∫ u : ℝ, D u := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hDInt
    _ = gmAffineTransformIntegral f
        (gmCubicDirectAffineScales r s).1
        (gmCubicDirectAffineScales r s).2.1
        (gmCubicDirectAffineScales r s).2.2 := rfl
    _ ≤ gmAffineJ f (gmCubicAffineTerminalScale s) :=
      gmAffineTransformIntegral_le_J f
        (show 0 < gmCubicAffineTerminalScale s by
          unfold gmCubicAffineTerminalScale
          positivity)
        (gmCubicDirectAffineScales_mem_terminal hrs)

theorem setIntegral_sq_gmCubicReflectedAffineAggregate_inv_le_sixtyfour_J
    (f : SchwartzMap ℝ ℝ) {s : ℕ} :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicReflectedAffineAggregate f s u⁻¹ ^ 2) ≤
      64 * gmAffineJ f (gmCubicAffineTerminalScale s) := by
  let R : ℝ → ℝ := fun u => gmCubicReflectedAffineAggregate f s u ^ 2
  have hRInt : Integrable R := by
    exact integrable_sq_gmCubicReflectedAffineAggregate f s
  have hinv := setIntegral_comp_inv_le_four_mul hRInt.integrableOn
    (fun u => sq_nonneg (gmCubicReflectedAffineAggregate f s u))
  have hglobal := integral_sq_gmCubicReflectedAffineAggregate_le_sixteen_J
    (f := f) (s := s)
  have hrestrict : (∫ u in Set.Icc (1 / 2 : ℝ) 2, R u) ≤ ∫ u : ℝ, R u := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hRInt
  calc
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicReflectedAffineAggregate f s u⁻¹ ^ 2) =
        ∫ u in Set.Icc (1 / 2 : ℝ) 2, R u⁻¹ := rfl
    _ ≤ 4 * ∫ u in Set.Icc (1 / 2 : ℝ) 2, R u := hinv
    _ ≤ 4 * ∫ u : ℝ, R u :=
      mul_le_mul_of_nonneg_left hrestrict (by norm_num)
    _ ≤ 4 * (16 * gmAffineJ f (gmCubicAffineTerminalScale s)) := by
      gcongr
    _ = 64 * gmAffineJ f (gmCubicAffineTerminalScale s) := by ring

noncomputable def gmCubicSelectedSmoothedBlock
    (η T : ℝ) (N M H r s : ℕ) (W : Finset ℝ) (u : ℝ) : ℝ :=
  ∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
    gmCubicSmoothedModeIntegrand η T N M W m u

theorem gmCubicSelectedSmoothedBlock_nonneg
    (η T : ℝ) (N M H r s : ℕ) (W : Finset ℝ) (u : ℝ) :
    0 ≤ gmCubicSelectedSmoothedBlock η T N M H r s W u := by
  unfold gmCubicSelectedSmoothedBlock
  exact Finset.sum_nonneg fun m _ =>
    gmCubicSmoothedModeIntegrand_nonneg η T N M W m u

theorem gmCubicSelectedSmoothedBlock_pointwise_affine_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M)
    {u : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    gmCubicSelectedSmoothedBlock η T N M H r s W u ≤
      2 * ‖gmR W u‖ *
        Real.sqrt (gmCubicReflectedAffineAggregate
          (gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N M) hB W) s u⁻¹) *
        Real.sqrt (gmAffineTransformSum
          (gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N M) hB W)
          (gmCubicDirectAffineScales r s).1
          (gmCubicDirectAffineScales r s).2.1
          (gmCubicDirectAffineScales r s).2.2 u) := by
  let B := gmCubicDyadicFrequencyBlock H r s
  let f := gmCubicNormalizedAffineSourceSchwartz
    (gmCubicSmoothingScale η T N M) hB W
  let A : ℤ × (ℤ × ℤ) → ℝ := fun m =>
    gmCubicSmoothedRSq η T N M W
      (gmCubicReflectedCancellationCenter m u)
  let D : ℤ × (ℤ × ℤ) → ℝ := fun m =>
    gmCubicSmoothedRSq η T N M W (gmCubicCancellationCenter m u)
  let RA := gmCubicReflectedAffineAggregate f s u⁻¹
  let DA := gmAffineTransformSum f
    (gmCubicDirectAffineScales r s).1
    (gmCubicDirectAffineScales r s).2.1
    (gmCubicDirectAffineScales r s).2.2 u
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)
  have hA0 (m : ℤ × (ℤ × ℤ)) : 0 ≤ A m :=
    gmCubicSmoothedRSq_nonneg W _ hB.le
  have hD0 (m : ℤ × (ℤ × ℤ)) : 0 ≤ D m :=
    gmCubicSmoothedRSq_nonneg W _ hB.le
  have hcs := Real.sum_sqrt_mul_sqrt_le B hA0 hD0
  have hDsum : (∑ m ∈ B, D m) ≤ 2 * DA := by
    have hsource := sum_gmCubicDirectAffineSource_le_two_transform hB W
      (H := H) (r := r) (s := s) u
    convert hsource using 1
    apply Finset.sum_congr rfl
    intro m hm
    have hmBlock : m ∈ gmCubicDyadicFrequencyBlock H r s := hm
    have hb := (mem_gmCubicNonzeroFrequencyBox.mp
      (mem_gmCubicOrderedFrequencyBox.mp
        (mem_gmCubicBalancedOrderedFrequencyBox.mp
          (mem_gmCubicDyadicFrequencyBlock.mp hmBlock).1).1).1).2.2.1
    dsimp only [D, f]
    rw [← gmCubicSmoothedRSqSchwartz_apply]
    exact (gmCubicNormalizedAffineSource_directTriple hB W hb u).symm
  have hRsum : (∑ m ∈ B, A m) ≤ 2 * RA := by
    have hsource := sum_gmCubicReflectedAffineSource_le_two_aggregate hB W
      (H := H) (r := r) (s := s) u⁻¹
    convert hsource using 1
    apply Finset.sum_congr rfl
    intro m hm
    have hmBlock : m ∈ gmCubicDyadicFrequencyBlock H r s := hm
    have hb := (mem_gmCubicNonzeroFrequencyBox.mp
      (mem_gmCubicOrderedFrequencyBox.mp
        (mem_gmCubicBalancedOrderedFrequencyBox.mp
          (mem_gmCubicDyadicFrequencyBlock.mp hmBlock).1).1).1).2.2.1
    have hbR : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hb
    have hcenter : gmCubicReflectedCancellationCenter m u =
        -((m.2.2 : ℝ) * u⁻¹ + (m.1 : ℝ)) / (m.2.1 : ℝ) := by
      unfold gmCubicReflectedCancellationCenter gmCubicCancellationCenter
      field_simp [hbR, hu0]
      ring
    dsimp only [A, f]
    rw [hcenter, ← gmCubicSmoothedRSqSchwartz_apply]
    exact (gmCubicNormalizedAffineSource_reflectedTriple hB W hb u⁻¹).symm
  have hRA0 : 0 ≤ RA := gmCubicReflectedAffineAggregate_nonneg
    (gmCubicNormalizedAffineSourceSchwartz_nonneg _ hB W) s u⁻¹
  have hDA0 : 0 ≤ DA := gmAffineTransformSum_nonneg
    (gmCubicNormalizedAffineSourceSchwartz_nonneg _ hB W) _ _ _ u
  have hsqrtR := Real.sqrt_le_sqrt hRsum
  have hsqrtD := Real.sqrt_le_sqrt hDsum
  have hsqrtTwo : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [Real.mul_self_sqrt (by norm_num)]
  unfold gmCubicSelectedSmoothedBlock
  simp_rw [gmCubicSmoothedModeIntegrand, gmCubicSmoothedR]
  change (∑ m ∈ B, ‖gmR W u‖ * Real.sqrt (A m) * Real.sqrt (D m)) ≤ _
  have hfactor :
      (∑ m ∈ B, ‖gmR W u‖ * Real.sqrt (A m) * Real.sqrt (D m)) =
        ‖gmR W u‖ * ∑ m ∈ B, Real.sqrt (A m) * Real.sqrt (D m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hfactor]
  calc
    ‖gmR W u‖ * (∑ m ∈ B, Real.sqrt (A m) * Real.sqrt (D m)) ≤
        ‖gmR W u‖ *
          (Real.sqrt (∑ m ∈ B, A m) * Real.sqrt (∑ m ∈ B, D m)) := by
      gcongr
    _ ≤ ‖gmR W u‖ * (Real.sqrt (2 * RA) * Real.sqrt (2 * DA)) := by
      gcongr
    _ = 2 * ‖gmR W u‖ * Real.sqrt RA * Real.sqrt DA := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        ‖gmR W u‖ * (Real.sqrt 2 * Real.sqrt RA *
            (Real.sqrt 2 * Real.sqrt DA)) =
            ‖gmR W u‖ * (Real.sqrt 2 * Real.sqrt 2) *
              Real.sqrt RA * Real.sqrt DA := by ring
        _ = 2 * ‖gmR W u‖ * Real.sqrt RA * Real.sqrt DA := by
          rw [hsqrtTwo]
          ring
    _ = _ := rfl

/-- Taking a square root sends an `L²` nonnegative function to `L⁴`.
This is the exact exponent conversion needed after the two finite
Cauchy--Schwarz inequalities in Proposition 10.1. -/
theorem memLp_sqrt_four_of_memLp_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hmeas : AEStronglyMeasurable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hf : MemLp f (ENNReal.ofReal 2) μ) :
    MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal 4) μ := by
  have hpow := (memLp_norm_rpow_iff
    (p := ENNReal.ofReal 2) (q := (1 / 2 : ENNReal)) hmeas
      (by norm_num) (by norm_num)).2 hf
  have heq : (fun x => Real.sqrt (f x)) =
      (fun x => ‖f x‖ ^ (1 / 2 : ENNReal).toReal) := by
    funext x
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    norm_num
  rw [heq]
  convert hpow using 1
  rw [ENNReal.div_eq_inv_mul]
  norm_num

/-- The selected Section 10 block satisfies the source `L²-L⁴-L⁴`
bound.  Both affine factors here are the literal reindexings of the
direct and reflected cancellation centers, not independent majorants. -/
theorem setIntegral_gmCubicSelectedSmoothedBlock_holder
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSelectedSmoothedBlock η T N M H r s W u) ≤
      2 * Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
        Real.sqrt
          (Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2,
              gmCubicReflectedAffineAggregate
                (gmCubicNormalizedAffineSourceSchwartz
                  (gmCubicSmoothingScale η T N M) hB W) s u⁻¹ ^ 2) *
            Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2,
              gmAffineTransformSum
                (gmCubicNormalizedAffineSourceSchwartz
                  (gmCubicSmoothingScale η T N M) hB W)
                (gmCubicDirectAffineScales r s).1
                (gmCubicDirectAffineScales r s).2.1
                (gmCubicDirectAffineScales r s).2.2 u ^ 2)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 / 2 : ℝ) 2)
  let f := gmCubicNormalizedAffineSourceSchwartz
    (gmCubicSmoothingScale η T N M) hB W
  let A : ℝ → ℝ := fun u => ‖gmR W u‖
  let R : ℝ → ℝ := fun u => gmCubicReflectedAffineAggregate f s u⁻¹
  let D : ℝ → ℝ := fun u => gmAffineTransformSum f
    (gmCubicDirectAffineScales r s).1
    (gmCubicDirectAffineScales r s).2.1
    (gmCubicDirectAffineScales r s).2.2 u
  let B : ℝ → ℝ := fun u => Real.sqrt (R u)
  let C : ℝ → ℝ := fun u => Real.sqrt (D u)
  have hinvCont : ContinuousOn (fun u : ℝ => u⁻¹)
      (Set.Icc (1 / 2 : ℝ) 2) := by
    apply continuousOn_id.inv₀
    intro u hu
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)
  have hRcont : ContinuousOn R (Set.Icc (1 / 2 : ℝ) 2) := by
    simpa only [R, Function.comp_def] using
      (continuous_gmCubicReflectedAffineAggregate f s).comp_continuousOn hinvCont
  have hDcont : Continuous D := by
    exact continuous_gmAffineTransformSum f.continuous _ _ _
  have hAmeas : AEStronglyMeasurable A μ :=
    (measurable_gmR W).norm.aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable R μ :=
    hRcont.aestronglyMeasurable measurableSet_Icc
  have hDmeas : AEStronglyMeasurable D μ :=
    hDcont.aestronglyMeasurable
  have hR0 : ∀ u, 0 ≤ R u := fun u =>
    gmCubicReflectedAffineAggregate_nonneg
      (gmCubicNormalizedAffineSourceSchwartz_nonneg _ hB W) s u⁻¹
  have hD0 : ∀ u, 0 ≤ D u := fun u =>
    gmAffineTransformSum_nonneg
      (gmCubicNormalizedAffineSourceSchwartz_nonneg _ hB W) _ _ _ u
  have hA2 : MemLp A (ENNReal.ofReal 2) μ := by
    apply MemLp.of_bound hAmeas (W.card : ℝ)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_gmR_le_card_all W u
  have hR2 : MemLp R (ENNReal.ofReal 2) μ := by
    simpa using (memLp_two_iff_integrable_sq hRmeas).2
      (hRcont.pow 2).integrableOn_Icc
  have hD2 : MemLp D (ENNReal.ofReal 2) μ := by
    simpa using (memLp_two_iff_integrable_sq hDmeas).2
      (hDcont.pow 2).continuousOn.integrableOn_Icc
  have hB4 : MemLp B (ENNReal.ofReal 4) μ := by
    simpa only [B] using memLp_sqrt_four_of_memLp_two hRmeas hR0 hR2
  have hC4 : MemLp C (ENNReal.ofReal 4) μ := by
    simpa only [C] using memLp_sqrt_four_of_memLp_two hDmeas hD0 hD2
  have h442 : (4 : ℝ).HolderTriple 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num
  letI : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4)
      (ENNReal.ofReal 2) :=
    h442.ennrealOfReal
  have hBC2 : MemLp (fun u => B u * C u) (ENNReal.ofReal 2) μ := by
    exact hC4.mul' hB4
  have h22 : (2 : ℝ).HolderTriple 2 1 := by
    rw [Real.holderTriple_iff]
    norm_num
  letI : ENNReal.HolderTriple (ENNReal.ofReal 2) (ENNReal.ofReal 2)
      (ENNReal.ofReal 1) :=
    h22.ennrealOfReal
  have hABC1 : MemLp (fun u => A u * (B u * C u))
      (ENNReal.ofReal 1) μ := by
    exact hBC2.mul' hA2
  have hmajorInt : Integrable (fun u => 2 * (A u * B u * C u)) μ := by
    have hABCInt : Integrable (fun u => A u * (B u * C u)) μ := by
      exact hABC1.integrable (by norm_num)
    apply Integrable.const_mul
    convert hABCInt using 1
    funext u
    ring
  have hmono : (∫ u, gmCubicSelectedSmoothedBlock η T N M H r s W u ∂μ) ≤
      ∫ u, 2 * (A u * B u * C u) ∂μ := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun u =>
        gmCubicSelectedSmoothedBlock_nonneg η T N M H r s W u
    · exact hmajorInt
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have hp := gmCubicSelectedSmoothedBlock_pointwise_affine_le
        (H := H) (r := r) (s := s) W hB hu
      dsimp only [A, B, C, R, D, f]
      convert hp using 1
      ring
  have hholder := integral_triple_le_L2_L4_L4
    (A := A) (B := B) (C := C) (μ := μ)
    (Filter.Eventually.of_forall fun u => by dsimp only [A]; positivity)
    (Filter.Eventually.of_forall fun u => by dsimp only [B]; positivity)
    (Filter.Eventually.of_forall fun u => by dsimp only [C]; positivity)
    hA2 hB4 hC4
  have hfour (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
    exact Real.rpow_natCast x 4
  have hBfour (u : ℝ) : B u ^ (4 : ℝ) = R u ^ 2 := by
    rw [hfour]
    dsimp only [B]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (hR0 u)]
  have hCfour (u : ℝ) : C u ^ (4 : ℝ) = D u ^ 2 := by
    rw [hfour]
    dsimp only [C]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sq_sqrt (hD0 u)]
  calc
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSelectedSmoothedBlock η T N M H r s W u) =
        ∫ u, gmCubicSelectedSmoothedBlock η T N M H r s W u ∂μ := rfl
    _ ≤ ∫ u, 2 * (A u * B u * C u) ∂μ := hmono
    _ = 2 * ∫ u, A u * B u * C u ∂μ := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((∫ u, A u ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (((∫ u, B u ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ u, C u ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))) ^
            (1 / (2 : ℝ))) := by gcongr
    _ = _ := by
      simp only [μ, A, B, C, R, D, f, Real.rpow_two, hBfour, hCfour,
        ← Real.sqrt_eq_rpow]
      ring

/-- The two affine square integrals in the selected block are both
absorbed by the single terminal-scale functional `J`.  The numerical
The constant is deliberately explicit, so no `\ll`-notation is hidden in
the Section 10 consumer. -/
theorem setIntegral_gmCubicSelectedSmoothedBlock_le_six
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (hrs : r ≤ s) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSelectedSmoothedBlock η T N M H r s W u) ≤
      6 * Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
        Real.sqrt (gmAffineJ
          (gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N M) hB W)
          (gmCubicAffineTerminalScale s)) := by
  let f := gmCubicNormalizedAffineSourceSchwartz
    (gmCubicSmoothingScale η T N M) hB W
  let L := ∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2
  let Rv := ∫ u in Set.Icc (1 / 2 : ℝ) 2,
    gmCubicReflectedAffineAggregate f s u⁻¹ ^ 2
  let Dv := ∫ u in Set.Icc (1 / 2 : ℝ) 2,
    gmAffineTransformSum f
      (gmCubicDirectAffineScales r s).1
      (gmCubicDirectAffineScales r s).2.1
      (gmCubicDirectAffineScales r s).2.2 u ^ 2
  let J := gmAffineJ f (gmCubicAffineTerminalScale s)
  have hholder := setIntegral_gmCubicSelectedSmoothedBlock_holder
    (H := H) (r := r) (s := s) W hB
  have hholder' :
      (∫ u in Set.Icc (1 / 2 : ℝ) 2,
          gmCubicSelectedSmoothedBlock η T N M H r s W u) ≤
        2 * Real.sqrt L * Real.sqrt (Real.sqrt Rv * Real.sqrt Dv) := by
    simpa only [f, L, Rv, Dv] using hholder
  have hR : Rv ≤ 64 * J := by
    exact setIntegral_sq_gmCubicReflectedAffineAggregate_inv_le_sixtyfour_J
      f
  have hD : Dv ≤ J := by
    exact setIntegral_sq_gmCubicDirectAffineTransform_le_J f hrs
  have hJ0 : 0 ≤ J := by
    apply gmAffineJ_nonneg
    unfold gmCubicAffineTerminalScale
    positivity
  have hL0 : 0 ≤ L := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hR0 : 0 ≤ Rv := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hD0 : 0 ≤ Dv := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hsR0 : 0 ≤ Real.sqrt Rv := Real.sqrt_nonneg _
  have hsD0 : 0 ≤ Real.sqrt Dv := Real.sqrt_nonneg _
  have hsJ0 : 0 ≤ Real.sqrt J := Real.sqrt_nonneg _
  have hsR : Real.sqrt Rv ≤ 8 * Real.sqrt J := by
    have hsqR := Real.sq_sqrt hR0
    have hsqJ := Real.sq_sqrt hJ0
    nlinarith
  have hsD : Real.sqrt Dv ≤ Real.sqrt J := by
    exact Real.sqrt_le_sqrt hD
  have hprod : Real.sqrt Rv * Real.sqrt Dv ≤ 8 * J := by
    have hmul := mul_le_mul hsR hsD hsD0 (mul_nonneg (by norm_num) hsJ0)
    have hsqJ := Real.sq_sqrt hJ0
    nlinarith
  have hnested : Real.sqrt (Real.sqrt Rv * Real.sqrt Dv) ≤
      3 * Real.sqrt J := by
    have hprod0 : 0 ≤ Real.sqrt Rv * Real.sqrt Dv := mul_nonneg hsR0 hsD0
    have hsquare := Real.sq_sqrt hprod0
    have hsqJ := Real.sq_sqrt hJ0
    have hnested0 := Real.sqrt_nonneg (Real.sqrt Rv * Real.sqrt Dv)
    nlinarith
  change (∫ u in Set.Icc (1 / 2 : ℝ) 2,
      gmCubicSelectedSmoothedBlock η T N M H r s W u) ≤
    6 * Real.sqrt L * Real.sqrt J
  calc
    _ ≤ 2 * Real.sqrt L * Real.sqrt (Real.sqrt Rv * Real.sqrt Dv) := hholder'
    _ ≤ 2 * Real.sqrt L * (3 * Real.sqrt J) := by
      exact mul_le_mul_of_nonneg_left hnested
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = 6 * Real.sqrt L * Real.sqrt J := by
      have harith (x y : ℝ) : 2 * x * (3 * y) = 6 * x * y := by ring
      exact harith (Real.sqrt L) (Real.sqrt J)

/-- Finite Fubini for the selected dyadic block: the block integral is
exactly the sum of the source mode integrals from equation (7.6). -/
theorem sum_gmCubicSmoothedModeIntegral_selected_eq
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) =
      ∫ u in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSelectedSmoothedBlock η T N M H r s W u := by
  unfold gmCubicSelectedSmoothedBlock gmCubicSmoothedModeIntegral
  rw [MeasureTheory.integral_finsetSum]
  intro m hm
  exact integrableOn_gmCubicSmoothedModeIntegrand W m hB.le

/-- The selected source sum in Proposition 10.1, after the two
Cauchy--Schwarz steps and the affine reindexing, is controlled by one
terminal-scale `J` functional. -/
theorem sum_gmCubicSmoothedModeIntegral_selected_le_six
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) (hrs : r ≤ s) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) ≤
      6 * Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
        Real.sqrt (gmAffineJ
          (gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N M) hB W)
          (gmCubicAffineTerminalScale s)) := by
  rw [sum_gmCubicSmoothedModeIntegral_selected_eq W hB]
  exact setIntegral_gmCubicSelectedSmoothedBlock_le_six W hB hrs

/-- Proposition 9.1 specialized to the genuine Section 10 source family.
The constants are fixed before the physical height, smoothing scale, set
of ordinates and affine shell size. -/
theorem gmCubicNativeAffineSource_proposition9_1
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ {T B : ℝ}, T₀ ≤ T → ∀ (hB : 0 < B), 32 ≤ B →
      ∀ {W : Finset ℝ}, InBaseInterval T W →
      ∀ {M : ℕ}, 0 < M → (M : ℝ) ≤ T ^ 4 →
        gmAffineJ (gmCubicNativeAffineSourceSchwartz B hB W) M ≤
          C * T ^ epsilon *
            ((M : ℝ) ^ 6 *
                (∫ u : ℝ, gmCubicNativeAffineSourceSchwartz B
                  hB W u) ^ 2 +
              (M : ℝ) ^ 4 *
                ∫ u : ℝ,
                  gmCubicNativeAffineSourceSchwartz B hB W u ^ 2) := by
  obtain ⟨C, T₀, hC, hT₀, hprop⟩ :=
    gmAffine_proposition9_1_height_family_native
      gmCubicNativeHeightProfileConstant
      gmCubicNativeHeightProfileConstant_nonneg hepsilon
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T B hT hB hB32 W hW M hM hMT
  exact hprop hT (gmCubicNativeAffineSourceSchwartz B hB W)
    (gmCubicNativeAffineSourceSchwartz_nonneg B hB W)
    (gmCubicNativeAffineSource_supportedOn hB hB32 W)
    (gmCubicNativeAffineSource_heightFourierMassFamilyAtDepth_zero
      (one_le_two.trans (hT₀.trans hT)) hB hW) hM hMT

/-! ## Proposition 10.1: physical scale bridges and final assembly -/

/-- At the central Guth--Maynard scale the equation-(7.5) smoothing
parameter is large enough for the compact-support input to Proposition
9.1.  The bound is uniform in the selected dyadic index. -/
theorem thirtytwo_le_gmCubicSmoothingScale
    {η T : ℝ} {N s : ℕ} (hT : 4096 ≤ T)
    (hη : η ≤ 1 / 6) (hN : 0 < N)
    (hNlower : T ^ (2 / 3 : ℝ) ≤ (N : ℝ)) :
    32 ≤ gmCubicSmoothingScale η T N (2 ^ s) := by
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4096).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hsNat : (1 : ℕ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hs : (1 : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast hsNat
  have hpη : T ^ η ≤ T ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hTone hη
  have hsqrt : (64 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hsq : (64 : ℝ) ^ 2 ≤ T := by norm_num at hT ⊢; exact hT
    have := Real.sqrt_le_sqrt hsq
    norm_num at this ⊢
    exact this
  have hpowSplit : T ^ (2 / 3 : ℝ) =
      T ^ (1 / 2 : ℝ) * T ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  have hscalePower : 64 * T ^ η ≤ T ^ (2 / 3 : ℝ) := by
    calc
      64 * T ^ η ≤ 64 * T ^ (1 / 6 : ℝ) := by gcongr
      _ ≤ T ^ (1 / 2 : ℝ) * T ^ (1 / 6 : ℝ) := by gcongr
      _ = T ^ (2 / 3 : ℝ) := hpowSplit.symm
  have hnumerator : 64 * T ^ η ≤
      (N : ℝ) * ((2 ^ s : ℕ) : ℝ) := by
    calc
      64 * T ^ η ≤ T ^ (2 / 3 : ℝ) := hscalePower
      _ ≤ (N : ℝ) := hNlower
      _ ≤ (N : ℝ) * ((2 ^ s : ℕ) : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) hs
  unfold gmCubicSmoothingScale
  rw [le_div_iff₀ (mul_pos (by norm_num) (Real.rpow_pos_of_pos hTpos _))]
  nlinarith

/-- The terminal affine scale selected in Section 10 lies within the
`T^4` range of Proposition 9.1.  This uses the actual Section 7 dyadic
index, rather than an independent scale assumption. -/
theorem gmCubicAffineTerminalScale_le_height_four
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 4096 ≤ T) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 6)
    (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    (gmCubicAffineTerminalScale p.2 : ℝ) ≤ T ^ 4 := by
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4096).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hscale := twoPow_second_dyadicIndex_le_two_ratio
    hTone hη0 hN hNT hp
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hratio : 2 * T ^ (1 + η) / (N : ℝ) ≤ 2 * T ^ (1 + η) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
    nlinarith [Real.rpow_nonneg hTpos.le (1 + η)]
  have hpScale : ((2 ^ p.2 : ℕ) : ℝ) ≤ 2 * T ^ (1 + η) :=
    hscale.trans hratio
  have hpScale' : (2 : ℝ) ^ p.2 ≤ 2 * T ^ (1 + η) := by
    norm_num at hpScale ⊢
    exact hpScale
  have hpow : T ^ (1 + η) ≤ T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have hterminal : (gmCubicAffineTerminalScale p.2 : ℝ) ≤
      256 * T ^ (2 : ℝ) := by
    unfold gmCubicAffineTerminalScale
    push_cast
    calc
      (128 : ℝ) * (2 : ℝ) ^ p.2 ≤
          128 * (2 * T ^ (1 + η)) := by gcongr
      _ ≤ 128 * (2 * T ^ (2 : ℝ)) := by gcongr
      _ = 256 * T ^ (2 : ℝ) := by ring
  have hTtwo : (256 : ℝ) ≤ T ^ (2 : ℝ) := by
    rw [show T ^ (2 : ℝ) = T ^ (2 : ℕ) by norm_num [Real.rpow_natCast]]
    nlinarith [sq_nonneg (T - 16)]
  calc
    (gmCubicAffineTerminalScale p.2 : ℝ) ≤ 256 * T ^ (2 : ℝ) := hterminal
    _ ≤ T ^ (2 : ℝ) * T ^ (2 : ℝ) := by gcongr
    _ = T ^ (4 : ℝ) := by rw [← Real.rpow_add hTpos]; norm_num
    _ = T ^ 4 := by norm_num [Real.rpow_natCast]

/-- Guth--Maynard Proposition 10.1 before the final elementary scale
simplification.  The displayed two summands inside `J` are respectively
the `T² |W|^(3/2)` and `TN |W|^(1/2) E(W)^(1/2)` branches of the source
argument.  All objects are the literal selected Section 7 block and the
literal normalized affine source. -/
theorem gmCubicS3_prop10_1_selected_explicit
    (cutoff : GMSmoothCutoff) (μ η : ℝ)
    (hμ : 0 < μ) (hηpos : 0 < η) (hη : η ≤ 1 / 6) :
    ∃ K C₇ C₉ T₀ : ℝ,
      0 < K ∧ 0 < C₇ ∧ 0 < C₉ ∧ 4096 ≤ T₀ ∧
      ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      T₀ ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ∃ p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N),
        ‖gmCubicS3 cutoff N W‖ ≤
          6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            (C₇ * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
                (6 *
                  Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
                  Real.sqrt
                    (C₉ * T ^ μ *
                      ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
                          (2 * gmCubicWideL2Constant μ * T ^ μ *
                            (W.card : ℝ)) ^ 2 +
                        (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
                          (6 * gmCubicWideFourthConstant μ * T ^ μ *
                            (ApproxAddEnergy 1 W : ℝ))))) +
              ((gmCubicDyadicFrequencyBlock
                (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) *
                (C₇ / T ^ 200)) +
            K / T ^ 100 := by
  obtain ⟨K, C₇, hK, hC₇, hprop7⟩ :=
    gmCubicS3_prop7_2_explicit cutoff η hηpos (hη.trans (by norm_num))
  obtain ⟨C₉, T₉, hC₉, hT₉, hprop9⟩ :=
    gmCubicNormalizedAffineSource_proposition9_1 hμ
  let T₀ : ℝ := max 4096 T₉
  refine ⟨K, C₇, C₉, T₀, hK, hC₇, hC₉, le_max_left _ _, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  have h4096 : (4096 : ℝ) ≤ T := (le_max_left _ _).trans hT
  have hT9 : T₉ ≤ T := (le_max_right _ _).trans hT
  have hTone : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4096).trans h4096
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  obtain ⟨p, hp, hpbound⟩ := hprop7 hTone hN hNT hNlower hSep hBase
  refine ⟨p, hp, hpbound.trans ?_⟩
  have hpMem := mem_gmCubicDyadicIndexPairs.mp hp
  have hrs : p.1 ≤ p.2 := hpMem.2.2
  have hM : 0 < 2 ^ p.2 := by positivity
  have hB : 0 < gmCubicSmoothingScale η T N (2 ^ p.2) :=
    gmCubicSmoothingScale_pos hTpos hN hM
  have hB32 : 32 ≤ gmCubicSmoothingScale η T N (2 ^ p.2) :=
    thirtytwo_le_gmCubicSmoothingScale h4096 hη hN hNlower
  have hQ : 0 < gmCubicAffineTerminalScale p.2 := by
    unfold gmCubicAffineTerminalScale
    positivity
  have hQT : (gmCubicAffineTerminalScale p.2 : ℝ) ≤ T ^ 4 :=
    gmCubicAffineTerminalScale_le_height_four h4096 hηpos.le hη hN hNT hp
  have hJ := hprop9 hT9 hB hB32 hBase hQ hQT
  have hL := setIntegral_norm_gmR_sq_le_epsilon_budget
    hμ hTone hSep hBase
  have hWide := setIntegral_norm_gmR_sq_wide_le_epsilon_budget
    hμ hTone hSep hBase
  have hFourth := setIntegral_norm_gmR_fourth_wide_le_epsilon_budget
    hμ hTone hBase
  have hmass0 : 0 ≤ ∫ u : ℝ,
      gmCubicNormalizedAffineSourceSchwartz
        (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u :=
    integral_nonneg
      (gmCubicNormalizedAffineSourceSchwartz_nonneg _ hB W)
  have hmass :=
    integral_gmCubicNormalizedAffineSource_le_two_secondMoment
      (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W
  have hmassBound :
      (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
          (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u) ≤
        2 * gmCubicWideL2Constant μ * T ^ μ * (W.card : ℝ) := by
    calc
      _ ≤ 2 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 2 := hmass
      _ ≤ 2 * (gmCubicWideL2Constant μ * T ^ μ * (W.card : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hsqMass :=
    integral_sq_gmCubicNormalizedAffineSource_le_six_fourthMoment
      (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W
  have hsqMassBound :
      (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
          (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u ^ 2) ≤
        6 * gmCubicWideFourthConstant μ * T ^ μ *
          (ApproxAddEnergy 1 W : ℝ) := by
    calc
      _ ≤ 6 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := hsqMass
      _ ≤ 6 * (gmCubicWideFourthConstant μ * T ^ μ *
          (ApproxAddEnergy 1 W : ℝ)) := by gcongr
      _ = _ := by ring
  have hJbound :
      gmAffineJ
          (gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
          (gmCubicAffineTerminalScale p.2) ≤
        C₉ * T ^ μ *
          ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
              (2 * gmCubicWideL2Constant μ * T ^ μ *
                (W.card : ℝ)) ^ 2 +
            (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
              (6 * gmCubicWideFourthConstant μ * T ^ μ *
                (ApproxAddEnergy 1 W : ℝ))) := by
    have hmassPow :
        (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
            (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u) ^ 2 ≤
          (2 * gmCubicWideL2Constant μ * T ^ μ *
            (W.card : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hmass0 hmassBound 2
    have hinside :
        (gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
              (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
                (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u) ^ 2 +
            (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
              ∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
                (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u ^ 2 ≤
          (gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
              (2 * gmCubicWideL2Constant μ * T ^ μ *
                (W.card : ℝ)) ^ 2 +
            (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
              (6 * gmCubicWideFourthConstant μ * T ^ μ *
                (ApproxAddEnergy 1 W : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hmassPow (by positivity))
        (mul_le_mul_of_nonneg_left hsqMassBound (by positivity))
    calc
      _ ≤ C₉ * T ^ μ *
          ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
              (∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
                (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u) ^ 2 +
            (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
              ∫ u : ℝ, gmCubicNormalizedAffineSourceSchwartz
                (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W u ^ 2) := hJ
      _ ≤ _ := mul_le_mul_of_nonneg_left hinside
        (mul_nonneg hC₉.le (Real.rpow_nonneg hTpos.le μ))
  have hsum := sum_gmCubicSmoothedModeIntegral_selected_le_six
    (H := gmCubicFrequencyRadius η T N) (r := p.1) (s := p.2)
    W hB hrs
  have hsqrtL := Real.sqrt_le_sqrt hL
  have hsqrtJ := Real.sqrt_le_sqrt hJbound
  have hsumBound :
      (∑ m ∈ gmCubicDyadicFrequencyBlock
          (gmCubicFrequencyRadius η T N) p.1 p.2,
          gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) ≤
        6 * Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
          Real.sqrt
            (C₉ * T ^ μ *
              ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
                  (2 * gmCubicWideL2Constant μ * T ^ μ *
                    (W.card : ℝ)) ^ 2 +
                (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
                  (6 * gmCubicWideFourthConstant μ * T ^ μ *
                    (ApproxAddEnergy 1 W : ℝ)))) := by
    calc
      _ ≤ 6 * Real.sqrt
          (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
            Real.sqrt (gmAffineJ
              (gmCubicNormalizedAffineSourceSchwartz
                (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
              (gmCubicAffineTerminalScale p.2)) := hsum
      _ ≤ _ := by
        have hleft :
            Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
                Real.sqrt (gmAffineJ
                  (gmCubicNormalizedAffineSourceSchwartz
                    (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
                  (gmCubicAffineTerminalScale p.2)) ≤
              Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
                Real.sqrt (gmAffineJ
                  (gmCubicNormalizedAffineSourceSchwartz
                    (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
                  (gmCubicAffineTerminalScale p.2)) := by
          exact mul_le_mul_of_nonneg_right hsqrtL (Real.sqrt_nonneg _)
        have hright :
            Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
                Real.sqrt (gmAffineJ
                  (gmCubicNormalizedAffineSourceSchwartz
                    (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
                  (gmCubicAffineTerminalScale p.2)) ≤
              Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
                Real.sqrt
                  (C₉ * T ^ μ *
                    ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
                        (2 * gmCubicWideL2Constant μ * T ^ μ *
                          (W.card : ℝ)) ^ 2 +
                      (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
                        (6 * gmCubicWideFourthConstant μ * T ^ μ *
                          (ApproxAddEnergy 1 W : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left hsqrtJ (Real.sqrt_nonneg _)
        have hproduct := hleft.trans hright
        calc
          6 * Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
                Real.sqrt (gmAffineJ
                  (gmCubicNormalizedAffineSourceSchwartz
                    (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
                  (gmCubicAffineTerminalScale p.2)) =
              6 * (Real.sqrt (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) *
                Real.sqrt (gmAffineJ
                  (gmCubicNormalizedAffineSourceSchwartz
                    (gmCubicSmoothingScale η T N (2 ^ p.2)) hB W)
                  (gmCubicAffineTerminalScale p.2))) := by ring
          _ ≤ 6 *
              (Real.sqrt (gmCubicL2Constant μ * T ^ μ * (W.card : ℝ)) *
                Real.sqrt
                  (C₉ * T ^ μ *
                    ((gmCubicAffineTerminalScale p.2 : ℝ) ^ 6 *
                        (2 * gmCubicWideL2Constant μ * T ^ μ *
                          (W.card : ℝ)) ^ 2 +
                      (gmCubicAffineTerminalScale p.2 : ℝ) ^ 4 *
                        (6 * gmCubicWideFourthConstant μ * T ^ μ *
                          (ApproxAddEnergy 1 W : ℝ))))) :=
            mul_le_mul_of_nonneg_left hproduct (by norm_num)
          _ = _ := by ring
  have hcoeff : 0 ≤ C₇ * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) := by
    positivity
  have hmain := mul_le_mul_of_nonneg_left hsumBound hcoeff
  have hlog0 : 0 ≤
      6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 := by
    positivity
  exact add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add hmain le_rfl) hlog0) le_rfl

end RiemannZeta.GuthMaynard
