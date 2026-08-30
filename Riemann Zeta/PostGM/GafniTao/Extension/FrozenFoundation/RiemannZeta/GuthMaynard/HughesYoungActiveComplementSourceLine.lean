import RiemannZeta.GuthMaynard.HughesYoungEndpointDecay

open Complex Filter Finset MeasureTheory Set Topology
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The Hughes--Young active-complement source as a holomorphic family

The product-complement introduced before Hughes--Young equation (61) has
to be moved as one signed DFI equation-(27) source.  This file gives that
source a genuine complex Mellin parameter.  The definition deliberately
keeps the real product multiplier independent of the Mellin variable; all
complex dependence is carried by the source contour factor and the two
positive logarithmic powers.
-/

/-- The height- and mollifier-dependent scalar in the gcd-reduced source,
with the Mellin variable allowed to range over the complex plane. -/
noncomputable def hughesYoungReducedMellinScaleConstantComplex
    (T t : ℝ) (w : ℂ) (h k : ℕ) : ℂ :=
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
    (1 / (Real.pi : ℂ)) * hughesYoungRightContourWeightComplex t w *
    Complex.exp ((afeCriticalPoint t + w) *
      (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
    Complex.exp ((afeCriticalPoint (-t) + w) *
      (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))

/-- On a vertical line the complex scalar is exactly the scalar already
used by the DFI central source. -/
theorem hughesYoungReducedMellinScaleConstantComplex_vertical
    (T t c u : ℝ) (h k : ℕ) :
    hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k =
      hughesYoungReducedMellinScaleConstant T t c u h k := by
  unfold hughesYoungReducedMellinScaleConstantComplex
    hughesYoungReducedMellinScaleConstant hughesYoungMellinScalar
  rw [hughesYoungRightContourWeightComplex_vertical]

/-- The reduced scalar is holomorphic throughout the open right
half-plane. -/
theorem differentiableAt_hughesYoungReducedMellinScaleConstantComplex
    (T t : ℝ) (h k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun z => hughesYoungReducedMellinScaleConstantComplex T t z h k) w := by
  have hweight := differentiableAt_hughesYoungRightContourWeightComplex t hw
  unfold hughesYoungReducedMellinScaleConstantComplex
  fun_prop (disch := first | exact hweight | assumption)

/-- The lower-boundary-removed product complement with a genuine complex
Mellin parameter.  Its multiplier is the exact finite dyadic complement,
not an abstract cutoff or an assumed support certificate. -/
noncomputable def hughesYoungNonLowerActiveComplementMellinWeightComplex
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) (x y : ℝ) : ℂ :=
  if 0 < x ∧ 0 < y then
    hughesYoungReducedMellinScaleConstantComplex T t w h k *
      (hughesYoungNonLowerActiveComplementMultiplier a b R K x y : ℂ) *
      hughesYoungLogPower (afeCriticalPoint t + w) x *
      hughesYoungLogPower (afeCriticalPoint (-t) + w) y
  else 0

/-- The scale-free physical part of the non-lower Mellin source.  Keeping
this factor separate is useful when a contour rectangle is moved through
the improper DFI integral: the compact Mellin scalar can then be bounded
once, while all physical decay remains visible in this kernel. -/
noncomputable def hughesYoungNonLowerActiveComplementMellinShapeComplex
    (t : ℝ) (w : ℂ) (a b R K : ℕ) (x y : ℝ) : ℂ :=
  if 0 < x ∧ 0 < y then
    (hughesYoungNonLowerActiveComplementMultiplier a b R K x y : ℂ) *
      hughesYoungLogPower (afeCriticalPoint t + w) x *
      hughesYoungLogPower (afeCriticalPoint (-t) + w) y
  else 0

/-- Exact separation of the compact Mellin scalar from the scale-free
physical complement kernel. -/
theorem hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) (x y : ℝ) :
    hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K x y =
      hughesYoungReducedMellinScaleConstantComplex T t w h k *
        hughesYoungNonLowerActiveComplementMellinShapeComplex
          t w a b R K x y := by
  unfold hughesYoungNonLowerActiveComplementMellinWeightComplex
    hughesYoungNonLowerActiveComplementMellinShapeComplex
  by_cases hxy : 0 < x ∧ 0 < y
  · simp only [hxy.1, hxy.2, and_self, if_true]
    ring
  · simp [hxy]

/-- The complex family specializes exactly to the previously constructed
non-lower DFI weight on every vertical line. -/
theorem hughesYoungNonLowerActiveComplementMellinWeightComplex_vertical
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) :
    hughesYoungNonLowerActiveComplementMellinWeightComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k a b R K =
      hughesYoungNonLowerActiveComplementReducedMellinWeight
        T t c u h k a b R K := by
  funext x y
  by_cases hxy : 0 < x ∧ 0 < y
  · rw [hughesYoungNonLowerActiveComplementMellinWeightComplex,
      if_pos hxy,
      hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_scaled
        T t c u hh hk a b R K hxy.1 hxy.2,
      hughesYoungReducedMellinScaleConstantComplex_vertical]
    rw [hughesYoungLogPower_eq_cpow hxy.1,
      hughesYoungLogPower_eq_cpow hxy.2]
  · rw [hughesYoungNonLowerActiveComplementMellinWeightComplex,
      if_neg hxy]
    unfold hughesYoungNonLowerActiveComplementReducedMellinWeight
      hughesYoungLowerCompleteReducedMellinWeight
      hughesYoungActiveReassembledReducedMellinWeight
    by_cases hx : 0 < x
    · have hy : ¬ 0 < y := fun hy => hxy ⟨hx, hy⟩
      have hy0 : y ≤ 0 := le_of_not_gt hy
      simp only [hx, hy, and_false, if_false, zero_sub]
      symm
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro ij _hij
      have hcut : hughesYoungFullDyadicCutoff ij.2 y = 0 := by
        by_contra hne
        have hsupp := support_hughesYoungDyadicCutoffAt_subset
          (hughesYoungFullDyadicScale_pos ij.2) hne
        exact (not_lt_of_ge hy0)
          ((hughesYoungFullDyadicScale_pos ij.2).trans_le hsupp.1)
      unfold hughesYoungFullDyadicCutoff at hcut
      unfold hughesYoungFullDyadicReducedMellinWeight
        hughesYoungReducedLocalizedMellinWeight
      dsimp only
      unfold hughesYoungLocalizedLogKernel
      simp only [hcut, Complex.ofReal_zero, mul_zero, zero_mul]
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      simp only [hx, false_and, if_false, zero_sub]
      symm
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro ij _hij
      have hcut : hughesYoungFullDyadicCutoff ij.1 x = 0 := by
        by_contra hne
        have hsupp := support_hughesYoungDyadicCutoffAt_subset
          (hughesYoungFullDyadicScale_pos ij.1) hne
        exact (not_lt_of_ge hx0)
          ((hughesYoungFullDyadicScale_pos ij.1).trans_le hsupp.1)
      unfold hughesYoungFullDyadicCutoff at hcut
      unfold hughesYoungFullDyadicReducedMellinWeight
        hughesYoungReducedLocalizedMellinWeight
      dsimp only
      unfold hughesYoungLocalizedLogKernel
      simp only [hcut, Complex.ofReal_zero, mul_zero, zero_mul]

/-- At every fixed pair of physical variables, the complement weight is
holomorphic on `Re w > 0`.  The source cutoff is independent of `w`, so no
derivative of a support indicator is introduced. -/
theorem differentiableAt_hughesYoungNonLowerActiveComplementMellinWeightComplex
    (T t : ℝ) (h k a b R K : ℕ) (x y : ℝ)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun z => hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t z h k a b R K x y) w := by
  by_cases hxy : 0 < x ∧ 0 < y
  · have hscale :=
      differentiableAt_hughesYoungReducedMellinScaleConstantComplex
        T t h k hw
    have hxpow : DifferentiableAt ℂ
        (fun z => hughesYoungLogPower (afeCriticalPoint t + z) x) w := by
      unfold hughesYoungLogPower
      fun_prop
    have hypow : DifferentiableAt ℂ
        (fun z => hughesYoungLogPower (afeCriticalPoint (-t) + z) y) w := by
      unfold hughesYoungLogPower
      fun_prop
    simp only [hughesYoungNonLowerActiveComplementMellinWeightComplex,
      if_pos hxy]
    exact (((hscale.mul_const
      (hughesYoungNonLowerActiveComplementMultiplier a b R K x y)).mul
        hxpow).mul hypow)
  · simp [hughesYoungNonLowerActiveComplementMellinWeightComplex, hxy]

/-- The literal non-lower DFI source weight is holomorphic on every
closed rectangle contained in the open right half-plane.  This is kept at
the physical-variable level so that later contour transfer can be lifted
through the improper central integral and the Ramanujan series by genuine
Fubini arguments. -/
theorem differentiableOn_hughesYoungNonLowerActiveComplementMellinWeightComplex_rectangle
    (T t : ℝ) (h k a b R K : ℕ) (x y : ℝ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    DifferentiableOn ℂ
      (fun w => hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K x y)
      ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
  intro w hw
  apply
    (differentiableAt_hughesYoungNonLowerActiveComplementMellinWeightComplex
      T t h k a b R K x y ?_).differentiableWithinAt
  rw [mem_reProdIm] at hw
  have hwre : c₀ ≤ w.re := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.1
  exact hc₀.trans_le hwre

/-- Exact finite-height rectangle identity for one physical value of the
literal non-lower source weight.  No residue is crossed because the whole
rectangle remains in `Re w > 0`. -/
theorem hughesYoungNonLowerActiveComplementMellinWeightComplex_boundaryRect_zero
    (T t : ℝ) (h k a b R K : ℕ) (x y : ℝ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((s : ℂ) + (-H : ℂ) * I) h k a b R K x y) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((s : ℂ) + (H : ℂ) * I) h k a b R K x y) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K x y) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K x y) = 0 := by
  have hdiff :=
    differentiableOn_hughesYoungNonLowerActiveComplementMellinWeightComplex_rectangle
      T t h k a b R K x y hc₀ hc (H := H)
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun w => hughesYoungNonLowerActiveComplementMellinWeightComplex
      T t w h k a b R K x y)
    ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hdiff)
  simpa using hrect

/-- The complete equation-(27) logarithmic kernel remains holomorphic in
the Mellin variable at each physical point. -/
theorem differentiableAt_dfiEquation27C_nonLowerActiveComplementComplex
    (T t : ℝ) (h k a b qx qy R K : ℕ) (x y : ℝ)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun z => dfiEquation27C a b qx qy
        (hughesYoungNonLowerActiveComplementMellinWeightComplex
          T t z h k a b R K) x y) w := by
  unfold dfiEquation27C
  exact
    ((differentiableAt_const
      (c := dfiEquation27LogFactor a qx x)).mul_const
        (dfiEquation27LogFactor b qy y)).mul
      (differentiableAt_hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t h k a b R K x y hw)

/-- Exact finite-height rectangle identity for one physical value of the
full equation-(27) logarithmic kernel. -/
theorem dfiEquation27C_nonLowerActiveComplementComplex_boundaryRect_zero
    (T t : ℝ) (h k a b qx qy R K : ℕ) (x y : ℝ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + (-H : ℂ) * I) h k a b R K) x y) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + (H : ℂ) * I) h k a b R K) x y) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K) x y) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K) x y) = 0 := by
  have hdiff : DifferentiableOn ℂ
      (fun w => dfiEquation27C a b qx qy
        (hughesYoungNonLowerActiveComplementMellinWeightComplex
          T t w h k a b R K) x y)
      ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
    intro w hw
    apply
      (differentiableAt_dfiEquation27C_nonLowerActiveComplementComplex
        T t h k a b qx qy R K x y ?_).differentiableWithinAt
    rw [mem_reProdIm] at hw
    have hwre : c₀ ≤ w.re := by
      rw [uIcc_of_le hc] at hw
      exact hw.1.1
    exact hc₀.trans_le hwre
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun w => dfiEquation27C a b qx qy
      (hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K) x y)
    ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hdiff)
  simpa using hrect

/-- Away from the singular endpoint, the affine beta kernel is absolutely
integrable for every positive contour real part up to the Hughes--Young
right line.  This is the precise replacement for the source-strip
restriction `c < 1/2`: the non-lower multiplier supplies the missing
positive lower endpoint. -/
theorem integrableOn_hughesYoungCriticalAffineBetaIntegrand_away_zero
    {t u c δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ)
    (CX COne : ℂ) :
    IntegrableOn
      (fun x : ℝ =>
        hughesYoungCriticalAffineBetaIntegrand t u c x CX COne)
      (Set.Ioi δ) := by
  let f : ℝ → ℂ := fun x =>
    hughesYoungCriticalAffineBetaIntegrand t u c x CX COne
  let C : ℝ := 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2
  have htailMajor : IntegrableOn
      (fun x : ℝ => C * x ^ (-1 - c)) (Set.Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul C
  have hfMeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable
    · intro x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      unfold f hughesYoungCriticalAffineBetaIntegrand
      have hbeta := continuousOn_hughesYoungBetaIntegrand
        (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
        (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
      have hlogX : ContinuousAt (fun y : ℝ => (Real.log y : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_log (ne_of_gt hx0))
      have hlogOne : ContinuousAt
          (fun y : ℝ => (Real.log (1 + y) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuousAt_log (by linarith : 1 + x ≠ 0)).comp
            (continuousAt_const.add continuousAt_id))
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).continuousWithinAt.mul
          (hbeta x (show x ∈ Set.Ioi 0 by exact hx0))).mono
            (by intro y hy; change 0 < y; exact lt_trans zero_lt_one hy)
    · exact measurableSet_Ioi
  have htail : IntegrableOn f (Set.Ioi 1) := by
    apply Integrable.mono' htailMajor hfMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [f, C]
    exact norm_hughesYoungCriticalAffineBetaIntegrand_tail_le hc hc1 hx.le
  by_cases hδ1 : δ ≤ 1
  · have hlocalCont : ContinuousOn f (Set.Icc δ 1) := by
      intro x hx
      have hx0 : 0 < x := hδ.trans_le hx.1
      unfold f hughesYoungCriticalAffineBetaIntegrand
      have hbeta := continuousOn_hughesYoungBetaIntegrand
        (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
        (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
      have hlogX : ContinuousAt (fun y : ℝ => (Real.log y : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_log (ne_of_gt hx0))
      have hlogOne : ContinuousAt
          (fun y : ℝ => (Real.log (1 + y) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuousAt_log (by linarith : 1 + x ≠ 0)).comp
            (continuousAt_const.add continuousAt_id))
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).continuousWithinAt.mul
          (hbeta x (show x ∈ Set.Ioi 0 by exact hx0))).mono
            (by intro y hy; exact hδ.trans_le hy.1)
    have hlocal : IntegrableOn f (Set.Icc δ 1) :=
      hlocalCont.integrableOn_compact isCompact_Icc
    apply (hlocal.union htail).mono_set
    intro x hx
    by_cases hx1 : x ≤ 1
    · exact Or.inl ⟨le_of_lt hx, hx1⟩
    · exact Or.inr (lt_of_not_ge hx1)
  · exact htail.mono_set (Set.Ioi_subset_Ioi (le_of_not_ge hδ1))

/-- Uniform boundedness of the affine beta kernel on a compact rectangle
which stays away from its physical endpoint. -/
theorem exists_uniform_norm_hughesYoungCriticalAffineBetaIntegrand_compact
    (t u : ℝ) {c₀ c₁ δ : ℝ}
    (hδ : 0 < δ) (CX COne : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c ∈ Set.Icc c₀ c₁, ∀ x ∈ Set.Icc δ 1,
        ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ ≤ C := by
  let F : ℝ × ℝ → ℝ := fun p =>
    ‖hughesYoungCriticalAffineBetaIntegrand t u p.1 p.2 CX COne‖
  have hcont : ContinuousOn F (Set.Icc c₀ c₁ ×ˢ Set.Icc δ 1) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans_le hp.2.1
    have hxbase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx0
    have hone0 : 0 < 1 + p.2 := by linarith
    have honebase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hone0
    have hlogX : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx0)).comp continuousAt_snd)
    have hlogOne : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (ne_of_gt hone0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt
        (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt
        (fun q : ℝ × ℝ => 1 + (q.2 : ℂ)) p :=
      continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) + ((q.1 : ℂ) + (u : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t + ((q.1 : ℂ) + (u : ℂ) * I))) p := by
      fun_prop
    have hpowX := hbaseX.cpow hexpX hxbase
    have hpowOne := hbaseOne.cpow hexpOne honebase
    dsimp only [F, hughesYoungCriticalAffineBetaIntegrand]
    exact ((((hlogX.add continuousAt_const).mul
      (hlogOne.add continuousAt_const)).mul
        (hpowX.mul hpowOne)).norm).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image hcont
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro c hcMem x hxMem
  exact (hC ⟨(c, x), ⟨hcMem, hxMem⟩, rfl⟩).trans
    (le_max_right 1 C)

/-- An integrable physical majorant for a compact positive contour strip
after the lower endpoint has been removed. -/
noncomputable def hughesYoungAwayZeroBetaStripMajorant
    (c₀ C₀ Ctail δ x : ℝ) : ℝ :=
  (Set.Ioc δ 1).indicator (fun _ => C₀) x +
    (Set.Ioi 1).indicator (fun y => Ctail * y ^ (-1 - c₀)) x

theorem integrable_hughesYoungAwayZeroBetaStripMajorant
    {c₀ C₀ Ctail δ : ℝ} (hc₀ : 0 < c₀) :
    Integrable (hughesYoungAwayZeroBetaStripMajorant c₀ C₀ Ctail δ) := by
  have hlocal : IntegrableOn (fun _ : ℝ => C₀) (Set.Ioc δ 1) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  have hlocalInd : Integrable
      ((Set.Ioc δ 1).indicator (fun _ : ℝ => C₀)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hlocal
  have htail : IntegrableOn (fun y : ℝ =>
      Ctail * y ^ (-1 - c₀)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul Ctail
  have htailInd : Integrable
      ((Set.Ioi 1).indicator (fun y : ℝ => Ctail * y ^ (-1 - c₀))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 htail
  exact hlocalInd.add htailInd

/-- Uniform affine-beta domination on a compact positive real-part strip
and on the full physical tail beyond the dyadic lower endpoint. -/
theorem exists_norm_hughesYoungCriticalAffineBetaIntegrand_le_awayZeroStripMajorant
    (t u : ℝ) {c₀ c₁ δ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ ≤ 1)
    (hδ : 0 < δ) (CX COne : ℂ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ c ∈ Set.Icc c₀ c₁, ∀ x ∈ Set.Ioi δ,
        ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
          hughesYoungAwayZeroBetaStripMajorant c₀ C₀
            (9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c₀⁻¹ ^ 2) δ x := by
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    exists_uniform_norm_hughesYoungCriticalAffineBetaIntegrand_compact
      t u hδ CX COne (c₀ := c₀) (c₁ := c₁)
  refine ⟨C₀, hC₀, ?_⟩
  intro c hcMem x hx
  have hcPos : 0 < c := hc₀.trans_le hcMem.1
  have hcOne : c ≤ 1 := hcMem.2.trans hc₁
  by_cases hx1 : x ≤ 1
  · have hxCompact : x ∈ Set.Icc δ 1 := ⟨le_of_lt hx, hx1⟩
    rw [hughesYoungAwayZeroBetaStripMajorant,
      Set.indicator_of_mem (show x ∈ Set.Ioc δ 1 from ⟨hx, hx1⟩),
      Set.indicator_of_notMem (show x ∉ Set.Ioi 1 from not_lt_of_ge hx1)]
    simpa using hcompact c hcMem x hxCompact
  · have hxOne : 1 ≤ x := le_of_not_ge hx1
    have hraw := norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
      hcPos hcOne hxOne (t := t) (u := u) (CX := CX) (COne := COne)
    have hinv : c⁻¹ ≤ c₀⁻¹ :=
      (inv_le_inv₀ hcPos hc₀).2 hcMem.1
    have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcPos.le
    have hinv₀ : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
    have hinvSq : c⁻¹ ^ 2 ≤ c₀⁻¹ ^ 2 := by nlinarith
    have hexp : -1 - c ≤ -1 - c₀ := by linarith [hcMem.1]
    have hpow : x ^ (-1 - c) ≤ x ^ (-1 - c₀) :=
      Real.rpow_le_rpow_of_exponent_le hxOne hexp
    rw [hughesYoungAwayZeroBetaStripMajorant,
      Set.indicator_of_notMem (show x ∉ Set.Ioc δ 1 from
        fun hxmem => hx1 hxmem.2),
      Set.indicator_of_mem (show x ∈ Set.Ioi 1 from lt_of_not_ge hx1),
      zero_add]
    calc
      _ ≤ 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2 *
          x ^ (-1 - c) := hraw
      _ ≤ 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c₀⁻¹ ^ 2 *
          x ^ (-1 - c₀) := by gcongr

/-- Uniform version of the explicit critical affine-beta majorant when the
real part of the contour varies between a fixed positive lower line and the
Hughes--Young small-line ceiling.  Crucially, the right-hand side retains the
quadratic dependence on the two DFI logarithmic constants, so it can later be
summed against the inverse-square Ramanujan coefficient. -/
theorem norm_hughesYoungCriticalAffineBetaIntegrand_le_lowerMajorant
    {t u c₀ c x : ℝ} {CX COne : ℂ}
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) (hc4 : c ≤ 1 / 4) (hx : 0 < x) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      hughesYoungCriticalAffineBetaMajorant
        c₀ (1 + ‖CX‖ + ‖COne‖) x := by
  by_cases hx1 : x ≤ 1
  · have hnear := norm_hughesYoungCriticalAffineBetaIntegrand_near_le
      (t := t) (u := u) (c := c) (CX := CX) (COne := COne)
      hx hx1 (hc₀.le.trans hcc) hc4
    simpa [hughesYoungCriticalAffineBetaMajorant, hx, hx1,
      not_lt_of_ge hx1] using hnear
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have hc : 0 < c := hc₀.trans_le hcc
    have hraw := norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
      (t := t) (u := u) (c := c) (CX := CX) (COne := COne)
      hc (hc4.trans (by norm_num)) hx1'.le
    have hinv : c⁻¹ ≤ c₀⁻¹ :=
      (inv_le_inv₀ hc hc₀).2 hcc
    have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    have hinv₀0 : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
    have hinvSq : c⁻¹ ^ 2 ≤ c₀⁻¹ ^ 2 := by nlinarith
    have hexp : -1 - c ≤ -1 - c₀ := by linarith
    have hpow : x ^ (-1 - c) ≤ x ^ (-1 - c₀) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le hexp
    rw [hughesYoungCriticalAffineBetaMajorant,
      Set.indicator_of_notMem (show x ∉ Set.Ioc (0 : ℝ) 1 from
        fun hxmem => hx1 hxmem.2),
      Set.indicator_of_mem (show x ∈ Set.Ioi 1 from hx1'), zero_add]
    exact hraw.trans (by gcongr)

/-- An integrable affine-beta majorant valid on the full DFI contour strip
`c₀ ≤ Re w ≤ 1` once the physical dilation stays a fixed positive distance
`δ` from the singular endpoint.  The non-lower active-complement multiplier
supplies precisely this positive lower cutoff. -/
noncomputable def hughesYoungCriticalAffineBetaFullStripMajorant
    (c₀ δ S x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator
      (fun y => 289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2 *
        y ^ (-(7 / 8 : ℝ))) x +
    (Set.Ioi (1 : ℝ)).indicator
      (fun y => 9 * S ^ 2 * c₀⁻¹ ^ 2 * y ^ (-1 - c₀)) x

theorem integrable_hughesYoungCriticalAffineBetaFullStripMajorant
    {c₀ δ S : ℝ} (hc₀ : 0 < c₀) :
    Integrable (hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ S) := by
  have hnearInterval : IntervalIntegrable
      (fun x : ℝ => x ^ (-(7 / 8 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnear : IntegrableOn (fun x : ℝ =>
      (289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2) *
        x ^ (-(7 / 8 : ℝ))) (Set.Ioc 0 1) := by
    have hraw : IntegrableOn (fun x : ℝ => x ^ (-(7 / 8 : ℝ)))
        (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        hnearInterval
    exact hraw.const_mul (289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2)
  have htail : IntegrableOn (fun x : ℝ =>
      (9 * S ^ 2 * c₀⁻¹ ^ 2) * x ^ (-1 - c₀)) (Set.Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul
      (9 * S ^ 2 * c₀⁻¹ ^ 2)
  have hnearInd : Integrable ((Set.Ioc (0 : ℝ) 1).indicator
      (fun y => (289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2) *
        y ^ (-(7 / 8 : ℝ)))) :=
    integrable_indicator_iff measurableSet_Ioc |>.2 hnear
  have htailInd : Integrable ((Set.Ioi (1 : ℝ)).indicator
      (fun y => (9 * S ^ 2 * c₀⁻¹ ^ 2) * y ^ (-1 - c₀))) :=
    integrable_indicator_iff measurableSet_Ioi |>.2 htail
  simpa only [hughesYoungCriticalAffineBetaFullStripMajorant] using
    hnearInd.add htailInd

theorem integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq
    {c₀ δ S : ℝ} (hc₀ : 0 < c₀) :
    ∫ x : ℝ, hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ S x =
      2312 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2 +
        9 * S ^ 2 * c₀⁻¹ ^ 3 := by
  have hnearInterval : IntervalIntegrable
      (fun x : ℝ => x ^ (-(7 / 8 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hnear : IntegrableOn (fun x : ℝ =>
      289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2 *
        x ^ (-(7 / 8 : ℝ))) (Set.Ioc 0 1) := by
    have hraw : IntegrableOn (fun x : ℝ => x ^ (-(7 / 8 : ℝ)))
        (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        hnearInterval
    exact hraw.const_mul
      (289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2)
  have htail : IntegrableOn (fun x : ℝ =>
      9 * S ^ 2 * c₀⁻¹ ^ 2 * x ^ (-1 - c₀)) (Set.Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul
      (9 * S ^ 2 * c₀⁻¹ ^ 2)
  have hnearInd : Integrable ((Set.Ioc (0 : ℝ) 1).indicator
      (fun x : ℝ => 289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2 *
        x ^ (-(7 / 8 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ioc).2 hnear
  have htailInd : Integrable ((Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => 9 * S ^ 2 * c₀⁻¹ ^ 2 * x ^ (-1 - c₀))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 htail
  unfold hughesYoungCriticalAffineBetaFullStripMajorant
  rw [MeasureTheory.integral_add hnearInd htailInd]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ x in Set.Ioc (0 : ℝ) 1,
      289 * max 1 (δ ^ (-(3 / 4 : ℝ))) * S ^ 2 *
        x ^ (-(7 / 8 : ℝ))) +
    (∫ x in Set.Ioi (1 : ℝ),
      9 * S ^ 2 * c₀⁻¹ ^ 2 * x ^ (-1 - c₀)) = _
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_rpow (Or.inl (by norm_num : (-(1 : ℝ)) < -(7 / 8 : ℝ)))]
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  have hcne : c₀ ≠ 0 := hc₀.ne'
  norm_num [Real.zero_rpow]
  rw [show -1 - c₀ + 1 = -c₀ by ring]
  field_simp [hcne]
  ring

theorem hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    {c₀ δ S x : ℝ} :
    0 ≤ hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ S x := by
  unfold hughesYoungCriticalAffineBetaFullStripMajorant
  apply add_nonneg
  · apply Set.indicator_nonneg
    intro y hy
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num)
          (zero_le_one.trans (le_max_left 1 (δ ^ (-(3 / 4 : ℝ)))))
      · exact sq_nonneg S
    · exact Real.rpow_nonneg hy.1.le _
  · apply Set.indicator_nonneg
    intro y hy
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (sq_nonneg S)
      · exact sq_nonneg c₀⁻¹
    · exact Real.rpow_nonneg (zero_le_one.trans hy.le) _

/-- Uniform pointwise domination on the full right strip.  Unlike the
small-contour estimate, this theorem uses the exact positive physical cutoff
`δ < x`; hence it remains integrable when the contour reaches `Re w = 1`. -/
theorem norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
    {t u c₀ c δ x : ℝ} {CX COne : ℂ}
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) (hc1 : c ≤ 1)
    (hδ : 0 < δ) (hxδ : δ < x) :
    ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
      hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
        (1 + ‖CX‖ + ‖COne‖) x := by
  have hx : 0 < x := hδ.trans hxδ
  by_cases hx1 : x ≤ 1
  · let S : ℝ := 1 + ‖CX‖ + ‖COne‖
    let P : ℝ := x ^ (-(1 / 16 : ℝ))
    let D : ℝ := max 1 (δ ^ (-(3 / 4 : ℝ)))
    have hS : 1 ≤ S := by
      dsimp only [S]
      linarith [norm_nonneg CX, norm_nonneg COne]
    have hP : 0 ≤ P := Real.rpow_nonneg hx.le _
    have hlogx0 : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    have hlogone0 : 0 ≤ Real.log (1 + x) :=
      Real.log_nonneg (by linarith)
    have hlogone1 : Real.log (1 + x) ≤ 1 := by
      calc
        Real.log (1 + x) ≤ x := by
          simpa only [add_sub_cancel_left] using
            Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
        _ ≤ 1 := hx1
    have hprofile :=
      one_add_abs_log_le_seventeen_mul_rpow_neg_sixteenth hx hx1
    have hCXaff : ‖(Real.log x : ℂ) + CX‖ ≤ 17 * S * P := by
      calc
        _ ≤ |Real.log x| + ‖CX‖ := by
          simpa only [norm_real] using
            (norm_add_le (Real.log x : ℂ) CX)
        _ ≤ S * (1 + |Real.log x|) := by
          dsimp only [S]
          nlinarith [abs_nonneg (Real.log x), norm_nonneg CX, norm_nonneg COne]
        _ ≤ S * (17 * P) :=
          mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
        _ = 17 * S * P := by ring
    have hOneAff : ‖(Real.log (1 + x) : ℂ) + COne‖ ≤ 17 * S * P := by
      calc
        _ ≤ Real.log (1 + x) + ‖COne‖ := by
          have h := norm_add_le (Real.log (1 + x) : ℂ) COne
          calc
            _ ≤ ‖(Real.log (1 + x) : ℂ)‖ + ‖COne‖ := h
            _ = Real.log (1 + x) + ‖COne‖ := by
              rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hlogone0]
        _ ≤ S * (1 + |Real.log x|) := by
          dsimp only [S]
          nlinarith [abs_nonneg (Real.log x), norm_nonneg CX, norm_nonneg COne]
        _ ≤ S * (17 * P) :=
          mul_le_mul_of_nonneg_left hprofile (zero_le_one.trans hS)
        _ = 17 * S * P := by ring
    have hbase :
        ‖((x : ℂ) ^ (-(afeCriticalPoint (-t) +
              ((c : ℂ) + (u : ℂ) * I))) *
            (1 + (x : ℂ)) ^ (-(afeCriticalPoint t +
              ((c : ℂ) + (u : ℂ) * I))))‖ ≤
          x ^ (-(3 / 2 : ℝ)) := by
      rw [norm_hughesYoungCriticalAffineBetaPower_eq hx]
      have hfirst : x ^ (-(1 / 2 : ℝ) - c) ≤ x ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
      have hsecond : (1 + x) ^ (-(1 / 2 : ℝ) - c) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      exact (mul_le_mul hfirst hsecond
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx.le _)).trans_eq
          (mul_one _)
    have hPP : P * P = x ^ (-(1 / 8 : ℝ)) := by
      dsimp only [P]
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hdeltaPow : x ^ (-(3 / 4 : ℝ)) ≤ D := by
      have hraw := Real.rpow_le_rpow_of_nonpos hδ hxδ.le
        (by norm_num : (-(3 / 4 : ℝ)) ≤ 0)
      exact hraw.trans (le_max_right 1 (δ ^ (-(3 / 4 : ℝ))))
    have hsplit : x ^ (-(1 / 8 : ℝ)) * x ^ (-(3 / 2 : ℝ)) =
        x ^ (-(3 / 4 : ℝ)) * x ^ (-(7 / 8 : ℝ)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      ring
    unfold hughesYoungCriticalAffineBetaIntegrand
    dsimp only
    rw [norm_mul, norm_mul]
    rw [hughesYoungCriticalAffineBetaFullStripMajorant,
      Set.indicator_of_mem (show x ∈ Set.Ioc (0 : ℝ) 1 from ⟨hx, hx1⟩),
      Set.indicator_of_notMem (show x ∉ Set.Ioi (1 : ℝ) from not_lt_of_ge hx1),
      add_zero]
    calc
      _ ≤ (17 * S * P) * (17 * S * P) * x ^ (-(3 / 2 : ℝ)) := by
        gcongr
      _ = 289 * S ^ 2 *
          (x ^ (-(1 / 8 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by
        rw [show (17 * S * P) * (17 * S * P) * x ^ (-(3 / 2 : ℝ)) =
          289 * S ^ 2 * (P * P) * x ^ (-(3 / 2 : ℝ)) by ring, hPP]
        ring
      _ = 289 * S ^ 2 *
          (x ^ (-(3 / 4 : ℝ)) * x ^ (-(7 / 8 : ℝ))) := by rw [hsplit]
      _ ≤ 289 * S ^ 2 * (D * x ^ (-(7 / 8 : ℝ))) := by gcongr
      _ = 289 * D * S ^ 2 * x ^ (-(7 / 8 : ℝ)) := by ring
  · have hxOne : 1 ≤ x := le_of_not_ge hx1
    have hraw := norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
      (t := t) (u := u) (c := c) (CX := CX) (COne := COne)
      (hc₀.trans_le hcc) hc1 hxOne
    have hinv : c⁻¹ ≤ c₀⁻¹ :=
      (inv_le_inv₀ (hc₀.trans_le hcc) hc₀).2 hcc
    have hinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr (hc₀.trans_le hcc).le
    have hinv₀0 : 0 ≤ c₀⁻¹ := inv_nonneg.mpr hc₀.le
    have hinvSq : c⁻¹ ^ 2 ≤ c₀⁻¹ ^ 2 := by nlinarith
    have hexp : -1 - c ≤ -1 - c₀ := by linarith
    have hpow : x ^ (-1 - c) ≤ x ^ (-1 - c₀) :=
      Real.rpow_le_rpow_of_exponent_le hxOne hexp
    rw [hughesYoungCriticalAffineBetaFullStripMajorant,
      Set.indicator_of_notMem (show x ∉ Set.Ioc (0 : ℝ) 1 from
        fun hxmem => hx1 hxmem.2),
      Set.indicator_of_mem (show x ∈ Set.Ioi (1 : ℝ) from lt_of_not_ge hx1),
      zero_add]
    exact hraw.trans (by gcongr)

/-- The two physical dilation powers are uniformly bounded as the real
part of the contour varies on a compact interval. -/
theorem exists_uniform_norm_hughesYoungDilationPowerPair
    (t u : ℝ) {r : ℝ} (hr : 0 < r) (c₀ c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Set.Icc c₀ c₁,
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ ≤ C := by
  let F : ℝ → ℝ := fun c =>
    ‖(r : ℂ) ^ (-(afeCriticalPoint t +
        ((c : ℂ) + (u : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((c : ℂ) + (u : ℂ) * I)))‖
  have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hr
  have hcont : Continuous F := by
    dsimp only [F]
    have hpow₁ : Continuous (fun c : ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I)))) := by
      exact continuous_const.cpow (by fun_prop) (fun _ => hrBase)
    have hpow₂ : Continuous (fun c : ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))) := by
      exact continuous_const.cpow (by fun_prop) (fun _ => hrBase)
    exact (hpow₁.mul hpow₂).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro c hc
  exact (hC ⟨c, hc, rfl⟩).trans (le_max_right 1 C)

/-- The complete reduced Mellin scalar is uniformly bounded on each
horizontal side of a compact rectangle in the open right half-plane. -/
theorem exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal
    (T t H : ℝ) (h k : ℕ) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Set.Icc c₀ c₁,
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (H : ℂ) * I) h k‖ ≤ C := by
  let F : ℝ → ℝ := fun c =>
    ‖hughesYoungReducedMellinScaleConstantComplex T t
      ((c : ℂ) + (H : ℂ) * I) h k‖
  have hcont : ContinuousOn F (Set.Icc c₀ c₁) := by
    intro c hc
    have hcPos : 0 < c := hc₀.trans_le hc.1
    exact ((differentiableAt_hughesYoungReducedMellinScaleConstantComplex
      T t h k (by simpa using hcPos)).continuousAt.comp
        (by fun_prop)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro c hc
  exact (hC ⟨c, hc, rfl⟩).trans (le_max_right 1 C)

/-- Exact factorization of the genuinely complex reduced Mellin scalar into
the entire static factor and the common completed-zeta contour weight. -/
theorem hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour
    (T t : ℝ) (w : ℂ) (h k : ℕ) :
    hughesYoungReducedMellinScaleConstantComplex T t w h k =
      hughesYoungReducedMellinStaticComplex T t h k w *
        hughesYoungRightContourWeightComplex t w := by
  unfold hughesYoungReducedMellinScaleConstantComplex
    hughesYoungReducedMellinStaticComplex
  ring

/-- The norm of the entire static factor is independent of the ordinate of
the Mellin variable. -/
theorem norm_hughesYoungReducedMellinStaticComplex_horizontal
    (T t c H : ℝ) (h k : ℕ) :
    ‖hughesYoungReducedMellinStaticComplex T t h k
        ((c : ℂ) + (H : ℂ) * I)‖ =
      ‖hughesYoungReducedMellinStaticComplex T t h k (c : ℂ)‖ := by
  unfold hughesYoungReducedMellinStaticComplex
  simp only [norm_mul, Complex.norm_exp]
  have hleftIm :
      ((Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)).im = 0 := rfl
  have hrightIm :
      ((Real.log (hughesYoungReducedRight h k : ℝ) : ℂ)).im = 0 := rfl
  simp only [Complex.mul_re, hleftIm, hrightIm, mul_zero, sub_zero]
  simp [afeCriticalPoint]

/-- The two positive dilation powers likewise have norm independent of the
ordinate. -/
theorem norm_hughesYoungDilationPowerPair_horizontal
    (t c H : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ =
      (r : ℝ) ^ (-(1 + 2 * c : ℝ)) := by
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp [afeCriticalPoint]
  rw [← Real.rpow_add hr]
  congr 1
  ring

/-- Uniform horizontal Gaussian decay of the complete reduced Mellin scalar.
All ordinate dependence outside the completed-zeta contour weight has been
removed exactly before the estimate is taken. -/
theorem exists_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal_le_gaussian
    (T t : ℝ) (h k : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ c ∈ Set.Icc c₀ c₁,
      ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨K, hK, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeightComplex_horizontal_le t hc₀ hc
  let F : ℝ → ℝ := fun c =>
    ‖hughesYoungReducedMellinStaticComplex T t h k (c : ℂ)‖
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro c
    exact ((differentiableAt_hughesYoungReducedMellinStaticComplex
      T t h k (c : ℂ)).continuousAt.comp (by fun_prop)).norm
  obtain ⟨S₀, hS₀⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn
  let S : ℝ := max 1 S₀
  let C : ℝ := S * K
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos hS hK
  refine ⟨C, hC, ?_⟩
  intro H hH c hcMem
  have hstatic :
      ‖hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (H : ℂ) * I)‖ ≤ S := by
    rw [norm_hughesYoungReducedMellinStaticComplex_horizontal]
    exact (hS₀ ⟨c, hcMem, rfl⟩).trans (le_max_right 1 S₀)
  have hcontour := hweight H hH c hcMem
  rw [hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour,
    norm_mul]
  calc
    _ ≤ S * (K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + H) ^ 16) := by gcongr
    _ = C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + H) ^ 16 := by
      dsimp only [C]
      ring

/-- Lower-edge analogue of the reduced Mellin scalar estimate. -/
theorem exists_norm_hughesYoungReducedMellinScaleConstantComplex_bottom_le_gaussian
    (T t : ℝ) (h k : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H → ∀ c ∈ Set.Icc c₀ c₁,
      ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (-H : ℂ) * I) h k‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by
  obtain ⟨K, hK, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeightComplex_bottom_le t hc₀ hc
  let F : ℝ → ℝ := fun c =>
    ‖hughesYoungReducedMellinStaticComplex T t h k (c : ℂ)‖
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro c
    exact ((differentiableAt_hughesYoungReducedMellinStaticComplex
      T t h k (c : ℂ)).continuousAt.comp (by fun_prop)).norm
  obtain ⟨S₀, hS₀⟩ := isCompact_Icc.bddAbove_image hFcont.continuousOn
  let S : ℝ := max 1 S₀
  let C : ℝ := S * K
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos hS hK
  refine ⟨C, hC, ?_⟩
  intro H hH c hcMem
  have hstatic :
      ‖hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (-H : ℂ) * I)‖ ≤ S := by
    rw [show (-H : ℂ) = ((-H : ℝ) : ℂ) by norm_num,
      norm_hughesYoungReducedMellinStaticComplex_horizontal]
    exact (hS₀ ⟨c, hcMem, rfl⟩).trans (le_max_right 1 S₀)
  have hcontour := hweight H hH c hcMem
  rw [hughesYoungReducedMellinScaleConstantComplex_eq_static_mul_contour,
    norm_mul]
  calc
    _ ≤ S * (K * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + H) ^ 16) := by gcongr
    _ = C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + H) ^ 16 := by
      dsimp only [C]
      ring

/-- Two-sided horizontal estimate, stated in terms of the absolute ordinate.
It is the common input for both disappearing horizontal edges. -/
theorem exists_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal_le_gaussian_abs
    (T t : ℝ) (h k : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ |H| → ∀ c ∈ Set.Icc c₀ c₁,
      ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ ≤
        C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16 := by
  obtain ⟨Ct, hCt, htop⟩ :=
    exists_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal_le_gaussian
      T t h k hc₀ hc
  obtain ⟨Cb, hCb, hbottom⟩ :=
    exists_norm_hughesYoungReducedMellinScaleConstantComplex_bottom_le_gaussian
      T t h k hc₀ hc
  let C : ℝ := max Ct Cb
  have hC : 0 < C := hCt.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro H hHabs c hcMem
  by_cases hH0 : 0 ≤ H
  · have hH : 1 ≤ H := by simpa only [abs_of_nonneg hH0] using hHabs
    have hbound := htop H hH c hcMem
    calc
      _ ≤ Ct * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := hbound
      _ ≤ C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + H) ^ 16 := by gcongr; exact le_max_left _ _
      _ = C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16 := by rw [abs_of_nonneg hH0]
  · have hHneg : H < 0 := lt_of_not_ge hH0
    have hH : 1 ≤ -H := by simpa only [abs_of_neg hHneg] using hHabs
    have hbound := hbottom (-H) hH c hcMem
    have hw : (c : ℂ) + -(((-H : ℝ) : ℂ)) * I =
        (c : ℂ) + (H : ℂ) * I := by push_cast; ring
    rw [hw] at hbound
    calc
      _ ≤ Cb * Real.exp (100 * c₁ ^ 2 - 100 * (-H) ^ 2) *
          (2 + |t| + c₁ + (-H)) ^ 16 := hbound
      _ ≤ C * Real.exp (100 * c₁ ^ 2 - 100 * (-H) ^ 2) *
          (2 + |t| + c₁ + (-H)) ^ 16 := by gcongr; exact le_max_right _ _
      _ = C * Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16 := by
        rw [abs_of_neg hHneg]
        rw [neg_sq]

/-- Compact-strip control of the two dilation powers with a constant that is
uniform in the horizontal ordinate. -/
theorem exists_uniform_norm_hughesYoungDilationPowerPair_all_horizontal
    (t : ℝ) {r : ℝ} (hr : 0 < r) (c₀ c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair t 0 hr c₀ c₁
  refine ⟨C, hC, ?_⟩
  intro H c hc
  rw [norm_hughesYoungDilationPowerPair_horizontal t c H hr,
    ← norm_hughesYoungDilationPowerPair_horizontal t c 0 hr]
  exact hbound c hc

/-- The source-line multiplier is at most one on the positive quadrant.
This local copy is positioned before the rectangle-integrability consumer. -/
private theorem nonLowerActiveComplementMultiplier_le_one_for_rectangle
    (a b R K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≤ 1 := by
  have hactive := hughesYoungActiveContinuousDyadicWeight_nonneg
    a b R K hx hy
  have hx0 := hughesYoungDyadicStep_nonneg
    (x * hughesYoungDyadicRatio)
  have hy0 := hughesYoungDyadicStep_nonneg
    (y * hughesYoungDyadicRatio)
  have hx1 := hughesYoungDyadicStep_le_one
    (x * hughesYoungDyadicRatio)
  have hy1 := hughesYoungDyadicStep_le_one
    (y * hughesYoungDyadicRatio)
  unfold hughesYoungNonLowerActiveComplementMultiplier
  have hprod :
      (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
          (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
  linarith

/-- Exact DFI dilation used by the rectangle-integrability consumer. -/
theorem dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
    (t c u : ℝ) (a b qx qy R K : ℕ)
    {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    dfiEquation27C a b qx qy
        (hughesYoungNonLowerActiveComplementMellinShapeComplex
          t ((c : ℂ) + (u : ℂ) * I) a b R K)
        (r * x + r) (r * x) =
      (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) : ℂ) *
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) *
        hughesYoungCriticalAffineBetaIntegrand t u c x
          ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
          ((Real.log r : ℂ) + dfiEquation27LogConstant a qx) := by
  have hOne : 0 < 1 + x := by linarith
  have hrx : 0 < r * x := mul_pos hr hx
  have hrOne : 0 < r * (1 + x) := mul_pos hr hOne
  have hsum : r * x + r = r * (1 + x) := by ring
  rw [hsum]
  unfold dfiEquation27C
    hughesYoungNonLowerActiveComplementMellinShapeComplex
  rw [if_pos ⟨hrOne, hrx⟩]
  rw [dfiEquation27LogFactor_eq_log_add_constant,
    dfiEquation27LogFactor_eq_log_add_constant]
  rw [Real.log_mul hr.ne' hOne.ne', Real.log_mul hr.ne' hx.ne']
  rw [hughesYoungLogPower_eq_cpow hrOne,
    hughesYoungLogPower_eq_cpow hrx]
  rw [show ((r * (1 + x) : ℝ) : ℂ) =
      (r : ℂ) * (1 + (x : ℂ)) by push_cast; rfl,
    show ((r * x : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by
      push_cast; rfl]
  have hone : 1 + (x : ℂ) = (((1 + x : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hone]
  rw [Complex.mul_cpow_ofReal_nonneg hr.le hOne.le,
    Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
  unfold hughesYoungCriticalAffineBetaIntegrand afeCriticalPoint
  dsimp only
  push_cast
  ring_nf

set_option maxHeartbeats 1000000 in
/-- Joint absolute integrability on one horizontal edge after the exact
positive-shift DFI dilation.  This is the Tonelli hypothesis for moving
the physical integral through the horizontal contour segment. -/
theorem integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) {h k : ℕ}
    (a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  let CX : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  obtain ⟨C₀, hC₀, hbeta⟩ :=
    exists_norm_hughesYoungCriticalAffineBetaIntegrand_le_awayZeroStripMajorant
      t H hc₀ hc₁ hδ CX COne (c₁ := c₁)
  let Ctail : ℝ := 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c₀⁻¹ ^ 2
  let G : ℝ → ℝ :=
    hughesYoungAwayZeroBetaStripMajorant c₀ C₀ Ctail δ
  have hG : Integrable G := by
    simpa only [G] using
      (integrable_hughesYoungAwayZeroBetaStripMajorant
        (c₀ := c₀) (C₀ := C₀) (Ctail := Ctail) (δ := δ) hc₀)
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair
      t H hr c₀ c₁
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal
      T t H h k hc₀ (c₁ := c₁)
  let D : ℝ := ‖z‖ * Cs * Cr
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hconst : Integrable (fun _ : ℝ => D)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hGon : Integrable G (volume.restrict (Set.Ioi δ)) :=
    hG.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ => D * G p.2)
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hD] using
      hconst.norm.mul_prod hGon
  let F : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Q : ℝ × ℝ → ℂ := fun p =>
    z *
      hughesYoungReducedMellinScaleConstantComplex T t
        ((p.1 : ℂ) + (H : ℂ) * I) h k *
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (r * p.2 + r) (r * p.2) : ℂ) *
      (r : ℂ) ^ (-(afeCriticalPoint t +
        ((p.1 : ℂ) + (H : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((p.1 : ℂ) + (H : ℂ) * I))) *
      hughesYoungCriticalAffineBetaIntegrand t H p.1 p.2 CX COne
  have hQcont : ContinuousOn Q
      (Set.Icc c₀ c₁ ×ˢ Set.Ioi δ) := by
    intro p hp
    have hcPos : 0 < p.1 := hc₀.trans_le hp.1.1
    have hx0 : 0 < p.2 := hδ.trans hp.2
    have hrx : 0 < r * p.2 := mul_pos hr hx0
    have hrOne : 0 < r * p.2 + r := add_pos hrx hr
    have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hr
    have hxBase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx0
    have hOneBase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using (show 0 < 1 + p.2 by linarith)
    have hscaleAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungReducedMellinScaleConstantComplex T t
          ((q.1 : ℂ) + (H : ℂ) * I) h k) p :=
      (differentiableAt_hughesYoungReducedMellinScaleConstantComplex
        T t h k (by simpa using hcPos)).continuousAt.comp (by fun_prop)
    have hmultAt : ContinuousAt (fun q : ℝ × ℝ =>
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * q.2 + r) (r * q.2) : ℂ)) p := by
      apply (Complex.continuous_ofReal.comp ?_).continuousAt
      unfold hughesYoungNonLowerActiveComplementMultiplier
        hughesYoungActiveContinuousDyadicWeight
        hughesYoungFullDyadicCutoff
      apply Continuous.sub
      · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
          (continuous_const.sub
            (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
      · apply continuous_finsetSum
        intro ij _hij
        exact ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.1)).continuous.comp
              (by fun_prop)).mul
          ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.2)).continuous.comp
              (by fun_prop))
    have hrpow₁ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((q.1 : ℂ) + (H : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hrpow₂ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((q.1 : ℂ) + (H : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hlogX : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx0)).comp continuousAt_snd)
    have hlogOne : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (by linarith : 1 + p.2 ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt
        (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt
        (fun q : ℝ × ℝ => 1 + (q.2 : ℂ)) p :=
      continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) +
          ((q.1 : ℂ) + (H : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t +
          ((q.1 : ℂ) + (H : ℂ) * I))) p := by
      fun_prop
    have hbetaAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungCriticalAffineBetaIntegrand
          t H q.1 q.2 CX COne) p := by
      unfold hughesYoungCriticalAffineBetaIntegrand
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).mul
          ((hbaseX.cpow hexpX hxBase).mul
            (hbaseOne.cpow hexpOne hOneBase)))
    dsimp only [Q]
    exact (((((continuousAt_const.mul hscaleAt).mul hmultAt).mul
      hrpow₁).mul hrpow₂).mul hbetaAt).continuousWithinAt
  have hFQ : Set.EqOn F Q
      (Set.Icc c₀ c₁ ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans hp.2
    dsimp only [F, Q]
    rw [show dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2) =
        z *
          hughesYoungReducedMellinScaleConstantComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinShapeComplex
              t ((p.1 : ℂ) + (H : ℂ) * I) a b R K)
            (r * p.2 + r) (r * p.2) by
      unfold dfiEquation27C
      dsimp only
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
      ring]
    rw [dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t p.1 H a b qx qy R K hr hx0]
    dsimp only [CX, COne]
    ring
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact (hQcont.congr hFQ).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Ioi)
  change Integrable F
    ((volume.restrict (Set.Icc c₀ c₁)).prod
      (volume.restrict (Set.Ioi δ)))
  apply hmajor.mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
  rcases hp with ⟨hcMem, hx⟩
  let c := p.1
  let x := p.2
  change ‖dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x)‖ ≤ D * G x
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := nonLowerActiveComplementMultiplier_le_one_for_rectangle
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta' :
      ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤ G x := by
    simpa only [G, Ctail] using hbeta c hcMem x hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c H a b qx qy R K hr hx0
  have hscale' := hscale c hcMem
  have hrpow' := hrpow c hcMem
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (H : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤
      ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ :=
    norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤
        G x := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ := one_mul _
      _ ≤ G x := hbeta'
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (H : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (H : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand
            t H c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ ‖z‖ * Cs * Cr * G x := by
      gcongr
    _ = D * G x := by rfl

/-- The scalar-parametric horizontal Tonelli theorem specialized to the
literal Hughes--Young height cutoff. -/
theorem integrable_nonLowerActiveComplement_horizontal_dilate_joint
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) {h k : ℕ}
    (a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  exact integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint
    hc₀ hc₁ (hughesYoungHeightWeight T t : ℂ) t H a b qx qy R K hr

/-- A quantitative, modulus-uniform horizontal-edge bound for the literal
non-lower active-complement source after DFI dilation.  The only dependence
on the two reduced moduli is through the explicit quadratic logarithmic
profile of the critical affine-beta majorant. -/
theorem exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_majorant
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) {h k : ℕ}
    (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (qx qy : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * hughesYoungCriticalAffineBetaFullStripMajorant c₀
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair t H hr c₀ c₁
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal
      T t H h k hc₀ (c₁ := c₁)
  let D₀ : ℝ := ‖z‖ * Cs * Cr
  let D : ℝ := max 1 D₀
  have hD : 0 < D := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro qx qy c hcMem x hx
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  let CX : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let G : ℝ := hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
    (1 + ‖CX‖ + ‖COne‖) x
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := nonLowerActiveComplementMultiplier_le_one_for_rectangle
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta :
      ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤ G := by
    exact norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
      hc₀ hcMem.1 (hcMem.2.trans hc₁) hδ hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c H a b qx qy R K hr hx0
  have hscale' := hscale c hcMem
  have hrpow' := hrpow c hcMem
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (H : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤ ‖hughesYoungCriticalAffineBetaIntegrand
      t H c x CX COne‖ := norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤ G := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ := one_mul _
      _ ≤ G := hbeta
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  have hG0 : 0 ≤ G := hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (H : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (H : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ D₀ * G := by
      dsimp only [D₀]
      gcongr
    _ ≤ D * G := mul_le_mul_of_nonneg_right (le_max_right 1 D₀) hG0
    _ = D * hughesYoungCriticalAffineBetaFullStripMajorant c₀
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
      rfl

/-- Height-uniform version of the horizontal DFI-dilate estimate.  The
common Gaussian envelope is exposed explicitly, so its constant is fixed
before the rectangle height is chosen. -/
theorem exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_gaussianMajorant
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t : ℝ) {h k : ℕ}
    (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ |H| →
      ∀ (qx qy : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
            (2 + |t| + c₁ + |H|) ^ 16) *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀
            ((1 / hughesYoungDyadicRatio) / r)
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair_all_horizontal
      t hr c₀ c₁
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_norm_hughesYoungReducedMellinScaleConstantComplex_horizontal_le_gaussian_abs
      T t h k hc₀ hc
  let D₀ : ℝ := ‖z‖ * Cs * Cr
  let D : ℝ := max 1 D₀
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro H hH qx qy c hcMem x hx
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  let CX : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let G : ℝ := hughesYoungCriticalAffineBetaFullStripMajorant c₀ δ
    (1 + ‖CX‖ + ‖COne‖) x
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := nonLowerActiveComplementMultiplier_le_one_for_rectangle
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta :
      ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤ G := by
    exact norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
      hc₀ hcMem.1 (hcMem.2.trans hc₁) hδ hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c H a b qx qy R K hr hx0
  have hscale' := hscale H hH c hcMem
  have hrpow' := hrpow H c hcMem
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (H : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤ ‖hughesYoungCriticalAffineBetaIntegrand
      t H c x CX COne‖ := norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖ ≤ G := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t H c x CX COne‖ := one_mul _
      _ ≤ G := hbeta
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (H : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (H : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  have hG0 : 0 ≤ G := hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hscaleE :
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (H : ℂ) * I) h k‖ ≤ Cs * E := by
    simpa only [E, mul_assoc] using hscale'
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (H : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (H : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (H : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t H c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ ‖z‖ * (Cs * E) * Cr * G := by
      gcongr
    _ = D₀ * E * G := by
      dsimp only [D₀]
      ring
    _ ≤ D * E * G := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 D₀) hE0) hG0
    _ = D * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
            (2 + |t| + c₁ + |H|) ^ 16) *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀
            ((1 / hughesYoungDyadicRatio) / r)
            (1 +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
              ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
      rfl

/-- The scalar-parametric horizontal estimate specialized to the literal
Hughes--Young physical-height cutoff. -/
theorem exists_norm_nonLowerActiveComplement_horizontal_dilate_le_majorant
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) {h k : ℕ}
    (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (qx qy : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * hughesYoungCriticalAffineBetaFullStripMajorant c₀
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  exact exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_majorant
    hc₀ hc₁ (hughesYoungHeightWeight T t : ℂ) t H a b R K hr

/-- Uniform affine-beta domination when the imaginary part, rather than
the real part, moves along a compact contour edge. -/
theorem exists_norm_hughesYoungCriticalAffineBetaIntegrand_le_verticalMajorant
    (t c H : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (CX COne : ℂ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ u ∈ Set.Icc (-H) H, ∀ x ∈ Set.Ioi δ,
        ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
          hughesYoungAwayZeroBetaStripMajorant c C₀
            (9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2) δ x := by
  let F : ℝ × ℝ → ℝ := fun p =>
    ‖hughesYoungCriticalAffineBetaIntegrand t p.1 c p.2 CX COne‖
  have hcont : ContinuousOn F (Set.Icc (-H) H ×ˢ Set.Icc δ 1) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans_le hp.2.1
    have hxbase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx0
    have hone0 : 0 < 1 + p.2 := by linarith
    have honebase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using hone0
    have hlogX : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx0)).comp continuousAt_snd)
    have hlogOne : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (ne_of_gt hone0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt
        (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt
        (fun q : ℝ × ℝ => 1 + (q.2 : ℂ)) p :=
      continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    dsimp only [F, hughesYoungCriticalAffineBetaIntegrand]
    exact ((((hlogX.add continuousAt_const).mul
      (hlogOne.add continuousAt_const)).mul
        ((hbaseX.cpow hexpX hxbase).mul
          (hbaseOne.cpow hexpOne honebase))).norm).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image hcont
  let C := max 1 C₀
  have hC : 0 < C := lt_max_of_lt_left zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro u hu x hx
  by_cases hx1 : x ≤ 1
  · rw [hughesYoungAwayZeroBetaStripMajorant,
      Set.indicator_of_mem (show x ∈ Set.Ioc δ 1 from ⟨hx, hx1⟩),
      Set.indicator_of_notMem (show x ∉ Set.Ioi 1 from not_lt_of_ge hx1)]
    simpa only [C, add_zero] using
      ((hC₀ ⟨(u, x), ⟨hu, ⟨le_of_lt hx, hx1⟩⟩, rfl⟩).trans
        (le_max_right 1 C₀))
  · have hxOne : 1 ≤ x := le_of_not_ge hx1
    rw [hughesYoungAwayZeroBetaStripMajorant,
      Set.indicator_of_notMem (show x ∉ Set.Ioc δ 1 from
        fun hxmem => hx1 hxmem.2),
      Set.indicator_of_mem (show x ∈ Set.Ioi 1 from lt_of_not_ge hx1),
      zero_add]
    exact norm_hughesYoungCriticalAffineBetaIntegrand_tail_le
      hc hc1 hxOne

/-- The dilation powers are uniformly bounded on a compact vertical
edge. -/
theorem exists_uniform_norm_hughesYoungDilationPowerPair_vertical
    (t c H : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (-H) H,
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ ≤ C := by
  let F : ℝ → ℝ := fun u =>
    ‖(r : ℂ) ^ (-(afeCriticalPoint t +
        ((c : ℂ) + (u : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((c : ℂ) + (u : ℂ) * I)))‖
  have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hr
  have hcont : Continuous F := by
    dsimp only [F]
    exact ((continuous_const.cpow (by fun_prop) (fun _ => hrBase)).mul
      (continuous_const.cpow (by fun_prop) (fun _ => hrBase))).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro u hu
  exact (hC ⟨u, hu, rfl⟩).trans (le_max_right 1 C)

/-- The complete reduced Mellin scalar is uniformly bounded on a compact
vertical edge in the open right half-plane. -/
theorem exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_vertical
    (T t c H : ℝ) (h k : ℕ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (-H) H,
      ‖hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k‖ ≤ C := by
  let F : ℝ → ℝ := fun u =>
    ‖hughesYoungReducedMellinScaleConstantComplex T t
      ((c : ℂ) + (u : ℂ) * I) h k‖
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro u
    dsimp only [F]
    have hdiff := differentiableAt_hughesYoungReducedMellinScaleConstantComplex
      T t h k (w := (c : ℂ) + (u : ℂ) * I)
        (by simpa using hc)
    have hline : ContinuousAt
        (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) u := by
      fun_prop
    exact (ContinuousAt.comp
      (g := fun z : ℂ =>
        hughesYoungReducedMellinScaleConstantComplex T t z h k)
      (f := fun v : ℝ => (c : ℂ) + (v : ℂ) * I)
      hdiff.continuousAt hline).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro u hu
  exact (hC ⟨u, hu, rfl⟩).trans (le_max_right 1 C)

set_option maxHeartbeats 1000000 in
/-- Joint absolute integrability on one vertical edge after the exact
positive-shift DFI dilation. -/
theorem integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (z : ℂ) (t H : ℝ) {h k : ℕ} (a b qx qy R K : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  let CX : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  obtain ⟨C₀, hC₀, hbeta⟩ :=
    exists_norm_hughesYoungCriticalAffineBetaIntegrand_le_verticalMajorant
      t c H hc hc1 hδ CX COne
  let Ctail : ℝ := 9 * (1 + ‖CX‖ + ‖COne‖) ^ 2 * c⁻¹ ^ 2
  let G : ℝ → ℝ :=
    hughesYoungAwayZeroBetaStripMajorant c C₀ Ctail δ
  have hG : Integrable G := by
    simpa only [G] using
      (integrable_hughesYoungAwayZeroBetaStripMajorant
        (c₀ := c) (C₀ := C₀) (Ctail := Ctail) (δ := δ) hc)
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair_vertical
      t c H hr
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_vertical
      T t c H h k hc
  let D : ℝ := ‖z‖ * Cs * Cr
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hconst : Integrable (fun _ : ℝ => D)
      (volume.restrict (Set.Icc (-H) H)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hGon : Integrable G (volume.restrict (Set.Ioi δ)) :=
    hG.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ => D * G p.2)
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hD] using
      hconst.norm.mul_prod hGon
  let F : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Q : ℝ × ℝ → ℂ := fun p =>
    z *
      hughesYoungReducedMellinScaleConstantComplex T t
        ((c : ℂ) + (p.1 : ℂ) * I) h k *
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (r * p.2 + r) (r * p.2) : ℂ) *
      (r : ℂ) ^ (-(afeCriticalPoint t +
        ((c : ℂ) + (p.1 : ℂ) * I))) *
      (r : ℂ) ^ (-(afeCriticalPoint (-t) +
        ((c : ℂ) + (p.1 : ℂ) * I))) *
      hughesYoungCriticalAffineBetaIntegrand t p.1 c p.2 CX COne
  have hQcont : ContinuousOn Q
      (Set.Icc (-H) H ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans hp.2
    have hrBase : (r : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hr
    have hxBase : (p.2 : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 hx0
    have hOneBase : 1 + (p.2 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using (show 0 < 1 + p.2 by linarith)
    have hline : ContinuousAt
        (fun q : ℝ × ℝ => (c : ℂ) + (q.1 : ℂ) * I) p := by
      fun_prop
    have hdiff :=
      differentiableAt_hughesYoungReducedMellinScaleConstantComplex
        T t h k (w := (c : ℂ) + (p.1 : ℂ) * I)
          (by simpa using hc)
    have hscaleAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (q.1 : ℂ) * I) h k) p :=
      ContinuousAt.comp
        (g := fun z : ℂ =>
          hughesYoungReducedMellinScaleConstantComplex T t z h k)
        (f := fun q : ℝ × ℝ => (c : ℂ) + (q.1 : ℂ) * I)
        hdiff.continuousAt hline
    have hmultAt : ContinuousAt (fun q : ℝ × ℝ =>
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * q.2 + r) (r * q.2) : ℂ)) p := by
      apply (Complex.continuous_ofReal.comp ?_).continuousAt
      unfold hughesYoungNonLowerActiveComplementMultiplier
        hughesYoungActiveContinuousDyadicWeight
        hughesYoungFullDyadicCutoff
      apply Continuous.sub
      · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
          (continuous_const.sub
            (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
      · apply continuous_finsetSum
        intro ij _hij
        exact ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.1)).continuous.comp
              (by fun_prop)).mul
          ((contDiff_hughesYoungDyadicCutoffAt
            (hughesYoungFullDyadicScale ij.2)).continuous.comp
              (by fun_prop))
    have hrpow₁ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (q.1 : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hrpow₂ : ContinuousAt (fun q : ℝ × ℝ =>
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (q.1 : ℂ) * I)))) p :=
      continuousAt_const.cpow (by fun_prop) hrBase
    have hlogX : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (ne_of_gt hx0)).comp continuousAt_snd)
    have hlogOne : ContinuousAt
        (fun q : ℝ × ℝ => (Real.log (1 + q.2) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log (by linarith : 1 + p.2 ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)).comp continuousAt_snd)
    have hbaseX : ContinuousAt
        (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
    have hbaseOne : ContinuousAt
        (fun q : ℝ × ℝ => 1 + (q.2 : ℂ)) p :=
      continuousAt_const.add hbaseX
    have hexpX : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint (-t) +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    have hexpOne : ContinuousAt (fun q : ℝ × ℝ =>
        -(afeCriticalPoint t +
          ((c : ℂ) + (q.1 : ℂ) * I))) p := by
      fun_prop
    have hbetaAt : ContinuousAt (fun q : ℝ × ℝ =>
        hughesYoungCriticalAffineBetaIntegrand
          t q.1 c q.2 CX COne) p := by
      unfold hughesYoungCriticalAffineBetaIntegrand
      exact (((hlogX.add continuousAt_const).mul
        (hlogOne.add continuousAt_const)).mul
          ((hbaseX.cpow hexpX hxBase).mul
            (hbaseOne.cpow hexpOne hOneBase)))
    dsimp only [Q]
    exact (((((continuousAt_const.mul hscaleAt).mul hmultAt).mul
      hrpow₁).mul hrpow₂).mul hbetaAt).continuousWithinAt
  have hFQ : Set.EqOn F Q
      (Set.Icc (-H) H ×ˢ Set.Ioi δ) := by
    intro p hp
    have hx0 : 0 < p.2 := hδ.trans hp.2
    dsimp only [F, Q]
    rw [show dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2) =
        z *
          hughesYoungReducedMellinScaleConstantComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinShapeComplex
              t ((c : ℂ) + (p.1 : ℂ) * I) a b R K)
            (r * p.2 + r) (r * p.2) by
      unfold dfiEquation27C
      dsimp only
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
      ring]
    rw [dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c p.1 a b qx qy R K hr hx0]
    dsimp only [CX, COne]
    ring
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    rw [Measure.prod_restrict]
    exact (hQcont.congr hFQ).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Ioi)
  change Integrable F
    ((volume.restrict (Set.Icc (-H) H)).prod
      (volume.restrict (Set.Ioi δ)))
  apply hmajor.mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
  rcases hp with ⟨hu, hx⟩
  let u := p.1
  let x := p.2
  change ‖dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x)‖ ≤ D * G x
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := nonLowerActiveComplementMultiplier_le_one_for_rectangle
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta' :
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤ G x := by
    simpa only [G, Ctail] using hbeta u hu x hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c u a b qx qy R K hr hx0
  have hscale' := hscale u hu
  have hrpow' := hrpow u hu
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ :=
    norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤
        G x := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ :=
        mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ := one_mul _
      _ ≤ G x := hbeta'
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (u : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (u : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand
            t u c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ ‖z‖ * Cs * Cr * G x := by
      gcongr
    _ = D * G x := by rfl

/-- The scalar-parametric vertical Tonelli theorem specialized to the
literal Hughes--Young height cutoff. -/
theorem integrable_nonLowerActiveComplement_vertical_dilate_joint
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (t H : ℝ) {h k : ℕ} (a b qx qy R K : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
        (r * p.2 + r) (r * p.2))
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r)))) := by
  exact integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint
    hc hc1 (hughesYoungHeightWeight T t : ℂ) t H a b qx qy R K hr

/-- Quantitative, modulus-uniform domination on a vertical Mellin edge.  The
critical beta power has norm independent of the ordinate, so the same
explicit quadratic logarithmic profile controls the whole edge. -/
theorem exists_norm_scalar_nonLowerActiveComplement_vertical_dilate_le_majorant
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (z : ℂ) (t H : ℝ) {h k : ℕ} (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (qx qy : ℕ) (u : ℝ), u ∈ Set.Icc (-H) H →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * hughesYoungCriticalAffineBetaFullStripMajorant c
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  obtain ⟨Cr, hCr, hrpow⟩ :=
    exists_uniform_norm_hughesYoungDilationPowerPair_vertical t c H hr
  obtain ⟨Cs, hCs, hscale⟩ :=
    exists_uniform_norm_hughesYoungReducedMellinScaleConstantComplex_vertical
      T t c H h k hc
  let D₀ : ℝ := ‖z‖ * Cs * Cr
  let D : ℝ := max 1 D₀
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro qx qy u hu x hx
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  have hδ : 0 < δ := div_pos
    (one_div_pos.mpr hughesYoungDyadicRatio_pos) hr
  let CX : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ := (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let G : ℝ := hughesYoungCriticalAffineBetaFullStripMajorant c δ
    (1 + ‖CX‖ + ‖COne‖) x
  have hx0 : 0 < x := hδ.trans hx
  have hrx : 0 ≤ r * x := (mul_pos hr hx0).le
  have hrOne : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
  have hmult := nonLowerActiveComplementMultiplier_le_one_for_rectangle
    a b R K hrOne hrx
  have hmult0 := hughesYoungNonLowerActiveComplementMultiplier_nonneg
    a b R K hrOne hrx
  have hbeta :
      ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤ G := by
    exact norm_hughesYoungCriticalAffineBetaIntegrand_le_fullStripMajorant
      hc le_rfl hc4 hδ hx
  have hshape :=
    dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq_for_rectangle
      t c u a b qx qy R K hr hx0
  have hscale' := hscale u hu
  have hrpow' := hrpow u hu
  rw [show dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
      (r * x + r) (r * x) =
      z *
        hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k *
        dfiEquation27C a b qx qy
          (hughesYoungNonLowerActiveComplementMellinShapeComplex
            t ((c : ℂ) + (u : ℂ) * I) a b R K)
          (r * x + r) (r * x) by
    unfold dfiEquation27C
    dsimp only
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_eq_scale_mul_shape]
    ring]
  rw [hshape]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult0]
  have hbeta0 : 0 ≤ ‖hughesYoungCriticalAffineBetaIntegrand
      t u c x CX COne‖ := norm_nonneg _
  have hmultBeta :
      hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖ ≤ G := by
    calc
      _ ≤ 1 * ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ := mul_le_mul_of_nonneg_right hmult hbeta0
      _ = ‖hughesYoungCriticalAffineBetaIntegrand
          t u c x CX COne‖ := one_mul _
      _ ≤ G := hbeta
  have hrpowNorm :
      ‖(r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I)))‖ *
        ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I)))‖ ≤ Cr := by
    simpa only [norm_mul] using hrpow'
  have hG0 : 0 ≤ G := hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
  calc
    _ = ‖z‖ *
        ‖hughesYoungReducedMellinScaleConstantComplex T t
          ((c : ℂ) + (u : ℂ) * I) h k‖ *
        (‖(r : ℂ) ^ (-(afeCriticalPoint t +
            ((c : ℂ) + (u : ℂ) * I)))‖ *
          ‖(r : ℂ) ^ (-(afeCriticalPoint (-t) +
            ((c : ℂ) + (u : ℂ) * I)))‖) *
        (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) *
          ‖hughesYoungCriticalAffineBetaIntegrand t u c x CX COne‖) := by
      dsimp only [CX, COne]
      ring
    _ ≤ D₀ * G := by
      dsimp only [D₀]
      gcongr
    _ ≤ D * G := mul_le_mul_of_nonneg_right (le_max_right 1 D₀) hG0
    _ = D * hughesYoungCriticalAffineBetaFullStripMajorant c
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
      rfl

/-- The scalar-parametric vertical estimate specialized to the literal
Hughes--Young physical-height cutoff. -/
theorem exists_norm_nonLowerActiveComplement_vertical_dilate_le_majorant
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (t H : ℝ) {h k : ℕ} (a b R K : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (qx qy : ℕ) (u : ℝ), u ∈ Set.Icc (-H) H →
      ∀ x : ℝ, (1 / hughesYoungDyadicRatio) / r < x →
        ‖dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
          (r * x + r) (r * x)‖ ≤
        D * hughesYoungCriticalAffineBetaFullStripMajorant c
          ((1 / hughesYoungDyadicRatio) / r)
          (1 +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
            ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖) x := by
  exact exists_norm_scalar_nonLowerActiveComplement_vertical_dilate_le_majorant
    hc hc4 (hughesYoungHeightWeight T t : ℂ) t H a b R K hr

/-- The height-weighted literal equation-(27) source has zero integral
around every rectangle in the open right half-plane. -/
theorem dfiEquation27C_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
    (T t : ℝ) (z : ℂ) (h k a b qx qy R K : ℕ) (x y : ℝ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y) x y) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y) x y) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K X Y) x y) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K X Y) x y) = 0 := by
  have hzero :=
    dfiEquation27C_nonLowerActiveComplementComplex_boundaryRect_zero
      T t h k a b qx qy R K x y hc₀ hc (H := H)
  have hscale (w : ℂ) :
      dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex
              T t w h k a b R K X Y) x y =
        z *
          dfiEquation27C a b qx qy
            (hughesYoungNonLowerActiveComplementMellinWeightComplex
              T t w h k a b R K) x y := by
    unfold dfiEquation27C
    ring
  simp only [smul_eq_mul]
  simp_rw [hscale, intervalIntegral.integral_const_mul]
  simp_rw [Complex.ofReal_neg]
  linear_combination z * hzero

/-- The scalar-parametric pointwise rectangle identity specialized to the
literal Hughes--Young height cutoff. -/
theorem dfiEquation27C_heightWeight_mul_nonLowerActiveComplement_boundaryRect_zero
    (T t : ℝ) (h k a b qx qy R K : ℕ) (x y : ℝ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y) x y) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y) x y) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K X Y) x y) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K X Y) x y) = 0 := by
  exact dfiEquation27C_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
    T t (hughesYoungHeightWeight T t : ℂ) h k a b qx qy R K x y hc₀ hc

set_option maxHeartbeats 4000000 in
/-- Exact rectangle identity after moving all four contour edges through
the same positive-shift physical integral. -/
theorem integral_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilated_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) +
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) = 0 := by
  let δ : ℝ := (1 / hughesYoungDyadicRatio) / r
  let Fb : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Ft : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Fr : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₁ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  let Fl : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy
      (fun X Y => z *
        hughesYoungNonLowerActiveComplementMellinWeightComplex T t
          ((c₀ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
      (r * p.2 + r) (r * p.2)
  change
    (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) -
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) +
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) -
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) = 0
  have hb : Integrable Fb
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((p.1 : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc c₀ c₁)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw := integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint
      hc₀ hc₁ z t (-H) a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have ht : Integrable Ft
      ((volume.restrict (Set.Icc c₀ c₁)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((p.1 : ℂ) + (H : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc c₀ c₁)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw := integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint
      hc₀ hc₁ z t H a b qx qy R K hr (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hrEdge : Integrable Fr
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc (-H) H)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw := integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint
      (hc₀.trans_le hc) hc₁ z t H a b qx qy R K hr
        (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hlEdge : Integrable Fl
      ((volume.restrict (Set.Icc (-H) H)).prod
        (volume.restrict (Set.Ioi δ))) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (p.1 : ℂ) * I) h k a b R K X Y)
          (r * p.2 + r) (r * p.2))
        ((volume.restrict (Set.Icc (-H) H)).prod
          (volume.restrict (Set.Ioi ((1 / hughesYoungDyadicRatio) / r))))
    have hraw := integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint
      hc₀ (hc.trans hc₁) z t H a b qx qy R K hr
        (T := T) (h := h) (k := k)
    refine hraw.congr ?_
    filter_upwards [] with p
    rfl
  have hswapB :
      (∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x) :=
    integral_integral_swap hb
  have hswapT :
      (∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x) :=
    integral_integral_swap ht
  have hswapR :
      (∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ u : ℝ in Set.Icc (-H) H, Fr (u, x) :=
    integral_integral_swap hrEdge
  have hswapL :
      (∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) =
        ∫ x : ℝ in Set.Ioi δ, ∫ u : ℝ in Set.Icc (-H) H, Fl (u, x) :=
    integral_integral_swap hlEdge
  have hpoint (x : ℝ) :
      (∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x)) -
        (∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x)) +
        I • (∫ u : ℝ in Set.Icc (-H) H, Fr (u, x)) -
        I • (∫ u : ℝ in Set.Icc (-H) H, Fl (u, x)) = 0 := by
    have hz :=
      dfiEquation27C_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
        T t z h k a b qx qy R K (r * x + r) (r * x) hc₀ hc (H := H)
    simpa only [Fb, Ft, Fr, Fl,
      intervalIntegral.integral_of_le hc,
      intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc] using hz
  have hBinterval :
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x)) =
        ∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Fb (s, x) := by
    rw [intervalIntegral.integral_of_le hc, restrict_Ioc_eq_restrict_Icc]
  have hTinterval :
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x)) =
        ∫ s : ℝ in Set.Icc c₀ c₁, ∫ x : ℝ in Set.Ioi δ, Ft (s, x) := by
    rw [intervalIntegral.integral_of_le hc, restrict_Ioc_eq_restrict_Icc]
  have hRinterval :
      (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x)) =
        ∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fr (u, x) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc]
  have hLinterval :
      (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x)) =
        ∫ u : ℝ in Set.Icc (-H) H, ∫ x : ℝ in Set.Ioi δ, Fl (u, x) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
      restrict_Ioc_eq_restrict_Icc]
  rw [hBinterval, hTinterval, hRinterval, hLinterval]
  rw [hswapB, hswapT, hswapR, hswapL]
  simp only [smul_eq_mul]
  have hBT := hb.integral_prod_right.sub ht.integral_prod_right
  have hIR := hrEdge.integral_prod_right.const_mul I
  have hIL := hlEdge.integral_prod_right.const_mul I
  have hBTIR := hBT.add hIR
  have hzeroIntegral :
      (∫ x : ℝ in Set.Ioi δ,
        ((∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, x)) -
          (∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, x)) +
          I * (∫ u : ℝ in Set.Icc (-H) H, Fr (u, x)) -
          I * (∫ u : ℝ in Set.Icc (-H) H, Fl (u, x)))) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    simpa only [smul_eq_mul] using hpoint x
  have hzeroAlgebraic :
      (∫ x : ℝ in Set.Ioi δ,
        ((((fun y : ℝ => ∫ s : ℝ in Set.Icc c₀ c₁, Fb (s, y)) -
              (fun y : ℝ => ∫ s : ℝ in Set.Icc c₀ c₁, Ft (s, y))) +
            (fun y : ℝ => I *
              (∫ u : ℝ in Set.Icc (-H) H, Fr (u, y)))) -
          (fun y : ℝ => I *
            (∫ u : ℝ in Set.Icc (-H) H, Fl (u, y)))) x) = 0 := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hzeroIntegral
  have hSubBT := integral_sub hb.integral_prod_right ht.integral_prod_right
  have hAddR := integral_add hBT hIR
  have hSubL := integral_sub hBTIR hIL
  have hMulR := MeasureTheory.integral_const_mul
    (μ := volume.restrict (Set.Ioi δ)) I
    (fun x : ℝ => ∫ u : ℝ in Set.Icc (-H) H, Fr (u, x))
  have hMulL := MeasureTheory.integral_const_mul
    (μ := volume.restrict (Set.Ioi δ)) I
    (fun x : ℝ => ∫ u : ℝ in Set.Icc (-H) H, Fl (u, x))
  linear_combination hzeroAlgebraic - hSubL - hAddR - hSubBT - hMulR + hMulL


/-- The scalar-parametric physical-integral rectangle identity specialized
to the literal Hughes--Young height cutoff. -/
theorem integral_dfiEquation27C_heightWeight_mul_nonLowerActiveComplement_dilated_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      (∫ s : ℝ in c₀..c₁, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) +
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) -
      I • (∫ u : ℝ in -H..H, ∫ x : ℝ in Set.Ioi
        ((1 / hughesYoungDyadicRatio) / r),
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        (r * x + r) (r * x)) = 0 := by
  exact integral_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilated_boundaryRect_zero
    hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) t hH
      h k a b qx qy R K hr
/-! ## Exact linearity of the DFI equation-(27) source

The central integral is improper, and the central series is infinite.  The
subtraction used by the active complement therefore has to pass through
both operations under explicit integrability and summability hypotheses.
The following lemmas provide that source-entry bridge without treating an
improper integral or a `tsum` as formal ring syntax.
-/

/-- The equation-(27) logarithmic kernel is pointwise linear in its source
weight. -/
theorem dfiEquation27C_sub_weight
    (a b qx qy : ℕ) (F G : ℝ → ℝ → ℂ) (x y : ℝ) :
    dfiEquation27C a b qx qy (fun X Y => F X Y - G X Y) x y =
      dfiEquation27C a b qx qy F x y -
        dfiEquation27C a b qx qy G x y := by
  unfold dfiEquation27C
  ring

/-- Subtraction passes through the improper central integral when both
source integrands are integrable. -/
theorem dfiEquation27CentralIntegral_sub_weight
    (a b qx qy : ℕ) (F G : ℝ → ℝ → ℂ) (r : ℝ)
    (hF : Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy F x (x - r)))
    (hG : Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy G x (x - r))) :
    dfiEquation27CentralIntegral a b qx qy
        (fun x y => F x y - G x y) r =
      dfiEquation27CentralIntegral a b qx qy F r -
        dfiEquation27CentralIntegral a b qx qy G r := by
  unfold dfiEquation27CentralIntegral
  simp_rw [dfiEquation27C_sub_weight]
  exact MeasureTheory.integral_sub hF hG

/-- One Ramanujan summand is linear in the source weight under the exact
central-integral hypotheses. -/
theorem dfiEquation27CentralSummand_sub_weight
    (a b r q : ℕ) (F G : ℝ → ℝ → ℂ)
    (hF : Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        F x (x - r)))
    (hG : Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        G x (x - r))) :
    dfiEquation27CentralSummand a b r
        (fun x y => F x y - G x y) q =
      dfiEquation27CentralSummand a b r F q -
        dfiEquation27CentralSummand a b r G q := by
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_sub_weight a b
    (dfiReducedDenominator a q) (dfiReducedDenominator b q) F G r hF hG]
  ring

/-- Subtraction passes through the complete positive-shift Ramanujan
series.  This is the infinite-series counterpart of
`dfiSignedCentralSeries_finsetSum`. -/
theorem dfiEquation27CentralSeries_sub_weight
    (a b r : ℕ) (F G : ℝ → ℝ → ℂ)
    (hFsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r F q))
    (hGsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r G q))
    (hFint : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        F x (x - r)))
    (hGint : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        G x (x - r))) :
    dfiEquation27CentralSeries a b r (fun x y => F x y - G x y) =
      dfiEquation27CentralSeries a b r F -
        dfiEquation27CentralSeries a b r G := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_sub_weight a b r _ F G
    (hFint _) (hGint _)]
  exact hFsum.tsum_sub hGsum

/-- Signed DFI source subtraction, including the coordinate swap in the
negative-shift branch.  Every analytic hypothesis is stated on the branch
where it is actually consumed. -/
theorem dfiSignedCentralSeries_sub_weight
    (a b : ℕ) (r : ℤ) (F G : ℝ → ℝ → ℂ)
    (hFsumPos : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r.toNat F q))
    (hGsumPos : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r.toNat G q))
    (hFintPos : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        F x (x - r.toNat)))
    (hGintPos : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        G x (x - r.toNat)))
    (hFsumNeg : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a (-r).toNat (dfiSwapWeight F) q))
    (hGsumNeg : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a (-r).toNat (dfiSwapWeight G) q))
    (hFintNeg : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C b a
        (dfiReducedDenominator b q) (dfiReducedDenominator a q)
        (dfiSwapWeight F) x (x - (-r).toNat)))
    (hGintNeg : ∀ q : ℕ, Integrable (fun x : ℝ =>
      dfiEquation27C b a
        (dfiReducedDenominator b q) (dfiReducedDenominator a q)
        (dfiSwapWeight G) x (x - (-r).toNat))) :
    dfiSignedCentralSeries a b r (fun x y => F x y - G x y) =
      dfiSignedCentralSeries a b r F -
        dfiSignedCentralSeries a b r G := by
  by_cases hr : 0 ≤ r
  · simp only [dfiSignedCentralSeries, if_pos hr]
    exact dfiEquation27CentralSeries_sub_weight a b r.toNat F G
      hFsumPos hGsumPos hFintPos hGintPos
  · simp only [dfiSignedCentralSeries, if_neg hr]
    have hswap : dfiSwapWeight (fun x y => F x y - G x y) =
        fun x y => dfiSwapWeight F x y - dfiSwapWeight G x y := by
      funext x y
      rfl
    rw [hswap]
    exact dfiEquation27CentralSeries_sub_weight b a (-r).toNat
      (dfiSwapWeight F) (dfiSwapWeight G)
      hFsumNeg hGsumNeg hFintNeg hGintNeg

/-! ## Scalar linearity of the DFI source

The physical-height cutoff is allowed to vanish.  Consequently the
source decomposition is transported through equation (27) after
multiplication by that cutoff, rather than by dividing by it.  These
lemmas make that operation explicit at every improper and infinite
stage. -/

/-- A scalar passes through the equation-(27) logarithmic kernel. -/
theorem dfiEquation27C_const_mul_weight
    (a b qx qy : ℕ) (z : ℂ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    dfiEquation27C a b qx qy (fun X Y => z * F X Y) x y =
      z * dfiEquation27C a b qx qy F x y := by
  unfold dfiEquation27C
  ring

/-- A scalar passes through the improper equation-(27) central integral
when the original physical integrand is integrable. -/
theorem dfiEquation27CentralIntegral_const_mul_weight
    (a b qx qy : ℕ) (z : ℂ) (F : ℝ → ℝ → ℂ) (r : ℝ) :
    dfiEquation27CentralIntegral a b qx qy
        (fun X Y => z * F X Y) r =
      z * dfiEquation27CentralIntegral a b qx qy F r := by
  unfold dfiEquation27CentralIntegral
  simp_rw [dfiEquation27C_const_mul_weight a b qx qy z F]
  exact integral_const_mul z
    (fun x : ℝ => dfiEquation27C a b qx qy F x (x - r))

/-- Scalar linearity for one complete equation-(27) modulus summand. -/
theorem dfiEquation27CentralSummand_const_mul_weight
    (a b r : ℕ) (z : ℂ) (F : ℝ → ℝ → ℂ) (q : ℕ) :
    dfiEquation27CentralSummand a b r (fun X Y => z * F X Y) q =
      z * dfiEquation27CentralSummand a b r F q := by
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_const_mul_weight a b
    (dfiReducedDenominator a q) (dfiReducedDenominator b q) z F r]
  ring

/-- Scalar linearity for the complete positive equation-(27) Ramanujan
series. -/
theorem dfiEquation27CentralSeries_const_mul_weight
    (a b r : ℕ) (z : ℂ) (F : ℝ → ℝ → ℂ) :
    dfiEquation27CentralSeries a b r (fun X Y => z * F X Y) =
      z * dfiEquation27CentralSeries a b r F := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_const_mul_weight a b r z F]
  exact tsum_mul_left

/-- Scalar linearity for the signed DFI central series, with the swapped
negative branch included explicitly. -/
theorem dfiSignedCentralSeries_const_mul_weight
    (a b : ℕ) (r : ℤ) (z : ℂ) (F : ℝ → ℝ → ℂ) :
    dfiSignedCentralSeries a b r (fun X Y => z * F X Y) =
      z * dfiSignedCentralSeries a b r F := by
  by_cases hr : 0 ≤ r
  · simp only [dfiSignedCentralSeries, if_pos hr]
    exact dfiEquation27CentralSeries_const_mul_weight a b r.toNat z F
  · simp only [dfiSignedCentralSeries, if_neg hr]
    have hswap : dfiSwapWeight (fun X Y => z * F X Y) =
        fun X Y => z * dfiSwapWeight F X Y := by
      funext X Y
      rfl
    rw [hswap]
    exact dfiEquation27CentralSeries_const_mul_weight b a (-r).toNat z
      (dfiSwapWeight F)

/-! ## Absolute convergence of the pure equation-(83) source

The pre-existing source-line theorem identified the values of the two
`tsum`s.  The subtraction argument below needs the stronger termwise
fact: the literal equation-(27) summands themselves are summable.  We
obtain it from the exact beta evaluation and the already proved absolute
convergence of the regularized equation-(84) contour terms. -/

/-- One positive literal equation-(27) modulus term is its regularized
equation-(84) contour term on the original Hughes--Young line. -/
theorem dfiEquation27CentralSummand_pureReduced_eq_contourTerm
    (T t c u : ℝ) {h k a b r : ℕ}
    (hc : 0 < c) (hcHalf : c < 1 / 2) (hr : 0 < r) (q : ℕ) :
    dfiEquation27CentralSummand a b r
        (hughesYoungPureReducedMellinWeight T t c u h k) q =
      hughesYoungEquation84PositiveContourTerm T t h k a b r q
        ((c : ℂ) + (u : ℂ) * I) := by
  rw [dfiEquation27CentralSummand_pureReduced_eq_equation83
    T t c u a b hr q]
  obtain ⟨hA, hAB⟩ :=
    hughesYoungEquation83_exponents_in_betaStrip t u hc hcHalf
  have hbeta :
      (∫ x in Set.Ioi (0 : ℝ),
        ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
          ((Real.log r : ℂ) + (Real.log x : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
          ((1 + (x : ℂ)) ^
              (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) *
            (x : ℂ) ^
              (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))))) =
        hughesYoungAffineLogBetaContinuation
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)) := by
    rw [← hughesYoungEquation83LogBetaIntegral_eq_continuation
      ((Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q))
      ((Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q)) hA hAB]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    ring
  rw [hbeta]
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : 0 < w.re := by simp [w, hc]
  have hleft : 0 < (afeCriticalPoint t - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  rw [hughesYoungAffineLogBetaContinuation_critical_eq_explicit hleft hw]
  rw [show
      -(afeCriticalPoint (-t) + w) +
          -(afeCriticalPoint t + w) + 1 = -(2 * w) by
        unfold afeCriticalPoint
        push_cast
        ring]
  dsimp only [w]
  exact hughesYoungEquation84Positive_summand_eq_contourTerm
    T t u hcHalf h k a b hr q

/-- One coordinate-swapped negative literal equation-(27) modulus term is
its regularized equation-(84) contour term. -/
theorem dfiEquation27CentralSummand_swappedPureReduced_eq_contourTerm
    (T t c u : ℝ) {h k a b r : ℕ}
    (hc : 0 < c) (hcHalf : c < 1 / 2) (hr : 0 < r) (q : ℕ) :
    dfiEquation27CentralSummand b a r
        (dfiSwapWeight
          (hughesYoungPureReducedMellinWeight T t c u h k)) q =
      hughesYoungEquation84NegativeContourTerm T t h k a b r q
        ((c : ℂ) + (u : ℂ) * I) := by
  rw [dfiEquation27CentralSummand_swappedPureReduced_eq_equation83
    T t c u a b hr q]
  obtain ⟨hA, hAB⟩ :=
    hughesYoungEquation83_swappedExponents_in_betaStrip t u hc hcHalf
  have hbeta :
      (∫ x in Set.Ioi (0 : ℝ),
        ((Real.log r : ℂ) + (Real.log (1 + x) : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)) *
          ((Real.log r : ℂ) + (Real.log x : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q)) *
          ((1 + (x : ℂ)) ^
              (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I))) *
            (x : ℂ) ^
              (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))))) =
        hughesYoungAffineLogBetaContinuation
          (-(afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)))
          (-(afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant a (dfiReducedDenominator a q))
          ((Real.log r : ℂ) +
            dfiEquation27LogConstant b (dfiReducedDenominator b q)) := by
    rw [← hughesYoungEquation83LogBetaIntegral_eq_continuation
      ((Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q))
      ((Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q)) hA hAB]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    ring
  rw [hbeta]
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : 0 < w.re := by simp [w, hc]
  have hleft : 0 < (afeCriticalPoint (-t) - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  rw [hughesYoungAffineLogBetaContinuation_critical_swapped_eq_explicit
    hleft hw]
  rw [show
      -(afeCriticalPoint t + w) +
          -(afeCriticalPoint (-t) + w) + 1 = -(2 * w) by
        unfold afeCriticalPoint
        push_cast
        ring]
  dsimp only [w]
  exact hughesYoungEquation84Negative_summand_eq_contourTerm
    T t u hcHalf h k a b hr q

/-- Absolute convergence of the literal positive pure DFI modulus
series. -/
theorem summable_dfiEquation27CentralSummand_pureReduced
    (T t c u : ℝ) {h k a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcHalf : c < 1 / 2) (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand a b r
      (hughesYoungPureReducedMellinWeight T t c u h k) q) := by
  exact (summable_hughesYoungEquation84PositiveContourTerm
    T t h k a b r ha hb hr ((c : ℂ) + (u : ℂ) * I)).congr
      (fun q => (dfiEquation27CentralSummand_pureReduced_eq_contourTerm
        T t c u hc hcHalf hr q).symm)

/-- Absolute convergence of the literal coordinate-swapped negative pure
DFI modulus series. -/
theorem summable_dfiEquation27CentralSummand_swappedPureReduced
    (T t c u : ℝ) {h k a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcHalf : c < 1 / 2) (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand b a r
      (dfiSwapWeight
        (hughesYoungPureReducedMellinWeight T t c u h k)) q) := by
  exact (summable_hughesYoungEquation84NegativeContourTerm
    T t h k a b r ha hb hr ((c : ℂ) + (u : ℂ) * I)).congr
      (fun q =>
        (dfiEquation27CentralSummand_swappedPureReduced_eq_contourTerm
          T t c u hc hcHalf hr q).symm)

/-! ## Physical integrability after applying the height cutoff -/

set_option maxHeartbeats 800000 in
/-- On a positive central slice, the height-weighted pure Mellin source is
integrable.  The proof uses the exact Fourier-character identity and the
height-independent critical-beta majorant. -/
theorem integrable_dfiEquation27C_heightWeight_mul_pureReduced
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y)
      x (x - r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hbase0 :=
    integrable_dfiEquation27C_pureReducedStaticWeight_posShift
      hc hcHalf T u hh hk a b qx qy hrR
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) x (x - r)) := by
    simpa [sub_eq_add_neg, add_assoc] using
      hbase0.comp_add_right (-(r : ℝ))
  have hmajor : Integrable (fun x : ℝ =>
      (hughesYoungHeightFourierInput T c u t : ℂ) *
        dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c u h k)
          x (x - r)) := hbase.const_mul _
  let phase : ℝ → ℂ := fun x =>
    Complex.exp ((((t * Real.log ((x - r) / x) : ℝ) : ℂ)) * I)
  have heq : (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y)
      x (x - r)) = fun x => phase x *
        ((hughesYoungHeightFourierInput T c u t : ℂ) *
          dfiEquation27C a b qx qy
            (hughesYoungPureReducedStaticWeight T c u h k)
            x (x - r)) := by
    funext x
    by_cases hx : 0 < x
    · by_cases hy : 0 < x - r
      · unfold dfiEquation27C
        change dfiEquation27LogFactor a qx x *
            dfiEquation27LogFactor b qy (x - r) *
              ((hughesYoungHeightWeight T t : ℂ) *
                hughesYoungPureReducedMellinWeight
                  T t c u h k x (x - r)) = _
        rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
          T t c u hh hk hx hy]
        dsimp only [phase]
        ring
      · have hy' : x - r ≤ 0 := le_of_not_gt hy
        unfold dfiEquation27C
        change dfiEquation27LogFactor a qx x *
            dfiEquation27LogFactor b qy (x - r) *
              ((hughesYoungHeightWeight T t : ℂ) *
                hughesYoungPureReducedMellinWeight
                  T t c u h k x (x - r)) = _
        rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
          T t c u h k hy']
        unfold hughesYoungPureReducedStaticWeight
        simp [hy]
    · have hx' : x ≤ 0 := le_of_not_gt hx
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx x *
          dfiEquation27LogFactor b qy (x - r) *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungPureReducedMellinWeight
                T t c u h k x (x - r)) = _
      rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
        T t c u h k hx']
      unfold hughesYoungPureReducedStaticWeight
      simp [hx]
  have hphaseMeas : AEStronglyMeasurable phase := by
    dsimp only [phase]
    have hratio : Measurable (fun x : ℝ => (x - (r : ℝ)) / x) :=
      (measurable_id.sub measurable_const).div measurable_id
    have hlog : Measurable (fun x : ℝ =>
        Real.log ((x - (r : ℝ)) / x)) :=
      Real.measurable_log.comp hratio
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hlog)).mul_const I)).aestronglyMeasurable
  have hphaseBound : ∀ x : ℝ, ‖phase x‖ ≤ 1 := by
    intro x
    dsimp only [phase]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [heq]
  exact hmajor.bdd_mul hphaseMeas
    (Filter.Eventually.of_forall hphaseBound)

set_option maxHeartbeats 800000 in
/-- Coordinate-swapped counterpart of the height-weighted physical
integrability theorem. -/
theorem integrable_dfiEquation27C_heightWeight_mul_swappedPureReduced
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b qx qy : ℕ)
    {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y))
      x (x - r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hbase0 :=
    integrable_dfiEquation27C_swappedPureReducedStaticWeight_posShift
      hc hcHalf T u hh hk a b qx qy hrR
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        x (x - r)) := by
    simpa [sub_eq_add_neg, add_assoc] using
      hbase0.comp_add_right (-(r : ℝ))
  have hmajor : Integrable (fun x : ℝ =>
      (hughesYoungHeightFourierInput T c u t : ℂ) *
        dfiEquation27C b a qy qx
          (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
          x (x - r)) := hbase.const_mul _
  let phase : ℝ → ℂ := fun x =>
    Complex.exp ((((t * Real.log (x / (x - r)) : ℝ) : ℂ)) * I)
  have heq : (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y))
      x (x - r)) = fun x => phase x *
        ((hughesYoungHeightFourierInput T c u t : ℂ) *
          dfiEquation27C b a qy qx
            (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
            x (x - r)) := by
    funext x
    by_cases hy : 0 < x - r
    · have hx : 0 < x := by
        have hr0 : (0 : ℝ) ≤ r := by positivity
        linarith
      rw [dfiEquation27C_swap, dfiEquation27C_swap]
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx (x - r) *
          dfiEquation27LogFactor b qy x *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungPureReducedMellinWeight
                T t c u h k (x - r) x) = _
      rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
        T t c u hh hk hy hx]
      dsimp only [phase]
      ring
    · have hy' : x - r ≤ 0 := le_of_not_gt hy
      rw [dfiEquation27C_swap, dfiEquation27C_swap]
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx (x - r) *
          dfiEquation27LogFactor b qy x *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungPureReducedMellinWeight
                T t c u h k (x - r) x) = _
      rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
        T t c u h k hy']
      unfold hughesYoungPureReducedStaticWeight
      simp [hy]
  have hphaseMeas : AEStronglyMeasurable phase := by
    dsimp only [phase]
    have hratio : Measurable (fun x : ℝ => x / (x - (r : ℝ))) :=
      measurable_id.div (measurable_id.sub measurable_const)
    have hlog : Measurable (fun x : ℝ =>
        Real.log (x / (x - (r : ℝ)))) :=
      Real.measurable_log.comp hratio
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hlog)).mul_const I)).aestronglyMeasurable
  have hphaseBound : ∀ x : ℝ, ‖phase x‖ ≤ 1 := by
    intro x
    dsimp only [phase]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [heq]
  exact hmajor.bdd_mul hphaseMeas
    (Filter.Eventually.of_forall hphaseBound)

/-! ## The literal non-lower multiplier inside the physical integral -/

/-- Pointwise, the non-lower active complement is exactly its real cutoff
multiplier times the pure equation-(83) Mellin source. -/
theorem hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) (x y : ℝ) :
    hughesYoungNonLowerActiveComplementReducedMellinWeight
        T t c u h k a b R K x y =
      (hughesYoungNonLowerActiveComplementMultiplier a b R K x y : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k x y := by
  rw [← congrFun (congrFun
    (hughesYoungNonLowerActiveComplementMellinWeightComplex_vertical
      T t c u hh hk a b R K) x) y]
  unfold hughesYoungNonLowerActiveComplementMellinWeightComplex
    hughesYoungPureReducedMellinWeight
  by_cases hxy : 0 < x ∧ 0 < y
  · simp only [hxy.1, hxy.2, and_self, if_true]
    rw [hughesYoungReducedMellinScaleConstantComplex_vertical,
      hughesYoungLogPower_eq_cpow hxy.1,
      hughesYoungLogPower_eq_cpow hxy.2]
    ring
  · simp [hxy]

/-- The non-lower multiplier upper bound, placed next to the physical
source consumer so it is available before the later public restatement. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_le_one_source
    (a b R K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≤ 1 := by
  have hactive := hughesYoungActiveContinuousDyadicWeight_nonneg
    a b R K hx hy
  have hx0 := hughesYoungDyadicStep_nonneg
    (x * hughesYoungDyadicRatio)
  have hy0 := hughesYoungDyadicStep_nonneg
    (y * hughesYoungDyadicRatio)
  have hx1 := hughesYoungDyadicStep_le_one
    (x * hughesYoungDyadicRatio)
  have hy1 := hughesYoungDyadicStep_le_one
    (y * hughesYoungDyadicRatio)
  unfold hughesYoungNonLowerActiveComplementMultiplier
  have hprod :
      (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
          (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
  linarith

set_option maxHeartbeats 800000 in
/-- The literal non-lower positive central slice is integrable after the
Hughes--Young height cutoff. -/
theorem integrable_dfiEquation27C_heightWeight_mul_nonLowerComplement
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y)
      x (x - r)) := by
  let P : ℝ → ℝ → ℂ := fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungPureReducedMellinWeight T t c u h k X Y
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy P x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_pureReduced
      hc hcHalf t u hh hk a b qx qy hr
  let m : ℝ → ℂ := fun x =>
    if 0 < x ∧ 0 < x - (r : ℝ) then
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K x (x - r) : ℂ)
    else 0
  have hmultCont : Continuous (fun x : ℝ =>
      hughesYoungNonLowerActiveComplementMultiplier
        a b R K x (x - (r : ℝ))) := by
    unfold hughesYoungNonLowerActiveComplementMultiplier
      hughesYoungActiveContinuousDyadicWeight hughesYoungFullDyadicCutoff
    apply Continuous.sub
    · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
        (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
    · apply continuous_finsetSum
      intro ij _hij
      exact ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.1)).continuous.comp (by fun_prop)).mul
        ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.2)).continuous.comp (by fun_prop))
  have hmMeas : AEStronglyMeasurable m := by
    apply Measurable.aestronglyMeasurable
    dsimp only [m]
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_const
          (measurable_id.sub measurable_const))
    · exact Complex.measurable_ofReal.comp hmultCont.measurable
    · exact measurable_const
  have hmBound : ∀ x : ℝ, ‖m x‖ ≤ 1 := by
    intro x
    dsimp only [m]
    by_cases hxy : 0 < x ∧ 0 < x - (r : ℝ)
    · rw [if_pos hxy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungNonLowerActiveComplementMultiplier_nonneg
          a b R K hxy.1.le hxy.2.le)]
      exact hughesYoungNonLowerActiveComplementMultiplier_le_one_source
        a b R K hxy.1.le hxy.2.le
    · rw [if_neg hxy, norm_zero]
      norm_num
  have heq : (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y)
      x (x - r)) = fun x => m x *
        dfiEquation27C a b qx qy P x (x - r) := by
    funext x
    unfold dfiEquation27C
    change dfiEquation27LogFactor a qx x *
        dfiEquation27LogFactor b qy (x - r) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementReducedMellinWeight
              T t c u h k a b R K x (x - r)) = _
    rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
      T t c u hh hk a b R K]
    by_cases hxy : 0 < x ∧ 0 < x - (r : ℝ)
    · dsimp only [m, P]
      rw [if_pos hxy]
      ring
    · have hpure : hughesYoungPureReducedMellinWeight
          T t c u h k x (x - r) = 0 := by
        by_cases hx : 0 < x
        · exact hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
            T t c u h k (le_of_not_gt (fun hy => hxy ⟨hx, hy⟩))
        · exact hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
            T t c u h k (le_of_not_gt hx)
      dsimp only [m, P]
      rw [if_neg hxy]
      rw [hpure]
      ring
  rw [heq]
  exact hbase.bdd_mul hmMeas
    (Filter.Eventually.of_forall hmBound)

set_option maxHeartbeats 800000 in
/-- Coordinate-swapped integrability of the literal non-lower source. -/
theorem integrable_dfiEquation27C_heightWeight_mul_swappedNonLowerComplement
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y))
      x (x - r)) := by
  let P : ℝ → ℝ → ℂ := fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungPureReducedMellinWeight T t c u h k X Y
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C b a qy qx (dfiSwapWeight P) x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_swappedPureReduced
      hc hcHalf t u hh hk a b qx qy hr
  let m : ℝ → ℂ := fun x =>
    if 0 < x - (r : ℝ) ∧ 0 < x then
      (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (x - r) x : ℂ)
    else 0
  have hmultCont : Continuous (fun x : ℝ =>
      hughesYoungNonLowerActiveComplementMultiplier
        a b R K (x - (r : ℝ)) x) := by
    unfold hughesYoungNonLowerActiveComplementMultiplier
      hughesYoungActiveContinuousDyadicWeight hughesYoungFullDyadicCutoff
    apply Continuous.sub
    · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
        (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
    · apply continuous_finsetSum
      intro ij _hij
      exact ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.1)).continuous.comp (by fun_prop)).mul
        ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.2)).continuous.comp (by fun_prop))
  have hmMeas : AEStronglyMeasurable m := by
    apply Measurable.aestronglyMeasurable
    dsimp only [m]
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const
          (measurable_id.sub measurable_const)).inter
        (measurableSet_lt measurable_const measurable_id)
    · exact Complex.measurable_ofReal.comp hmultCont.measurable
    · exact measurable_const
  have hmBound : ∀ x : ℝ, ‖m x‖ ≤ 1 := by
    intro x
    dsimp only [m]
    by_cases hxy : 0 < x - (r : ℝ) ∧ 0 < x
    · rw [if_pos hxy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungNonLowerActiveComplementMultiplier_nonneg
          a b R K hxy.1.le hxy.2.le)]
      exact hughesYoungNonLowerActiveComplementMultiplier_le_one_source
        a b R K hxy.1.le hxy.2.le
    · rw [if_neg hxy, norm_zero]
      norm_num
  have heq : (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y))
      x (x - r)) = fun x => m x *
        dfiEquation27C b a qy qx (dfiSwapWeight P) x (x - r) := by
    funext x
    rw [dfiEquation27C_swap, dfiEquation27C_swap]
    unfold dfiEquation27C
    change dfiEquation27LogFactor a qx (x - r) *
        dfiEquation27LogFactor b qy x *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementReducedMellinWeight
              T t c u h k a b R K (x - r) x) = _
    rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
      T t c u hh hk a b R K]
    by_cases hxy : 0 < x - (r : ℝ) ∧ 0 < x
    · dsimp only [m, P, dfiSwapWeight]
      rw [if_pos hxy]
      ring
    · have hpure : hughesYoungPureReducedMellinWeight
          T t c u h k (x - r) x = 0 := by
        by_cases hy : 0 < x - r
        · exact hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
            T t c u h k (le_of_not_gt (fun hx => hxy ⟨hy, hx⟩))
        · exact hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
            T t c u h k (le_of_not_gt hy)
      dsimp only [m, P, dfiSwapWeight]
      rw [if_neg hxy, hpure]
      ring
  rw [heq]
  exact hbase.bdd_mul hmMeas
    (Filter.Eventually.of_forall hmBound)

set_option maxHeartbeats 600000 in
/-- Integrability of the height-weighted lower endpoint on a positive
central slice. -/
theorem integrable_dfiEquation27C_heightWeight_mul_lowerBoundary
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y)
      x (x - r)) := by
  let P : ℝ → ℝ → ℂ := fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungPureReducedMellinWeight T t c u h k X Y
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C a b qx qy P x (x - r)) :=
    integrable_dfiEquation27C_heightWeight_mul_pureReduced
      hc hcHalf t u hh hk a b qx qy hr
  let m : ℝ → ℂ := fun x =>
    (hughesYoungLowerBoundaryMultiplier x (x - (r : ℝ)) : ℂ)
  have hmCont : Continuous m := by
    dsimp only [m]
    have hsx : Continuous (fun x : ℝ =>
        hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) :=
      contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)
    have hsy : Continuous (fun x : ℝ =>
        hughesYoungDyadicStep
          ((x - (r : ℝ)) * hughesYoungDyadicRatio)) :=
      contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)
    have hreal : Continuous (fun x : ℝ =>
        hughesYoungLowerBoundaryMultiplier x (x - (r : ℝ))) := by
      unfold hughesYoungLowerBoundaryMultiplier
      exact (hsx.add hsy).sub (hsx.mul hsy)
    exact Complex.continuous_ofReal.comp hreal
  have hmBound : ∀ x : ℝ, ‖m x‖ ≤ 1 := by
    intro x
    have hnorm : ‖m x‖ =
        hughesYoungLowerBoundaryMultiplier x (x - r) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungLowerBoundaryMultiplier_nonneg _ _)]
    rw [hnorm]
    exact hughesYoungLowerBoundaryMultiplier_le_one _ _
  have heq : (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y)
      x (x - r)) = fun x => m x *
        dfiEquation27C a b qx qy P x (x - r) := by
    funext x
    unfold dfiEquation27C
    change dfiEquation27LogFactor a qx x *
        dfiEquation27LogFactor b qy (x - r) *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k x (x - r)) = _
    rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul]
    dsimp only [m, P]
    ring
  rw [heq]
  exact hbase.bdd_mul hmCont.aestronglyMeasurable
    (Filter.Eventually.of_forall hmBound)

set_option maxHeartbeats 600000 in
/-- Coordinate-swapped integrability of the height-weighted lower
endpoint. -/
theorem integrable_dfiEquation27C_heightWeight_mul_swappedLowerBoundary
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y))
      x (x - r)) := by
  let P : ℝ → ℝ → ℂ := fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungPureReducedMellinWeight T t c u h k X Y
  have hbase : Integrable (fun x : ℝ =>
      dfiEquation27C b a qy qx (dfiSwapWeight P) x (x - r)) :=
    integrable_dfiEquation27C_heightWeight_mul_swappedPureReduced
      hc hcHalf t u hh hk a b qx qy hr
  let m : ℝ → ℂ := fun x =>
    (hughesYoungLowerBoundaryMultiplier (x - (r : ℝ)) x : ℂ)
  have hmCont : Continuous m := by
    dsimp only [m]
    have hsx : Continuous (fun x : ℝ =>
        hughesYoungDyadicStep
          ((x - (r : ℝ)) * hughesYoungDyadicRatio)) :=
      contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)
    have hsy : Continuous (fun x : ℝ =>
        hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) :=
      contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)
    have hreal : Continuous (fun x : ℝ =>
        hughesYoungLowerBoundaryMultiplier (x - (r : ℝ)) x) := by
      unfold hughesYoungLowerBoundaryMultiplier
      exact (hsx.add hsy).sub (hsx.mul hsy)
    exact Complex.continuous_ofReal.comp hreal
  have hmBound : ∀ x : ℝ, ‖m x‖ ≤ 1 := by
    intro x
    have hnorm : ‖m x‖ =
        hughesYoungLowerBoundaryMultiplier (x - r) x := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hughesYoungLowerBoundaryMultiplier_nonneg _ _)]
    rw [hnorm]
    exact hughesYoungLowerBoundaryMultiplier_le_one _ _
  have heq : (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y))
      x (x - r)) = fun x => m x *
        dfiEquation27C b a qy qx (dfiSwapWeight P) x (x - r) := by
    funext x
    rw [dfiEquation27C_swap, dfiEquation27C_swap]
    unfold dfiEquation27C
    change dfiEquation27LogFactor a qx (x - r) *
        dfiEquation27LogFactor b qy x *
          ((hughesYoungHeightWeight T t : ℂ) *
            hughesYoungLowerBoundaryReducedMellinCorrection
              T t c u h k (x - r) x) = _
    rw [hughesYoungLowerBoundaryReducedMellinCorrection_eq_multiplier_mul]
    dsimp only [m, P, dfiSwapWeight]
    ring
  rw [heq]
  exact hbase.bdd_mul hmCont.aestronglyMeasurable
    (Filter.Eventually.of_forall hmBound)

/-! ## Pointwise absolute convergence of the lower endpoint series -/

/-- Fixed-height norm bound for one positive endpoint modulus term. -/
theorem norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le_fixed
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (T t u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (hughesYoungPureReducedStaticWeight T c u h k)
              (y + r) y‖) *
          ‖hughesYoungHeightFourierInput T c u t‖) := by
  let J : ℝ → ℂ := fun y =>
    hughesYoungLowerBoundaryCentralHeightIntegrand T c u h k (r : ℝ)
      a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t
  let g : ℝ → ℝ := fun y =>
    ‖dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y‖ *
      ‖hughesYoungHeightFourierInput T c u t‖
  have hstatic := integrable_dfiEquation27C_pureReducedStaticWeight_posShift
    hc hcHalf T u hh hk a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (show (0 : ℝ) < r by exact_mod_cast hr)
  have hg : Integrable g (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (hstatic.norm.mul_const
      ‖hughesYoungHeightFourierInput T c u t‖).integrableOn
  have hJg : ∀ y : ℝ, ‖J y‖ ≤ g y := by
    intro y
    exact norm_hughesYoungLowerBoundaryCentralHeightIntegrand_le
      T c u hh hk (show (0 : ℝ) < r by exact_mod_cast hr)
        a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t
  have hIntegral : ‖∫ y in Set.Ioi (0 : ℝ), J y‖ ≤
      ∫ y in Set.Ioi (0 : ℝ), g y := by
    exact MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall hJg)
  rw [hughesYoungLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral]
  simp only [norm_mul]
  calc
    _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          (∫ y in Set.Ioi (0 : ℝ), g y) := by gcongr
    _ = _ := by
      dsimp only [g]
      rw [MeasureTheory.integral_mul_const]

set_option maxHeartbeats 1600000 in
/-- At every fixed height, the complete positive lower-endpoint modulus
series is absolutely summable. -/
theorem summable_hughesYoungLowerBoundaryCentralSeriesHeightTerm_fixed
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Summable (fun q : ℕ =>
      hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let H : ℝ := ‖hughesYoungHeightFourierInput T c u t‖
  let K₀ : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * H *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ =>
      K₀ * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K₀
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungLowerBoundaryCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
      ‖(Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q)‖
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hPhysical :=
      integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
        hc hc4 T u hh hk a b (dfiReducedDenominator a q)
          (dfiReducedDenominator b q)
          (show (1 : ℝ) ≤ r by exact_mod_cast hr)
    have hTerm := norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le_fixed
      hc (hc4.trans_lt (by norm_num)) T t u hh hk hr a b q
    calc
      ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
          T t c u h k a b r q‖ ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((∫ y in Set.Ioi (0 : ℝ),
              ‖dfiEquation27C a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (hughesYoungPureReducedStaticWeight T c u h k)
                (y + r) y‖) * H) := by simpa only [H] using hTerm
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) * H) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            ((2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2)) * H) := by
        gcongr
        calc
          2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = K₀ * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [K₀]
        ring

/-- Fixed-height norm bound for one swapped endpoint modulus term. -/
theorem norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le_fixed
    {c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2)
    (T t u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C b a
              (dfiReducedDenominator b q) (dfiReducedDenominator a q)
              (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
              (y + r) y‖) *
          ‖hughesYoungHeightFourierInput T c u t‖) := by
  let J : ℝ → ℂ := fun y =>
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
      T c u h k (r : ℝ) a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t
  let g : ℝ → ℝ := fun y =>
    ‖dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
      (y + r) y‖ * ‖hughesYoungHeightFourierInput T c u t‖
  have hstatic := integrable_dfiEquation27C_swappedPureReducedStaticWeight_posShift
    hc hcHalf T u hh hk a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (show (0 : ℝ) < r by exact_mod_cast hr)
  have hg : Integrable g (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (hstatic.norm.mul_const
      ‖hughesYoungHeightFourierInput T c u t‖).integrableOn
  have hJg : ∀ y : ℝ, ‖J y‖ ≤ g y := by
    intro y
    exact norm_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_le
      T c u hh hk (show (0 : ℝ) < r by exact_mod_cast hr)
        a b (dfiReducedDenominator a q) (dfiReducedDenominator b q) y t
  have hIntegral : ‖∫ y in Set.Ioi (0 : ℝ), J y‖ ≤
      ∫ y in Set.Ioi (0 : ℝ), g y := by
    exact MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall hJg)
  rw [hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral]
  simp only [norm_mul]
  calc
    _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          (∫ y in Set.Ioi (0 : ℝ), g y) := by gcongr
    _ = _ := by
      dsimp only [g]
      rw [MeasureTheory.integral_mul_const]

set_option maxHeartbeats 1600000 in
/-- At every fixed height, the complete swapped lower-endpoint modulus
series is absolutely summable. -/
theorem summable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_fixed
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Summable (fun q : ℕ =>
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q) := by
  let A : ℝ := hughesYoungEquation84LogBudget b a r
  let H : ℝ := ‖hughesYoungHeightFourierInput T c u t‖
  let K₀ : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) * H *
    (‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget b a r)
  have hmajor : Summable (fun q : ℕ =>
      K₀ * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K₀
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ +
      ‖(Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q)‖
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCA := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      have hCB := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      dsimp only [S, A]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log b a r q hq)
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq b a r q hb ha hr
    have hPhysical :=
      integral_norm_dfiEquation27C_swappedPureReducedStaticWeight_posShift_le
        hc hc4 T u hh hk a b (dfiReducedDenominator a q)
          (dfiReducedDenominator b q)
          (show (1 : ℝ) ≤ r by exact_mod_cast hr)
    have hTerm :=
      norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le_fixed
        hc (hc4.trans_lt (by norm_num)) T t u hh hk hr a b q
    calc
      ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
          T t c u h k a b r q‖ ≤
        ‖((b : ℂ) * a)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
          ((∫ y in Set.Ioi (0 : ℝ),
              ‖dfiEquation27C b a
                (dfiReducedDenominator b q) (dfiReducedDenominator a q)
                (dfiSwapWeight
                  (hughesYoungPureReducedStaticWeight T c u h k))
                (y + r) y‖) * H) := by simpa only [H] using hTerm
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) * H) := by
        gcongr
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungPureReducedStaticScaleConstant T c u h k‖ *
            (r : ℝ) ^ (-2 * c) *
            ((2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2)) * H) := by
        gcongr
        calc
          2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = K₀ * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [K₀]
        ring

/-! ## Height-weighted summability interfaces -/

/-- Absolute summability of the positive pure source after applying the
height cutoff. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_pure
    (T t c u : ℝ) {h k a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcHalf : c < 1 / 2) (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand a b r
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y) q) := by
  have hs := (summable_dfiEquation27CentralSummand_pureReduced
    T t c u (h := h) (k := k) ha hb hc hcHalf hr).mul_left
      (hughesYoungHeightWeight T t : ℂ)
  simpa only [dfiEquation27CentralSummand_const_mul_weight] using hs

/-- Absolute summability of the swapped pure source after applying the
height cutoff. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_swappedPure
    (T t c u : ℝ) {h k a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcHalf : c < 1 / 2) (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand b a r
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y)) q) := by
  have hs := (summable_dfiEquation27CentralSummand_swappedPureReduced
    T t c u (h := h) (k := k) ha hb hc hcHalf hr).mul_left
      (hughesYoungHeightWeight T t : ℂ)
  have hswap : dfiSwapWeight (fun X Y =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungPureReducedMellinWeight T t c u h k X Y) =
      fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        dfiSwapWeight
          (hughesYoungPureReducedMellinWeight T t c u h k) X Y := by
    funext X Y
    rfl
  rw [hswap]
  simpa only [dfiEquation27CentralSummand_const_mul_weight] using hs

/-- Absolute summability of the positive height-weighted lower endpoint. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_lowerBoundary
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand a b r
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y) q) := by
  have hs := summable_hughesYoungLowerBoundaryCentralSeriesHeightTerm_fixed
    hc hc4 T t u hh hk ha hb hr
  simpa only [hughesYoungLowerBoundaryCentralSeriesHeightTerm,
    dfiEquation27CentralSummand_const_mul_weight] using hs

/-- Absolute summability of the swapped height-weighted lower endpoint. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_swappedLowerBoundary
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand b a r
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k X Y)) q) := by
  have hs :=
    summable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_fixed
      hc hc4 T t u hh hk ha hb hr
  have hswap : dfiSwapWeight (fun X Y =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k X Y) =
      fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        dfiSwapWeight
          (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) X Y := by
    funext X Y
    rfl
  rw [hswap]
  simpa only [hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm,
    dfiEquation27CentralSummand_const_mul_weight] using hs

/-- One height-weighted full dyadic box has an absolutely summable
positive equation-(27) modulus series, including dyadic index zero. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_fullDyadic
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (t u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (i j : ℕ) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand a b r
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicReducedMellinWeight
          T t c u h k i j X Y) q) := by
  by_cases ht : hughesYoungHeightWeight T t = 0
  · have hq (q : ℕ) : dfiEquation27CentralSummand a b r
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFullDyadicReducedMellinWeight
            T t c u h k i j X Y) q = 0 := by
      rw [dfiEquation27CentralSummand_const_mul_weight, ht]
      simp
    exact (summable_zero : Summable (fun _q : ℕ => (0 : ℂ))).congr
      (fun q => (hq q).symm)
  · have hs :=
      summable_dfiEquation27CentralSummand_fullDyadic_of_heightWeight_ne
        hT hc u (hughesYoungFullDyadicScale_pos i)
          (hughesYoungFullDyadicScale_pos j) hh hk ha hb hr ht
    have hscaled := hs.mul_left (hughesYoungHeightWeight T t : ℂ)
    simpa only [dfiEquation27CentralSummand_const_mul_weight] using hscaled

/-- The complete finite active weight has an absolutely summable positive
equation-(27) modulus series after applying the height cutoff. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_activeReassembled
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand a b r
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K X Y) q) := by
  let S := hughesYoungActiveDyadicBoxes a b R K
  let F : ℕ × ℕ → ℝ → ℝ → ℂ := fun ij X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFullDyadicReducedMellinWeight
        T t c u h k ij.1 ij.2 X Y
  have hcomponent (ij : ℕ × ℕ) : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r (F ij) q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_fullDyadic
      hT hc t u hh hk ha hb hr ij.1 ij.2
  have hfinite : Summable (fun q : ℕ =>
      ∑ ij ∈ S, dfiEquation27CentralSummand a b r (F ij) q) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert ij S hij ih =>
        simpa only [Finset.sum_insert hij] using (hcomponent ij).add ih
  have hweight : (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungActiveReassembledReducedMellinWeight
        T t c u h k a b R K X Y) =
      fun X Y => ∑ ij ∈ S, F ij X Y := by
    funext X Y
    unfold hughesYoungActiveReassembledReducedMellinWeight
    dsimp only [S, F]
    rw [Finset.mul_sum]
  have hterm : ∀ q : ℕ,
      dfiEquation27CentralSummand a b r
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K X Y) q =
        ∑ ij ∈ S, dfiEquation27CentralSummand a b r (F ij) q := by
    intro q
    rw [hweight]
    apply dfiEquation27CentralSummand_finsetSum
    intro ij _hij
    have hi := integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
      T t c u (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2) hh hk a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q) r
    simpa only [F, dfiEquation27C_const_mul_weight] using
      hi.const_mul (hughesYoungHeightWeight T t : ℂ)
  exact hfinite.congr (fun q => (hterm q).symm)

/-- One height-weighted coordinate-swapped full dyadic box has an absolutely
summable negative equation-(27) modulus series, including dyadic index zero. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_swappedFullDyadic
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (t u : ℝ)
    {h k a b r : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (i j : ℕ) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand b a r
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicReducedMellinWeight
          T t c u h k i j X Y)) q) := by
  have hswap : dfiSwapWeight (fun X Y =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicReducedMellinWeight T t c u h k i j X Y) =
      fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        dfiSwapWeight
          (hughesYoungFullDyadicReducedMellinWeight T t c u h k i j) X Y := by
    funext X Y
    rfl
  rw [hswap]
  by_cases ht : hughesYoungHeightWeight T t = 0
  · have hq (q : ℕ) : dfiEquation27CentralSummand b a r
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          dfiSwapWeight
            (hughesYoungFullDyadicReducedMellinWeight
              T t c u h k i j) X Y) q = 0 := by
      rw [dfiEquation27CentralSummand_const_mul_weight, ht]
      simp
    exact (summable_zero : Summable (fun _q : ℕ => (0 : ℂ))).congr
      (fun q => (hq q).symm)
  · have hs :=
      summable_dfiEquation27CentralSummand_swappedFullDyadic_of_heightWeight_ne
        hT hc u (hughesYoungFullDyadicScale_pos i)
          (hughesYoungFullDyadicScale_pos j) hh hk ha hb hr ht
    have hscaled := hs.mul_left (hughesYoungHeightWeight T t : ℂ)
    simpa only [dfiEquation27CentralSummand_const_mul_weight] using hscaled

/-- The complete finite active weight has an absolutely summable
coordinate-swapped negative equation-(27) modulus series after applying the
height cutoff. -/
theorem summable_dfiEquation27CentralSummand_heightWeight_mul_swappedActiveReassembled
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => dfiEquation27CentralSummand b a r
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K X Y)) q) := by
  let S := hughesYoungActiveDyadicBoxes a b R K
  let F : ℕ × ℕ → ℝ → ℝ → ℂ := fun ij X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFullDyadicReducedMellinWeight
        T t c u h k ij.1 ij.2 X Y
  have hcomponent (ij : ℕ × ℕ) : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r (dfiSwapWeight (F ij)) q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_swappedFullDyadic
      hT hc t u hh hk ha hb hr ij.1 ij.2
  have hfinite : Summable (fun q : ℕ =>
      ∑ ij ∈ S, dfiEquation27CentralSummand b a r
        (dfiSwapWeight (F ij)) q) := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert ij S hij ih =>
        simpa only [Finset.sum_insert hij] using (hcomponent ij).add ih
  have hweight : dfiSwapWeight (fun X Y =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K X Y) =
      fun X Y => ∑ ij ∈ S, dfiSwapWeight (F ij) X Y := by
    funext X Y
    unfold hughesYoungActiveReassembledReducedMellinWeight dfiSwapWeight
    dsimp only [S, F]
    rw [Finset.mul_sum]
  have hterm : ∀ q : ℕ,
      dfiEquation27CentralSummand b a r
          (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K X Y)) q =
        ∑ ij ∈ S, dfiEquation27CentralSummand b a r
          (dfiSwapWeight (F ij)) q := by
    intro q
    rw [hweight]
    apply dfiEquation27CentralSummand_finsetSum
    intro ij _hij
    have hi := integrable_dfiEquation27C_reducedLocalizedMellinWeight_centralSlice
      T t c u (hughesYoungFullDyadicScale_pos ij.1)
        (hughesYoungFullDyadicScale_pos ij.2) hh hk a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (-(r : ℝ))
    have hshift := hi.comp_add_right (-(r : ℝ))
    have hscaled := hshift.const_mul (hughesYoungHeightWeight T t : ℂ)
    convert hscaled using 1
    funext x
    unfold dfiEquation27C dfiSwapWeight F
      hughesYoungFullDyadicReducedMellinWeight
    ring_nf
  exact hfinite.congr (fun q => (hterm q).symm)

/-- The lower-boundary-removed source weight is literally the pure
equation-(83) weight minus the lower endpoint and the active dyadic source.
This is the pointwise identity that the preceding improper-integral
linearity lemmas will transport through the DFI source. -/
theorem hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_pure_sub_lower_sub_active
    (T t c u : ℝ) (h k a b R K : ℕ) :
    hughesYoungNonLowerActiveComplementReducedMellinWeight
        T t c u h k a b R K =
      fun x y =>
        hughesYoungPureReducedMellinWeight T t c u h k x y -
          hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k x y -
          hughesYoungActiveReassembledReducedMellinWeight
            T t c u h k a b R K x y := by
  funext x y
  unfold hughesYoungNonLowerActiveComplementReducedMellinWeight
    hughesYoungLowerBoundaryReducedMellinCorrection
  ring

/-- Integrability of the height-weighted active source on a positive central
slice, deduced from the exact pure/lower/non-lower partition. -/
theorem integrable_dfiEquation27C_heightWeight_mul_activeReassembled
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K X Y) x (x - r)) := by
  have hP := integrable_dfiEquation27C_heightWeight_mul_pureReduced
    (T := T) hc hcHalf t u hh hk a b qx qy hr
  have hL := integrable_dfiEquation27C_heightWeight_mul_lowerBoundary
    (T := T) hc hcHalf t u hh hk a b qx qy hr
  have hN := integrable_dfiEquation27C_heightWeight_mul_nonLowerComplement
    (T := T) hc hcHalf t u hh hk a b qx qy R K hr
  have hPLN := (hP.sub hL).sub hN
  convert hPLN using 1
  funext x
  unfold dfiEquation27C
  dsimp only
  have hactive :
      hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K x (x - r) =
        hughesYoungPureReducedMellinWeight T t c u h k x (x - r) -
          hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k x (x - r) -
          hughesYoungNonLowerActiveComplementReducedMellinWeight
            T t c u h k a b R K x (x - r) := by
    have hn := congrFun (congrFun
      (hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_pure_sub_lower_sub_active
        T t c u h k a b R K) x) (x - r)
    rw [hn]
    ring
  rw [hactive]
  simp only [Pi.sub_apply]
  ring

/-- Coordinate-swapped integrability of the height-weighted active source on
the negative central slice. -/
theorem integrable_dfiEquation27C_heightWeight_mul_swappedActiveReassembled
    {T c : ℝ} (hc : 0 < c) (hcHalf : c < 1 / 2) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K X Y)) x (x - r)) := by
  have hP := integrable_dfiEquation27C_heightWeight_mul_swappedPureReduced
    (T := T) hc hcHalf t u hh hk a b qx qy hr
  have hL := integrable_dfiEquation27C_heightWeight_mul_swappedLowerBoundary
    (T := T) hc hcHalf t u hh hk a b qx qy hr
  have hN := integrable_dfiEquation27C_heightWeight_mul_swappedNonLowerComplement
    (T := T) hc hcHalf t u hh hk a b qx qy R K hr
  have hPLN := (hP.sub hL).sub hN
  convert hPLN using 1
  funext x
  unfold dfiEquation27C dfiSwapWeight
  dsimp only
  have hactive :
      hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K (x - r) x =
        hughesYoungPureReducedMellinWeight T t c u h k (x - r) x -
          hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k (x - r) x -
          hughesYoungNonLowerActiveComplementReducedMellinWeight
            T t c u h k a b R K (x - r) x := by
    have hn := congrFun (congrFun
      (hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_pure_sub_lower_sub_active
        T t c u h k a b R K) (x - r)) x
    rw [hn]
    ring
  rw [hactive]
  simp only [Pi.sub_apply]
  ring

set_option maxHeartbeats 800000 in
/-- Exact subtraction formula for one positive equation-(27) shift after the
height cutoff.  Both infinite Ramanujan subtractions are justified by absolute
summability and both improper-integral subtractions by integrability. -/
theorem dfiEquation27CentralSeries_heightWeight_mul_nonLower_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (R K : ℕ) :
    dfiEquation27CentralSeries a b r
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementReducedMellinWeight
            T t c u h k a b R K X Y) =
      (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungPureReducedMellinWeight T t c u h k) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries a b r
            (hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K) := by
  have hcHalf : c < 1 / 2 := by linarith
  let P : ℝ → ℝ → ℂ := fun X Y => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungPureReducedMellinWeight T t c u h k X Y
  let L : ℝ → ℝ → ℂ := fun X Y => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k X Y
  let A : ℝ → ℝ → ℂ := fun X Y => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungActiveReassembledReducedMellinWeight
      T t c u h k a b R K X Y
  let N : ℝ → ℝ → ℂ := fun X Y => (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungNonLowerActiveComplementReducedMellinWeight
      T t c u h k a b R K X Y
  have hPsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r P q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_pure
      T t c u (h := h) (k := k) ha hb hc hcHalf hr
  have hLsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r L q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_lowerBoundary
      hc hc4 T t u hh hk ha hb hr
  have hAsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r A q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_activeReassembled
      hT hc t u hh hk ha hb hr R K
  have hPint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      P x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_pureReduced
      (T := T) hc hcHalf t u hh hk a b _ _ hr
  have hLint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      L x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_lowerBoundary
      (T := T) hc hcHalf t u hh hk a b _ _ hr
  have hAint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      A x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_activeReassembled
      (T := T) hc hcHalf t u hh hk a b _ _ R K hr
  have hfirst := dfiEquation27CentralSeries_sub_weight a b r P L
    hPsum hLsum hPint hLint
  have hPLsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b r (fun X Y => P X Y - L X Y) q) :=
    (hPsum.sub hLsum).congr (fun q =>
      (dfiEquation27CentralSummand_sub_weight a b r q P L
        (hPint q) (hLint q)).symm)
  have hPLint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (fun X Y => P X Y - L X Y) x (x - r)) := by
    convert (hPint q).sub (hLint q) using 1
    funext x
    exact dfiEquation27C_sub_weight a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) P L x (x - r)
  have hsecond := dfiEquation27CentralSeries_sub_weight a b r
    (fun X Y => P X Y - L X Y) A hPLsum hAsum hPLint hAint
  have hN : N = fun X Y => P X Y - L X Y - A X Y := by
    funext X Y
    dsimp only [N, P, L, A]
    rw [congrFun (congrFun
      (hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_pure_sub_lower_sub_active
        T t c u h k a b R K) X) Y]
    ring
  change dfiEquation27CentralSeries a b r N = _
  rw [hN, hsecond, hfirst]
  simp only [P, L, A, dfiEquation27CentralSeries_const_mul_weight]

set_option maxHeartbeats 800000 in
/-- Exact coordinate-swapped counterpart of the positive subtraction formula
for one negative equation-(27) shift after the height cutoff. -/
theorem dfiEquation27CentralSeries_heightWeight_mul_swappedNonLower_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (R K : ℕ) :
    dfiEquation27CentralSeries b a r
        (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementReducedMellinWeight
            T t c u h k a b R K X Y)) =
      (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight (hughesYoungPureReducedMellinWeight T t c u h k)) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight
              (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k)) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiEquation27CentralSeries b a r
            (dfiSwapWeight
              (hughesYoungActiveReassembledReducedMellinWeight
                T t c u h k a b R K)) := by
  have hcHalf : c < 1 / 2 := by linarith
  let P : ℝ → ℝ → ℂ := dfiSwapWeight (fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungPureReducedMellinWeight T t c u h k X Y)
  let L : ℝ → ℝ → ℂ := dfiSwapWeight (fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k X Y)
  let A : ℝ → ℝ → ℂ := dfiSwapWeight (fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungActiveReassembledReducedMellinWeight
        T t c u h k a b R K X Y)
  let N : ℝ → ℝ → ℂ := dfiSwapWeight (fun X Y =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementReducedMellinWeight
        T t c u h k a b R K X Y)
  have hPsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r P q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_swappedPure
      T t c u (h := h) (k := k) ha hb hc hcHalf hr
  have hLsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r L q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_swappedLowerBoundary
      hc hc4 T t u hh hk ha hb hr
  have hAsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r A q) := by
    exact summable_dfiEquation27CentralSummand_heightWeight_mul_swappedActiveReassembled
      hT hc t u hh hk ha hb hr R K
  have hPint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      P x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_swappedPureReduced
      (T := T) hc hcHalf t u hh hk a b _ _ hr
  have hLint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      L x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_swappedLowerBoundary
      (T := T) hc hcHalf t u hh hk a b _ _ hr
  have hAint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      A x (x - r)) := by
    exact integrable_dfiEquation27C_heightWeight_mul_swappedActiveReassembled
      (T := T) hc hcHalf t u hh hk a b _ _ R K hr
  have hfirst := dfiEquation27CentralSeries_sub_weight b a r P L
    hPsum hLsum hPint hLint
  have hPLsum : Summable (fun q : ℕ =>
      dfiEquation27CentralSummand b a r (fun X Y => P X Y - L X Y) q) :=
    (hPsum.sub hLsum).congr (fun q =>
      (dfiEquation27CentralSummand_sub_weight b a r q P L
        (hPint q) (hLint q)).symm)
  have hPLint (q : ℕ) : Integrable (fun x : ℝ => dfiEquation27C b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q)
      (fun X Y => P X Y - L X Y) x (x - r)) := by
    convert (hPint q).sub (hLint q) using 1
    funext x
    exact dfiEquation27C_sub_weight b a
      (dfiReducedDenominator b q) (dfiReducedDenominator a q) P L x (x - r)
  have hsecond := dfiEquation27CentralSeries_sub_weight b a r
    (fun X Y => P X Y - L X Y) A hPLsum hAsum hPLint hAint
  have hN : N = fun X Y => P X Y - L X Y - A X Y := by
    funext X Y
    dsimp only [N, P, L, A, dfiSwapWeight]
    rw [congrFun (congrFun
      (hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_pure_sub_lower_sub_active
        T t c u h k a b R K) Y) X]
    ring
  change dfiEquation27CentralSeries b a r N = _
  rw [hN, hsecond, hfirst]
  have hswapP : P = fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      dfiSwapWeight (hughesYoungPureReducedMellinWeight T t c u h k) X Y := by
    funext X Y
    rfl
  have hswapL : L = fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      dfiSwapWeight
        (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) X Y := by
    funext X Y
    rfl
  have hswapA : A = fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      dfiSwapWeight
        (hughesYoungActiveReassembledReducedMellinWeight
          T t c u h k a b R K) X Y := by
    funext X Y
    rfl
  rw [hswapP, hswapL, hswapA]
  simp only [dfiEquation27CentralSeries_const_mul_weight]

set_option maxHeartbeats 800000 in
/-- Exact signed-shift subtraction formula for every nonzero DFI shift. -/
theorem heightWeight_mul_dfiSignedCentralSeries_nonLower_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) {h k a b : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (r : ℤ) (hr0 : r ≠ 0) (R K : ℕ) :
    (hughesYoungHeightWeight T t : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungNonLowerActiveComplementReducedMellinWeight
            T t c u h k a b R K) =
      (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungPureReducedMellinWeight T t c u h k) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) -
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungActiveReassembledReducedMellinWeight
              T t c u h k a b R K) := by
  by_cases hr : 0 ≤ r
  · have hrPos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hrNat : 0 < r.toNat := by omega
    have hmain := dfiEquation27CentralSeries_heightWeight_mul_nonLower_eq
      hT hc hc4 t u hh hk ha hb hrNat R K
    simp only [dfiSignedCentralSeries, if_pos hr]
    rw [← dfiEquation27CentralSeries_const_mul_weight]
    exact hmain
  · have hrNeg : r < 0 := lt_of_not_ge hr
    have hnegPos : 0 < -r := neg_pos.mpr hrNeg
    have hrNat : 0 < (-r).toNat := by omega
    have hmain := dfiEquation27CentralSeries_heightWeight_mul_swappedNonLower_eq
      hT hc hc4 t u hh hk ha hb hrNat R K
    simp only [dfiSignedCentralSeries, if_neg hr]
    rw [← dfiEquation27CentralSeries_const_mul_weight]
    exact hmain

/-- The non-lower complement multiplier is bounded by one. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_le_one
    (a b R K : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≤ 1 := by
  have hactive := hughesYoungActiveContinuousDyadicWeight_nonneg
    a b R K hx hy
  have hx0 := hughesYoungDyadicStep_nonneg
    (x * hughesYoungDyadicRatio)
  have hy0 := hughesYoungDyadicStep_nonneg
    (y * hughesYoungDyadicRatio)
  have hx1 := hughesYoungDyadicStep_le_one
    (x * hughesYoungDyadicRatio)
  have hy1 := hughesYoungDyadicStep_le_one
    (y * hughesYoungDyadicRatio)
  unfold hughesYoungNonLowerActiveComplementMultiplier
  have hprod :
      (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
          (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio)) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
  linarith

/-- Nonvanishing of the non-lower multiplier forces both source
coordinates past the lower dyadic endpoint. -/
theorem one_div_dyadicRatio_lt_coordinates_of_nonLowerMultiplier_ne_zero
    {a b R K : ℕ} {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hne : hughesYoungNonLowerActiveComplementMultiplier a b R K x y ≠ 0) :
    1 / hughesYoungDyadicRatio < x ∧
      1 / hughesYoungDyadicRatio < y := by
  let L : ℝ :=
    (1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio)) *
      (1 - hughesYoungDyadicStep (y * hughesYoungDyadicRatio))
  have hactive0 : 0 ≤ hughesYoungActiveContinuousDyadicWeight a b R K x y :=
    hughesYoungActiveContinuousDyadicWeight_nonneg a b R K hx hy
  have hM : hughesYoungNonLowerActiveComplementMultiplier a b R K x y =
      L - hughesYoungActiveContinuousDyadicWeight a b R K x y := by
    rfl
  have hLne : L ≠ 0 := by
    intro hL
    apply hne
    rw [hM, hL]
    have hactiveLe := hughesYoungActiveContinuousDyadicWeight_le_lowerComplete
      a b R K hx hy
    change hughesYoungActiveContinuousDyadicWeight a b R K x y ≤ L at hactiveLe
    have hactiveEq : hughesYoungActiveContinuousDyadicWeight a b R K x y = 0 :=
      le_antisymm (hactiveLe.trans_eq hL) hactive0
    rw [hactiveEq]
    ring
  have hxFactor : 1 - hughesYoungDyadicStep
      (x * hughesYoungDyadicRatio) ≠ 0 := by
    intro hz
    apply hLne
    dsimp only [L]
    rw [hz, zero_mul]
  have hyFactor : 1 - hughesYoungDyadicStep
      (y * hughesYoungDyadicRatio) ≠ 0 := by
    intro hz
    apply hLne
    dsimp only [L]
    rw [hz, mul_zero]
  constructor
  · by_contra hnot
    apply hxFactor
    have hxStep : hughesYoungDyadicStep
        (x * hughesYoungDyadicRatio) = 1 := by
      apply hughesYoungDyadicStep_eq_one
      calc
        x * hughesYoungDyadicRatio ≤
            (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio :=
          mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
            hughesYoungDyadicRatio_pos.le
        _ = 1 := by field_simp [ne_of_gt hughesYoungDyadicRatio_pos]
    rw [hxStep]
    ring
  · by_contra hnot
    apply hyFactor
    have hyStep : hughesYoungDyadicStep
        (y * hughesYoungDyadicRatio) = 1 := by
      apply hughesYoungDyadicStep_eq_one
      calc
        y * hughesYoungDyadicRatio ≤
            (1 / hughesYoungDyadicRatio) * hughesYoungDyadicRatio :=
          mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
            hughesYoungDyadicRatio_pos.le
        _ = 1 := by field_simp [ne_of_gt hughesYoungDyadicRatio_pos]
    rw [hyStep]
    ring

/-- Dilation of a complex Bochner integral above an arbitrary positive
scale, with the Jacobian placed on the source side. -/
theorem integral_Ioi_mul_eq_mul_integral_dilate
    (g : ℝ → ℂ) (delta : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ y in Set.Ioi (r * delta), g y) =
      (r : ℂ) * ∫ x in Set.Ioi delta, g (r * x) := by
  have hs := MeasureTheory.integral_comp_mul_left_Ioi g delta hr
  rw [Complex.real_smul] at hs
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcast : (((r⁻¹ : ℝ) : ℂ)) = (r : ℂ)⁻¹ := by
    push_cast
    rfl
  rw [hcast] at hs
  calc
    (∫ y in Set.Ioi (r * delta), g y) =
        (r : ℂ) * ((r : ℂ)⁻¹ *
          ∫ y in Set.Ioi (r * delta), g y) := by field_simp
    _ = (r : ℂ) * ∫ x in Set.Ioi delta, g (r * x) := by rw [hs]

/-- The literal complex active-complement central integral is exactly the
positive dilated physical integral used by the four-edge Tonelli theorem.
The lower endpoint is derived from the actual dyadic multiplier. -/
theorem dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    (T t : ℝ) (w z : ℂ) (h k a b qx qy R K : ℕ)
    {r : ℝ} (hr : 0 < r) :
    dfiEquation27CentralIntegral a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex
            T t w h k a b R K X Y) r =
      (r : ℂ) * ∫ x : ℝ in Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r),
        dfiEquation27C a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex
              T t w h k a b R K X Y)
          (r * x + r) (r * x) := by
  let L : ℝ := 1 / hughesYoungDyadicRatio
  let delta : ℝ := L / r
  let F : ℝ → ℝ → ℂ := fun X Y =>
    z *
      hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K X Y
  let g : ℝ → ℂ := fun y => dfiEquation27C a b qx qy F (y + r) y
  have hL : 0 < L := by
    dsimp only [L]
    exact one_div_pos.mpr hughesYoungDyadicRatio_pos
  have hsourceZero (y : ℝ) (hy : y ≤ L) : F (y + r) y = 0 := by
    by_cases hy0 : 0 < y
    · have hyr0 : 0 ≤ y + r := (add_pos hy0 hr).le
      have hmult :
          hughesYoungNonLowerActiveComplementMultiplier
            a b R K (y + r) y = 0 := by
        by_contra hne
        have hcoords :=
          one_div_dyadicRatio_lt_coordinates_of_nonLowerMultiplier_ne_zero
            (a := a) (b := b) (R := R) (K := K) hyr0 hy0.le hne
        exact (not_lt_of_ge hy) hcoords.2
      dsimp only [F]
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex,
        if_pos ⟨add_pos hy0 hr, hy0⟩, hmult, Complex.ofReal_zero]
      ring
    · have hyle : y ≤ 0 := le_of_not_gt hy0
      dsimp only [F]
      rw [hughesYoungNonLowerActiveComplementMellinWeightComplex]
      simp [hyle]
  have hcentral :
      dfiEquation27CentralIntegral a b qx qy F r =
        ∫ y in Set.Ioi (0 : ℝ), g y := by
    rw [dfiEquation27CentralIntegral_eq_Ioi_shift]
    intro y hy
    exact hsourceZero y (hy.trans hL.le)
  have hrestrict :
      (∫ y in Set.Ioi (0 : ℝ), g y) = ∫ y in Set.Ioi L, g y := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · intro y hy
      exact hL.trans hy
    · intro y hy
      dsimp only [g]
      unfold dfiEquation27C
      rw [hsourceZero y (le_of_not_gt hy.2)]
      simp
  have hrdelta : r * delta = L := by
    dsimp only [delta]
    field_simp [hr.ne']
  have hdilate := integral_Ioi_mul_eq_mul_integral_dilate g delta hr
  rw [hrdelta] at hdilate
  change dfiEquation27CentralIntegral a b qx qy F r = _
  rw [hcentral, hrestrict, hdilate]

/-- The scalar-parametric exact DFI dilation specialized to the literal
Hughes--Young height cutoff. -/
theorem dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_eq_dilated
    (T t : ℝ) (w : ℂ) (h k a b qx qy R K : ℕ)
    {r : ℝ} (hr : 0 < r) :
    dfiEquation27CentralIntegral a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex
            T t w h k a b R K X Y) r =
      (r : ℂ) * ∫ x : ℝ in Set.Ioi
          ((1 / hughesYoungDyadicRatio) / r),
        dfiEquation27C a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex
              T t w h k a b R K X Y)
          (r * x + r) (r * x) := by
  exact dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    T t w (hughesYoungHeightWeight T t : ℂ) h k a b qx qy R K hr

/-- Exact four-edge contour identity for the literal DFI equation-(27)
central integral of the height-weighted active-complement source. -/
theorem dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
              h k a b R K X Y) r) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + (H : ℂ) * I)
              h k a b R K X Y) r) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => z *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) = 0 := by
  have hrect :=
    integral_dfiEquation27C_scalar_mul_nonLowerActiveComplement_dilated_boundaryRect_zero
      hc₀ hc hc₁ z t hH h k a b qx qy R K hr (T := T)
  have hcentral (w : ℂ) :=
    dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
      T t w z h k a b qx qy R K hr
  simp only [smul_eq_mul]
  simp_rw [hcentral, intervalIntegral.integral_const_mul]
  linear_combination (r : ℂ) * hrect

/-- The scalar-parametric central-series-integral rectangle identity specialized
to the literal Hughes--Young height cutoff. -/
theorem dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
              h k a b R K X Y) r) -
      (∫ s : ℝ in c₀..c₁,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((s : ℂ) + (H : ℂ) * I)
              h k a b R K X Y) r) +
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₁ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) -
      I • (∫ u : ℝ in -H..H,
        dfiEquation27CentralIntegral a b qx qy
          (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungNonLowerActiveComplementMellinWeightComplex T t
              ((c₀ : ℂ) + (u : ℂ) * I)
              h k a b R K X Y) r) = 0 := by
  exact dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
    hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) t hH
      h k a b qx qy R K hr

/-- One positive-shift equation-(27) modulus summand of the literal complex
active-complement source. -/
noncomputable def hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
    (T t : ℝ) (w : ℂ) (h k a b R K r q : ℕ) : ℂ :=
  dfiEquation27CentralSummand a b r
    (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K X Y) q

set_option maxHeartbeats 1600000 in
/-- Uniform inverse-square/log-square domination of every positive modulus
summand on a horizontal Mellin edge.  This is the Weierstrass majorant needed
to pass the Ramanujan series through the contour integral. -/
theorem exists_uniform_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ ≤ 1)
    (t H : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_nonLowerActiveComplement_horizontal_dilate_le_majorant
      hc₀ hc₁ t H a b R K hrR
        (T := T) (h := h) (k := k)
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c₀⁻¹ ^ 3)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q c hcMem
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S) := by
      exact integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc₀
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x) :=
      hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        exact hsource qx qy c hcMem x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD.le
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant
              c₀ delta S x := hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc₀]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (H : ℂ) * I) h k a b qx qy R K hrR
    unfold hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * Ddelta * S ^ 2 +
              9 * S ^ 2 * c₀⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ring

/-- Every individual positive-shift modulus summand has zero integral around
the same Mellin rectangle. -/
theorem hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b R K : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r q) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r q) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) = 0 := by
  have hcentral :=
    dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_boundaryRect_zero
      hc₀ hc hc₁ t hH h k a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        R K (show (0 : ℝ) < r by exact_mod_cast hr) (T := T)
  let z : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  simp only [smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  change z * _ - z * _ + I * (z * _) - I * (z * _) = 0
  linear_combination z * hcentral

/-- Horizontal-edge interval integrability for one positive-shift modulus
summand, obtained from the joint physical/Mellin Tonelli theorem. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q)
      volume c₀ c₁ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint := integrable_nonLowerActiveComplement_horizontal_dilate_joint
    hc₀ hc₁ t H a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let coeff : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul coeff
  have hinterval : IntervalIntegrable
      (fun s : ℝ => coeff * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume c₀ c₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    exact hscaled
  convert hinterval using 1
  funext s
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_eq_dilated
    T t ((s : ℂ) + (H : ℂ) * I) h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [coeff]
  push_cast
  ring

set_option maxHeartbeats 1200000 in
/-- The horizontal-edge `L¹` norms of the positive Ramanujan summands are
summable, uniformly on every small-line rectangle. -/
theorem summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁,
        ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le
      hc₀ (hc₁.trans (by norm_num)) t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (c₁ - c₀) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((c₁ - c₀) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun s =>
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
    have hfInterval :=
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc (hc₁.trans (by norm_num)) t H h k a b R K hr q
        (T := T)
    have hf : Integrable f (volume.restrict (Set.Icc c₀ c₁)) := by
      change IntegrableOn f (Set.Icc c₀ c₁)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
      exact hfInterval
    have hM0 : 0 ≤ M q := by
      dsimp only [M]
      positivity
    have hconst : Integrable (fun _s : ℝ => M q)
        (volume.restrict (Set.Icc c₀ c₁)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ s : ℝ in Set.Icc c₀ c₁, ‖f s‖) ≤
          ∫ _s : ℝ in Set.Icc c₀ c₁, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        simpa only [f, M, A] using hbound q s hs
      _ = (c₁ - c₀) * M q := by
        simp [MeasureTheory.integral_const, hc]

/-- Vertical-edge interval integrability for one positive-shift modulus
summand. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q)
      volume (-H) H := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint := integrable_nonLowerActiveComplement_vertical_dilate_joint
    hc hc1 t H a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let z : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul z
  have hinterval : IntervalIntegrable
      (fun u : ℝ => z * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume (-H) H := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -H ≤ H)]
    exact hscaled
  convert hinterval using 1
  funext u
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_eq_dilated
    T t ((c : ℂ) + (u : ℂ) * I) h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [z]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
/-- Uniform inverse-square/log-square domination of every positive modulus
summand on a vertical Mellin edge. -/
theorem exists_uniform_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical_le
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (u : ℝ), u ∈ Set.Icc (-H) H →
      ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_nonLowerActiveComplement_vertical_dilate_le_majorant
      hc hc4 t H a b R K hrR (T := T) (h := h) (k := k)
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c⁻¹ ^ 3)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q u hu
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x) :=
      hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D *
          hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        exact hsource qx qy u hu x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD.le
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant
              c delta S x := hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_heightWeight_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (u : ℂ) * I) h k a b qx qy R K hrR
    unfold hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * Ddelta * S ^ 2 +
              9 * S ^ 2 * c⁻¹ ^ 3))) := by gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * Ddelta + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ring

set_option maxHeartbeats 1200000 in
/-- The vertical-edge `L¹` norms of the positive Ramanujan summands are
summable. -/
theorem summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H,
        ‖hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical_le
      hc hc4 t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (H - (-H)) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((H - (-H)) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun u =>
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
    have horder : -H ≤ H := by linarith
    have hfInterval :=
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc (hc4.trans (by norm_num)) t hH h k a b R K hr q (T := T)
    have hf : Integrable f (volume.restrict (Set.Icc (-H) H)) := by
      change IntegrableOn f (Set.Icc (-H) H)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
      exact hfInterval
    have hM0 : 0 ≤ M q := by dsimp only [M]; positivity
    have hconst : Integrable (fun _u : ℝ => M q)
        (volume.restrict (Set.Icc (-H) H)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ u : ℝ in Set.Icc (-H) H, ‖f u‖) ≤
          ∫ _u : ℝ in Set.Icc (-H) H, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        simpa only [f, M, A] using hbound q u hu
      _ = (H - (-H)) * M q := by
        simp [MeasureTheory.integral_const, hH]

/-- The complete positive-shift Ramanujan series of the literal complex
active-complement source. -/
noncomputable def hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
    (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) : ℂ :=
  ∑' q : ℕ,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t w h k a b R K r q

/-- The named positive source series is definitionally the literal DFI
equation-(27) central series with the height-weighted complex Mellin weight. -/
theorem hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_eq_dfiEquation27CentralSeries
    (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) :
    hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t w h k a b R K r =
      dfiEquation27CentralSeries a b r
        (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementMellinWeightComplex
            T t w h k a b R K X Y) := by
  rfl

/-- Absolute summability of the horizontal interval integrals themselves. -/
theorem summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
      hc₀ hc hc₁ t H h k ha hb hr R K (T := T)
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- Absolute summability of the vertical interval integrals themselves. -/
theorem summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => ∫ u : ℝ in -H..H,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
        T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
      hc hc4 t hH h k ha hb hr R K (T := T)
  have horder : -H ≤ H := by linarith
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- The positive Ramanujan series may be passed through a horizontal edge. -/
theorem integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) =
      ∑' q : ℕ, ∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q := by
  let F : ℕ → ℝ → ℂ := fun q s =>
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc c₀ c₁)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc c₀ c₁)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    simpa only [F] using
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc (hc₁.trans (by norm_num)) t H h k a b R K hr q (T := T)
  have hNorm : Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁, ‖F q s‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ t H h k ha hb hr R K (T := T)
  have hswap : (∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s) =
      ∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s) =
        ∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s := hswap.symm
    _ = ∑' q : ℕ, ∫ s : ℝ in c₀..c₁, F q s := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]

/-- The positive Ramanujan series may be passed through a vertical edge. -/
theorem integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
    {T c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    (∫ u : ℝ in -H..H,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r) =
      ∑' q : ℕ, ∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q := by
  have horder : -H ≤ H := by linarith
  let F : ℕ → ℝ → ℂ := fun q u =>
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc (-H) H)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc (-H) H)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
    simpa only [F] using
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc (hc4.trans (by norm_num)) t hH h k a b R K hr q (T := T)
  have hNorm : Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H, ‖F q u‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc hc4 t hH h k ha hb hr R K (T := T)
  have hswap : (∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u) =
      ∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u) =
        ∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u := hswap.symm
    _ = ∑' q : ℕ, ∫ u : ℝ in -H..H, F q u := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]

/-- The first `Q` positive-shift Ramanujan summands of the literal complex
active-complement source. -/
noncomputable def hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex
    (T t : ℝ) (w : ℂ) (h k a b R K r Q : ℕ) : ℂ :=
  ∑ q ∈ Finset.range Q,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t w h k a b R K r q

/-- Every finite Ramanujan partial sum obeys the exact four-edge contour
identity. -/
theorem hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b R K : ℕ) {r : ℕ} (hr : 0 < r) (Q : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r Q) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex
          T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r Q) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex
          T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r Q) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralPartialSumComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r Q) = 0 := by
  let S := Finset.range Q
  let f (w : ℂ) (q : ℕ) :=
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t w h k a b R K r q
  have hBottom :
      (∫ s : ℝ in c₀..c₁, ∑ q ∈ S,
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) q) =
        ∑ q ∈ S, ∫ s : ℝ in c₀..c₁,
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) q := by
    rw [intervalIntegral.integral_finsetSum]
    intro q _hq
    exact
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ t (-H) h k a b R K hr q
  have hTop :
      (∫ s : ℝ in c₀..c₁, ∑ q ∈ S,
          f ((s : ℂ) + (H : ℂ) * I) q) =
        ∑ q ∈ S, ∫ s : ℝ in c₀..c₁,
          f ((s : ℂ) + (H : ℂ) * I) q := by
    rw [intervalIntegral.integral_finsetSum]
    intro q _hq
    exact
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ t H h k a b R K hr q
  have hRight :
      (∫ u : ℝ in -H..H, ∑ q ∈ S,
          f ((c₁ : ℂ) + (u : ℂ) * I) q) =
        ∑ q ∈ S, ∫ u : ℝ in -H..H,
          f ((c₁ : ℂ) + (u : ℂ) * I) q := by
    rw [intervalIntegral.integral_finsetSum]
    intro q _hq
    exact
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        (hc₀.trans_le hc) hc₁ t hH h k a b R K hr q
  have hLeft :
      (∫ u : ℝ in -H..H, ∑ q ∈ S,
          f ((c₀ : ℂ) + (u : ℂ) * I) q) =
        ∑ q ∈ S, ∫ u : ℝ in -H..H,
          f ((c₀ : ℂ) + (u : ℂ) * I) q := by
    rw [intervalIntegral.integral_finsetSum]
    intro q _hq
    exact
      intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc₀ (hc.trans hc₁) t hH h k a b R K hr q
  change
    (∫ s : ℝ in c₀..c₁, ∑ q ∈ S,
      f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) q) -
    (∫ s : ℝ in c₀..c₁, ∑ q ∈ S,
      f ((s : ℂ) + (H : ℂ) * I) q) +
    I • (∫ u : ℝ in -H..H, ∑ q ∈ S,
      f ((c₁ : ℂ) + (u : ℂ) * I) q) -
    I • (∫ u : ℝ in -H..H, ∑ q ∈ S,
      f ((c₀ : ℂ) + (u : ℂ) * I) q) = 0
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  calc
    _ = ∑ q ∈ S,
        ((∫ s : ℝ in c₀..c₁,
            f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) q) -
          (∫ s : ℝ in c₀..c₁,
            f ((s : ℂ) + (H : ℂ) * I) q) +
          I * (∫ u : ℝ in -H..H,
            f ((c₁ : ℂ) + (u : ℂ) * I) q) -
          I * (∫ u : ℝ in -H..H,
            f ((c₀ : ℂ) + (u : ℂ) * I) q)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro q _hq
      exact
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero
          hc₀ hc hc₁ t hH h k a b R K hr q

set_option maxHeartbeats 1200000 in
/-- The complete positive equation-(27) Ramanujan series obeys the exact
four-edge contour identity.  This upgrades the finite partial-sum identity
using the explicit inverse-square/log-square edge majorants. -/
theorem hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r) = 0 := by
  let Bottom : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..c₁,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r q
  let Top : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..c₁,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  let Right : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K r q
  let Left : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex
      T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K r q
  have hBottom :=
    integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
      hc₀ hc hc₁ t (-H) h k ha hb hr R K (T := T)
  have hTop :=
    integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
      hc₀ hc hc₁ t H h k ha hb hr R K (T := T)
  have hRight :=
    integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
      (hc₀.trans_le hc) hc₁ t hH h k ha hb hr R K (T := T)
  have hLeft :=
    integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
      hc₀ (hc.trans hc₁) t hH h k ha hb hr R K (T := T)
  have hsBottom : Summable Bottom := by
    simpa only [Bottom] using
      summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ t (-H) h k ha hb hr R K (T := T)
  have hsTop : Summable Top := by
    simpa only [Top] using
      summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ t H h k ha hb hr R K (T := T)
  have hsRight : Summable Right := by
    simpa only [Right] using
      summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        (hc₀.trans_le hc) hc₁ t hH h k ha hb hr R K (T := T)
  have hsLeft : Summable Left := by
    simpa only [Left] using
      summable_intervalIntegral_hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc₀ (hc.trans hc₁) t hH h k ha hb hr R K (T := T)
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  change (∑' q : ℕ, Bottom q) - (∑' q : ℕ, Top q) +
      I * (∑' q : ℕ, Right q) - I * (∑' q : ℕ, Left q) = 0
  calc
    _ = (∑' q : ℕ, (Bottom q - Top q)) +
        (∑' q : ℕ, (I * Right q - I * Left q)) := by
      rw [hsBottom.tsum_sub hsTop,
        (hsRight.mul_left I).tsum_sub (hsLeft.mul_left I),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = ∑' q : ℕ,
        ((Bottom q - Top q) + (I * Right q - I * Left q)) := by
      rw [← (hsBottom.sub hsTop).tsum_add
        ((hsRight.mul_left I).sub (hsLeft.mul_left I))]
    _ = ∑' _q : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro q
      have hq :=
        hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero
          hc₀ hc (hc₁.trans (by norm_num)) t hH h k a b R K hr q
          (T := T)
      dsimp only [Bottom, Top, Right, Left]
      linear_combination hq
    _ = 0 := tsum_zero

/-- Exact coordinate symmetry of the continuous active complement. -/
theorem hughesYoungNonLowerActiveComplementMultiplier_swap
    (a b R K : ℕ) (x y : ℝ) :
    hughesYoungNonLowerActiveComplementMultiplier b a R K y x =
      hughesYoungNonLowerActiveComplementMultiplier a b R K x y := by
  classical
  have hactive :
      hughesYoungActiveContinuousDyadicWeight b a R K y x =
        hughesYoungActiveContinuousDyadicWeight a b R K x y := by
    unfold hughesYoungActiveContinuousDyadicWeight
    apply Finset.sum_bij (fun ij _hij => (ij.2, ij.1))
    · intro ij hij
      unfold hughesYoungActiveDyadicBoxes at hij ⊢
      rw [Finset.mem_filter] at hij ⊢
      rcases hij with ⟨hijRange, hijProd⟩
      have hijRange' := Finset.mem_product.mp hijRange
      exact ⟨Finset.mem_product.mpr ⟨hijRange'.2, hijRange'.1⟩, by
        simpa [Nat.mul_comm, mul_comm] using hijProd⟩
    · intro i hi j hj hs
      apply Prod.ext
      · exact congrArg Prod.snd hs
      · exact congrArg Prod.fst hs
    · intro ij hij
      refine ⟨(ij.2, ij.1), ?_, by simp⟩
      unfold hughesYoungActiveDyadicBoxes at hij ⊢
      rw [Finset.mem_filter] at hij ⊢
      rcases hij with ⟨hijRange, hijProd⟩
      have hijRange' := Finset.mem_product.mp hijRange
      exact ⟨Finset.mem_product.mpr ⟨hijRange'.2, hijRange'.1⟩, by
        simpa [Nat.mul_comm, mul_comm] using hijProd⟩
    · intro ij hij
      ring
  unfold hughesYoungNonLowerActiveComplementMultiplier
  rw [hactive]
  ring

/-- Exchanging the two mollifier indices and the two critical-line points
leaves the reduced complex Mellin scalar unchanged. -/
theorem hughesYoungReducedMellinScaleConstantComplex_swap
    (T t : ℝ) (w : ℂ) (h k : ℕ) :
    hughesYoungReducedMellinScaleConstantComplex T (-t) w k h =
      hughesYoungReducedMellinScaleConstantComplex T t w h k := by
  unfold hughesYoungReducedMellinScaleConstantComplex
  rw [hughesYoungReducedLeft_swap h k,
    hughesYoungReducedRight_swap h k]
  rw [← hughesYoungRightContourWeightComplex_neg t w]
  simp only [neg_neg]
  ring

/-- Exact coordinate symmetry of the genuine complex non-lower source
weight.  This is the negative-shift bridge required by `dfiSignedCentralSeries`;
no absolute values or separately supplied symmetry certificate is used. -/
theorem dfiSwapWeight_hughesYoungNonLowerActiveComplementMellinWeightComplex
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) :
    dfiSwapWeight
        (hughesYoungNonLowerActiveComplementMellinWeightComplex
          T t w h k a b R K) =
      hughesYoungNonLowerActiveComplementMellinWeightComplex
        T (-t) w k h b a R K := by
  funext x y
  unfold dfiSwapWeight
    hughesYoungNonLowerActiveComplementMellinWeightComplex
  by_cases hx : 0 < x <;> by_cases hy : 0 < y
  · simp only [hx, hy, and_self, if_true]
    rw [hughesYoungReducedMellinScaleConstantComplex_swap,
      hughesYoungNonLowerActiveComplementMultiplier_swap]
    simp only [neg_neg]
    ring
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

/-- Exact DFI dilation of the scale-free non-lower complex kernel.  This
identity keeps the product-complement multiplier outside the affine beta
kernel and is valid on every positive contour line. -/
theorem dfiEquation27C_nonLowerActiveComplementMellinShapeComplex_dilate_eq
    (t c u : ℝ) (a b qx qy R K : ℕ)
    {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    dfiEquation27C a b qx qy
        (hughesYoungNonLowerActiveComplementMellinShapeComplex
          t ((c : ℂ) + (u : ℂ) * I) a b R K)
        (r * x + r) (r * x) =
      (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (r * x + r) (r * x) : ℂ) *
        (r : ℂ) ^ (-(afeCriticalPoint t +
          ((c : ℂ) + (u : ℂ) * I))) *
        (r : ℂ) ^ (-(afeCriticalPoint (-t) +
          ((c : ℂ) + (u : ℂ) * I))) *
        hughesYoungCriticalAffineBetaIntegrand t u c x
          ((Real.log r : ℂ) + dfiEquation27LogConstant b qy)
          ((Real.log r : ℂ) + dfiEquation27LogConstant a qx) := by
  have hOne : 0 < 1 + x := by linarith
  have hrx : 0 < r * x := mul_pos hr hx
  have hrOne : 0 < r * (1 + x) := mul_pos hr hOne
  have hsum : r * x + r = r * (1 + x) := by ring
  rw [hsum]
  unfold dfiEquation27C
    hughesYoungNonLowerActiveComplementMellinShapeComplex
  rw [if_pos ⟨hrOne, hrx⟩]
  rw [dfiEquation27LogFactor_eq_log_add_constant,
    dfiEquation27LogFactor_eq_log_add_constant]
  rw [Real.log_mul hr.ne' hOne.ne', Real.log_mul hr.ne' hx.ne']
  rw [hughesYoungLogPower_eq_cpow hrOne,
    hughesYoungLogPower_eq_cpow hrx]
  rw [show ((r * (1 + x) : ℝ) : ℂ) =
      (r : ℂ) * (1 + (x : ℂ)) by push_cast; rfl,
    show ((r * x : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by
      push_cast; rfl]
  have hone : 1 + (x : ℂ) = (((1 + x : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hone]
  rw [Complex.mul_cpow_ofReal_nonneg hr.le hOne.le,
    Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
  unfold hughesYoungCriticalAffineBetaIntegrand afeCriticalPoint
  dsimp only
  push_cast
  ring_nf

set_option maxHeartbeats 800000 in
/-- The non-lower multiplier makes the positive equation-(27) physical
slice absolutely integrable on the entire contour strip `0 < c ≤ 1`.
The proof uses the exact DFI dilation and the literal dyadic lower endpoint,
not an abstract support assumption. -/
theorem integrable_nonLowerMultiplier_mul_dfiEquation27C_pureReducedStaticWeight
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : ℝ =>
      (hughesYoungNonLowerActiveComplementMultiplier
          a b R K (y + r) y : ℂ) *
        dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y) := by
  let L : ℝ := 1 / hughesYoungDyadicRatio
  have hL : 0 < L := by
    dsimp only [L]
    exact one_div_pos.mpr hughesYoungDyadicRatio_pos
  let δ : ℝ := L / r
  have hδ : 0 < δ := div_pos hL hr
  let CX : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant b qy
  let COne : ℂ :=
    (Real.log r : ℂ) + dfiEquation27LogConstant a qx
  let C : ℂ :=
    hughesYoungPureReducedStaticScaleConstant T c u h k *
      (r : ℂ) ^
        (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) *
      (r : ℂ) ^
        (-((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)))
  let β : ℝ → ℂ := fun x =>
    hughesYoungCriticalAffineBetaIntegrand 0 u c x CX COne
  have hβ : IntegrableOn β (Set.Ioi δ) := by
    simpa only [β] using
      integrableOn_hughesYoungCriticalAffineBetaIntegrand_away_zero
        hc hc1 hδ CX COne
  have hscaled : IntegrableOn (fun x => C * β x) (Set.Ioi δ) :=
    hβ.const_mul C
  let m : ℝ → ℂ := fun x =>
    (hughesYoungNonLowerActiveComplementMultiplier
      a b R K (r * x + r) (r * x) : ℂ)
  have hmCont : Continuous m := by
    dsimp only [m]
    apply Complex.continuous_ofReal.comp
    unfold hughesYoungNonLowerActiveComplementMultiplier
      hughesYoungActiveContinuousDyadicWeight hughesYoungFullDyadicCutoff
    apply Continuous.sub
    · exact (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop))).mul
        (continuous_const.sub
          (contDiff_hughesYoungDyadicStep.continuous.comp (by fun_prop)))
    · apply continuous_finsetSum
      intro ij _hij
      exact ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.1)).continuous.comp (by fun_prop)).mul
        ((contDiff_hughesYoungDyadicCutoffAt
          (hughesYoungFullDyadicScale ij.2)).continuous.comp (by fun_prop))
  have hmBound : ∀ x ∈ Set.Ioi δ, ‖m x‖ ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := hδ.trans hx
    have hry : 0 ≤ r * x := (mul_pos hr hx0).le
    have hrxy : 0 ≤ r * x + r := (add_pos (mul_pos hr hx0) hr).le
    dsimp only [m]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungNonLowerActiveComplementMultiplier_nonneg
        a b R K hrxy hry)]
    exact hughesYoungNonLowerActiveComplementMultiplier_le_one_source
      a b R K hrxy hry
  have hcomp : IntegrableOn (fun x =>
      m x * dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k)
        (r * x + r) (r * x)) (Set.Ioi δ) := by
    have hmul : IntegrableOn (fun x => m x * (C * β x)) (Set.Ioi δ) := by
      exact hscaled.bdd_mul hmCont.aestronglyMeasurable
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hmBound x hx)
    refine hmul.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hδ.trans hx
    change m x * (C * β x) = m x *
      dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k)
        (r * x + r) (r * x)
    congr 1
    exact (dfiEquation27C_pureReducedStaticWeight_dilate_eq_criticalBeta
      T c u hh hk a b qx qy hr hx0).symm
  let f : ℝ → ℂ := fun y =>
    (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (y + r) y : ℂ) *
      dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) (y + r) y
  have htail : IntegrableOn f (Set.Ioi L) := by
    have hiff := MeasureTheory.integrableOn_Ioi_comp_mul_left_iff f δ hr
    have hcomp' : IntegrableOn (fun x => f (r * x)) (Set.Ioi δ) := by
      simpa only [f, m, mul_add] using hcomp
    have hrδ : r * δ = L := by
      dsimp only [δ]
      field_simp [hr.ne']
    simpa only [hrδ] using hiff.mp hcomp'
  have hzero : ∀ y ∈ Set.univ \ Set.Ioi L, f y = 0 := by
    intro y hy
    have hyL : y ≤ L := le_of_not_gt hy.2
    by_cases hy0 : 0 < y
    · have hyr0 : 0 ≤ y + r := (add_pos hy0 hr).le
      have hymult :
          hughesYoungNonLowerActiveComplementMultiplier
            a b R K (y + r) y = 0 := by
        by_contra hne
        have hcoords :=
          one_div_dyadicRatio_lt_coordinates_of_nonLowerMultiplier_ne_zero
            (a := a) (b := b) (R := R) (K := K) hyr0 hy0.le hne
        exact (not_lt_of_ge hyL) hcoords.2
      dsimp only [f]
      rw [hymult, Complex.ofReal_zero, zero_mul]
    · have hyle : y ≤ 0 := le_of_not_gt hy0
      dsimp only [f]
      unfold dfiEquation27C hughesYoungPureReducedStaticWeight
      simp [hyle]
  have hfull : IntegrableOn f Set.univ :=
    htail.of_forall_diff_eq_zero MeasurableSet.univ hzero
  simpa only [f, IntegrableOn, Measure.restrict_univ] using hfull

/-- Coordinate-swapped counterpart of the non-lower physical
integrability theorem. -/
theorem integrable_swappedNonLowerMultiplier_mul_dfiEquation27C_pureReducedStaticWeight
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (T u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : ℝ =>
      (hughesYoungNonLowerActiveComplementMultiplier
          a b R K y (y + r) : ℂ) *
        dfiEquation27C b a qy qx
          (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
          (y + r) y) := by
  have hmain :=
    integrable_nonLowerMultiplier_mul_dfiEquation27C_pureReducedStaticWeight
      hc hc1 T u hk hh b a qy qx R K hr
  rw [dfiSwapWeight_hughesYoungPureReducedStaticWeight T c u h k]
  convert hmain using 1
  ext y
  rw [hughesYoungNonLowerActiveComplementMultiplier_swap a b R K y (y + r)]

set_option maxHeartbeats 800000 in
/-- Absolute convergence of the literal height-weighted non-lower source
on every vertical line `0 < c ≤ 1`.  This is the physical-integral
Fubini input needed to move the actual DFI source to the right line. -/
theorem integrable_dfiEquation27C_heightWeight_mul_nonLowerComplement_rightStrip
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y)
      x (x - r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let A : ℝ → ℂ := fun x =>
    (hughesYoungNonLowerActiveComplementMultiplier
        a b R K x (x - r) : ℂ) *
      dfiEquation27C a b qx qy
        (hughesYoungPureReducedStaticWeight T c u h k) x (x - r)
  have hbase0 :=
    integrable_nonLowerMultiplier_mul_dfiEquation27C_pureReducedStaticWeight
      hc hc1 T u hh hk a b qx qy R K hrR
  have hbase : Integrable A := by
    convert hbase0.comp_add_right (-(r : ℝ)) using 1
    ext x
    dsimp only [A]
    congr 2 <;> ring_nf
  have hmajor : Integrable (fun x : ℝ =>
      (hughesYoungHeightFourierInput T c u t : ℂ) * A x) :=
    hbase.const_mul _
  let phase : ℝ → ℂ := fun x =>
    Complex.exp ((((t * Real.log ((x - r) / x) : ℝ) : ℂ)) * I)
  have heq : (fun x : ℝ => dfiEquation27C a b qx qy
      (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y)
      x (x - r)) = fun x => phase x *
        ((hughesYoungHeightFourierInput T c u t : ℂ) * A x) := by
    funext x
    by_cases hx : 0 < x
    · by_cases hy : 0 < x - r
      · unfold dfiEquation27C
        change dfiEquation27LogFactor a qx x *
            dfiEquation27LogFactor b qy (x - r) *
              ((hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementReducedMellinWeight
                  T t c u h k a b R K x (x - r)) = _
        rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
          T t c u hh hk a b R K]
        rw [show (hughesYoungHeightWeight T t : ℂ) *
            ((hughesYoungNonLowerActiveComplementMultiplier
                a b R K x (x - r) : ℂ) *
              hughesYoungPureReducedMellinWeight T t c u h k x (x - r)) =
            (hughesYoungNonLowerActiveComplementMultiplier
                a b R K x (x - r) : ℂ) *
              ((hughesYoungHeightWeight T t : ℂ) *
                hughesYoungPureReducedMellinWeight
                  T t c u h k x (x - r)) by ring]
        rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
          T t c u hh hk hx hy]
        dsimp only [phase, A]
        unfold dfiEquation27C
        ring
      · have hy' : x - r ≤ 0 := le_of_not_gt hy
        unfold dfiEquation27C
        change dfiEquation27LogFactor a qx x *
            dfiEquation27LogFactor b qy (x - r) *
              ((hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementReducedMellinWeight
                  T t c u h k a b R K x (x - r)) = _
        rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
          T t c u hh hk a b R K]
        rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_right
          T t c u h k hy']
        dsimp only [phase, A]
        unfold dfiEquation27C hughesYoungPureReducedStaticWeight
        simp [hy]
    · have hx' : x ≤ 0 := le_of_not_gt hx
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx x *
          dfiEquation27LogFactor b qy (x - r) *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementReducedMellinWeight
                T t c u h k a b R K x (x - r)) = _
      rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
        T t c u hh hk a b R K]
      rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
        T t c u h k hx']
      dsimp only [phase, A]
      unfold dfiEquation27C hughesYoungPureReducedStaticWeight
      simp [hx]
  have hphaseMeas : AEStronglyMeasurable phase := by
    dsimp only [phase]
    have hratio : Measurable (fun x : ℝ => (x - (r : ℝ)) / x) :=
      (measurable_id.sub measurable_const).div measurable_id
    have hlog : Measurable (fun x : ℝ =>
        Real.log ((x - (r : ℝ)) / x)) :=
      Real.measurable_log.comp hratio
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp
        (measurable_const.mul hlog)).mul_const I)).aestronglyMeasurable
  have hphaseBound : ∀ x : ℝ, ‖phase x‖ ≤ 1 := by
    intro x
    dsimp only [phase]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [heq]
  exact hmajor.bdd_mul hphaseMeas
    (Filter.Eventually.of_forall hphaseBound)

set_option maxHeartbeats 800000 in
/-- Coordinate-swapped absolute convergence of the literal non-lower
source throughout the same right strip. -/
theorem integrable_dfiEquation27C_heightWeight_mul_swappedNonLowerComplement_rightStrip
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t u : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b qx qy R K : ℕ) {r : ℕ} (hr : 0 < r) :
    Integrable (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y))
      x (x - r)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let A : ℝ → ℂ := fun x =>
    (hughesYoungNonLowerActiveComplementMultiplier
        a b R K (x - r) x : ℂ) *
      dfiEquation27C b a qy qx
        (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
        x (x - r)
  have hbase0 :=
    integrable_swappedNonLowerMultiplier_mul_dfiEquation27C_pureReducedStaticWeight
      hc hc1 T u hh hk a b qx qy R K hrR
  have hbase : Integrable A := by
    convert hbase0.comp_add_right (-(r : ℝ)) using 1
    ext x
    dsimp only [A]
    congr 2 <;> ring_nf
  have hmajor : Integrable (fun x : ℝ =>
      (hughesYoungHeightFourierInput T c u t : ℂ) * A x) :=
    hbase.const_mul _
  let phase : ℝ → ℂ := fun x =>
    Complex.exp ((((t * Real.log (x / (x - r)) : ℝ) : ℂ)) * I)
  have heq : (fun x : ℝ => dfiEquation27C b a qy qx
      (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K X Y))
      x (x - r)) = fun x => phase x *
        ((hughesYoungHeightFourierInput T c u t : ℂ) * A x) := by
    funext x
    by_cases hy : 0 < x - r
    · have hx : 0 < x := by
        have hr0 : (0 : ℝ) ≤ r := by positivity
        linarith
      rw [dfiEquation27C_swap]
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx (x - r) *
          dfiEquation27LogFactor b qy x *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementReducedMellinWeight
                T t c u h k a b R K (x - r) x) = _
      rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
        T t c u hh hk a b R K]
      rw [show (hughesYoungHeightWeight T t : ℂ) *
          ((hughesYoungNonLowerActiveComplementMultiplier
              a b R K (x - r) x : ℂ) *
            hughesYoungPureReducedMellinWeight T t c u h k (x - r) x) =
          (hughesYoungNonLowerActiveComplementMultiplier
              a b R K (x - r) x : ℂ) *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungPureReducedMellinWeight
                T t c u h k (x - r) x) by ring]
      rw [heightWeight_mul_hughesYoungPureReducedMellinWeight_eq_static_mul_phase
        T t c u hh hk hy hx]
      dsimp only [phase, A]
      unfold dfiEquation27C dfiSwapWeight
      ring
    · have hy' : x - r ≤ 0 := le_of_not_gt hy
      rw [dfiEquation27C_swap]
      unfold dfiEquation27C
      change dfiEquation27LogFactor a qx (x - r) *
          dfiEquation27LogFactor b qy x *
            ((hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementReducedMellinWeight
                T t c u h k a b R K (x - r) x) = _
      rw [hughesYoungNonLowerActiveComplementReducedMellinWeight_eq_multiplier_mul_pure
        T t c u hh hk a b R K]
      rw [hughesYoungPureReducedMellinWeight_eq_zero_of_nonpos_left
        T t c u h k hy']
      dsimp only [phase, A]
      unfold dfiEquation27C dfiSwapWeight hughesYoungPureReducedStaticWeight
      simp [hy]
  have hphaseMeas : AEStronglyMeasurable phase := by
    dsimp only [phase]
    have hratio : Measurable (fun x : ℝ => x / (x - (r : ℝ))) :=
      measurable_id.div (measurable_id.sub measurable_const)
    have hlog : Measurable (fun x : ℝ =>
        Real.log (x / (x - (r : ℝ)))) :=
      Real.measurable_log.comp hratio
    exact (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp
        (measurable_const.mul hlog)).mul_const I)).aestronglyMeasurable
  have hphaseBound : ∀ x : ℝ, ‖phase x‖ ≤ 1 := by
    intro x
    dsimp only [phase]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [heq]
  exact hmajor.bdd_mul hphaseMeas
    (Filter.Eventually.of_forall hphaseBound)

/-- One signed DFI equation-(27) shift of the holomorphic complement
family. -/
noncomputable def hughesYoungNonLowerActiveComplementSignedCentralComplex
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) (r : ℤ) : ℂ :=
  dfiSignedCentralSeries a b r
    (hughesYoungNonLowerActiveComplementMellinWeightComplex
      T t w h k a b R K)

/-- The complete finite signed-shift family carried by the non-lower
active complement. -/
noncomputable def hughesYoungNonLowerActiveComplementSignedSourceComplex
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      hughesYoungNonLowerActiveComplementSignedCentralComplex
        T t w h k a b R K r

/-- Vertical specialization of the genuine finite signed source. -/
theorem hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) :
    hughesYoungNonLowerActiveComplementSignedSourceComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k a b R K =
      let B := hughesYoungFullDyadicBound (K + 1)
      ∑ r ∈ hughesYoungShiftInterval a b B B,
        if r = 0 then 0 else
          dfiSignedCentralSeries a b r
            (hughesYoungNonLowerActiveComplementReducedMellinWeight
              T t c u h k a b R K) := by
  classical
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
    hughesYoungNonLowerActiveComplementSignedCentralComplex
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hr0 : r = 0
  · simp [hr0]
  · simp only [hr0, if_false]
    rw [hughesYoungNonLowerActiveComplementMellinWeightComplex_vertical
      T t c u hh hk a b R K]

/-- The literal small-line signed central source after the lower endpoint
has been removed. -/
noncomputable def hughesYoungNonLowerActiveComplementSignedCentralAtHeight
    (T t c u : ℝ) (h k a b R K : ℕ) : ℂ :=
  let B := hughesYoungFullDyadicBound (K + 1)
  ∑ r ∈ hughesYoungShiftInterval a b B B,
    if r = 0 then 0 else
      dfiSignedCentralSeries a b r
        (hughesYoungNonLowerActiveComplementReducedMellinWeight
          T t c u h k a b R K)

/-- The complex source has exactly the literal small-line value. -/
theorem hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical_eq
    (T t c u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b R K : ℕ) :
    hughesYoungNonLowerActiveComplementSignedSourceComplex T t
        ((c : ℂ) + (u : ℂ) * I) h k a b R K =
      hughesYoungNonLowerActiveComplementSignedCentralAtHeight
        T t c u h k a b R K := by
  exact hughesYoungNonLowerActiveComplementSignedSourceComplex_vertical
    T t c u hh hk a b R K

/-- The genuine globally integrated non-lower source.  Unlike the earlier
residual definition, this expression visibly consumes the DFI
equation-(27) series with the product-complement weight. -/
noncomputable def hughesYoungNonLowerActiveComplementIntegratedCentralSource
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K

set_option maxHeartbeats 800000 in
/-- Exact finite signed-window source identity at fixed physical height and
Mellin ordinate. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (t u : ℝ) {h k a b : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralAtHeight
          T t c u h k a b R K =
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFinitePureSignedCentralAtHeight T t c u h k a b K -
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteLowerBoundarySignedCentralAtHeight
            T t c u h k a b K -
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t c u h k a b R K := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  have hterm (r : ℤ) :
      (hughesYoungHeightWeight T t : ℂ) *
          (if r = 0 then 0 else
            dfiSignedCentralSeries a b r
              (hughesYoungNonLowerActiveComplementReducedMellinWeight
                T t c u h k a b R K)) =
        (hughesYoungHeightWeight T t : ℂ) *
            (if r = 0 then 0 else
              dfiSignedCentralSeries a b r
                (hughesYoungPureReducedMellinWeight T t c u h k)) -
          (hughesYoungHeightWeight T t : ℂ) *
            (if r = 0 then 0 else
              dfiSignedCentralSeries a b r
                (hughesYoungLowerBoundaryReducedMellinCorrection
                  T t c u h k)) -
          (hughesYoungHeightWeight T t : ℂ) *
            (if r = 0 then 0 else
              dfiSignedCentralSeries a b r
                (hughesYoungActiveReassembledReducedMellinWeight
                  T t c u h k a b R K)) := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp only [hr0, if_false]
      exact heightWeight_mul_dfiSignedCentralSeries_nonLower_eq
        hT hc hc4 t u hh hk ha hb r hr0 R K
  unfold hughesYoungNonLowerActiveComplementSignedCentralAtHeight
    hughesYoungFinitePureSignedCentralAtHeight
    hughesYoungFiniteLowerBoundarySignedCentralAtHeight
    hughesYoungActiveReassembledSignedCentralAtHeight
  dsimp only [B, S]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-! ## Joint integrability of the finite lower boundary

The fixed-ordinate endpoint calculation above must be integrated in the
opposite order from the definition of the native source.  The next lemmas
provide the genuine Tonelli/Fubini hypothesis.  In particular, this is not
obtained by exchanging two formal integrals: the compact physical-height
cutoff and the bounded Mellin segment are used explicitly.
-/

/-- The untransformed Hughes--Young height input is jointly continuous in
the physical height and Mellin ordinate. -/
theorem continuous_uncurry_hughesYoungHeightFourierInput
    (T : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungHeightFourierInput T c p.2 p.1) := by
  unfold hughesYoungHeightFourierInput
  have hcut : Continuous (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((contDiff_hughesYoungHeightWeight T).continuous.comp continuous_fst)
  have hright : Continuous (fun p : ℝ × ℝ =>
      hughesYoungRightContourWeight p.1 c p.2) :=
    continuous_uncurry_hughesYoungRightContourWeight hc
  exact hcut.mul hright

/-- The exact height input is integrable on the full physical-height line
times every bounded Mellin-ordinate segment. -/
theorem integrable_uncurry_hughesYoungHeightFourierInput
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun p : ℝ × ℝ =>
      hughesYoungHeightFourierInput T c p.2 p.1)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
  let f : ℝ × ℝ → ℂ := fun p =>
    hughesYoungHeightFourierInput T c p.2 p.1
  let C : Set (ℝ × ℝ) :=
    Set.Icc (T / 4) (4 * T) ×ˢ Set.Icc (-H) H
  have hsmall : IntegrableOn f C (volume.prod volume) :=
    (continuous_uncurry_hughesYoungHeightFourierInput T hc).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hbig : IntegrableOn f
      (Set.univ ×ˢ Set.uIoc (-H) H) (volume.prod volume) := by
    apply hsmall.of_forall_diff_eq_zero
      (MeasurableSet.univ.prod measurableSet_uIoc)
    intro p hp
    have ht : p.1 ∉ Set.Icc (T / 4) (4 * T) := by
      intro ht
      apply hp.2
      have hu : p.2 ∈ Set.Icc (-H) H := by
        have hu' := Set.uIoc_subset_uIcc hp.1.2
        simpa only [Set.uIcc_of_le (by linarith : -H ≤ H)] using hu'
      exact ⟨ht, hu⟩
    have hzero : hughesYoungHeightWeight T p.1 = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    dsimp only [f]
    simp [hughesYoungHeightFourierInput, hzero]
  rw [IntegrableOn, ← Measure.prod_restrict] at hbig
  simpa [f] using hbig

/-- One positive lower-boundary physical kernel is jointly measurable in
the physical height, Mellin ordinate, and DFI integration variable. -/
theorem stronglyMeasurable_hughesYoungLowerBoundaryCentralHeightIntegrand_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ =>
      hughesYoungLowerBoundaryCentralHeightIntegrand
        T c z.1.2 h k r a b qx qy z.2 z.1.1) := by
  rw [show (fun z : (ℝ × ℝ) × ℝ =>
      hughesYoungLowerBoundaryCentralHeightIntegrand
        T c z.1.2 h k r a b qx qy z.2 z.1.1) = fun z =>
      ((hughesYoungLowerBoundaryMultiplier (z.2 + r) z.2 : ℝ) : ℂ) *
        dfiEquation27C a b qx qy
          (hughesYoungPureReducedStaticWeight T c z.1.2 h k)
          (z.2 + r) z.2 *
        Complex.exp ((((z.1.1 * Real.log (z.2 / (z.2 + r)) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c z.1.2 z.1.1 by
    funext z
    exact hughesYoungLowerBoundaryCentralHeightIntegrand_eq
      T c z.1.2 hh hk hr a b qx qy z.2 z.1.1]
  unfold dfiEquation27C hughesYoungPureReducedStaticWeight
    hughesYoungHeightFourierInput
  simp only [mul_ite, ite_mul, mul_zero]
  apply StronglyMeasurable.ite
  · measurability
  · have hright : StronglyMeasurable (fun x : (ℝ × ℝ) × ℝ =>
        hughesYoungRightContourWeight x.1.1 c x.1.2) :=
      ((continuous_uncurry_hughesYoungRightContourWeight hc).comp
        (continuous_fst.comp continuous_fst |>.prodMk
          (continuous_snd.comp continuous_fst))).stronglyMeasurable
    have hheight : StronglyMeasurable (fun x : (ℝ × ℝ) × ℝ =>
        (hughesYoungHeightWeight T x.1.1 : ℂ)) :=
      (Complex.continuous_ofReal.comp
        ((contDiff_hughesYoungHeightWeight T).continuous.comp
          (continuous_fst.comp continuous_fst))).stronglyMeasurable
    apply StronglyMeasurable.mul
    · have hmult : StronglyMeasurable
          (fun x : (ℝ × ℝ) × ℝ =>
            (hughesYoungLowerBoundaryMultiplier (x.2 + r) x.2 : ℂ)) := by
        apply Continuous.stronglyMeasurable
        apply Complex.continuous_ofReal.comp
        unfold hughesYoungLowerBoundaryMultiplier
        have hs : Continuous hughesYoungDyadicStep :=
          contDiff_hughesYoungDyadicStep.continuous
        exact ((hs.comp (by fun_prop)).add (hs.comp (by fun_prop))).sub
          ((hs.comp (by fun_prop)).mul (hs.comp (by fun_prop)))
      rw [show (fun x : (ℝ × ℝ) × ℝ =>
          (hughesYoungLowerBoundaryMultiplier (x.2 + r) x.2 : ℂ) *
            (dfiEquation27LogFactor a qx (x.2 + r) *
              dfiEquation27LogFactor b qy x.2 *
              (hughesYoungLocalizedStaticScalar T h k *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  ((x.2 + r) / hughesYoungReducedLeft h k) *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  (x.2 / hughesYoungReducedRight h k))) *
              Complex.exp ((((x.1.1 * Real.log (x.2 / (x.2 + r)) : ℝ) : ℂ)) * I)) =
          (fun x => (hughesYoungLowerBoundaryMultiplier (x.2 + r) x.2 : ℂ)) *
          (fun x =>
            (dfiEquation27LogFactor a qx (x.2 + r) *
              dfiEquation27LogFactor b qy x.2 *
              (hughesYoungLocalizedStaticScalar T h k *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  ((x.2 + r) / hughesYoungReducedLeft h k) *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  (x.2 / hughesYoungReducedRight h k))) *
              Complex.exp ((((x.1.1 * Real.log (x.2 / (x.2 + r)) : ℝ) : ℂ)) * I)) by
            funext x
            simp only [Pi.mul_apply]
            ring]
      apply hmult.mul
      unfold hughesYoungLogPower dfiEquation27LogFactor
      measurability
    · exact hheight.mul hright
  · simpa using
      (stronglyMeasurable_const : StronglyMeasurable
        (fun _ : (ℝ × ℝ) × ℝ => (0 : ℂ)))

/-- One negative-shift lower-boundary physical kernel is jointly
measurable in all three integration variables. -/
theorem stronglyMeasurable_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (a b qx qy : ℕ) :
    StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ =>
      hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c z.1.2 h k r a b qx qy z.2 z.1.1) := by
  rw [show (fun z : (ℝ × ℝ) × ℝ =>
      hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
        T c z.1.2 h k r a b qx qy z.2 z.1.1) = fun z =>
      ((hughesYoungLowerBoundaryMultiplier z.2 (z.2 + r) : ℝ) : ℂ) *
        dfiEquation27C b a qy qx
          (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c z.1.2 h k))
          (z.2 + r) z.2 *
        Complex.exp ((((z.1.1 * Real.log ((z.2 + r) / z.2) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c z.1.2 z.1.1 by
    funext z
    exact hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_eq
      T c z.1.2 hh hk hr a b qx qy z.2 z.1.1]
  unfold dfiEquation27C dfiSwapWeight hughesYoungPureReducedStaticWeight
    hughesYoungHeightFourierInput
  simp only [mul_ite, ite_mul, mul_zero]
  apply StronglyMeasurable.ite
  · measurability
  · have hright : StronglyMeasurable (fun x : (ℝ × ℝ) × ℝ =>
        hughesYoungRightContourWeight x.1.1 c x.1.2) :=
      ((continuous_uncurry_hughesYoungRightContourWeight hc).comp
        (continuous_fst.comp continuous_fst |>.prodMk
          (continuous_snd.comp continuous_fst))).stronglyMeasurable
    have hheight : StronglyMeasurable (fun x : (ℝ × ℝ) × ℝ =>
        (hughesYoungHeightWeight T x.1.1 : ℂ)) :=
      (Complex.continuous_ofReal.comp
        ((contDiff_hughesYoungHeightWeight T).continuous.comp
          (continuous_fst.comp continuous_fst))).stronglyMeasurable
    apply StronglyMeasurable.mul
    · have hmult : StronglyMeasurable
          (fun x : (ℝ × ℝ) × ℝ =>
            (hughesYoungLowerBoundaryMultiplier x.2 (x.2 + r) : ℂ)) := by
        apply Continuous.stronglyMeasurable
        apply Complex.continuous_ofReal.comp
        unfold hughesYoungLowerBoundaryMultiplier
        have hs : Continuous hughesYoungDyadicStep :=
          contDiff_hughesYoungDyadicStep.continuous
        exact ((hs.comp (by fun_prop)).add (hs.comp (by fun_prop))).sub
          ((hs.comp (by fun_prop)).mul (hs.comp (by fun_prop)))
      rw [show (fun x : (ℝ × ℝ) × ℝ =>
          (hughesYoungLowerBoundaryMultiplier x.2 (x.2 + r) : ℂ) *
            (dfiEquation27LogFactor b qy (x.2 + r) *
              dfiEquation27LogFactor a qx x.2 *
              (hughesYoungLocalizedStaticScalar T h k *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  (x.2 / hughesYoungReducedLeft h k) *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  ((x.2 + r) / hughesYoungReducedRight h k))) *
              Complex.exp ((((x.1.1 * Real.log ((x.2 + r) / x.2) : ℝ) : ℂ)) * I)) =
          (fun x => (hughesYoungLowerBoundaryMultiplier x.2 (x.2 + r) : ℂ)) *
          (fun x =>
            (dfiEquation27LogFactor b qy (x.2 + r) *
              dfiEquation27LogFactor a qx x.2 *
              (hughesYoungLocalizedStaticScalar T h k *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  (x.2 / hughesYoungReducedLeft h k) *
                hughesYoungLogPower (1 / 2 + ((c : ℂ) + (x.1.2 : ℂ) * I))
                  ((x.2 + r) / hughesYoungReducedRight h k))) *
              Complex.exp ((((x.1.1 * Real.log ((x.2 + r) / x.2) : ℝ) : ℂ)) * I)) by
            funext x
            simp only [Pi.mul_apply]
            ring]
      apply hmult.mul
      unfold hughesYoungLogPower dfiEquation27LogFactor
      measurability
    · exact hheight.mul hright
  · simpa using
      (stronglyMeasurable_const : StronglyMeasurable
        (fun _ : (ℝ × ℝ) × ℝ => (0 : ℂ)))

/-- A positive-shift lower-boundary modulus term is jointly measurable in
the two outer integration variables. -/
theorem stronglyMeasurable_hughesYoungLowerBoundaryCentralSeriesHeightTerm_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T p.1 c p.2 h k a b r q) := by
  let J : (ℝ × ℝ) × ℝ → ℂ := fun z =>
    hughesYoungLowerBoundaryCentralHeightIntegrand
      T c z.1.2 h k (r : ℝ) a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        z.2 z.1.1
  have hJ : StronglyMeasurable J := by
    simpa only [J] using
      stronglyMeasurable_hughesYoungLowerBoundaryCentralHeightIntegrand_joint
        T hc hh hk (show (0 : ℝ) < r by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hI : StronglyMeasurable (fun p : ℝ × ℝ =>
      ∫ y in Set.Ioi (0 : ℝ), J (p, y)) :=
    hJ.integral_prod_right'
      (ν := volume.restrict (Set.Ioi (0 : ℝ)))
  let A : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have heq : (fun p : ℝ × ℝ =>
      hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T p.1 c p.2 h k a b r q) =
      fun p => A * ∫ y in Set.Ioi (0 : ℝ), J (p, y) := by
    funext p
    simpa only [A, J] using
      hughesYoungLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
        T p.1 c p.2 h k a b r q
  rw [heq]
  exact stronglyMeasurable_const.mul hI

/-- A negative-shift lower-boundary modulus term is jointly measurable in
the two outer integration variables. -/
theorem stronglyMeasurable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T p.1 c p.2 h k a b r q) := by
  let J : (ℝ × ℝ) × ℝ → ℂ := fun z =>
    hughesYoungSwappedLowerBoundaryCentralHeightIntegrand
      T c z.1.2 h k (r : ℝ) a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        z.2 z.1.1
  have hJ : StronglyMeasurable J := by
    simpa only [J] using
      stronglyMeasurable_hughesYoungSwappedLowerBoundaryCentralHeightIntegrand_joint
        T hc hh hk (show (0 : ℝ) < r by exact_mod_cast hr) a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
  have hI : StronglyMeasurable (fun p : ℝ × ℝ =>
      ∫ y in Set.Ioi (0 : ℝ), J (p, y)) :=
    hJ.integral_prod_right'
      (ν := volume.restrict (Set.Ioi (0 : ℝ)))
  let A : ℂ := (((b : ℂ) * a)⁻¹ *
    dfiEquation27ArithmeticCoefficient b a r q)
  have heq : (fun p : ℝ × ℝ =>
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T p.1 c p.2 h k a b r q) =
      fun p => A * ∫ y in Set.Ioi (0 : ℝ), J (p, y) := by
    funext p
    simpa only [A, J] using
      hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_eq_setIntegral
        T p.1 c p.2 h k a b r q
  rw [heq]
  exact stronglyMeasurable_const.mul hI

/-- The complete positive Ramanujan lower-boundary series is jointly
measurable in physical height and Mellin ordinate. -/
theorem aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c) {μ : Measure (ℝ × ℝ)}
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T p.1 c p.2 h k)) μ := by
  let F : ℕ → ℝ × ℝ → ℂ := fun q p =>
    hughesYoungLowerBoundaryCentralSeriesHeightTerm
      T p.1 c p.2 h k a b r q
  have hF : ∀ q, AEStronglyMeasurable (F q) μ := by
    intro q
    exact (stronglyMeasurable_hughesYoungLowerBoundaryCentralSeriesHeightTerm_joint
      T hc hh hk hr a b q).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (fun p : ℝ × ℝ => ∑' q, F q p) μ :=
    (AEMeasurable.tsum fun q => (hF q).aemeasurable).aestronglyMeasurable
  refine hsum.congr ?_
  filter_upwards [] with p
  unfold F hughesYoungLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSeries
  rw [tsum_mul_left]

/-- The complete swapped Ramanujan lower-boundary series is jointly
measurable in physical height and Mellin ordinate. -/
theorem aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c) {μ : Measure (ℝ × ℝ)}
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight (hughesYoungLowerBoundaryReducedMellinCorrection
            T p.1 c p.2 h k))) μ := by
  let F : ℕ → ℝ × ℝ → ℂ := fun q p =>
    hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      T p.1 c p.2 h k a b r q
  have hF : ∀ q, AEStronglyMeasurable (F q) μ := by
    intro q
    exact
      (stronglyMeasurable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_joint
        T hc hh hk hr a b q).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (fun p : ℝ × ℝ => ∑' q, F q p) μ :=
    (AEMeasurable.tsum fun q => (hF q).aemeasurable).aestronglyMeasurable
  refine hsum.congr ?_
  filter_upwards [] with p
  unfold F hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
    dfiEquation27CentralSeries
  rw [tsum_mul_left]

/-- The literal finite signed lower-boundary source is jointly measurable
before either outer integral is evaluated. -/
theorem aestronglyMeasurable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_joint
    (T : ℝ) {c : ℝ} (hc : 0 < c)
    {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (K : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T p.1 c p.2 h k a b K) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let F : ℤ → ℝ × ℝ → ℂ := fun r p =>
    if r = 0 then 0 else
        (hughesYoungHeightWeight T p.1 : ℂ) *
          dfiSignedCentralSeries a b r
            (hughesYoungLowerBoundaryReducedMellinCorrection
              T p.1 c p.2 h k)
  have hm : AEStronglyMeasurable (∑ r ∈ S, F r) := by
    apply Finset.aestronglyMeasurable_sum
    intro r _hrmem
    by_cases hr0 : r = 0
    · simp only [F, hr0, if_true]
      exact aestronglyMeasurable_const
    · simp only [F, hr0, if_false]
      cases r with
      | ofNat n =>
          have hn : 0 < n := by
            by_contra hn0
            apply hr0
            simp [Nat.eq_zero_of_not_pos hn0]
          simpa only [dfiSignedCentralSeries_ofNat] using
            aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_joint
              (μ := volume) T hc hh hk hn a b
      | negSucc m =>
          let n : ℕ := m + 1
          have hn : 0 < n := by dsimp only [n]; omega
          have hrCast : Int.negSucc m = -(n : ℤ) := by
            dsimp only [n]
            omega
          rw [hrCast]
          simpa only [dfiSignedCentralSeries_neg_ofNat a b n hn] using
            aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_joint
              (μ := volume) T hc hh hk hn a b
  have heq : (fun p : ℝ × ℝ => ∑ r ∈ S, F r p) = ∑ r ∈ S, F r := by
    funext p
    exact (Finset.sum_apply p S F).symm
  have hsum : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ∑ r ∈ S, F r p) := by
    rw [heq]
    exact hm
  refine hsum.congr ?_
  filter_upwards [] with p
  unfold hughesYoungFiniteLowerBoundarySignedCentralAtHeight
  simp only [B, S, F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr0 : r = 0 <;> simp [hr0]

/-! ### Uniform endpoint majorants

The Mellin ordinate occurs in the static physical source only through
unit-modulus powers.  Consequently the following coefficient is
independent of both outer integration variables. -/

/-- Outer-variable-independent majorant for one positive Ramanujan
modulus term of the lower boundary. -/
noncomputable def hughesYoungLowerBoundarySeriesTermMajorant
    (T c : ℝ) (h k a b r q : ℕ) : ℝ :=
  ‖((a : ℂ) * b)⁻¹‖ *
    ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
    ((‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
      (r : ℝ) ^ (-2 * c) *
      (2312 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖) ^ 2 +
        9 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖) ^ 2 *
          c⁻¹ ^ 3))

theorem hughesYoungLowerBoundarySeriesTermMajorant_nonneg
    (T : ℝ) {c : ℝ} (hc : 0 < c) (h k a b r q : ℕ) :
    0 ≤ hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q := by
  unfold hughesYoungLowerBoundarySeriesTermMajorant
  positivity

/-- Pointwise domination of one positive modulus term by the common
height input and an outer-variable-independent coefficient. -/
theorem norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le_majorant_mul_heightInput
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q *
        ‖hughesYoungHeightFourierInput T c u t‖ := by
  have hterm := norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le_fixed
    hc (hc4.trans_lt (by norm_num)) T t u hh hk hr a b q
  have hphysical :=
    integral_norm_dfiEquation27C_pureReducedStaticWeight_posShift_le
      hc hc4 T u hh hk a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)
        (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  rw [norm_hughesYoungPureReducedStaticScaleConstant_eq T c u hh hk] at hphysical
  let C : ℝ :=
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
      (r : ℝ) ^ (-2 * c) *
      (2312 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖) ^ 2 +
        9 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖) ^ 2 *
          c⁻¹ ^ 3)
  have hphysical' :
      (∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation27C a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (hughesYoungPureReducedStaticWeight T c u h k)
          (y + r) y‖) ≤ C := by
    simpa only [C] using hphysical
  calc
    ‖hughesYoungLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (hughesYoungPureReducedStaticWeight T c u h k)
              (y + r) y‖) *
          ‖hughesYoungHeightFourierInput T c u t‖) := hterm
    _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        (C * ‖hughesYoungHeightFourierInput T c u t‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hphysical' (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      unfold hughesYoungLowerBoundarySeriesTermMajorant
      dsimp only [C]
      ring

/-- The negative signed-shift term has the same uniform majorant after
the exact coordinate swap. -/
theorem norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le_majorant_mul_heightInput
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {r : ℕ} (hr : 0 < r) (a b q : ℕ) :
    ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      hughesYoungLowerBoundarySeriesTermMajorant T c h k b a r q *
        ‖hughesYoungHeightFourierInput T c u t‖ := by
  have hterm :=
    norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le_fixed
      hc (hc4.trans_lt (by norm_num)) T t u hh hk hr a b q
  have hphysical :=
    integral_norm_dfiEquation27C_swappedPureReducedStaticWeight_posShift_le
      hc hc4 T u hh hk a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)
        (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  rw [norm_hughesYoungPureReducedStaticScaleConstant_eq T c u hh hk] at hphysical
  let C : ℝ :=
    (‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
      (r : ℝ) ^ (-2 * c) *
      (2312 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖) ^ 2 +
        9 *
          (1 +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ +
            ‖(Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q)‖) ^ 2 *
          c⁻¹ ^ 3)
  have hphysical' :
      (∫ y in Set.Ioi (0 : ℝ),
        ‖dfiEquation27C b a
          (dfiReducedDenominator b q) (dfiReducedDenominator a q)
          (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
          (y + r) y‖) ≤ C := by
    simpa only [C] using hphysical
  calc
    ‖hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
        T t c u h k a b r q‖ ≤
      ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        ((∫ y in Set.Ioi (0 : ℝ),
            ‖dfiEquation27C b a
              (dfiReducedDenominator b q) (dfiReducedDenominator a q)
              (dfiSwapWeight (hughesYoungPureReducedStaticWeight T c u h k))
              (y + r) y‖) *
          ‖hughesYoungHeightFourierInput T c u t‖) := hterm
    _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        (C * ‖hughesYoungHeightFourierInput T c u t‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hphysical' (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      unfold hughesYoungLowerBoundarySeriesTermMajorant
      dsimp only [C]
      ring

set_option maxHeartbeats 1600000 in
/-- The outer-variable-independent Ramanujan majorants are summable. -/
theorem summable_hughesYoungLowerBoundarySeriesTermMajorant
    {c : ℝ} (hc : 0 < c) (T : ℝ)
    {h k a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Summable (fun q : ℕ =>
      hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q) := by
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let K₀ : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) *
    ((‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
      (r : ℝ) ^ (-2 * c) * (2312 + 9 * c⁻¹ ^ 3))
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ =>
      K₀ * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left K₀
  apply hmajor.of_nonneg_of_le
  · intro q
    exact hughesYoungLowerBoundarySeriesTermMajorant_nonneg T hc h k a b r q
  · intro q
    by_cases hq0 : q = 0
    · subst q
      simp [hughesYoungLowerBoundarySeriesTermMajorant,
        dfiEquation27ArithmeticCoefficient]
    · have hq : 0 < q := Nat.pos_of_ne_zero hq0
      letI : NeZero q := ⟨hq0⟩
      let S : ℝ := 1 +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant b (dfiReducedDenominator b q)‖ +
        ‖(Real.log r : ℂ) +
          dfiEquation27LogConstant a (dfiReducedDenominator a q)‖
      have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
        have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
        have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
        dsimp only [S, A]
        unfold hughesYoungEquation84LogBudget
        linarith
      have hS0 : 0 ≤ S := by dsimp only [S]; positivity
      have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
        zero_le_one.trans
          (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
      have hCoeff :=
        norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
      unfold hughesYoungLowerBoundarySeriesTermMajorant
      calc
        ‖((a : ℂ) * b)⁻¹‖ *
            ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
            ((‖hughesYoungLocalizedStaticScalar T h k‖ *
                (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
                (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
              (r : ℝ) ^ (-2 * c) *
              (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) ≤
          ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungLocalizedStaticScalar T h k‖ *
                (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
                (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
              (r : ℝ) ^ (-2 * c) *
              (2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3)) := by
            gcongr
        _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
            (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
            ((‖hughesYoungLocalizedStaticScalar T h k‖ *
                (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 + c) *
                (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 + c)) *
              (r : ℝ) ^ (-2 * c) *
              ((2312 + 9 * c⁻¹ ^ 3) *
                (A + 4 * Real.log (q : ℝ)) ^ 2)) := by
            gcongr
            calc
              2312 * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
                  (2312 + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
              _ ≤ (2312 + 9 * c⁻¹ ^ 3) *
                  (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
        _ = K₀ * (((q : ℝ) ^ 2)⁻¹ *
            (A + 4 * Real.log (q : ℝ)) ^ 2) := by
          dsimp only [K₀]
          ring

/-- The entire positive Ramanujan series is dominated by the common
height input with the summed uniform coefficient. -/
theorem norm_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_le
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k)‖ ≤
      (∑' q : ℕ,
        hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q) *
        ‖hughesYoungHeightFourierInput T c u t‖ := by
  let F : ℕ → ℂ := fun q =>
    hughesYoungLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  let C : ℕ → ℝ := fun q =>
    hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q
  have hF : Summable F := by
    simpa only [F, hughesYoungLowerBoundaryCentralSeriesHeightTerm,
      dfiEquation27CentralSummand_const_mul_weight] using
      summable_dfiEquation27CentralSummand_heightWeight_mul_lowerBoundary
        hc hc4 T t u hh hk ha hb hr
  have hC : Summable C := by
    simpa only [C] using
      summable_hughesYoungLowerBoundarySeriesTermMajorant hc T ha hb hr
  have hCH : Summable (fun q =>
      C q * ‖hughesYoungHeightFourierInput T c u t‖) :=
    hC.mul_right _
  have hpoint : ∀ q, ‖F q‖ ≤
      C q * ‖hughesYoungHeightFourierInput T c u t‖ := by
    intro q
    exact
      norm_hughesYoungLowerBoundaryCentralSeriesHeightTerm_le_majorant_mul_heightInput
        hc hc4 T t u hh hk hr a b q
  have heq : (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries a b r
        (hughesYoungLowerBoundaryReducedMellinCorrection T t c u h k) =
      ∑' q, F q := by
    unfold F hughesYoungLowerBoundaryCentralSeriesHeightTerm
      dfiEquation27CentralSeries
    rw [tsum_mul_left]
  rw [heq]
  calc
    ‖∑' q, F q‖ ≤ ∑' q, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q, C q * ‖hughesYoungHeightFourierInput T c u t‖ :=
      hF.norm.tsum_le_tsum hpoint hCH
    _ = (∑' q, C q) * ‖hughesYoungHeightFourierInput T c u t‖ := by
      rw [tsum_mul_right]

/-- Coordinate-swapped counterpart of the uniform full-series bound. -/
theorem norm_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_le
    {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (T t u : ℝ) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    ‖(hughesYoungHeightWeight T t : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight (hughesYoungLowerBoundaryReducedMellinCorrection
            T t c u h k))‖ ≤
      (∑' q : ℕ,
        hughesYoungLowerBoundarySeriesTermMajorant T c h k b a r q) *
        ‖hughesYoungHeightFourierInput T c u t‖ := by
  let F : ℕ → ℂ := fun q =>
    hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      T t c u h k a b r q
  let C : ℕ → ℝ := fun q =>
    hughesYoungLowerBoundarySeriesTermMajorant T c h k b a r q
  have hF : Summable F := by
    simpa only [F] using
      summable_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_fixed
        hc hc4 T t u hh hk ha hb hr
  have hC : Summable C := by
    simpa only [C] using
      summable_hughesYoungLowerBoundarySeriesTermMajorant hc T hb ha hr
  have hCH : Summable (fun q =>
      C q * ‖hughesYoungHeightFourierInput T c u t‖) :=
    hC.mul_right _
  have hpoint : ∀ q, ‖F q‖ ≤
      C q * ‖hughesYoungHeightFourierInput T c u t‖ := by
    intro q
    exact
      norm_hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm_le_majorant_mul_heightInput
        hc hc4 T t u hh hk hr a b q
  have heq : (hughesYoungHeightWeight T t : ℂ) *
      dfiEquation27CentralSeries b a r
        (dfiSwapWeight (hughesYoungLowerBoundaryReducedMellinCorrection
          T t c u h k)) = ∑' q, F q := by
    unfold F hughesYoungSwappedLowerBoundaryCentralSeriesHeightTerm
      dfiEquation27CentralSeries
    rw [tsum_mul_left]
  rw [heq]
  calc
    ‖∑' q, F q‖ ≤ ∑' q, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q, C q * ‖hughesYoungHeightFourierInput T c u t‖ :=
      hF.norm.tsum_le_tsum hpoint hCH
    _ = (∑' q, C q) * ‖hughesYoungHeightFourierInput T c u t‖ := by
      rw [tsum_mul_right]

/-- Product integrability of a complete positive lower-boundary Ramanujan
series on a bounded Mellin segment. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_joint
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {H : ℝ} (hH : 0 ≤ H) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        dfiEquation27CentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T p.1 c p.2 h k))
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
  let C : ℝ := ∑' q : ℕ,
    hughesYoungLowerBoundarySeriesTermMajorant T c h k a b r q
  have hheight := integrable_uncurry_hughesYoungHeightFourierInput hT hc hH
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      C * ‖hughesYoungHeightFourierInput T c p.2 p.1‖)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) :=
    hheight.norm.const_mul C
  have hmeas :=
    aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_joint
      (μ := volume.prod (volume.restrict (Set.uIoc (-H) H)))
      T hc hh hk hr a b
  apply hmajor.mono' hmeas
  filter_upwards [] with p
  simpa only [C] using
    norm_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_le
      hc hc4 T p.1 p.2 hh hk ha hb hr

/-- Product integrability of the coordinate-swapped lower-boundary
Ramanujan series. -/
theorem integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_joint
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {H : ℝ} (hH : 0 ≤ H) {h k a b r : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        dfiEquation27CentralSeries b a r
          (dfiSwapWeight (hughesYoungLowerBoundaryReducedMellinCorrection
            T p.1 c p.2 h k)))
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
  let C : ℝ := ∑' q : ℕ,
    hughesYoungLowerBoundarySeriesTermMajorant T c h k b a r q
  have hheight := integrable_uncurry_hughesYoungHeightFourierInput hT hc hH
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      C * ‖hughesYoungHeightFourierInput T c p.2 p.1‖)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) :=
    hheight.norm.const_mul C
  have hmeas :=
    aestronglyMeasurable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_joint
      (μ := volume.prod (volume.restrict (Set.uIoc (-H) H)))
      T hc hh hk hr a b
  apply hmajor.mono' hmeas
  filter_upwards [] with p
  simpa only [C] using
    norm_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_le
      hc hc4 T p.1 p.2 hh hk ha hb hr

/-- The literal finite signed lower-boundary source is integrable on the
full physical-height line times the bounded Mellin segment. -/
theorem integrable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_joint
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {H : ℝ} (hH : 0 ≤ H) {h k a b : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (K : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.1 : ℂ) *
        hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T p.1 c p.2 h k a b K)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let F : ℤ → ℝ × ℝ → ℂ := fun r p =>
    if r = 0 then 0 else
      (hughesYoungHeightWeight T p.1 : ℂ) *
        dfiSignedCentralSeries a b r
          (hughesYoungLowerBoundaryReducedMellinCorrection
            T p.1 c p.2 h k)
  have hsum : Integrable (fun p : ℝ × ℝ => ∑ r ∈ S, F r p)
      (volume.prod (volume.restrict (Set.uIoc (-H) H))) := by
    apply integrable_finsetSum S
    intro r _hrmem
    by_cases hr0 : r = 0
    · simp [F, hr0]
    · simp only [F, hr0, if_false]
      cases r with
      | ofNat n =>
          have hn : 0 < n := by
            by_contra hn0
            apply hr0
            simp [Nat.eq_zero_of_not_pos hn0]
          simpa only [dfiSignedCentralSeries_ofNat] using
            integrable_heightWeight_mul_dfiEquation27CentralSeries_lowerBoundary_joint
              hT hc hc4 hH hh hk ha hb hn
      | negSucc m =>
          let n : ℕ := m + 1
          have hn : 0 < n := by dsimp only [n]; omega
          have hrCast : Int.negSucc m = -(n : ℤ) := by
            dsimp only [n]
            omega
          rw [hrCast]
          simpa only [dfiSignedCentralSeries_neg_ofNat a b n hn] using
            integrable_heightWeight_mul_dfiEquation27CentralSeries_swappedLowerBoundary_joint
              hT hc hc4 hH hh hk ha hb hn
  apply hsum.congr
  filter_upwards [] with p
  unfold F hughesYoungFiniteLowerBoundarySignedCentralAtHeight
  simp only [B, S, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hrmem
  by_cases hr0 : r = 0 <;> simp [hr0]

/-- Fubini for the exact finite lower-boundary source. -/
theorem integral_intervalIntegral_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_swap
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {H : ℝ} (hH : 0 ≤ H) {h k a b : ℕ}
    (hh : 0 < h) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (K : ℕ) :
    (∫ t : ℝ, ∫ u in -H..H,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteLowerBoundarySignedCentralAtHeight
          T t c u h k a b K) =
      ∫ u in -H..H, ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteLowerBoundarySignedCentralAtHeight
            T t c u h k a b K := by
  let f : ℝ → ℝ → ℂ := fun u t =>
    (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteLowerBoundarySignedCentralAtHeight
        T t c u h k a b K
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc (-H) H)).prod volume) := by
    have h :=
      (integrable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_joint
        hT hc hc4 hH hh hk ha hb K).swap
    simpa only [f, Function.comp_apply, Prod.swap_prod_mk,
      Function.uncurry_apply_pair] using h
  simpa only [f] using (intervalIntegral_integral_swap hf).symm

/-- For one positive mollifier pair, the literal non-lower source is the
active-complement source minus the already evaluated lower boundary. -/
theorem integral_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    {H : ℝ} (hH : 0 ≤ H) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∫ t : ℝ, ∫ u in -H..H,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralAtHeight
          T t c u h k (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) R K) =
      (∫ t : ℝ, ∫ u in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveComplementSignedCentralAtHeight
            T t c u h k (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K) -
        ∫ u in -H..H,
          hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T c u h k
            (hughesYoungReducedLeft h k)
            (hughesYoungReducedRight h k) K := by
  let ν : Measure ℝ := volume.restrict (Set.uIoc (-H) H)
  let fp : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungFinitePureSignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  let fa : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungActiveReassembledSignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let fac : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungActiveComplementSignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let fl : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungFiniteLowerBoundarySignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  let fn : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungNonLowerActiveComplementSignedCentralAtHeight
        T p.1 c p.2 h k (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  have hcHalf : c < 1 / 2 := hc4.trans_lt (by norm_num)
  have hp : Integrable fp (volume.prod ν) := by
    simpa only [fp, ν] using
      integrable_uncurry_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
        hT hc hcHalf hH hh hk K
  have ha0 :=
    integrable_uncurry_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
      hT hc hH hh hk R K
  have ha : Integrable fa (volume.prod ν) := by
    simpa only [fa, ν, Function.comp_apply, Prod.swap_prod_mk] using ha0.swap
  have hac : Integrable fac (volume.prod ν) := by
    apply (hp.sub ha).congr
    filter_upwards [] with p
    unfold fp fa fac hughesYoungActiveComplementSignedCentralAtHeight
    simp only [Pi.sub_apply, mul_sub]
  have hl : Integrable fl (volume.prod ν) := by
    simpa only [fl, ν] using
      integrable_heightWeight_mul_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_joint
        hT hc hc4 hH hh hk
          (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) K
  have hn : Integrable fn (volume.prod ν) := by
    apply (hac.sub hl).congr
    filter_upwards [] with p
    unfold fn fac fl hughesYoungActiveComplementSignedCentralAtHeight
    rw [heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
      hT hc hc4 p.1 p.2 hh hk
        (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) R K]
    simp only [Pi.sub_apply, mul_sub]
    abel
  have hinterval : -H ≤ H := by linarith
  have hsub : (∫ p : ℝ × ℝ, fn p ∂volume.prod ν) =
      (∫ p : ℝ × ℝ, fac p ∂volume.prod ν) -
        ∫ p : ℝ × ℝ, fl p ∂volume.prod ν := by
    calc
      _ = ∫ p : ℝ × ℝ, fac p - fl p ∂volume.prod ν := by
        apply integral_congr_ae
        filter_upwards [] with p
        unfold fn fac fl hughesYoungActiveComplementSignedCentralAtHeight
        rw [heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
          hT hc hc4 p.1 p.2 hh hk
            (hughesYoungReducedLeft_pos hh)
            (hughesYoungReducedRight_pos hh hk) R K]
        ring
      _ = _ := integral_sub hac hl
  have hlEval : (∫ t : ℝ, ∫ u in -H..H, fl (t, u)) =
      ∫ u in -H..H,
        hughesYoungFiniteLowerBoundaryHeightIntegratedCentral T c u h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K := by
    calc
      _ = ∫ u in -H..H, ∫ t : ℝ, fl (t, u) := by
        simpa only [fl] using
          integral_intervalIntegral_hughesYoungFiniteLowerBoundarySignedCentralAtHeight_swap
            hT hc hc4 hH hh hk
              (hughesYoungReducedLeft_pos hh)
              (hughesYoungReducedRight_pos hh hk) K
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro u _hu
        exact
          (hughesYoungFiniteLowerBoundaryHeightIntegratedCentral_eq_heightIntegral
            hT hc hc4 u hh hk
              (hughesYoungReducedLeft_pos hh)
              (hughesYoungReducedRight_pos hh hk) K).symm
  calc
    (∫ t : ℝ, ∫ u in -H..H, fn (t, u)) =
        ∫ p : ℝ × ℝ, fn p ∂volume.prod ν := by
      simpa only [ν, intervalIntegral.integral_of_le hinterval,
        Set.uIoc_of_le hinterval] using (integral_prod fn hn).symm
    _ = (∫ p : ℝ × ℝ, fac p ∂volume.prod ν) -
        ∫ p : ℝ × ℝ, fl p ∂volume.prod ν := hsub
    _ = (∫ t : ℝ, ∫ u in -H..H, fac (t, u)) -
        ∫ t : ℝ, ∫ u in -H..H, fl (t, u) := by
      rw [integral_prod fac hac, integral_prod fl hl]
      simp only [ν, intervalIntegral.integral_of_le hinterval,
        Set.uIoc_of_le hinterval]
    _ = _ := by rw [hlEval]

/-- The globally integrated literal source is exactly the previously
defined non-lower active complement.  This is the source-entry identity
needed before the contour can be moved as one cancellation-preserving
object. -/
theorem hughesYoungNonLowerActiveComplementIntegratedCentralSource_eq
    {T : ℝ} (hT : Real.exp 4 ≤ T) (R K : ℕ) :
    hughesYoungNonLowerActiveComplementIntegratedCentralSource T R K =
      hughesYoungNonLowerActiveComplementIntegratedCentral T R K := by
  classical
  have hT0 : 0 < T := (Real.exp_pos 4).trans_le hT
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)).trans hT
  have hc := hughesYoungSmallContour_spec hT1
  have hlog4 : 4 ≤ Real.log T := by
    rw [← Real.log_exp (4 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 4) hT
  have hc4 : hughesYoungSmallContour T ≤ 1 / 4 := by
    unfold hughesYoungSmallContour
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < Real.log T)
        (show (0 : ℝ) < 4 by norm_num)).2 hlog4
  have hH : 0 ≤ T / 8 := by positivity
  unfold hughesYoungNonLowerActiveComplementIntegratedCentralSource
    hughesYoungNonLowerActiveComplementIntegratedCentral
    hughesYoungActiveComplementIntegratedCentral
    hughesYoungFiniteLowerBoundaryIntegratedCentral
    hughesYoungFiniteLowerBoundaryContourIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hhmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hkmem
  have hh : 0 < h := (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := (Finset.mem_Icc.mp hkmem).1
  exact integral_hughesYoungNonLowerActiveComplementSignedCentralAtHeight_eq
    hT0 hc.1 hc4 hH hh hk R K

/-! ## Scalar-parametric signed contour transfer

The negative DFI shift retains the original height cutoff while swapping the
two critical-line points.  The following scalar-parametric series makes that
distinction explicit and avoids any division by a cutoff value that may be
zero. -/

/-- One positive-shift equation-(27) summand with an arbitrary fixed scalar
outside the genuine complex Hughes--Young source weight. -/
noncomputable def hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    (z : ℂ) (T t : ℝ) (w : ℂ) (h k a b R K r q : ℕ) : ℂ :=
  dfiEquation27CentralSummand a b r
    (fun X Y => z *
      hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K X Y) q

theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ ≤ 1) (z : ℂ)
    (t H : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (c : ℝ), c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_majorant
      hc₀ hc₁ z t H a b R K hrR
        (T := T) (h := h) (k := k)
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c₀⁻¹ ^ 3)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q c hcMem
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S) := by
      exact integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc₀
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x) :=
      hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        exact hsource qx qy c hcMem x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD.le
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant
              c₀ delta S x := hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc₀]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (H : ℂ) * I) z h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * Ddelta * S ^ 2 +
              9 * S ^ 2 * c₀⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ring

/-- Height-uniform equation-(27) summand bound.  Unlike the compact-edge
bound above, the constant is chosen before `H` and the Gaussian decay is
retained explicitly for the contour-exhaustion argument. -/
theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_gaussian
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 1 ≤ |H| → ∀ (q : ℕ) (c : ℝ),
      c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q‖ ≤
      B * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16) *
        (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_scalar_nonLowerActiveComplement_horizontal_dilate_le_gaussianMajorant
      hc₀ hc hc₁ z t a b R K hrR (T := T) (h := h) (k := k)
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c₀⁻¹ ^ 3)
  have hB : 0 < B := by
    dsimp only [B]
    have habC : ((a : ℂ) * b) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb))
    have habr : 0 < ((a * b * r ^ 2 : ℕ) : ℝ) := by positivity
    have hnorm : 0 < ‖((a : ℂ) * b)⁻¹‖ :=
      norm_pos_iff.mpr (inv_ne_zero habC)
    have hlast : 0 < 2312 * Ddelta + 9 * c₀⁻¹ ^ 3 := by
      have hDdelta : 0 < Ddelta := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      positivity
    exact mul_pos (mul_pos (mul_pos (mul_pos hnorm habr) hrR) hD) hlast
  refine ⟨B, hB, ?_⟩
  intro H hH q c hcMem
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (H : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
        (hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc₀
    have hDEGint : Integrable (fun x : ℝ =>
        (D * E) * hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x) :=
      hGint.const_mul (D * E)
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ (D * E) *
          hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        simpa only [E, mul_assoc] using hsource H hH qx qy c hcMem x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg (mul_nonneg hD.le hE0)
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDEGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          (D * E) * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ, (D * E) *
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := hIntRaw
        _ = (D * E) * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c₀ delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = (D * E) *
            (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc₀]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (H : ℂ) * I) z h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) * ((D * E) *
            (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3))) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) * ((D * E) *
            ((2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c₀⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c₀⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * E * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ac_rfl

theorem hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k a b R K : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r q) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r q) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r q) = 0 := by
  have hcentral :=
    dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_boundaryRect_zero
      hc₀ hc hc₁ z t hH h k a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        R K (show (0 : ℝ) < r by exact_mod_cast hr) (T := T)
  let z : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  simp only [smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  change z * _ - z * _ + I * (z * _) - I * (z * _) = 0
  linear_combination z * hcentral

theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q)
      volume c₀ c₁ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint := integrable_scalar_nonLowerActiveComplement_horizontal_dilate_joint
    hc₀ hc₁ z t H a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let coeff : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul coeff
  have hinterval : IntervalIntegrable
      (fun s : ℝ => coeff * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => z *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((s : ℂ) + (H : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume c₀ c₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    exact hscaled
  convert hinterval using 1
  funext s
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    T t ((s : ℂ) + (H : ℂ) * I) z h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [coeff]
  push_cast
  ring

set_option maxHeartbeats 1200000 in
theorem summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁,
        ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le
      hc₀ (hc₁.trans (by norm_num)) z t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (c₁ - c₀) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((c₁ - c₀) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun s =>
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
    have hfInterval :=
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc (hc₁.trans (by norm_num)) z t H h k a b R K hr q
        (T := T)
    have hf : Integrable f (volume.restrict (Set.Icc c₀ c₁)) := by
      change IntegrableOn f (Set.Icc c₀ c₁)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
      exact hfInterval
    have hM0 : 0 ≤ M q := by
      dsimp only [M]
      positivity
    have hconst : Integrable (fun _s : ℝ => M q)
        (volume.restrict (Set.Icc c₀ c₁)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ s : ℝ in Set.Icc c₀ c₁, ‖f s‖) ≤
          ∫ _s : ℝ in Set.Icc c₀ c₁, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        simpa only [f, M, A] using hbound q s hs
      _ = (c₁ - c₀) * M q := by
        simp [MeasureTheory.integral_const, hc]

theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k a b R K : ℕ)
    {r : ℕ} (hr : 0 < r) (q : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q)
      volume (-H) H := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjoint := integrable_scalar_nonLowerActiveComplement_vertical_dilate_joint
    hc hc1 z t H a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR
      (T := T) (h := h) (k := k)
  let coeff : ℂ := (((a : ℂ) * b)⁻¹ *
    dfiEquation27ArithmeticCoefficient a b r q)
  have hinner := hjoint.integral_prod_left
  have hscaled := (hinner.const_mul (r : ℂ)).const_mul coeff
  have hinterval : IntervalIntegrable
      (fun u : ℝ => coeff * ((r : ℂ) *
        ∫ x : ℝ in Set.Ioi ((1 / hughesYoungDyadicRatio) / (r : ℝ)),
          dfiEquation27C a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (fun X Y => z *
              hughesYoungNonLowerActiveComplementMellinWeightComplex T t
                ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
            ((r : ℝ) * x + r) ((r : ℝ) * x))) volume (-H) H := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -H ≤ H)]
    exact hscaled
  convert hinterval using 1
  funext u
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
    dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
    T t ((c : ℂ) + (u : ℂ) * I) z h k a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) R K hrR]
  dsimp only [coeff]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_le
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ)
    (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) (u : ℝ), u ∈ Set.Icc (-H) H →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖ ≤
      B * (((q : ℝ) ^ 2)⁻¹ *
        (hughesYoungEquation84LogBudget a b r +
          4 * Real.log (q : ℝ)) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨D, hD, hsource⟩ :=
    exists_norm_scalar_nonLowerActiveComplement_vertical_dilate_le_majorant
      hc hc1 z t H a b R K hrR (T := T) (h := h) (k := k)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let delta : ℝ := (1 / hughesYoungDyadicRatio) / (r : ℝ)
  let Ddelta : ℝ := max 1 (delta ^ (-(3 / 4 : ℝ)))
  let B : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) * (r : ℝ) * D *
      (2312 * Ddelta + 9 * c⁻¹ ^ 3)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q u hu
  by_cases hq0 : q = 0
  · subst q
    simp [hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex,
      dfiEquation27CentralSummand, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    let qx : ℕ := dfiReducedDenominator a q
    let qy : ℕ := dfiReducedDenominator b q
    let S : ℝ := 1 +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant b qy‖ +
      ‖(Real.log r : ℂ) + dfiEquation27LogConstant a qx‖
    let F : ℝ → ℂ := fun x =>
      dfiEquation27C a b qx qy
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex T t
            ((c : ℂ) + (u : ℂ) * I) h k a b R K X Y)
        ((r : ℝ) * x + r) ((r : ℝ) * x)
    let J : ℝ → ℂ := fun x => (Set.Ioi delta).indicator F x
    have hdelta : 0 < delta := div_pos
      (one_div_pos.mpr hughesYoungDyadicRatio_pos) hrR
    have hGint : Integrable
      (hughesYoungCriticalAffineBetaFullStripMajorant c delta S) :=
      integrable_hughesYoungCriticalAffineBetaFullStripMajorant hc
    have hDGint : Integrable (fun x : ℝ =>
        D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x) :=
      hGint.const_mul D
    have hJbound (x : ℝ) :
        ‖J x‖ ≤ D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
      by_cases hxmem : x ∈ Set.Ioi delta
      · have hJ : J x = F x := by simp [J, hxmem]
        rw [hJ]
        exact hsource qx qy u hu x hxmem
      · have hJ : J x = 0 := by simp [J, hxmem]
        rw [hJ, norm_zero]
        exact mul_nonneg hD.le
          hughesYoungCriticalAffineBetaFullStripMajorant_nonneg
    have hIntRaw := MeasureTheory.norm_integral_le_of_norm_le hDGint
      (Filter.Eventually.of_forall hJbound)
    have hInt :
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ ≤
          D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) := by
      calc
        ‖∫ x : ℝ in Set.Ioi delta, F x‖ = ‖∫ x : ℝ, J x‖ := by
          simp only [J, MeasureTheory.integral_indicator measurableSet_Ioi]
        _ ≤ ∫ x : ℝ,
            D * hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := hIntRaw
        _ = D * ∫ x : ℝ,
            hughesYoungCriticalAffineBetaFullStripMajorant c delta S x := by
          rw [MeasureTheory.integral_const_mul]
        _ = D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3) := by
          rw [integral_hughesYoungCriticalAffineBetaFullStripMajorant_eq hc]
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hS : S ≤ A + 4 * Real.log (q : ℝ) := by
      have hCX := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
      have hCOne := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
      dsimp only [S, A, qx, qy]
      unfold hughesYoungEquation84LogBudget
      linarith
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hProfile0 : 0 ≤ A + 4 * Real.log (q : ℝ) :=
      zero_le_one.trans
        (one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq)
    have hCentral :=
      dfiEquation27CentralIntegral_scalar_mul_nonLowerActiveComplement_eq_dilated
        T t ((c : ℂ) + (u : ℂ) * I) z h k a b qx qy R K hrR
    unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      dfiEquation27CentralSummand
    rw [hCentral]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrR]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
          ((r : ℝ) * ‖∫ x : ℝ in Set.Ioi delta, F x‖) ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * (2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3))) := by gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((r : ℝ) *
            (D * ((2312 * Ddelta + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2))) := by
        gcongr
        calc
          2312 * Ddelta * S ^ 2 + 9 * S ^ 2 * c⁻¹ ^ 3 =
              (2312 * Ddelta + 9 * c⁻¹ ^ 3) * S ^ 2 := by ring
          _ ≤ (2312 * Ddelta + 9 * c⁻¹ ^ 3) *
              (A + 4 * Real.log (q : ℝ)) ^ 2 := by gcongr
      _ = B * (((q : ℝ) ^ 2)⁻¹ *
          (hughesYoungEquation84LogBudget a b r +
            4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp only [B, A]
        ring

set_option maxHeartbeats 1200000 in
theorem summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H,
        ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_le
      hc hc1 z t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hmajor : Summable (fun q : ℕ => (H - (-H)) * M q) := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left
        ((H - (-H)) * B)
    simpa only [M, mul_assoc] using hbase
  apply hmajor.of_nonneg_of_le
  · intro q
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => norm_nonneg _)
  · intro q
    let f : ℝ → ℂ := fun u =>
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
    have horder : -H ≤ H := by linarith
    have hfInterval :=
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc hc1 z t hH h k a b R K hr q (T := T)
    have hf : Integrable f (volume.restrict (Set.Icc (-H) H)) := by
      change IntegrableOn f (Set.Icc (-H) H)
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
      exact hfInterval
    have hM0 : 0 ≤ M q := by dsimp only [M]; positivity
    have hconst : Integrable (fun _u : ℝ => M q)
        (volume.restrict (Set.Icc (-H) H)) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    calc
      (∫ u : ℝ in Set.Icc (-H) H, ‖f u‖) ≤
          ∫ _u : ℝ in Set.Icc (-H) H, M q := by
        apply MeasureTheory.integral_mono_ae hf.norm hconst
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        simpa only [f, M, A] using hbound q u hu
      _ = (H - (-H)) * M q := by
        simp [MeasureTheory.integral_const, hH]

/-- The complete scalar-parametric positive-shift Ramanujan series. -/
noncomputable def hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
    (z : ℂ) (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) : ℂ :=
  ∑' q : ℕ,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t w h k a b R K r q

/-- The complete positive Ramanujan series inherits the same height-uniform
Gaussian envelope.  This is the Weierstrass summation step needed before the
horizontal contour edges can be sent to infinity. -/
theorem exists_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ |H| → ∀ c : ℝ,
      c ∈ Set.Icc c₀ c₁ →
      ‖hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r‖ ≤
      C * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + |H|) ^ 16) := by
  obtain ⟨B, hB, hterm⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le_gaussian
      hc₀ hc hc₁ z t h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let Q : ℕ → ℝ := fun q => ((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hQ : Summable Q := by
    simpa only [Q] using summable_natCast_inv_sq_mul_four_log_profile_sq A hA
  let C₀ : ℝ := B * ∑' q : ℕ, Q q
  let C : ℝ := max 1 C₀
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro H hH c hcMem
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let F : ℕ → ℂ := fun q =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c : ℂ) + (H : ℂ) * I) h k a b R K r q
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hmajor : Summable (fun q : ℕ => (B * E) * Q q) :=
    hQ.mul_left (B * E)
  have hFbound (q : ℕ) : ‖F q‖ ≤ (B * E) * Q q := by
    simpa only [F, E, Q, A, mul_assoc] using hterm H hH q c hcMem
  have hF : Summable F := Summable.of_norm_bounded hmajor hFbound
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  change ‖∑' q : ℕ, F q‖ ≤ _
  calc
    ‖∑' q : ℕ, F q‖ ≤ ∑' q : ℕ, ‖F q‖ :=
      norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' q : ℕ, (B * E) * Q q :=
      hF.norm.tsum_le_tsum hFbound hmajor
    _ = (B * E) * ∑' q : ℕ, Q q := by rw [tsum_mul_left]
    _ = C₀ * E := by dsimp only [C₀]; ring
    _ ≤ C * E := mul_le_mul_of_nonneg_right (le_max_right 1 C₀) hE0
    _ = C * (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
        (2 + |t| + c₁ + |H|) ^ 16) := rfl

/-- The horizontal integral of the complete positive series has the same
Gaussian envelope, with only the length of the fixed source strip lost. -/
theorem exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ |H| →
      ‖∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r‖ ≤
      (c₁ - c₀) * C *
        (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
          (2 + |t| + c₁ + |H|) ^ 16) := by
  obtain ⟨C, hC, hseries⟩ :=
    exists_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian
      hc₀ hc hc₁ z t h k ha hb hr R K (T := T)
  refine ⟨C, hC, ?_⟩
  intro H hH
  let E : ℝ := Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) *
    (2 + |t| + c₁ + |H|) ^ 16
  let f : ℝ → ℂ := fun s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r
  have hpoint : ∀ s ∈ Set.uIoc c₀ c₁, ‖f s‖ ≤ C * E := by
    intro s hs
    have hs' : s ∈ Set.uIcc c₀ c₁ := Set.uIoc_subset_uIcc hs
    rw [Set.uIcc_of_le hc] at hs'
    exact hseries H hH s hs'
  have hInt : ‖∫ s : ℝ in c₀..c₁, f s‖ ≤ (C * E) * |c₁ - c₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := f) (C := C * E) hpoint
  have hlen : |c₁ - c₀| = c₁ - c₀ := abs_of_nonneg (sub_nonneg.mpr hc)
  change ‖∫ s : ℝ in c₀..c₁, f s‖ ≤ (c₁ - c₀) * C * E
  calc
    _ ≤ (C * E) * |c₁ - c₀| := hInt
    _ = (c₁ - c₀) * C * E := by rw [hlen]; ac_rfl

set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric positive equation-(27) series has a
vanishing upper horizontal edge. -/
theorem tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian
      hc₀ hc hc₁ z t h k ha hb hr R K (T := T)
  let C₀ : ℝ := (c₁ - c₀) * C
  let B₀ : ℝ := 2 + |t| + c₁
  let envelope : ℝ → ℝ := fun H =>
    (c₁ - c₀) * C *
      (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) * (B₀ + H) ^ 16)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sub_nonneg.mpr hc) hC.le
  have hB₀ : 0 ≤ B₀ := by
    dsimp only [B₀]
    have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
    positivity
  have henv : Tendsto envelope atTop (𝓝 0) := by
    simpa only [envelope, C₀, mul_assoc] using
      tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
        C₀ (100 * c₁ ^ 2) B₀ hC₀ hB₀
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ henv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hHabs : 1 ≤ |H| := by simpa only [abs_of_nonneg hH0] using hH
    have hb := hbound H hHabs
    simpa only [envelope, B₀, abs_of_nonneg hH0] using hb

set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric positive equation-(27) series also has a
vanishing lower horizontal edge. -/
theorem tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (z : ℂ) (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_le_gaussian
      hc₀ hc hc₁ z t h k ha hb hr R K (T := T)
  let C₀ : ℝ := (c₁ - c₀) * C
  let B₀ : ℝ := 2 + |t| + c₁
  let envelope : ℝ → ℝ := fun H =>
    (c₁ - c₀) * C *
      (Real.exp (100 * c₁ ^ 2 - 100 * H ^ 2) * (B₀ + H) ^ 16)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sub_nonneg.mpr hc) hC.le
  have hB₀ : 0 ≤ B₀ := by
    dsimp only [B₀]
    have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
    positivity
  have henv : Tendsto envelope atTop (𝓝 0) := by
    simpa only [envelope, C₀, mul_assoc] using
      tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen
        C₀ (100 * c₁ ^ 2) B₀ hC₀ hB₀
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ henv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 ≤ H := zero_le_one.trans hH
    have hHabs : 1 ≤ |-H| := by simpa only [abs_neg, abs_of_nonneg hH0] using hH
    have hb := hbound (-H) hHabs
    rw [abs_neg, abs_of_nonneg hH0, neg_sq] at hb
    simpa only [envelope, B₀] using hb

/-- The named scalar-parametric series is exactly the literal DFI
equation-(27) central series. -/
theorem hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_eq_dfiEquation27CentralSeries
    (z : ℂ) (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) :
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t w h k a b R K r =
      dfiEquation27CentralSeries a b r
        (fun X Y => z *
          hughesYoungNonLowerActiveComplementMellinWeightComplex
            T t w h k a b R K X Y) := by
  rfl

theorem summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => ∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
      hc₀ hc hc₁ z t H h k ha hb hr R K (T := T)
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _

theorem summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Summable (fun q : ℕ => ∫ u : ℝ in -H..H,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q) := by
  have hNorm :=
    summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
      hc hc1 z t hH h k ha hb hr R K (T := T)
  have horder : -H ≤ H := by linarith
  apply Summable.of_norm_bounded hNorm
  intro q
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.norm_integral_le_integral_norm _

theorem integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) =
      ∑' q : ℕ, ∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q := by
  let F : ℕ → ℝ → ℂ := fun q s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc c₀ c₁)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc c₀ c₁)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc (hc₁.trans (by norm_num)) z t H h k a b R K hr q (T := T)
  have hNorm : Summable (fun q : ℕ =>
      ∫ s : ℝ in Set.Icc c₀ c₁, ‖F q s‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ z t H h k ha hb hr R K (T := T)
  have hswap : (∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s) =
      ∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ s : ℝ in Set.Icc c₀ c₁, ∑' q : ℕ, F q s) =
        ∑' q : ℕ, ∫ s : ℝ in Set.Icc c₀ c₁, F q s := hswap.symm
    _ = ∑' q : ℕ, ∫ s : ℝ in c₀..c₁, F q s := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le hc, ← integral_Icc_eq_integral_Ioc]

theorem integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    (∫ u : ℝ in -H..H,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r) =
      ∑' q : ℕ, ∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
          z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q := by
  have horder : -H ≤ H := by linarith
  let F : ℕ → ℝ → ℂ := fun q u =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
  have hInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc (-H) H)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc (-H) H)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc hc1 z t hH h k a b R K hr q (T := T)
  have hNorm : Summable (fun q : ℕ =>
      ∫ u : ℝ in Set.Icc (-H) H, ‖F q u‖) := by
    simpa only [F] using
      summable_integral_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc hc1 z t hH h k ha hb hr R K (T := T)
  have hswap : (∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u) =
      ∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hInt hNorm
  unfold hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
  rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ u : ℝ in Set.Icc (-H) H, ∑' q : ℕ, F q u) =
        ∑' q : ℕ, ∫ u : ℝ in Set.Icc (-H) H, F q u := hswap.symm
    _ = ∑' q : ℕ, ∫ u : ℝ in -H..H, F q u := by
      apply tsum_congr
      intro q
      rw [intervalIntegral.integral_of_le horder, ← integral_Icc_eq_integral_Ioc]

set_option maxHeartbeats 1200000 in
theorem hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r) = 0 := by
  let Bottom : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..c₁,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r q
  let Top : ℕ → ℂ := fun q => ∫ s : ℝ in c₀..c₁,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  let Right : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c₁ : ℂ) + (u : ℂ) * I) h k a b R K r q
  let Left : ℕ → ℂ := fun q => ∫ u : ℝ in -H..H,
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c₀ : ℂ) + (u : ℂ) * I) h k a b R K r q
  have hBottom :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
      hc₀ hc hc₁ z t (-H) h k ha hb hr R K (T := T)
  have hTop :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_eq_tsum
      hc₀ hc hc₁ z t H h k ha hb hr R K (T := T)
  have hRight :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
      (hc₀.trans_le hc) hc₁ z t hH h k ha hb hr R K (T := T)
  have hLeft :=
    integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical_eq_tsum
      hc₀ (hc.trans hc₁) z t hH h k ha hb hr R K (T := T)
  have hsBottom : Summable Bottom := by
    simpa only [Bottom] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ z t (-H) h k ha hb hr R K (T := T)
  have hsTop : Summable Top := by
    simpa only [Top] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc hc₁ z t H h k ha hb hr R K (T := T)
  have hsRight : Summable Right := by
    simpa only [Right] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        (hc₀.trans_le hc) hc₁ z t hH h k ha hb hr R K (T := T)
  have hsLeft : Summable Left := by
    simpa only [Left] using
      summable_intervalIntegral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc₀ (hc.trans hc₁) z t hH h k ha hb hr R K (T := T)
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  change (∑' q : ℕ, Bottom q) - (∑' q : ℕ, Top q) +
      I * (∑' q : ℕ, Right q) - I * (∑' q : ℕ, Left q) = 0
  calc
    _ = (∑' q : ℕ, (Bottom q - Top q)) +
        (∑' q : ℕ, (I * Right q - I * Left q)) := by
      rw [hsBottom.tsum_sub hsTop,
        (hsRight.mul_left I).tsum_sub (hsLeft.mul_left I),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = ∑' q : ℕ,
        ((Bottom q - Top q) + (I * Right q - I * Left q)) := by
      rw [← (hsBottom.sub hsTop).tsum_add
        ((hsRight.mul_left I).sub (hsLeft.mul_left I))]
    _ = ∑' _q : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro q
      have hq :=
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_boundaryRect_zero
          hc₀ hc (hc₁.trans (by norm_num)) z t hH h k a b R K hr q
          (T := T)
      dsimp only [Bottom, Top, Right, Left]
      linear_combination hq
    _ = 0 := tsum_zero

/-- The literal negative-shift DFI central series, retaining the original
physical-height cutoff outside the coordinate-swapped complex source. -/
noncomputable def hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
    (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) : ℂ :=
  dfiEquation27CentralSeries b a r
    (dfiSwapWeight (fun X Y => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K X Y))

/-- Exact reduction of the negative DFI branch to the scalar-parametric
positive branch with the two critical-line points and arithmetic coordinates
swapped. -/
theorem hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive
    (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) :
    hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t w h k a b R K r =
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
        (hughesYoungHeightWeight T t : ℂ) T (-t) w
          k h b a R K r := by
  rw [hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_eq_dfiEquation27CentralSeries]
  unfold hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
  congr 1
  funext X Y
  unfold dfiSwapWeight
  have hswap := congrFun (congrFun
    (dfiSwapWeight_hughesYoungNonLowerActiveComplementMellinWeightComplex
      T t w h k a b R K) X) Y
  unfold dfiSwapWeight at hswap
  dsimp only
  rw [hswap]

/-- The complete negative-shift Ramanujan series obeys the same exact
four-edge contour identity, with no evenness assumption on the height
cutoff. -/
theorem hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
          h k a b R K r) -
      (∫ s : ℝ in c₀..c₁,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I)
          h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((c₁ : ℂ) + (u : ℂ) * I)
          h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((c₀ : ℂ) + (u : ℂ) * I)
          h k a b R K r) = 0 := by
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) (-t) hH
        k h hb ha hr R K

/-- A positive signed shift, after multiplication by the physical-height
cutoff, is exactly the named complete positive Ramanujan series. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
    (T t : ℝ) (w : ℂ) (h k a b R K r : ℕ) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K (r : ℤ) =
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t w h k a b R K r := by
  unfold hughesYoungNonLowerActiveComplementSignedCentralComplex
  rw [dfiSignedCentralSeries_ofNat]
  rw [hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_eq_dfiEquation27CentralSeries]
  symm
  exact dfiEquation27CentralSeries_const_mul_weight
    a b r (hughesYoungHeightWeight T t : ℂ)
      (hughesYoungNonLowerActiveComplementMellinWeightComplex
        T t w h k a b R K)

/-- A negative signed shift, after multiplication by the same physical-height
cutoff, is exactly the coordinate-swapped complete negative Ramanujan
series. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
    (T t : ℝ) (w : ℂ) (h k a b R K : ℕ) {r : ℕ} (hr : 0 < r) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K (-(r : ℤ)) =
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t w h k a b R K r := by
  unfold hughesYoungNonLowerActiveComplementSignedCentralComplex
    hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
  rw [dfiSignedCentralSeries_neg_ofNat a b r hr]
  rw [← dfiEquation27CentralSeries_const_mul_weight]
  congr 1

/-- Vanishing upper edge for the physical positive-shift series. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) t h k
        ha hb hr R K (T := T)

/-- Vanishing lower edge for the physical positive-shift series. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) t h k
        ha hb hr R K (T := T)

/-- Vanishing upper edge for the physical negative-shift series. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) (-t) k h
        hb ha hr R K (T := T)

/-- Vanishing lower edge for the physical negative-shift series. -/
theorem tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_bottom_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  simp_rw [hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive]
  exact
    tendsto_integral_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) (-t) k h
        hb ha hr R K (T := T)

/-- Each nonzero signed DFI shift has a vanishing upper horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal_atTop
          hc₀ hc hc₁ t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K n
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal_atTop
          hc₀ hc hc₁ t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      rw [hrCast]
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
        T t ((s : ℂ) + (H : ℂ) * I) h k a b R K hn

/-- Each nonzero signed DFI shift has a vanishing lower horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_bottom_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K r) atTop (𝓝 0) := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_bottom_atTop
          hc₀ hc hc₁ t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K n
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by dsimp only [n]; omega
      have hbase :=
        tendsto_integral_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_bottom_atTop
          hc₀ hc hc₁ t h k ha hb hn R K (T := T)
      convert hbase using 1
      ext H
      apply intervalIntegral.integral_congr
      intro s _hs
      rw [hrCast]
      exact heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
        T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K hn

set_option maxHeartbeats 1200000 in
/-- The complete scalar-parametric Ramanujan series is integrable on every
horizontal edge of a small Mellin rectangle.  The proof uses the same
inverse-square/log-square Weierstrass majorant as the exact contour swap. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (z : ℂ) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  let F : ℕ → ℝ → ℂ := fun q s =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r q
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal_le
      hc₀ (hc₁.trans (by norm_num)) z t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left B
    simpa only [M, mul_assoc] using hbase
  have hFInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc c₀ c₁)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc c₀ c₁)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hc]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_horizontal
        hc₀ hc (hc₁.trans (by norm_num)) z t H h k a b R K hr q (T := T)
  have hmeas : AEStronglyMeasurable (fun s : ℝ => ∑' q : ℕ, F q s)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    AEStronglyMeasurable.tsum (fun q => (hFInt q).aestronglyMeasurable)
  have hconst : Integrable (fun _s : ℝ => ∑' q : ℕ, M q)
      (volume.restrict (Set.Icc c₀ c₁)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc]
  change Integrable (fun s : ℝ => ∑' q : ℕ, F q s)
    (volume.restrict (Set.Icc c₀ c₁))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hnorm : Summable (fun q : ℕ => ‖F q s‖) :=
    hM.of_nonneg_of_le (fun q => norm_nonneg (F q s)) (fun q => by
      simpa only [F, M, A] using hbound q s hs)
  calc
    ‖∑' q : ℕ, F q s‖ ≤ ∑' q : ℕ, ‖F q s‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, M q :=
      hnorm.tsum_le_tsum (fun q => by
        simpa only [F, M, A] using hbound q s hs) hM

set_option maxHeartbeats 1200000 in
/-- Vertical-edge interval integrability of the complete scalar-parametric
Ramanujan series. -/
theorem intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (z : ℂ)
    (t : ℝ) {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex
          z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r)
      volume (-H) H := by
  have horder : -H ≤ H := by linarith
  let F : ℕ → ℝ → ℂ := fun q u =>
    hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex
      z T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r q
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_norm_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical_le
      hc hc1 z t H h k ha hb hr R K (T := T)
  let A : ℝ := hughesYoungEquation84LogBudget a b r
  let M : ℕ → ℝ := fun q => B * (((q : ℝ) ^ 2)⁻¹ *
    (A + 4 * Real.log (q : ℝ)) ^ 2)
  have hA : 0 ≤ A :=
    zero_le_one.trans (one_le_hughesYoungEquation84LogBudget a b r)
  have hM : Summable M := by
    have hbase :=
      (summable_natCast_inv_sq_mul_four_log_profile_sq A hA).mul_left B
    simpa only [M, mul_assoc] using hbase
  have hFInt : ∀ q : ℕ, Integrable (F q)
      (volume.restrict (Set.Icc (-H) H)) := by
    intro q
    change IntegrableOn (F q) (Set.Icc (-H) H)
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le horder]
    simpa only [F] using
      intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex_vertical
        hc hc1 z t hH h k a b R K hr q (T := T)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => ∑' q : ℕ, F q u)
      (volume.restrict (Set.Icc (-H) H)) :=
    AEStronglyMeasurable.tsum (fun q => (hFInt q).aestronglyMeasurable)
  have hconst : Integrable (fun _u : ℝ => ∑' q : ℕ, M q)
      (volume.restrict (Set.Icc (-H) H)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le horder]
  change Integrable (fun u : ℝ => ∑' q : ℕ, F q u)
    (volume.restrict (Set.Icc (-H) H))
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hnorm : Summable (fun q : ℕ => ‖F q u‖) :=
    hM.of_nonneg_of_le (fun q => norm_nonneg (F q u)) (fun q => by
      simpa only [F, M, A] using hbound q u hu)
  calc
    ‖∑' q : ℕ, F q u‖ ≤ ∑' q : ℕ, ‖F q u‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ℕ, M q :=
      hnorm.tsum_le_tsum (fun q => by
        simpa only [F, M, A] using hbound q u hu) hM

/-- Horizontal-edge integrability of the physical positive-shift series. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) t H h k
        ha hb hr R K (T := T)

/-- Vertical-edge integrability of the physical positive-shift series. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r)
      volume (-H) H := by
  simpa only [
      hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungNonLowerActiveComplementPositiveCentralSummandComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex,
      hughesYoungScalarNonLowerActiveComplementPositiveCentralSummandComplex] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical
      hc hc1 (hughesYoungHeightWeight T t : ℂ) t hH h k
        ha hb hr R K (T := T)

/-- Horizontal-edge integrability of the coordinate-swapped negative-shift
series. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  simpa only [
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal
      hc₀ hc hc₁ (hughesYoungHeightWeight T t : ℂ) (-t) H k h
        hb ha hr R K (T := T)

/-- Vertical-edge integrability of the coordinate-swapped negative-shift
series. -/
theorem intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b r : ℕ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (R K : ℕ) :
    IntervalIntegrable
      (fun u : ℝ =>
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r)
      volume (-H) H := by
  simpa only [
      hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_eq_scalarPositive] using
    intervalIntegrable_hughesYoungScalarNonLowerActiveComplementPositiveCentralSeriesComplex_vertical
      hc hc1 (hughesYoungHeightWeight T t : ℂ) (-t) hH k h
        hb ha hr R K (T := T)

/-- Every nonzero height-weighted signed source term is integrable on a
horizontal edge. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t H : ℝ) (h k : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (R K : ℕ)
    {r : ℤ} (hr₀ : r ≠ 0) :
    IntervalIntegrable
      (fun s : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K r)
      volume c₀ c₁ := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_horizontal
          hc₀ hc hc₁ t H h k ha hb hn R K (T := T)
      apply hbase.congr
      intro s _hs
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K n).symm
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_horizontal
          hc₀ hc hc₁ t H h k ha hb hn R K (T := T)
      apply hbase.congr
      intro s _hs
      rw [hrCast]
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K hn).symm

/-- The complete finite signed complement source has a vanishing upper
horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_horizontal_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((s : ℂ) + (H : ℂ) * I) h k a b R K) atTop (𝓝 0) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hterm : ∀ r ∈ S, Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      f ((s : ℂ) + (H : ℂ) * I) r) atTop (𝓝 0) := by
    intro r _hrmem
    by_cases hr₀ : r = 0
    · subst r
      simpa only [f, if_pos, mul_zero, intervalIntegral.integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _H : ℝ => (0 : ℂ)) atTop (nhds 0))
    · simpa only [f, hr₀, if_false] using
        tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal_atTop
          hc₀ hc hc₁ t h k ha hb R K hr₀ (T := T)
  have hsum : Tendsto (fun H : ℝ => ∑ r ∈ S,
      ∫ s : ℝ in c₀..c₁, f ((s : ℂ) + (H : ℂ) * I) r) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S hterm
  convert hsum using 1
  ext H
  have hpoint (w : ℂ) :
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t w h k a b R K =
        ∑ r ∈ S, f w r := by
    simp only [hughesYoungNonLowerActiveComplementSignedSourceComplex]
    dsimp only [B, S, f]
    rw [Finset.mul_sum]
  calc
    (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + (H : ℂ) * I) h k a b R K) =
      ∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
        f ((s : ℂ) + (H : ℂ) * I) r := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hpoint _
    _ = ∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
        f ((s : ℂ) + (H : ℂ) * I) r := by
      rw [intervalIntegral.integral_finsetSum]
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · have hbase :=
          intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal
            hc₀ hc hc₁ t H h k ha hb R K hr₀ (T := T)
        apply hbase.congr
        intro s _hs
        simp only [f, hr₀, if_false]

/-- The complete finite signed complement source has a vanishing lower
horizontal edge. -/
theorem tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_bottom_atTop
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ ≤ 1)
    (t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedSourceComplex
          T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K) atTop (𝓝 0) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hterm : ∀ r ∈ S, Tendsto (fun H : ℝ => ∫ s : ℝ in c₀..c₁,
      f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) atTop (𝓝 0) := by
    intro r _hrmem
    by_cases hr₀ : r = 0
    · subst r
      simpa only [f, if_pos, mul_zero, intervalIntegral.integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _H : ℝ => (0 : ℂ)) atTop (nhds 0))
    · simpa only [f, hr₀, if_false] using
        tendsto_integral_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_bottom_atTop
          hc₀ hc hc₁ t h k ha hb R K hr₀ (T := T)
  have hsum : Tendsto (fun H : ℝ => ∑ r ∈ S,
      ∫ s : ℝ in c₀..c₁, f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum S hterm
  convert hsum using 1
  ext H
  have hpoint (w : ℂ) :
      (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t w h k a b R K =
        ∑ r ∈ S, f w r := by
    simp only [hughesYoungNonLowerActiveComplementSignedSourceComplex]
    dsimp only [B, S, f]
    rw [Finset.mul_sum]
  calc
    (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I) h k a b R K) =
      ∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
        f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hpoint _
    _ = ∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
        f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r := by
      rw [intervalIntegral.integral_finsetSum]
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · have hbase :=
          intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal
            hc₀ hc hc₁ t (-H) h k ha hb R K hr₀ (T := T)
        apply hbase.congr
        intro s _hs
        simp only [f, hr₀, if_false, Complex.ofReal_neg]

/-- Every nonzero height-weighted signed source term is integrable on a
vertical edge. -/
theorem intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical
    {T c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h k : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (R K : ℕ)
    {r : ℤ} (hr₀ : r ≠ 0) :
    IntervalIntegrable
      (fun u : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K r)
      volume (-H) H := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hn0
        subst n
        exact hr₀ rfl
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_vertical
          hc hc1 t hH h k ha hb hn R K (T := T)
      apply hbase.congr
      intro u _hu
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K n).symm
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      have hbase :=
        intervalIntegrable_hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_vertical
          hc hc1 t hH h k ha hb hn R K (T := T)
      apply hbase.congr
      intro u _hu
      rw [hrCast]
      exact
        (heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t ((c : ℂ) + (u : ℂ) * I) h k a b R K hn).symm

/-- Every nonzero signed DFI shift of the literal height-weighted complex
source obeys the exact four-edge contour identity.  Positive and negative
shifts are dispatched to their complete Ramanujan series, not finite
partial sums. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) {r : ℤ} (hr₀ : r ≠ 0) :
    (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
            h k a b R K r) -
      (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((s : ℂ) + (H : ℂ) * I)
            h k a b R K r) +
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((c₁ : ℂ) + (u : ℂ) * I)
            h k a b R K r) -
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedCentralComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I)
            h k a b R K r) = 0 := by
  cases r with
  | ofNat n =>
      by_cases hn0 : n = 0
      · subst n
        exact False.elim (hr₀ rfl)
      · have hn : 0 < n := Nat.pos_of_ne_zero hn0
        have hre (w : ℂ) :
            (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t w h k a b R K (n : ℤ) =
              hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                T t w h k a b R K n :=
          heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_ofNat
            T t w h k a b R K n
        have hbottom :
            (∫ s : ℝ in c₀..c₁,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ s : ℝ in c₀..c₁,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hre _
        have htop :
            (∫ s : ℝ in c₀..c₁,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((s : ℂ) + (H : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ s : ℝ in c₀..c₁,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((s : ℂ) + (H : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro s _hs
          exact hre _
        have hright :
            (∫ u : ℝ in -H..H,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((c₁ : ℂ) + (u : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ u : ℝ in -H..H,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((c₁ : ℂ) + (u : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro u _hu
          exact hre _
        have hleft :
            (∫ u : ℝ in -H..H,
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungNonLowerActiveComplementSignedCentralComplex
                  T t ((c₀ : ℂ) + (u : ℂ) * I)
                  h k a b R K (Int.ofNat n)) =
              ∫ u : ℝ in -H..H,
                hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex
                  T t ((c₀ : ℂ) + (u : ℂ) * I)
                  h k a b R K n := by
          apply intervalIntegral.integral_congr
          intro u _hu
          exact hre _
        rw [hbottom, htop, hright, hleft]
        exact
          hughesYoungNonLowerActiveComplementPositiveCentralSeriesComplex_boundaryRect_zero
            hc₀ hc hc₁ t hH h k ha hb hn R K (T := T)
  | negSucc m =>
      let n : ℕ := m + 1
      have hn : 0 < n := by dsimp only [n]; omega
      have hrCast : Int.negSucc m = -(n : ℤ) := by
        dsimp only [n]
        omega
      rw [hrCast]
      have hre (w : ℂ) :
          (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungNonLowerActiveComplementSignedCentralComplex
                T t w h k a b R K (-(n : ℤ)) =
            hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex
              T t w h k a b R K n :=
        heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_neg_ofNat
          T t w h k a b R K hn
      simp_rw [hre]
      exact
        hughesYoungNonLowerActiveComplementNegativeCentralSeriesComplex_boundaryRect_zero
          hc₀ hc hc₁ t hH h k ha hb hn R K (T := T)

/-- The complete finite signed Hughes--Young source obeys the exact four-edge
rectangle identity.  This is the source-level contour theorem: the complete
Ramanujan series has already been summed inside every signed shift, while the
remaining signed-shift family is finite and its zero shift is omitted exactly. -/
theorem heightWeight_mul_hughesYoungNonLowerActiveComplementSignedSourceComplex_boundaryRect_zero
    {T c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ ≤ 1) (t : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R K : ℕ) :
    (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + ((-H : ℝ) : ℂ) * I)
            h k a b R K) -
      (∫ s : ℝ in c₀..c₁,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((s : ℂ) + (H : ℂ) * I)
            h k a b R K) +
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₁ : ℂ) + (u : ℂ) * I)
            h k a b R K) -
      I • (∫ u : ℝ in -H..H,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungNonLowerActiveComplementSignedSourceComplex
            T t ((c₀ : ℂ) + (u : ℂ) * I)
            h k a b R K) = 0 := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let S := hughesYoungShiftInterval a b B B
  let f : ℂ → ℤ → ℂ := fun w r =>
    (hughesYoungHeightWeight T t : ℂ) *
      (if r = 0 then 0 else
        hughesYoungNonLowerActiveComplementSignedCentralComplex
          T t w h k a b R K r)
  have hBottom :
      (∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) =
        ∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
          f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal
          hc₀ hc hc₁ t (-H) h k ha hb R K hr₀ (T := T)
  have hTop :
      (∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
          f ((s : ℂ) + (H : ℂ) * I) r) =
        ∑ r ∈ S, ∫ s : ℝ in c₀..c₁,
          f ((s : ℂ) + (H : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_horizontal
          hc₀ hc hc₁ t H h k ha hb R K hr₀ (T := T)
  have hRight :
      (∫ u : ℝ in -H..H, ∑ r ∈ S,
          f ((c₁ : ℂ) + (u : ℂ) * I) r) =
        ∑ r ∈ S, ∫ u : ℝ in -H..H,
          f ((c₁ : ℂ) + (u : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical
          (hc₀.trans_le hc) hc₁ t hH h k ha hb R K hr₀ (T := T)
  have hLeft :
      (∫ u : ℝ in -H..H, ∑ r ∈ S,
          f ((c₀ : ℂ) + (u : ℂ) * I) r) =
        ∑ r ∈ S, ∫ u : ℝ in -H..H,
          f ((c₀ : ℂ) + (u : ℂ) * I) r := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _hrmem
    by_cases hr₀ : r = 0
    · simp [f, hr₀]
    · simpa only [f, hr₀, if_false] using
        intervalIntegrable_heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_vertical
          hc₀ (hc.trans hc₁) t hH h k ha hb R K hr₀ (T := T)
  unfold hughesYoungNonLowerActiveComplementSignedSourceComplex
  simp_rw [Finset.mul_sum]
  change
    (∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
      f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) -
    (∫ s : ℝ in c₀..c₁, ∑ r ∈ S,
      f ((s : ℂ) + (H : ℂ) * I) r) +
    I • (∫ u : ℝ in -H..H, ∑ r ∈ S,
      f ((c₁ : ℂ) + (u : ℂ) * I) r) -
    I • (∫ u : ℝ in -H..H, ∑ r ∈ S,
      f ((c₀ : ℂ) + (u : ℂ) * I) r) = 0
  rw [hBottom, hTop, hRight, hLeft]
  simp only [smul_eq_mul]
  calc
    _ = ∑ r ∈ S,
        ((∫ s : ℝ in c₀..c₁,
            f ((s : ℂ) + ((-H : ℝ) : ℂ) * I) r) -
          (∫ s : ℝ in c₀..c₁,
            f ((s : ℂ) + (H : ℂ) * I) r) +
          I * (∫ u : ℝ in -H..H,
            f ((c₁ : ℂ) + (u : ℂ) * I) r) -
          I * (∫ u : ℝ in -H..H,
            f ((c₀ : ℂ) + (u : ℂ) * I) r)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _hrmem
      by_cases hr₀ : r = 0
      · simp [f, hr₀]
      · simpa only [f, hr₀, if_false, smul_eq_mul] using
          heightWeight_mul_hughesYoungNonLowerActiveComplementSignedCentralComplex_boundaryRect_zero
            hc₀ hc hc₁ t hH h k ha hb R K hr₀ (T := T)

end RiemannZeta.GuthMaynard
