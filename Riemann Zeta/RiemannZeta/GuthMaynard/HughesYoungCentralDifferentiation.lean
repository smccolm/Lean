import RiemannZeta.GuthMaynard.HughesYoungCentralResidueLimit

open Complex Filter MeasureTheory Metric Set
open scoped Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Differentiating the Hughes--Young central contour

This file supplies the measure-theoretic bridge needed to take the two
auxiliary-shift derivatives after the cancellation-preserving contour shift.
The hypotheses expose both derivative families and their integrable
majorants, so no exchange of a derivative and an improper integral is hidden.
-/

/-- Cauchy's estimate on a translated half-radius disc, stated in the form
used for the two auxiliary Hughes--Young shifts. -/
theorem norm_deriv_le_div_halfRadius_of_differentiableOn_ball
    {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ C)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) (R / 2)) :
    ‖deriv f x‖ ≤ C / (R / 2) := by
  have hhalf : 0 < R / 2 := by positivity
  have hclosed : closedBall x (R / 2) ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball, dist_zero_right] at hx ⊢
    calc
      ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - x) x
      _ < R / 2 + R / 2 := add_lt_add_of_le_of_lt (by
        simpa [dist_eq] using hz) hx
      _ = R := by ring
  have hdiff : DiffContOnCl ℂ f (ball x (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball x hhalf.ne']
    exact hf.mono hclosed
  exact norm_deriv_le_of_forall_mem_sphere_norm_le hhalf hdiff
    (fun z hz => hC z (hclosed (sphere_subset_closedBall hz)))

/-- Two successive complex derivatives commute with a whole-line integral
when both differentiated families have uniform integrable majorants on one
common neighbourhood. -/
theorem deriv_right_deriv_left_integral_of_dominated
    (F Fz Fzw : ℂ → ℂ → ℝ → ℂ) {r : ℝ}
    (hr : 0 < r)
    (hFmeas : ∀ z ∈ ball (0 : ℂ) r, ∀ w ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (F z w))
    (hFint : ∀ w ∈ ball (0 : ℂ) r, Integrable (F 0 w))
    (hFzmeas : ∀ w ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (Fz 0 w))
    (g₁ : ℝ → ℝ) (hg₁ : Integrable g₁)
    (hFzbound : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) r,
      ∀ w ∈ ball (0 : ℂ) r, ‖Fz z w u‖ ≤ g₁ u)
    (hFz : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) r,
      ∀ w ∈ ball (0 : ℂ) r,
        HasDerivAt (fun v => F v w u) (Fz z w u) z)
    (hFzwmeas : AEStronglyMeasurable (Fzw 0 0))
    (g₂ : ℝ → ℝ) (hg₂ : Integrable g₂)
    (hFzwbound : ∀ u : ℝ, ∀ w ∈ ball (0 : ℂ) r,
      ‖Fzw 0 w u‖ ≤ g₂ u)
    (hFzw : ∀ u : ℝ, ∀ w ∈ ball (0 : ℂ) r,
      HasDerivAt (fun v => Fz 0 v u) (Fzw 0 w u) w) :
    deriv (fun w => deriv (fun z => ∫ u : ℝ, F z w u) 0) 0 =
      ∫ u : ℝ, Fzw 0 0 u := by
  have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hfirst : ∀ w ∈ ball (0 : ℂ) r,
      Integrable (Fz 0 w) ∧
        HasDerivAt (fun z => ∫ u : ℝ, F z w u)
          (∫ u : ℝ, Fz 0 w u) 0 := by
    intro w hw
    exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := ball (0 : ℂ) r) (x₀ := (0 : ℂ)) (F := fun z u => F z w u)
      (bound := g₁) (F' := fun z u => Fz z w u)
      (ball_mem_nhds 0 hr)
      (by
        filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
        exact hFmeas z hz w hw)
      (hFint w hw) (hFzmeas w hw)
      (Filter.Eventually.of_forall fun u z hz => hFzbound u z hz w hw)
      hg₁
      (Filter.Eventually.of_forall fun u z hz => hFz u z hz w hw)
  have hfirstEq :
      (fun w => deriv (fun z => ∫ u : ℝ, F z w u) 0) =ᶠ[𝓝 (0 : ℂ)]
        fun w => ∫ u : ℝ, Fz 0 w u := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with w hw
    exact (hfirst w hw).2.deriv
  rw [hfirstEq.deriv_eq]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball (0 : ℂ) r) (x₀ := (0 : ℂ))
    (F := fun w u => Fz 0 w u) (bound := g₂)
    (F' := fun w u => Fzw 0 w u)
    (ball_mem_nhds 0 hr)
    (by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr] with w hw
      exact hFzmeas w hw)
    (hfirst 0 hzero).1 hFzwmeas
    (Filter.Eventually.of_forall fun u w hw => hFzwbound u w hw)
    hg₂
    (Filter.Eventually.of_forall fun u w hw => hFzw u w hw)).2.deriv

private theorem analyticAt_auxiliary_fst (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => x.1) p :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p

private theorem analyticAt_auxiliary_snd (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => x.2) p :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt p

attribute [local fun_prop] analyticAt_auxiliary_fst analyticAt_auxiliary_snd

/-- The first-coordinate slice derivative of a jointly analytic function is
analytic in the second coordinate. -/
theorem AnalyticAt.deriv_fst_curry {F : ℂ × ℂ → ℂ} {w : ℂ}
    (hF : AnalyticAt ℂ F (0, w)) :
    AnalyticAt ℂ (fun v => deriv (fun z => F (z, v)) 0) w := by
  let e : ℂ → ℂ × ℂ := fun v => (0, v)
  have he : AnalyticAt ℂ e w := by
    simpa only [e, ContinuousLinearMap.inr_apply] using
      (ContinuousLinearMap.inr ℂ ℂ ℂ).analyticAt w
  have hfderiv : AnalyticAt ℂ (fun v => fderiv ℂ F (e v)) w :=
    hF.fderiv.comp' he
  have happly : AnalyticAt ℂ
      (fun v => (fderiv ℂ F (e v)) ((1 : ℂ), 0)) w :=
    ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), 0)).analyticAt _).comp'
      hfderiv
  have hevent : ∀ᶠ v in 𝓝 w, AnalyticAt ℂ F (0, v) := by
    simpa only [e] using he.continuousAt.tendsto (hF.eventually_analyticAt)
  have hEq :
      (fun v => deriv (fun z => F (z, v)) 0) =ᶠ[𝓝 w]
        fun v => (fderiv ℂ F (e v)) ((1 : ℂ), 0) := by
    filter_upwards [hevent] with v hv
    have hslice : HasDerivAt (fun z => F (z, v))
        ((fderiv ℂ F (0, v)) ((1 : ℂ), 0)) 0 :=
      hv.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_id (x := (0 : ℂ))).prodMk
          (hasDerivAt_const (x := (0 : ℂ)) v))
    simpa only [e] using hslice.deriv
  rwa [analyticAt_congr hEq]

/-- The second-coordinate slice derivative of a jointly analytic function
is analytic in the first coordinate. -/
theorem AnalyticAt.deriv_snd_curry {F : ℂ × ℂ → ℂ} {q : ℂ}
    (hF : AnalyticAt ℂ F (q, 0)) :
    AnalyticAt ℂ (fun v => deriv (fun z => F (v, z)) 0) q := by
  let swap : ℂ × ℂ → ℂ × ℂ := fun p => (p.2, p.1)
  let G : ℂ × ℂ → ℂ := fun p => F (swap p)
  have hswap : AnalyticAt ℂ swap (0, q) := by
    dsimp only [swap]
    fun_prop
  have hG : AnalyticAt ℂ G (0, q) := by
    have hcomp := hF.comp' (g := F) (f := swap) (x := (0, q)) hswap
    simpa only [G, swap] using hcomp
  simpa only [G, swap] using AnalyticAt.deriv_fst_curry hG

/-- A fourth-order zero on the diagonal `z+w=0` kills the mixed auxiliary
derivative.  The order four is deliberately stronger than the order-two
derivative ultimately taken in Hughes--Young. -/
theorem deriv_right_deriv_left_add_pow_four_mul_zero
    {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F (0, 0)) :
    deriv (fun w => deriv (fun z => (z + w) ^ 4 * F (z, w)) 0) 0 = 0 := by
  let D : ℂ → ℂ := fun w => deriv (fun z => F (z, w)) 0
  let R : ℂ → ℂ := fun w =>
    4 * w ^ 3 * F (0, w) + w ^ 4 * D w
  have hFslice : DifferentiableAt ℂ (fun w => F (0, w)) 0 := by
    exact hF.differentiableAt.comp 0
      ((hasDerivAt_const (x := (0 : ℂ)) (0 : ℂ)).prodMk
        (hasDerivAt_id (x := (0 : ℂ)))).differentiableAt
  have hD : AnalyticAt ℂ D 0 := by
    simpa only [D] using AnalyticAt.deriv_fst_curry hF
  have hR : HasDerivAt R 0 0 := by
    have hfirst := (((hasDerivAt_id (x := (0 : ℂ))).pow 3).const_mul 4).mul
      hFslice.hasDerivAt
    have hsecond := ((hasDerivAt_id (x := (0 : ℂ))).pow 4).mul
      hD.differentiableAt.hasDerivAt
    convert hfirst.add hsecond using 1
    all_goals simp [D]
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), AnalyticAt ℂ F (0, w) := by
    let e : ℂ → ℂ × ℂ := fun w => (0, w)
    have he : ContinuousAt e 0 := by
      dsimp only [e]
      fun_prop
    simpa only [e] using he.tendsto hF.eventually_analyticAt
  have hEq : (fun w => deriv (fun z => (z + w) ^ 4 * F (z, w)) 0) =ᶠ[𝓝 0] R := by
    filter_upwards [hnear] with w hw
    have hpoly : HasDerivAt (fun z : ℂ => (z + w) ^ 4) (4 * w ^ 3) 0 := by
      convert (((hasDerivAt_id (x := (0 : ℂ))).add_const w).pow 4) using 1
      simp
    have hslice : DifferentiableAt ℂ (fun z => F (z, w)) 0 := by
      exact hw.differentiableAt.comp 0
        ((hasDerivAt_id (x := (0 : ℂ))).prodMk
          (hasDerivAt_const (x := (0 : ℂ)) w)).differentiableAt
    have hprod := hpoly.mul hslice.hasDerivAt
    simpa only [Pi.mul_apply, R, D, zero_add] using hprod.deriv
  rw [Filter.EventuallyEq.deriv_eq hEq]
  exact hR.deriv

/-- A one-variable function differentiable throughout the standard
equation-(84) strip is analytic at every source-line point. -/
theorem analyticAt_sourceLine_of_differentiableAt_centralStrip
    (f : ℂ → ℂ)
    (hf : ∀ V : ℂ, 0 < V.re → V.re < 3 / 2 → DifferentiableAt ℂ f V)
    (u : ℝ) : AnalyticAt ℂ f ((1 : ℂ) + (u : ℂ) * I) := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [ball_mem_nhds ((1 : ℂ) + (u : ℂ) * I)
      (by norm_num : (0 : ℝ) < 1 / 4)] with V hV
  rw [mem_ball] at hV
  have hre : |V.re - 1| < 1 / 4 := by
    calc
      |V.re - 1| = |(V - ((1 : ℂ) + (u : ℂ) * I)).re| := by
        norm_num [Complex.mul_re]
      _ ≤ ‖V - ((1 : ℂ) + (u : ℂ) * I)‖ := abs_re_le_norm _
      _ = dist V ((1 : ℂ) + (u : ℂ) * I) := by rw [dist_eq]
      _ < 1 / 4 := hV
  exact hf V (by linarith [neg_abs_le (V.re - 1)])
    (by linarith [le_abs_self (V.re - 1)])

/-- Joint holomorphy in the source contour variable and the left auxiliary
shift, with the right shift fixed in its genuine equation-(98) bidisc. -/
theorem analyticAt_hughesYoungCompletePositiveCentralMaster_source_W_left
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) {w : ℂ}
    (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungCompletePositiveCentralMaster T t h k a b
          p.1 p.2 w)
      ((1 : ℂ) + (u : ℂ) * I, 0) := by
  let W : ℂ := (1 : ℂ) + (u : ℂ) * I
  let q : ℂ := hughesYoungEquation96ContourParameter W
  have hq : -(1 / 4 : ℝ) < q.re := by
    dsimp only [q, W, hughesYoungEquation96ContourParameter]
    norm_num [Complex.mul_re]
  have hstatic : AnalyticAt ℂ
      (hughesYoungReducedMellinStaticComplex T t h k) W := by
    rw [analyticAt_iff_eventually_differentiableAt]
    exact Filter.Eventually.of_forall fun V =>
      differentiableAt_hughesYoungReducedMellinStaticComplex T t h k V
  have hjetAll := analyticAt_hughesYoungEquation96ContinuationJet_all
    (h := a) (k := b) (q := q) (z := (0 : ℂ)) (w := w)
    hq (by norm_num) hw
  have hmap : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        (hughesYoungEquation96ContourParameter p.1, (p.2, w))) (W, 0) := by
    unfold hughesYoungEquation96ContourParameter
    fun_prop
  have hjet : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungEquation96ContinuationJet a b
          (hughesYoungEquation96ContourParameter p.1) p.2 w) (W, 0) := by
    exact hjetAll.comp'
      (g := fun p : ℂ × (ℂ × ℂ) =>
        hughesYoungEquation96ContinuationJet a b p.1 p.2.1 p.2.2)
      (f := fun p : ℂ × ℂ =>
        (hughesYoungEquation96ContourParameter p.1, (p.2, w)))
      (x := (W, 0)) hmap
  have hk₀₀ : AnalyticAt ℂ (hughesYoungEquation84Kernel00 t) W :=
    analyticAt_sourceLine_of_differentiableAt_centralStrip _
      (fun V hV0 hV3 => differentiableAt_hughesYoungEquation84Kernel00 t hV0 hV3) u
  have hk₁₀ : AnalyticAt ℂ (hughesYoungEquation84Kernel10 t) W :=
    analyticAt_sourceLine_of_differentiableAt_centralStrip _
      (fun V hV0 hV3 => differentiableAt_hughesYoungEquation84Kernel10 t hV0 hV3) u
  have hk₀₁ : AnalyticAt ℂ (hughesYoungEquation84Kernel01 t) W :=
    analyticAt_sourceLine_of_differentiableAt_centralStrip _
      (fun V hV0 hV3 => differentiableAt_hughesYoungEquation84Kernel01 t hV0 hV3) u
  have hk₁₁ : AnalyticAt ℂ (hughesYoungEquation84Kernel11 t) W :=
    analyticAt_sourceLine_of_differentiableAt_centralStrip _
      (fun V hV0 hV3 => differentiableAt_hughesYoungEquation84Kernel11 t hV0 hV3) u
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (W, 0) :=
    analyticAt_auxiliary_fst _
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (W, 0) :=
    analyticAt_auxiliary_snd _
  have hk₀₀' : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84Kernel00 t p.1) (W, 0) :=
    hk₀₀.comp' (g := hughesYoungEquation84Kernel00 t)
      (f := fun p : ℂ × ℂ => p.1) (x := (W, 0)) hfst
  have hk₁₀' : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84Kernel10 t p.1) (W, 0) :=
    hk₁₀.comp' (g := hughesYoungEquation84Kernel10 t)
      (f := fun p : ℂ × ℂ => p.1) (x := (W, 0)) hfst
  have hk₀₁' : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84Kernel01 t p.1) (W, 0) :=
    hk₀₁.comp' (g := hughesYoungEquation84Kernel01 t)
      (f := fun p : ℂ × ℂ => p.1) (x := (W, 0)) hfst
  have hk₁₁' : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84Kernel11 t p.1) (W, 0) :=
    hk₁₁.comp' (g := hughesYoungEquation84Kernel11 t)
      (f := fun p : ℂ × ℂ => p.1) (x := (W, 0)) hfst
  have hP : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungCentralReverseKernelPolynomial t p.1 p.2 w) (W, 0) := by
    unfold hughesYoungCentralReverseKernelPolynomial
    exact (((hk₁₁'.add (hsnd.mul hk₁₀')).add
      ((analyticAt_const.mul hk₀₁')))).add
      ((hsnd.mul analyticAt_const).mul hk₀₀')
  have houter : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (((a : ℂ) * b)⁻¹ *
        hughesYoungReducedMellinStaticComplex T t h k p.1)) (W, 0) := by
    have hs : AnalyticAt ℂ (fun p : ℂ × ℂ =>
        hughesYoungReducedMellinStaticComplex T t h k p.1) (W, 0) :=
      hstatic.comp' (g := hughesYoungReducedMellinStaticComplex T t h k)
        (f := fun p : ℂ × ℂ => p.1) (x := (W, 0)) hfst
    exact analyticAt_const.mul hs
  simpa only [W, hughesYoungCompletePositiveCentralMaster,
    hughesYoungCentralMasterJet] using houter.mul (hjet.mul hP)

/-- The first auxiliary derivative of the source master varies continuously
with the full real Mellin ordinate. -/
theorem continuous_deriv_left_hughesYoungCompletePositiveCentralMaster_source
    (T t : ℝ) (h k a b : ℕ) {w : ℂ} (hw : ‖w‖ < 1 / 8) :
    Continuous (fun u : ℝ => deriv (fun z =>
      hughesYoungCompletePositiveCentralMaster T t h k a b
        ((1 : ℂ) + (u : ℂ) * I) z w) 0) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hderiv := AnalyticAt.deriv_snd_curry
    (analyticAt_hughesYoungCompletePositiveCentralMaster_source_W_left
      T t h k a b u hw)
  have hline : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + (v : ℂ) * I) u := by fun_prop
  simpa only [Function.comp_apply] using
    hderiv.continuousAt.comp
      (f := fun v : ℝ => (1 : ℂ) + (v : ℂ) * I)
      (g := fun V : ℂ => deriv (fun z =>
        hughesYoungCompletePositiveCentralMaster T t h k a b V z w) 0)
      hline

/-- A jointly holomorphic two-shift family with one integrable uniform
envelope may be differentiated twice under the whole-line integral.  The
first- and mixed-derivative envelopes are consequences of Cauchy's estimate
on nested discs. -/
theorem deriv_right_deriv_left_integral_of_analytic_dominated
    (F : ℂ → ℂ → ℝ → ℂ) {R : ℝ} (hR : 0 < R)
    (hAnalytic : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R,
        AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2 u) (z, w))
    (hFmeas : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R,
      AEStronglyMeasurable (F z w))
    (hFzmeas : ∀ w ∈ ball (0 : ℂ) (R / 4),
      AEStronglyMeasurable
        (fun u => deriv (fun z => F z w u) 0))
    (hFzwmeas : AEStronglyMeasurable
      (fun u => deriv (fun w => deriv (fun z => F z w u) 0) 0))
    (g : ℝ → ℝ) (hg : Integrable g)
    (hbound : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R, ‖F z w u‖ ≤ g u) :
    deriv (fun w => deriv (fun z => ∫ u : ℝ, F z w u) 0) 0 =
      ∫ u : ℝ, deriv (fun w => deriv (fun z => F z w u) 0) 0 := by
  let r : ℝ := R / 4
  let Fz : ℂ → ℂ → ℝ → ℂ := fun z w u => deriv (fun v => F v w u) z
  let Fzw : ℂ → ℂ → ℝ → ℂ := fun z w u =>
    deriv (fun v => Fz z v u) w
  let g₁ : ℝ → ℝ := fun u => g u / (R / 2)
  let g₂ : ℝ → ℝ := fun u => g₁ u / (R / 4)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hhalf : 0 < R / 2 := by positivity
  have hzeroR : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hzeroHalf : (0 : ℂ) ∈ ball 0 (R / 2) := mem_ball_self hhalf
  have hrR : r < R := by dsimp only [r]; linarith
  have hhalfR : R / 2 < R := by linarith
  have hFint : ∀ w ∈ ball (0 : ℂ) r, Integrable (F 0 w) := by
    intro w hw
    have hwR : w ∈ ball (0 : ℂ) R := by
      exact (ball_subset_ball (le_of_lt hrR)) hw
    refine hg.mono' (hFmeas 0 hzeroR w hwR) ?_
    filter_upwards with u
    exact hbound u 0 hzeroR w hwR
  have hg₁ : Integrable g₁ := by
    have h := hg.const_mul (R / 2)⁻¹
    simpa only [g₁, div_eq_inv_mul] using h
  have hg₂ : Integrable g₂ := by
    have h := hg₁.const_mul (R / 4)⁻¹
    simpa only [g₂, div_eq_inv_mul] using h
  have hFz : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) r,
      ∀ w ∈ ball (0 : ℂ) r,
        HasDerivAt (fun v => F v w u) (Fz z w u) z := by
    intro u z hz w hw
    have hzR : z ∈ ball (0 : ℂ) R :=
      (ball_subset_ball (le_of_lt hrR)) hz
    have hwR : w ∈ ball (0 : ℂ) R :=
      (ball_subset_ball (le_of_lt hrR)) hw
    exact (hAnalytic u z hzR w hwR).curry_left.differentiableAt.hasDerivAt
  have hFzbound : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) r,
      ∀ w ∈ ball (0 : ℂ) r, ‖Fz z w u‖ ≤ g₁ u := by
    intro u z hz w hw
    have hzHalf : z ∈ ball (0 : ℂ) (R / 2) := by
      exact (ball_subset_ball (by dsimp only [r] at hz ⊢; linarith)) hz
    have hwR : w ∈ ball (0 : ℂ) R :=
      (ball_subset_ball (le_of_lt hrR)) hw
    have hdiff : DifferentiableOn ℂ (fun v => F v w u) (ball 0 R) := by
      intro v hv
      exact (hAnalytic u v hv w hwR).curry_left.differentiableAt.differentiableWithinAt
    simpa only [Fz, g₁] using
      norm_deriv_le_div_halfRadius_of_differentiableOn_ball hR hdiff
        (fun v hv => hbound u v hv w hwR) hzHalf
  have hFzw : ∀ u : ℝ, ∀ w ∈ ball (0 : ℂ) r,
      HasDerivAt (fun v => Fz 0 v u) (Fzw 0 w u) w := by
    intro u w hw
    have hwR : w ∈ ball (0 : ℂ) R :=
      (ball_subset_ball (le_of_lt hrR)) hw
    simpa only [Fz, Fzw] using
      (AnalyticAt.deriv_fst_curry
        (hAnalytic u 0 hzeroR w hwR)).differentiableAt.hasDerivAt
  have hFzwbound : ∀ u : ℝ, ∀ w ∈ ball (0 : ℂ) r,
      ‖Fzw 0 w u‖ ≤ g₂ u := by
    intro u w hw
    have hwQuarter : w ∈ ball (0 : ℂ) ((R / 2) / 2) := by
      have hradius : r = (R / 2) / 2 := by
        dsimp only [r]
        ring
      rwa [hradius] at hw
    have hdiff : DifferentiableOn ℂ (fun v => Fz 0 v u)
        (ball 0 (R / 2)) := by
      intro v hv
      have hvR : v ∈ ball (0 : ℂ) R :=
        (ball_subset_ball (le_of_lt hhalfR)) hv
      simpa only [Fz] using
        (AnalyticAt.deriv_fst_curry
          (hAnalytic u 0 hzeroR v hvR)).differentiableAt.differentiableWithinAt
    have hfirstBound : ∀ v ∈ ball (0 : ℂ) (R / 2),
        ‖Fz 0 v u‖ ≤ g₁ u := by
      intro v hv
      have hvR : v ∈ ball (0 : ℂ) R :=
        (ball_subset_ball (le_of_lt hhalfR)) hv
      have hslice : DifferentiableOn ℂ (fun q => F q v u) (ball 0 R) := by
        intro q hq
        exact (hAnalytic u q hq v hvR).curry_left.differentiableAt.differentiableWithinAt
      simpa only [Fz, g₁] using
        norm_deriv_le_div_halfRadius_of_differentiableOn_ball hR hslice
          (fun q hq => hbound u q hq v hvR) hzeroHalf
    have hradius : (R / 2) / 2 = R / 4 := by ring
    simpa only [Fzw, g₂, hradius] using
      norm_deriv_le_div_halfRadius_of_differentiableOn_ball hhalf hdiff
        hfirstBound hwQuarter
  exact deriv_right_deriv_left_integral_of_dominated
    (F := F) (Fz := Fz) (Fzw := Fzw) (r := r) hr
    (by
      intro z hz w hw
      exact hFmeas z ((ball_subset_ball (le_of_lt hrR)) hz)
        w ((ball_subset_ball (le_of_lt hrR)) hw))
    hFint
    (by
      intro w hw
      simpa only [Fz, r] using hFzmeas w hw)
    g₁ hg₁ hFzbound hFz
    (by simpa only [Fzw, Fz] using hFzwmeas)
    g₂ hg₂ hFzwbound hFzw

/-- On a compact source-line ordinate interval the complete reverse kernel
is uniformly bounded on the closed auxiliary-shift bidisc.  The constant is
obtained from the four actual equation-(84) kernel coefficients; no compact
bound for the full arithmetic expression is postulated. -/
theorem exists_uniform_norm_hughesYoungCentralReverseKernelPolynomial_source_compact
    (t : ℝ) {L δ : ℝ} (hδ0 : 0 ≤ δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {z w : ℂ},
      ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 → ∀ u ∈ Set.Icc (-L) L,
        ‖hughesYoungCentralReverseKernelPolynomial t
            ((1 : ℂ) + (u : ℂ) * I) z w‖ ≤ C := by
  let f₀₀ : ℝ → ℝ := fun u =>
    ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖
  let f₁₀ : ℝ → ℝ := fun u =>
    ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖
  let f₀₁ : ℝ → ℝ := fun u =>
    ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖
  let f₁₁ : ℝ → ℝ := fun u =>
    ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖
  have hc₀₀ : Continuous f₀₀ := by
    exact (continuous_hughesYoungEquation84Kernel00_sourceLine t).norm
  have hc₁₀ : Continuous f₁₀ := by
    exact (continuous_hughesYoungEquation84Kernel10_sourceLine t).norm
  have hc₀₁ : Continuous f₀₁ := by
    exact (continuous_hughesYoungEquation84Kernel01_sourceLine t).norm
  have hc₁₁ : Continuous f₁₁ := by
    exact (continuous_hughesYoungEquation84Kernel11_sourceLine t).norm
  obtain ⟨M₀₀, hM₀₀⟩ := isCompact_Icc.bddAbove_image hc₀₀.continuousOn
  obtain ⟨M₁₀, hM₁₀⟩ := isCompact_Icc.bddAbove_image hc₁₀.continuousOn
  obtain ⟨M₀₁, hM₀₁⟩ := isCompact_Icc.bddAbove_image hc₀₁.continuousOn
  obtain ⟨M₁₁, hM₁₁⟩ := isCompact_Icc.bddAbove_image hc₁₁.continuousOn
  let M : ℝ := max 1 M₀₀ + max 1 M₁₀ + max 1 M₀₁ + max 1 M₁₁
  let A : ℝ := 1 + δ / 4 + δ / 4 + (δ / 4) * (δ / 4)
  let C : ℝ := A * M
  have hM : 0 < M := by
    dsimp only [M]
    have h₀₀ : 0 < max 1 M₀₀ := lt_max_of_lt_left zero_lt_one
    have h₁₀ : 0 < max 1 M₁₀ := lt_max_of_lt_left zero_lt_one
    have h₀₁ : 0 < max 1 M₀₁ := lt_max_of_lt_left zero_lt_one
    have h₁₁ : 0 < max 1 M₁₁ := lt_max_of_lt_left zero_lt_one
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨C, mul_pos hA hM, ?_⟩
  intro z w hz hw u hu
  have hmax₀₀ : 0 < max 1 M₀₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmax₁₀ : 0 < max 1 M₁₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmax₀₁ : 0 < max 1 M₀₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmax₁₁ : 0 < max 1 M₁₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₀₀ : f₀₀ u ≤ M := by
    calc
      f₀₀ u ≤ M₀₀ := hM₀₀ ⟨u, hu, rfl⟩
      _ ≤ max 1 M₀₀ := le_max_right _ _
      _ ≤ M := by dsimp only [M]; linarith
  have hb₁₀ : f₁₀ u ≤ M := by
    calc
      f₁₀ u ≤ M₁₀ := hM₁₀ ⟨u, hu, rfl⟩
      _ ≤ max 1 M₁₀ := le_max_right _ _
      _ ≤ M := by dsimp only [M]; linarith
  have hb₀₁ : f₀₁ u ≤ M := by
    calc
      f₀₁ u ≤ M₀₁ := hM₀₁ ⟨u, hu, rfl⟩
      _ ≤ max 1 M₀₁ := le_max_right _ _
      _ ≤ M := by dsimp only [M]; linarith
  have hb₁₁ : f₁₁ u ≤ M := by
    calc
      f₁₁ u ≤ M₁₁ := hM₁₁ ⟨u, hu, rfl⟩
      _ ≤ max 1 M₁₁ := le_max_right _ _
      _ ≤ M := by dsimp only [M]; linarith
  have hM0 : 0 ≤ M := hM.le
  unfold hughesYoungCentralReverseKernelPolynomial
  calc
    _ ≤ f₁₁ u + ‖z‖ * f₁₀ u + ‖w‖ * f₀₁ u +
        (‖z‖ * ‖w‖) * f₀₀ u := by
      dsimp only [f₀₀, f₁₀, f₀₁, f₁₁]
      calc
        _ ≤ ‖hughesYoungEquation84Kernel11 t (1 + (u : ℂ) * I) +
                z * hughesYoungEquation84Kernel10 t (1 + (u : ℂ) * I) +
                w * hughesYoungEquation84Kernel01 t (1 + (u : ℂ) * I)‖ +
              ‖z * w * hughesYoungEquation84Kernel00 t (1 + (u : ℂ) * I)‖ :=
            norm_add_le _ _
        _ ≤ (‖hughesYoungEquation84Kernel11 t (1 + (u : ℂ) * I) +
                z * hughesYoungEquation84Kernel10 t (1 + (u : ℂ) * I)‖ +
              ‖w * hughesYoungEquation84Kernel01 t (1 + (u : ℂ) * I)‖) +
              ‖z * w * hughesYoungEquation84Kernel00 t (1 + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ ((‖hughesYoungEquation84Kernel11 t (1 + (u : ℂ) * I)‖ +
                ‖z * hughesYoungEquation84Kernel10 t (1 + (u : ℂ) * I)‖) +
              ‖w * hughesYoungEquation84Kernel01 t (1 + (u : ℂ) * I)‖) +
              ‖z * w * hughesYoungEquation84Kernel00 t (1 + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ M + (δ / 4) * M + (δ / 4) * M +
        ((δ / 4) * (δ / 4)) * M := by gcongr
    _ = C := by dsimp only [C, A]; ring

/-- Uniform compact-ordinate control of the undifferentiated Hughes--Young
source master on the entire closed shift bidisc.  The arithmetic jet is
bounded by its genuine equation-(98) Euler product and the archimedean part
by the preceding four-kernel compact estimate. -/
theorem exists_uniform_norm_hughesYoungCompletePositiveCentralMaster_source_compact
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {L δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ {z w : ℂ},
      ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 → ∀ u ∈ Set.Icc (-L) L,
        ‖hughesYoungCompletePositiveCentralMaster T t h k a b
            ((1 : ℂ) + (u : ℂ) * I) z w‖ ≤ C := by
  obtain ⟨K, hK, hStatic⟩ :=
    exists_uniform_norm_hughesYoungCompleteCentralStatic
      T t h k a b (δ := δ)
  obtain ⟨B, hB, hKernel⟩ :=
    exists_uniform_norm_hughesYoungCentralReverseKernelPolynomial_source_compact
      t (L := L) hδ0.le
  let r : ℝ := δ / 4
  let J : ℝ :=
    (Real.exp (4 * r * |Real.eulerMascheroniConstant|) *
        hughesYoungZetaHalfPlaneMajorant ^ 3 *
        (divisorEpsilonConstant ((1 : ℝ) / 5)) ^ 10) *
      ((a : ℝ) ^ (r + 1) * (b : ℝ) ^ (r + 1))
  let C : ℝ := K * (max 1 J) * B
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr8 : r < 1 / 8 := by dsimp only [r]; linarith
  have hJmax : 0 < max 1 J := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro z w hz hw u hu
  let W : ℂ := (1 : ℂ) + (u : ℂ) * I
  let q : ℂ := hughesYoungEquation96ContourParameter W
  have hq : -(1 / 4 : ℝ) ≤ q.re := by
    dsimp only [q, W, hughesYoungEquation96ContourParameter]
    norm_num [Complex.mul_re]
  have hjet : ‖hughesYoungEquation96ContinuationJet a b q z w‖ ≤ J := by
    simpa only [J, r] using
      norm_hughesYoungEquation96ContinuationJet_le_rpow
        (ε := (1 : ℝ)) (r := r) (by norm_num) hr0 hr8 ha hb hq hz hw
  have hstatic :
      ‖((a : ℂ) * b)⁻¹ *
          hughesYoungReducedMellinStaticComplex T t h k W‖ ≤ K := by
    have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
    simpa only [W] using hStatic u 1 ⟨hδ1, le_rfl⟩
  have hkernel :
      ‖hughesYoungCentralReverseKernelPolynomial t W z w‖ ≤ B := by
    simpa only [W] using hKernel hz hw u hu
  unfold hughesYoungCompletePositiveCentralMaster hughesYoungCentralMasterJet
  change ‖((((a : ℂ) * b)⁻¹ *
      hughesYoungReducedMellinStaticComplex T t h k W) *
        (hughesYoungEquation96ContinuationJet a b q z w *
          hughesYoungCentralReverseKernelPolynomial t W z w))‖ ≤ C
  calc
    _ = ‖((a : ℂ) * b)⁻¹ *
          hughesYoungReducedMellinStaticComplex T t h k W‖ *
        (‖hughesYoungEquation96ContinuationJet a b q z w‖ *
          ‖hughesYoungCentralReverseKernelPolynomial t W z w‖) := by
          simp only [norm_mul]
    _ ≤ K * ((max 1 J) * B) := mul_le_mul hstatic
      (mul_le_mul (hjet.trans (le_max_right _ _)) hkernel
        (norm_nonneg _) hJmax.le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
    _ = C := by dsimp only [C]; ring

/-- A single integrable source-line envelope works uniformly for every
auxiliary shift in the closed bidisc.  Outside the central ordinate interval
it is the proved Gaussian horizontal estimate; inside it is the compact
four-kernel bound. -/
theorem exists_integrable_uniform_hughesYoungCompletePositiveCentralMaster_source
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∀ {z w : ℂ},
      ‖z‖ ≤ δ / 4 → ‖w‖ ≤ δ / 4 → ∀ u : ℝ,
        ‖hughesYoungCompletePositiveCentralMaster T t h k a b
            ((1 : ℂ) + (u : ℂ) * I) z w‖ ≤ g u := by
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨Cₜ, hCₜ, htail⟩ :=
    exists_uniform_norm_hughesYoungCompletePositiveCentralMeromorphic_horizontal_le
      T t h k a b hδ0 hδ4
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    exists_uniform_norm_hughesYoungCompletePositiveCentralMaster_source_compact
      T t h k ha hb (L := L) hδ0 hδ4
  let gTail : ℝ → ℝ := fun u =>
    Cₜ * Real.exp (100 - 60 * u ^ 2) * (3 + |t| + |u|) ^ 11
  let gCompact : ℝ → ℝ :=
    (Set.Icc (-L) L).indicator (fun _ => C₀)
  let g : ℝ → ℝ := fun u => gTail u + gCompact u
  have hTailInt : Integrable gTail := by
    dsimp only [gTail]
    simpa only [mul_assoc] using
      (integrable_exp_sub_mul_sq_mul_add_abs_pow
        (100 : ℝ) (C := 3 + |t|) (by norm_num : (0 : ℝ) < 60) 11).const_mul Cₜ
  have hCompactInt : Integrable gCompact := by
    dsimp only [gCompact]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  refine ⟨g, hTailInt.add hCompactInt, ?_⟩
  intro z w hz hw u
  by_cases hu : L ≤ |u|
  · have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
    have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
    have hx : (1 : ℝ) ∈ Set.Icc δ 1 :=
      ⟨hδ4.le.trans (by norm_num), le_rfl⟩
    have hmain := htail hz hw u hu1 hut 1 hx
    rw [← hughesYoungCompletePositiveCentralMaster_eq_meromorphic] at hmain
    have hcompactNonneg : 0 ≤ gCompact u := by
      dsimp only [gCompact]
      exact Set.indicator_nonneg (fun _ _ => hC₀.le) _
    exact hmain.trans (by
      dsimp only [g, gTail]
      linarith)
  · have huLt : |u| < L := lt_of_not_ge hu
    have huIcc : u ∈ Set.Icc (-L) L := by
      exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    have hmain := hcompact hz hw u huIcc
    have htailNonneg : 0 ≤ gTail u := by
      dsimp only [gTail]
      positivity
    have hindicator : gCompact u = C₀ := by
      simp only [gCompact, Set.indicator_of_mem huIcc]
    exact hmain.trans (by
      dsimp only [g]
      rw [hindicator]
      linarith)


/-- Joint holomorphy in the two auxiliary shifts on the source vertical
line.  This is the analytic input used to differentiate the improper
integral, not merely separate pointwise differentiability. -/
theorem analyticAt_hughesYoungCompletePositiveCentralMaster_sourceAuxiliary
    (T t : ℝ) (h k a b : ℕ) {u : ℝ} {z w : ℂ}
    (hz : ‖z‖ < 1 / 8) (hw : ‖w‖ < 1 / 8) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungCompletePositiveCentralMaster T t h k a b
          ((1 : ℂ) + (u : ℂ) * I) p.1 p.2)
      (z, w) := by
  let W : ℂ := (1 : ℂ) + (u : ℂ) * I
  let q : ℂ := hughesYoungEquation96ContourParameter W
  let J : ℂ × ℂ → ℂ := fun p =>
    hughesYoungEquation96ContinuationJet a b q p.1 p.2
  let P : ℂ × ℂ → ℂ := fun p =>
    hughesYoungCentralReverseKernelPolynomial t W p.1 p.2
  have hq : -(1 / 4 : ℝ) < q.re := by
    dsimp only [q, W, hughesYoungEquation96ContourParameter]
    norm_num [Complex.mul_re]
  have hJ : AnalyticAt ℂ J (z, w) := by
    have hraw := analyticAt_hughesYoungEquation96ContinuationJet_all
      (h := a) (k := b) (q := q) (z := z) (w := w) hq hz hw
    simpa only [J] using hraw.curry_right
  have hP : AnalyticAt ℂ P (z, w) := by
    dsimp only [P, hughesYoungCentralReverseKernelPolynomial]
    fun_prop
  let O : ℂ := (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W
  have hmaster : AnalyticAt ℂ (fun p => O * (J p * P p)) (z, w) :=
    (analyticAt_const.mul (hJ.mul hP))
  simpa only [O, J, P, W, hughesYoungCompletePositiveCentralMaster,
    hughesYoungCentralMasterJet] using hmaster

/-- The two Hughes--Young auxiliary derivatives commute with the complete
source-line contour integral.  The right-hand side is the actual continued
equation-(84) coefficient, not an abstract derivative family. -/
theorem deriv_right_deriv_left_hughesYoungCompletePositiveCentralMaster_sourceIntegral
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) :
    deriv (fun w => deriv (fun z => ∫ u : ℝ,
      hughesYoungCompletePositiveCentralMaster T t h k a b
        ((1 : ℂ) + (u : ℂ) * I) z w) 0) 0 =
      ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I) := by
  let R : ℝ := δ / 4
  let F : ℂ → ℂ → ℝ → ℂ := fun z w u =>
    hughesYoungCompletePositiveCentralMaster T t h k a b
      ((1 : ℂ) + (u : ℂ) * I) z w
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR8 : R < 1 / 8 := by dsimp only [R]; linarith
  obtain ⟨g, hg, hbound⟩ :=
    exists_integrable_uniform_hughesYoungCompletePositiveCentralMaster_source
      T t h k ha hb hδ0 hδ4
  have hAnalytic : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R,
        AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2 u) (z, w) := by
    intro u z hz w hw
    have hz8 : ‖z‖ < 1 / 8 := by
      have hzR : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
      exact hzR.trans hR8
    have hw8 : ‖w‖ < 1 / 8 := by
      have hwR : ‖w‖ < R := by simpa [mem_ball, dist_zero_right] using hw
      exact hwR.trans hR8
    simpa only [F] using
      analyticAt_hughesYoungCompletePositiveCentralMaster_sourceAuxiliary
        T t h k a b hz8 hw8
  have hFmeas : ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R,
      AEStronglyMeasurable (F z w) := by
    intro z hz w hw
    have hzle : ‖z‖ ≤ δ / 4 := by
      have hz' : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
      simpa only [R] using hz'.le
    have hwle : ‖w‖ ≤ δ / 4 := by
      have hw' : ‖w‖ < R := by simpa [mem_ball, dist_zero_right] using hw
      simpa only [R] using hw'.le
    have hc : AEStronglyMeasurable (fun u : ℝ =>
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((1 : ℂ) + (u : ℂ) * I)) :=
      (continuous_hughesYoungCompletePositiveCentralMeromorphic_vertical
        T t h k a b hδ0 hδ4 hzle hwle (Or.inr rfl)).aestronglyMeasurable
    have heq : F z w = fun u : ℝ =>
        hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
          ((1 : ℂ) + (u : ℂ) * I) := by
      funext u
      exact hughesYoungCompletePositiveCentralMaster_eq_meromorphic
        T t h k a b ((1 : ℂ) + (u : ℂ) * I) z w
    rwa [heq]
  have hFzmeas : ∀ w ∈ ball (0 : ℂ) (R / 4),
      AEStronglyMeasurable (fun u => deriv (fun z => F z w u) 0) := by
    intro w hw
    have hw8 : ‖w‖ < 1 / 8 := by
      have hwSmall : ‖w‖ < R / 4 := by
        simpa [mem_ball, dist_zero_right] using hw
      exact hwSmall.trans (by dsimp only [R]; linarith)
    simpa only [F] using
      (continuous_deriv_left_hughesYoungCompletePositiveCentralMaster_source
        T t h k a b hw8).aestronglyMeasurable
  have hFzwmeas : AEStronglyMeasurable
      (fun u => deriv (fun w => deriv (fun z => F z w u) 0) 0) := by
    have hc : AEStronglyMeasurable (fun u : ℝ =>
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((1 : ℂ) + (u : ℂ) * I)) :=
      (continuous_hughesYoungCompletePositiveCentralContinuation_vertical
        T t h k a b (c := (1 : ℝ)) ⟨by norm_num, le_rfl⟩).aestronglyMeasurable
    have heq : (fun u => deriv (fun w => deriv (fun z => F z w u) 0) 0) =
        fun u : ℝ => hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I) := by
      funext u
      simpa only [F] using
        deriv_right_deriv_left_hughesYoungCompletePositiveCentralMaster_zero
          T t h k ((1 : ℂ) + (u : ℂ) * I) (by norm_num [Complex.mul_re])
    rwa [heq]
  have hEnvelope : ∀ u : ℝ, ∀ z ∈ ball (0 : ℂ) R,
      ∀ w ∈ ball (0 : ℂ) R, ‖F z w u‖ ≤ g u := by
    intro u z hz w hw
    have hzle : ‖z‖ ≤ δ / 4 := by
      have hz' : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
      simpa only [R] using hz'.le
    have hwle : ‖w‖ ≤ δ / 4 := by
      have hw' : ‖w‖ < R := by simpa [mem_ball, dist_zero_right] using hw
      simpa only [R] using hw'.le
    exact hbound hzle hwle u
  have hdiff := deriv_right_deriv_left_integral_of_analytic_dominated
    F hR hAnalytic hFmeas hFzmeas hFzwmeas g hg hEnvelope
  change deriv (fun w => deriv (fun z => ∫ u : ℝ, F z w u) 0) 0 = _
  calc
    _ = ∫ u : ℝ, deriv (fun w => deriv (fun z => F z w u) 0) 0 := hdiff
    _ = ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with u
      simpa only [F] using
        deriv_right_deriv_left_hughesYoungCompletePositiveCentralMaster_zero
          T t h k ((1 : ℂ) + (u : ℂ) * I) (by norm_num [Complex.mul_re])

/-- Differentiated whole-line residue crossing.  The low-contour integral
and the moving residue remain combined until after both auxiliary
derivatives, exactly as in the Hughes--Young cancellation. -/
theorem integral_hughesYoungCompletePositiveCentralContinuation_eq_mixedDeriv_low_add_residue
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) :
    (∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation
        T t h k a b ((1 : ℂ) + (u : ℂ) * I)) =
      deriv (fun w => deriv (fun z =>
        (∫ u : ℝ,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((δ : ℂ) + (u : ℂ) * I)) +
        (Real.pi : ℂ) *
          hughesYoungCompletePositiveCentralPoleFree T t h k a b
            (hughesYoungCentralMovingPole z w) z w) 0) 0 := by
  let A : ℂ → ℂ → ℂ := fun z w => ∫ u : ℝ,
    hughesYoungCompletePositiveCentralMaster T t h k a b
      ((1 : ℂ) + (u : ℂ) * I) z w
  let B : ℂ → ℂ → ℂ := fun z w => ∫ u : ℝ,
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
      ((δ : ℂ) + (u : ℂ) * I)
  let P : ℂ → ℂ → ℂ := fun z w =>
    hughesYoungCompletePositiveCentralPoleFree T t h k a b
      (hughesYoungCentralMovingPole z w) z w
  have hlocal : ∀ {z w : ℂ}, ‖z‖ < δ / 4 → ‖w‖ < δ / 4 →
      A z w = B z w + (Real.pi : ℂ) * P z w := by
    intro z w hz hw
    have hshift := hughesYoungCompletePositiveCentralMaster_verticalIntegral_shift
      T t h k a b hδ0 hδ4 hz hw
    dsimp only [A, B, P]
    have hsourceEq : (∫ u : ℝ,
        hughesYoungCompletePositiveCentralMaster T t h k a b
          ((1 : ℂ) + (u : ℂ) * I) z w) =
        ∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
          T t h k a b z w ((1 : ℂ) + (u : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with u
      exact hughesYoungCompletePositiveCentralMaster_eq_meromorphic
        T t h k a b ((1 : ℂ) + (u : ℂ) * I) z w
    rw [hsourceEq]
    have hc : (((1 / (2 * Real.pi) : ℝ) : ℂ)) ≠ 0 := by
      have hcReal : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by
        exact one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact_mod_cast hcReal
    have hscalar : (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (Real.pi : ℂ) = (2 : ℂ)⁻¹ := by
      push_cast
      field_simp [Real.pi_ne_zero]
    apply (mul_left_cancel₀ hc)
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((1 : ℂ) + (u : ℂ) * I)) =
        ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((1 : ℂ) + (u : ℂ) * I)) -
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((δ : ℂ) + (u : ℂ) * I))) +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((δ : ℂ) + (u : ℂ) * I)) := by ring
      _ = (2 : ℂ)⁻¹ * P z w +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((δ : ℂ) + (u : ℂ) * I)) := by rw [hshift]
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((δ : ℂ) + (u : ℂ) * I)) +
          (2 : ℂ)⁻¹ * P z w := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ((∫ u : ℝ, hughesYoungCompletePositiveCentralMeromorphic
            T t h k a b z w ((δ : ℂ) + (u : ℂ) * I)) +
            (Real.pi : ℂ) * P z w) := by
          rw [mul_add, ← mul_assoc, hscalar]
  have hinner : ∀ᶠ w in nhds (0 : ℂ),
      deriv (fun z => A z w) 0 = deriv (fun z => B z w + (Real.pi : ℂ) * P z w) 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < δ / 4)] with w hw
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : 0 < δ / 4)] with z hz
    apply hlocal
    · simpa [mem_ball, dist_zero_right] using hz
    · simpa [mem_ball, dist_zero_right] using hw
  have hmixed := Filter.EventuallyEq.deriv_eq hinner
  rw [← deriv_right_deriv_left_hughesYoungCompletePositiveCentralMaster_sourceIntegral
    T t h k ha hb hδ0 hδ4]
  simpa only [A, B, P] using hmixed

theorem hughesYoungAuxiliaryZero_movingPole (z w : ℂ) :
    hughesYoungAuxiliaryZero (hughesYoungCentralMovingPole z w) =
      (z + w) ^ 4 * (2 + z + w) ^ 4 := by
  unfold hughesYoungAuxiliaryZero hughesYoungCentralMovingPole
  ring

theorem analyticAt_hughesYoungEquation96PoleFreeMasterJet_movingPole
    (a b : ℕ) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungEquation96PoleFreeMasterJet a b
          (hughesYoungCentralMovingPole p.1 p.2) p.1 p.2) (0, 0) := by
  let qmap : ℂ × ℂ → ℂ := fun p => p.1 + p.2 - 1
  let emap : ℂ × ℂ → ℂ × (ℂ × ℂ) := fun p => (qmap p, (p.1, p.2))
  let eswap : ℂ × ℂ → ℂ × (ℂ × ℂ) := fun p => (qmap p, (p.2, p.1))
  have hemap : AnalyticAt ℂ emap (0, 0) := by
    dsimp only [emap, qmap]
    fun_prop
  have heswap : AnalyticAt ℂ eswap (0, 0) := by
    dsimp only [eswap, qmap]
    fun_prop
  have hCaRaw := analyticAt_hughesYoungC_shiftedJet_all
    a (q := (-1 : ℂ)) (z := 0) (w := 0)
      (by norm_num) (by norm_num) (by norm_num)
  have hCbRaw := analyticAt_hughesYoungC_shiftedJet_all
    b (q := (-1 : ℂ)) (z := 0) (w := 0)
      (by norm_num) (by norm_num) (by norm_num)
  have hCa := hCaRaw.comp' hemap
  have hCb := hCbRaw.comp' heswap
  have harg : AnalyticAt ℂ
      (fun p : ℂ × ℂ => 2 + 2 * p.1 + 2 * p.2) (0, 0) := by fun_prop
  have hzeta : AnalyticAt ℂ
      (fun p : ℂ × ℂ => riemannZeta (2 + 2 * p.1 + 2 * p.2)) (0, 0) :=
    (analyticAt_riemannZeta (by norm_num)).comp' harg
  have hzeta0 : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hquot := hzeta.div hzeta hzeta0
  have hexp : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      Complex.exp (p.1 * hughesYoungEquation96LeftConstant a +
        p.2 * hughesYoungEquation96RightConstant b)) (0, 0) := by fun_prop
  have hall := hexp.mul (hquot.mul (hCa.mul hCb))
  unfold hughesYoungEquation96PoleFreeMasterJet
  convert hall using 1
  · funext p
    dsimp only [emap, eswap, qmap, hughesYoungCentralMovingPole] at hCa hCb ⊢
    ring
  · norm_num

private theorem analyticAt_oneHalf_of_differentiableAt_centralStrip
    {f : ℂ → ℂ}
    (hf : ∀ {W : ℂ}, 0 < W.re → W.re < 3 / 2 → DifferentiableAt ℂ f W) :
    AnalyticAt ℂ f (1 / 2 : ℂ) := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with W hW
  rw [mem_ball] at hW
  have hnorm : ‖W - (1 / 2 : ℂ)‖ < 1 / 4 := by
    simpa [dist_eq] using hW
  have hre : |W.re - 1 / 2| < 1 / 4 := by
    calc
      |W.re - 1 / 2| = |(W - (1 / 2 : ℂ)).re| := by simp
      _ ≤ ‖W - (1 / 2 : ℂ)‖ := abs_re_le_norm _
      _ < 1 / 4 := hnorm
  apply hf
  · linarith [neg_abs_le (W.re - 1 / 2)]
  · linarith [le_abs_self (W.re - 1 / 2)]

theorem analyticAt_hughesYoungCompletePositiveCentralPoleFreeCore_movingPole
    (T t : ℝ) (h k a b : ℕ) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        (2 + p.1 + p.2) ^ 4 *
          hughesYoungCompletePositiveCentralPoleFreeCore T t h k a b
            (hughesYoungCentralMovingPole p.1 p.2) p.1 p.2) (0, 0) := by
  let m : ℂ × ℂ → ℂ := fun p => hughesYoungCentralMovingPole p.1 p.2
  have hm : AnalyticAt ℂ m (0, 0) := by
    dsimp only [m, hughesYoungCentralMovingPole]
    fun_prop
  have hMellinAll : Differentiable ℂ
      (hughesYoungReducedMellinStaticComplex T t h k) :=
    fun W => differentiableAt_hughesYoungReducedMellinStaticComplex T t h k W
  have hMellin : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungReducedMellinStaticComplex T t h k (m p))
      (0, 0) := hMellinAll.analyticAt.comp' hm
  have hJet := analyticAt_hughesYoungEquation96PoleFreeMasterJet_movingPole a b
  have hK00 : AnalyticAt ℂ (hughesYoungEquation84KernelCore00 t) (1 / 2 : ℂ) :=
    analyticAt_oneHalf_of_differentiableAt_centralStrip
      (fun h0 h3 => differentiableAt_hughesYoungEquation84KernelCore00 t h0 h3)
  have hK10 : AnalyticAt ℂ (hughesYoungEquation84KernelCore10 t) (1 / 2 : ℂ) :=
    analyticAt_oneHalf_of_differentiableAt_centralStrip
      (fun h0 h3 => differentiableAt_hughesYoungEquation84KernelCore10 t h0 h3)
  have hK01 : AnalyticAt ℂ (hughesYoungEquation84KernelCore01 t) (1 / 2 : ℂ) :=
    analyticAt_oneHalf_of_differentiableAt_centralStrip
      (fun h0 h3 => differentiableAt_hughesYoungEquation84KernelCore01 t h0 h3)
  have hK11 : AnalyticAt ℂ (hughesYoungEquation84KernelCore11 t) (1 / 2 : ℂ) :=
    analyticAt_oneHalf_of_differentiableAt_centralStrip
      (fun h0 h3 => differentiableAt_hughesYoungEquation84KernelCore11 t h0 h3)
  have h00 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84KernelCore00 t (m p)) (0, 0) :=
    hK00.comp' hm
  have h10 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84KernelCore10 t (m p)) (0, 0) :=
    hK10.comp' hm
  have h01 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84KernelCore01 t (m p)) (0, 0) :=
    hK01.comp' hm
  have h11 : AnalyticAt ℂ
      (fun p : ℂ × ℂ => hughesYoungEquation84KernelCore11 t (m p)) (0, 0) :=
    hK11.comp' hm
  have hz : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (0, 0) := by fun_prop
  have hw : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (0, 0) := by fun_prop
  have hReverse : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        hughesYoungCentralReverseKernelPolynomialCore t (m p) p.1 p.2) (0, 0) := by
    unfold hughesYoungCentralReverseKernelPolynomialCore
    exact (((h11.add (hz.mul h10)).add (hw.mul h01)).add
      ((hz.mul hw).mul h00))
  have hscale : AnalyticAt ℂ (fun p : ℂ × ℂ => (2 + p.1 + p.2) ^ 4) (0, 0) := by
    fun_prop
  have hall := hscale.mul ((analyticAt_const.mul hMellin).mul (hJet.mul hReverse))
  simpa only [m, hughesYoungCompletePositiveCentralPoleFreeCore,
    mul_assoc] using hall

/-- Once the analytic core of the moving residue is exposed, the prescribed
fourth-order Hughes--Young auxiliary zero kills its mixed derivative. -/
theorem deriv_right_deriv_left_hughesYoungCompletePositiveCentralPoleFree_movingPole_zero_of_analytic
    (T t : ℝ) (h k a b : ℕ)
    (hcore : AnalyticAt ℂ
      (fun p : ℂ × ℂ =>
        (2 + p.1 + p.2) ^ 4 *
          hughesYoungCompletePositiveCentralPoleFreeCore T t h k a b
            (hughesYoungCentralMovingPole p.1 p.2) p.1 p.2) (0, 0)) :
    deriv (fun w => deriv (fun z =>
      hughesYoungCompletePositiveCentralPoleFree T t h k a b
        (hughesYoungCentralMovingPole z w) z w) 0) 0 = 0 := by
  let F : ℂ × ℂ → ℂ := fun p =>
    (2 + p.1 + p.2) ^ 4 *
      hughesYoungCompletePositiveCentralPoleFreeCore T t h k a b
        (hughesYoungCentralMovingPole p.1 p.2) p.1 p.2
  have hpoint : ∀ z w : ℂ,
      hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w =
        (z + w) ^ 4 * F (z, w) := by
    intro z w
    rw [hughesYoungCompletePositiveCentralPoleFree_eq_auxiliary_mul_core,
      hughesYoungAuxiliaryZero_movingPole]
    dsimp only [F]
    ring
  have hinner : ∀ w : ℂ,
      deriv (fun z => hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w) 0 =
        deriv (fun z => (z + w) ^ 4 * F (z, w)) 0 := by
    intro w
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.Eventually.of_forall (fun z => hpoint z w)
  rw [show (fun w => deriv (fun z =>
      hughesYoungCompletePositiveCentralPoleFree T t h k a b
        (hughesYoungCentralMovingPole z w) z w) 0) =
      (fun w => deriv (fun z => (z + w) ^ 4 * F (z, w)) 0) by
        funext w
        exact hinner w]
  exact deriv_right_deriv_left_add_pow_four_mul_zero (by simpa only [F] using hcore)

theorem deriv_right_deriv_left_hughesYoungCompletePositiveCentralPoleFree_movingPole_zero
    (T t : ℝ) (h k a b : ℕ) :
    deriv (fun w => deriv (fun z =>
      hughesYoungCompletePositiveCentralPoleFree T t h k a b
        (hughesYoungCentralMovingPole z w) z w) 0) 0 = 0 :=
  deriv_right_deriv_left_hughesYoungCompletePositiveCentralPoleFree_movingPole_zero_of_analytic
    T t h k a b
      (analyticAt_hughesYoungCompletePositiveCentralPoleFreeCore_movingPole
        T t h k a b)

end RiemannZeta.GuthMaynard
