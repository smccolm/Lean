import GafniTao.FordKHorizontal
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Ford's `K(s)` right vertical line

Absolute convergence of the von Mangoldt Dirichlet series on `Re w = alpha
> 1` permits termwise integration against Ford's literal `F₀(s-w)`.
Each normalized term is then the already formalized finite inverse-Laplace
integral `fordJTrunc`.
-/

open Complex Set Filter MeasureTheory
open scoped BigOperators Interval Topology
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- One von Mangoldt Dirichlet-series term in Ford's right-line integral. -/
noncomputable def fordKRightSeriesTerm
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((alpha : ℂ) + (u : ℂ) * I) n *
    F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))

private theorem norm_fordKRight_LSeriesTerm_vertical_eq
    {alpha u : ℝ} (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((alpha : ℂ) + (u : ℂ) * I) n‖ =
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (alpha : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    congr 1
    change
      ‖((n : ℝ) : ℂ) ^ ((alpha : ℂ) + (u : ℂ) * I)‖ =
        ‖((n : ℝ) : ℂ) ^ (alpha : ℂ)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp

private theorem fordKRight_weight_re
    (s : ℂ) (alpha u : ℝ) :
    (s - ((alpha : ℂ) + (u : ℂ) * I)).re = s.re - alpha := by
  simp

private theorem fordKRight_weight_norm_lower
    {s : ℂ} {alpha u : ℝ} :
    s.re - alpha ≤ ‖s - ((alpha : ℂ) + (u : ℂ) * I)‖ := by
  rw [← fordKRight_weight_re s alpha u]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

theorem norm_fordKRightSeriesTerm_le
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta : ℝ}
    (ha : alpha < s.re) (hD : 0 ≤ D) (heta : eta ≤ s.re - alpha)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (n : ℕ) (u : ℝ) :
    ‖fordKRightSeriesTerm F₀ s alpha n u‖ ≤
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * (D / (s.re - alpha) ^ 2) := by
  let z := s - ((alpha : ℂ) + (u : ℂ) * I)
  have hzre : z.re = s.re - alpha := fordKRight_weight_re s alpha u
  have hzreNonneg : 0 ≤ z.re := by rw [hzre]; linarith
  have hzlower : s.re - alpha ≤ ‖z‖ := fordKRight_weight_norm_lower
  have hetaNorm : eta ≤ ‖z‖ := heta.trans hzlower
  have hF := hF₀ z hzreNonneg hetaNorm
  have haPos : 0 < s.re - alpha := sub_pos.mpr ha
  have hzPos : 0 < ‖z‖ := haPos.trans_le hzlower
  have hquot : D / ‖z‖ ^ 2 ≤ D / (s.re - alpha) ^ 2 := by
    exact div_le_div_of_nonneg_left hD (sq_pos_of_pos haPos)
      ((sq_le_sq₀ haPos.le (norm_nonneg z)).2 hzlower)
  rw [fordKRightSeriesTerm, norm_mul,
    norm_fordKRight_LSeriesTerm_vertical_eq n]
  exact mul_le_mul_of_nonneg_left (hF.trans hquot) (norm_nonneg _)

private theorem aestronglyMeasurable_fordKRightSeriesTerm
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha : ℝ}
    (ha : alpha < s.re)
    (hF₀ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (n : ℕ) :
    AEStronglyMeasurable (fordKRightSeriesTerm F₀ s alpha n) volume := by
  have hw : Continuous (fun u : ℝ =>
      s - ((alpha : ℂ) + (u : ℂ) * I)) := by fun_prop
  have hFcont : Continuous (fun u : ℝ =>
      F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (hF₀ _ ?_).continuousAt.comp_of_eq (hw.continuousAt) rfl
    rw [fordKRight_weight_re]
    linarith
  by_cases hn : n = 0
  · subst n
    have hzero : fordKRightSeriesTerm F₀ s alpha 0 =
        fun _ : ℝ => (0 : ℂ) := by
      funext u
      rw [fordKRightSeriesTerm, LSeries.term_def]
      simp
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hline : Continuous (fun u : ℝ =>
        (alpha : ℂ) + (u : ℂ) * I) := by fun_prop
    have hnpow : Continuous (fun u : ℝ =>
        (n : ℂ) ^ ((alpha : ℂ) + (u : ℂ) * I)) := by
      exact Continuous.cpow continuous_const hline
        (fun _ => Complex.natCast_mem_slitPlane.mpr hn)
    have hnpowNe : ∀ u : ℝ,
        (n : ℂ) ^ ((alpha : ℂ) + (u : ℂ) * I) ≠ 0 := by
      intro u
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast hn)
    have hterm : Continuous (fun u : ℝ =>
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((alpha : ℂ) + (u : ℂ) * I) n) := by
      simp_rw [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnpow hnpowNe
    exact (hterm.mul hFcont).aestronglyMeasurable

/-- Absolute convergence on the right line justifies Ford's termwise
integration over every finite selected height. -/
theorem hasSum_integral_fordKRightSeriesTerm
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta R : ℝ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    HasSum
      (fun n : ℕ => ∫ u in (-R)..R, fordKRightSeriesTerm F₀ s alpha n u)
      (∫ u in (-R)..R,
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((alpha : ℂ) + (u : ℂ) * I) *
          F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by
  have hSeries : LSeriesSummable
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (alpha : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using halpha)
  have hBoundSummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * (D / (s.re - alpha) ^ 2)) :=
    hSeries.norm.mul_right (D / (s.re - alpha) ^ 2)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := fordKRightSeriesTerm F₀ s alpha)
    (f := fun u =>
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((alpha : ℂ) + (u : ℂ) * I) *
        F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)))
    (bound := fun n _u =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * (D / (s.re - alpha) ^ 2)) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (aestronglyMeasurable_fordKRightSeriesTerm ha hdiff n).mono_measure
      Measure.restrict_le_self
  · intro n
    exact ae_of_all _ fun u _hu =>
      norm_fordKRightSeriesTerm_le ha hD heta hF₀ n u
  · exact ae_of_all _ fun _u _hu => hBoundSummable
  · simp only [tsum_mul_right]
    exact intervalIntegrable_const
  · exact ae_of_all _ fun u _hu => by
      have hre : 1 < ((alpha : ℂ) + (u : ℂ) * I).re := by
        simpa using halpha
      have hsum :=
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hre).LSeriesHasSum
      simpa [fordKRightSeriesTerm] using hsum.mul_right
        (F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)))

/-- Each normalized right-line Dirichlet-series term is Ford's literal
finite inverse-Laplace term. -/
theorem normalized_integral_fordKRightSeriesTerm_eq
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ u in (-R)..R, fordKRightSeriesTerm F₀ s alpha n u =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp [fordKRightSeriesTerm, LSeries.term_def]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [fordJTrunc_log_nat_eq_cpow F₀ s alpha R hnPos]
    simp only [fordKRightSeriesTerm, LSeries.term_of_ne_zero hn]
    calc
      (1 / (2 * Real.pi) : ℂ) *
          ∫ u in (-R)..R,
            (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ ((alpha : ℂ) + (u : ℂ) * I) *
              F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)) =
        (1 / (2 * Real.pi) : ℂ) *
          ∫ u in (-R)..R,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^ (-((alpha : ℂ) + (u : ℂ) * I)) *
                F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro u _hu
          change (ArithmeticFunction.vonMangoldt n : ℂ) /
              (n : ℂ) ^ ((alpha : ℂ) + (u : ℂ) * I) *
                F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)) =
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^ (-((alpha : ℂ) + (u : ℂ) * I)) *
                F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)))
          rw [Complex.cpow_neg]
          simp only [inv_eq_one_div]
          ring
      _ = (1 / (2 * Real.pi) : ℂ) *
          ((ArithmeticFunction.vonMangoldt n : ℂ) *
            ∫ u in (-R)..R,
              (n : ℂ) ^ (-((alpha : ℂ) + (u : ℂ) * I)) *
                F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((1 / (2 * Real.pi) : ℂ) *
            ∫ u in (-R)..R,
              (n : ℂ) ^ (-((alpha : ℂ) + (u : ℂ) * I)) *
                F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by ring

/-- The translated Cauchy envelope governing the complete right-line
inverse-Laplace integral. -/
noncomputable def fordKRightEnvelope (s : ℂ) (alpha u : ℝ) : ℝ :=
  1 / ((s.re - alpha) ^ 2 + (s.im - u) ^ 2)

theorem integrable_fordKRightEnvelope
    {s : ℂ} {alpha : ℝ} (ha : alpha < s.re) :
    Integrable (fordKRightEnvelope s alpha) := by
  let a := s.re - alpha
  have haPos : 0 < a := by dsimp [a]; linarith
  let f : ℝ → ℝ := fun v => 1 / (a ^ 2 + v ^ 2)
  have hf : Integrable f := integrable_ford_inv_quadratic a haPos
  have hcomp := (MeasureTheory.integrable_comp_sub_left f s.im).2 hf
  simpa only [fordKRightEnvelope, one_div] using hcomp

theorem norm_sq_fordKRight_weight
    (s : ℂ) (alpha u : ℝ) :
    ‖s - ((alpha : ℂ) + (u : ℂ) * I)‖ ^ 2 =
      (s.re - alpha) ^ 2 + (s.im - u) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_fordKRightSeriesTerm_le_envelope
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta : ℝ}
    (ha : alpha < s.re) (heta : eta ≤ s.re - alpha)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (n : ℕ) (u : ℝ) :
    ‖fordKRightSeriesTerm F₀ s alpha n u‖ ≤
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * D * fordKRightEnvelope s alpha u := by
  let z := s - ((alpha : ℂ) + (u : ℂ) * I)
  have hzre : z.re = s.re - alpha := fordKRight_weight_re s alpha u
  have hzreNonneg : 0 ≤ z.re := by rw [hzre]; linarith
  have hzlower : s.re - alpha ≤ ‖z‖ := fordKRight_weight_norm_lower
  have hetaNorm : eta ≤ ‖z‖ := heta.trans hzlower
  have hF := hF₀ z hzreNonneg hetaNorm
  rw [fordKRightSeriesTerm, norm_mul,
    norm_fordKRight_LSeriesTerm_vertical_eq n]
  calc
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * ‖F₀ z‖ ≤
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * (D / ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    _ = ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (alpha : ℂ) n‖ * D * fordKRightEnvelope s alpha u := by
      rw [norm_sq_fordKRight_weight]
      simp only [fordKRightEnvelope]
      ring

/-- A height-independent summable majorant for every normalized finite
right-line term. -/
theorem norm_vonMangoldt_mul_fordJTrunc_le
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta R : ℝ}
    (ha : alpha < s.re) (hD : 0 ≤ D) (heta : eta ≤ s.re - alpha)
    (hR : 0 ≤ R)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (n : ℕ) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n)‖ ≤
      (1 / (2 * Real.pi)) *
        (‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            (alpha : ℂ) n‖ * D) *
          ∫ u : ℝ, fordKRightEnvelope s alpha u := by
  let A := ‖LSeries.term
    (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (alpha : ℂ) n‖ * D
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) hD
  have henv := integrable_fordKRightEnvelope ha
  have hmajorInt : Integrable (fun u : ℝ => A * fordKRightEnvelope s alpha u) :=
    henv.const_mul A
  have htermInt : Integrable (fordKRightSeriesTerm F₀ s alpha n) := by
    apply hmajorInt.mono'
    · exact aestronglyMeasurable_fordKRightSeriesTerm ha hdiff n
    · filter_upwards [] with u
      exact norm_fordKRightSeriesTerm_le_envelope ha heta hF₀ n u
  have hmono :
      (∫ u in (-R)..R, ‖fordKRightSeriesTerm F₀ s alpha n u‖) ≤
        ∫ u in (-R)..R, A * fordKRightEnvelope s alpha u := by
    apply intervalIntegral.integral_mono_on (by linarith)
      htermInt.norm.intervalIntegrable hmajorInt.intervalIntegrable
    intro u _hu
    exact norm_fordKRightSeriesTerm_le_envelope ha heta hF₀ n u
  have hsubset :
      (∫ u in (-R)..R, A * fordKRightEnvelope s alpha u) ≤
        ∫ u : ℝ, A * fordKRightEnvelope s alpha u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply MeasureTheory.setIntegral_le_integral hmajorInt
    exact ae_of_all _ fun u => mul_nonneg hA (by
      unfold fordKRightEnvelope
      positivity)
  rw [← normalized_integral_fordKRightSeriesTerm_eq F₀ s alpha R n]
  have hscalar : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    ‖(1 / (2 * Real.pi) : ℂ) *
        ∫ u in (-R)..R, fordKRightSeriesTerm F₀ s alpha n u‖ ≤
      (1 / (2 * Real.pi)) *
        ‖∫ u in (-R)..R, fordKRightSeriesTerm F₀ s alpha n u‖ := by
          rw [norm_mul, hscalar]
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ u in (-R)..R, ‖fordKRightSeriesTerm F₀ s alpha n u‖) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm (by linarith))
        (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ u in (-R)..R, A * fordKRightEnvelope s alpha u) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ u : ℝ, A * fordKRightEnvelope s alpha u) :=
      mul_le_mul_of_nonneg_left hsubset (by positivity)
    _ = (1 / (2 * Real.pi)) * A *
        ∫ u : ℝ, fordKRightEnvelope s alpha u := by
      rw [MeasureTheory.integral_const_mul]
      ring

/-- Ford's `D / |z|²` hypothesis makes the complete inverse-Laplace line
absolutely integrable for the actual pole-subtracted source. -/
theorem integrable_fordLaplaceRemainder_rightLine
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta x : ℝ}
    (ha : alpha < s.re) (heta : eta ≤ s.re - alpha)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    Integrable (fun v : ℝ =>
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral (fordLaplaceRemainder f)
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I)) := by
  let sigma : ℝ := s.re - alpha
  let z : ℝ → ℂ := fun v => (sigma : ℂ) + (v : ℂ) * I
  let M : ℝ → ℝ := fun v =>
    Real.exp (sigma * x) * D * (1 / (sigma ^ 2 + v ^ 2))
  have hsigma : 0 < sigma := by dsimp [sigma]; linarith
  have hzre (v : ℝ) : (z v).re = sigma := by simp [z]
  have heq (v : ℝ) :
      laplaceTransformBilateral (fordLaplaceRemainder f) (z v) =
        fordLaplaceF0 f (z v) := by
    apply laplaceTransformBilateral_fordLaplaceRemainder_eq
    · simpa [hzre] using hsigma
    · exact hAbs (z v) (by simpa [hzre] using hsigma)
  have hzcont : Continuous z := by
    dsimp [z]
    fun_prop
  have hFcont : Continuous (fun v : ℝ => fordLaplaceF0 f (z v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact (hdiff (z v) (by simpa [hzre] using hsigma)).continuousAt.comp_of_eq
      hzcont.continuousAt rfl
  have hsourceCont : Continuous (fun v : ℝ =>
      Complex.exp ((z v) * (x : ℂ)) * fordLaplaceF0 f (z v)) := by
    exact (Complex.continuous_exp.comp (hzcont.mul continuous_const)).mul hFcont
  have hmeas : AEStronglyMeasurable (fun v : ℝ =>
      Complex.exp ((z v) * (x : ℂ)) *
        laplaceTransformBilateral (fordLaplaceRemainder f) (z v)) volume := by
    apply hsourceCont.aestronglyMeasurable.congr
    filter_upwards with v
    rw [heq]
  have hbase : Integrable (fun v : ℝ => 1 / (sigma ^ 2 + v ^ 2)) :=
    integrable_ford_inv_quadratic sigma hsigma
  have hM : Integrable M := by
    simpa only [M] using hbase.const_mul (Real.exp (sigma * x) * D)
  apply hM.mono' hmeas
  filter_upwards with v
  have hnormLower : sigma ≤ ‖z v‖ := by
    rw [← hzre]
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hbound := hF₀ (z v) (by rw [hzre]; exact hsigma.le)
    (heta.trans hnormLower)
  have hnormsq : ‖z v‖ ^ 2 = sigma ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z]
    ring
  have hexp : ‖Complex.exp ((z v) * (x : ℂ))‖ = Real.exp (sigma * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [z]
  rw [heq, norm_mul, hexp]
  calc
    Real.exp (sigma * x) * ‖fordLaplaceF0 f (z v)‖ ≤
        Real.exp (sigma * x) * (D / ‖z v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
    _ = M v := by
      rw [hnormsq]
      simp only [M]
      ring

/-- On every finite shifted Bromwich window in the positive half-plane,
the bilateral transform of Ford's remainder is exactly the paper's
`F₀`; there is no limiting or almost-everywhere substitution here. -/
theorem fordShiftedLaplaceInvTrunc_remainder_eq_F0
    {f : ℝ → ℝ} {s : ℂ} {alpha R x : ℝ}
    (ha : alpha < s.re)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0)) :
    fordShiftedLaplaceInvTrunc
        (laplaceTransformBilateral (fordLaplaceRemainder f)) s alpha R x =
      fordShiftedLaplaceInvTrunc (fordLaplaceF0 f) s alpha R x := by
  unfold fordShiftedLaplaceInvTrunc
  congr 1
  apply intervalIntegral.integral_congr
  intro v _hv
  have hzpos : 0 <
      (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I).re := by
    simp
    linarith
  change Complex.exp
      ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral (fordLaplaceRemainder f)
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) =
    Complex.exp
      ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        fordLaplaceF0 f (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I)
  rw [laplaceTransformBilateral_fordLaplaceRemainder_eq
    hzpos (hAbs _ hzpos)]

/-- Ford's source hypotheses recover the actual remainder value at each
positive logarithm.  The radius `log n / 2` keeps the local inversion window
strictly inside the positive ray. -/
theorem tendsto_fordShiftedLaplaceInvTrunc_F0_log_nat
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ} {n : ℕ}
    (hn : 1 < n) (ha : alpha < s.re) (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    Tendsto
      (fun R : ℝ => fordShiftedLaplaceInvTrunc
        (fordLaplaceF0 f) s alpha R (Real.log n))
      atTop (𝓝 (fordLaplaceRemainder f (Real.log n))) := by
  have hsigma : 0 < s.re - alpha := sub_pos.mpr ha
  have hg : Integrable (fun y : ℝ =>
      Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) *
        fordLaplaceRemainder f y) := by
    apply integrable_exp_mul_fordLaplaceRemainder hsigma
    simpa only [neg_mul] using
      hAbs ((s.re - alpha : ℝ) : ℂ) (by simpa using hsigma)
  have hline := integrable_fordLaplaceRemainder_rightLine
    (f := f) (s := s) (alpha := alpha) (D := D) (eta := eta)
    (x := Real.log n) ha heta hFdiff hAbs hF₀
  have hinv : Tendsto
      (fun R : ℝ => fordShiftedLaplaceInvTrunc
        (laplaceTransformBilateral (fordLaplaceRemainder f))
          s alpha R (Real.log n))
      atTop (𝓝 (fordLaplaceRemainder f (Real.log n))) := by
    apply tendsto_fordShiftedLaplaceInvTrunc_of_local_regular
      (radius := Real.log n / 2)
    · have : 0 < Real.log n := Real.log_pos
        (show (1 : ℝ) < (n : ℝ) by exact_mod_cast hn)
      positivity
    · exact continuousOn_fordLaplaceRemainder_log_nat hfcont hn
    · exact differentiableAt_fordLaplaceRemainder_log_nat hn
        (hfdiff (Real.log n) (Real.log_pos
          (show (1 : ℝ) < (n : ℝ) by exact_mod_cast hn)))
    · exact hg
    · exact hline
  refine hinv.congr' ?_
  filter_upwards with R
  exact fordShiftedLaplaceInvTrunc_remainder_eq_F0 ha hAbs

/-- Multiplication by the von Mangoldt coefficient and Ford's exact
finite change of variables preserve the inverse-Laplace limit. -/
theorem tendsto_vonMangoldt_mul_fordJTrunc_of_inverse
    {F₀ : ℂ → ℂ} {g : ℝ → ℂ} {s : ℂ} {alpha x : ℝ} (n : ℕ)
    (hinv : Tendsto
      (fun R : ℝ => fordShiftedLaplaceInvTrunc F₀ s alpha R x)
      atTop (𝓝 (g x))) :
    Tendsto
      (fun R : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R x)
      atTop
      (𝓝 ((ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (x : ℂ)) * g x)) := by
  have h := hinv.const_mul
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (x : ℂ)))
  simpa only [fordJTrunc_eq_exp_neg_mul_shiftedLaplace, mul_assoc] using h

/-- Termwise source recovery for the actual bilateral Laplace transform.
All hypotheses are precisely the analytic hypotheses of the pinned inversion
theorem, now consumed by Ford's `J` term. -/
theorem tendsto_vonMangoldt_mul_fordJTrunc_laplaceTransform
    {g : ℝ → ℂ} {s : ℂ} {alpha x radius : ℝ} (n : ℕ)
    (hradius : 0 < radius)
    (hg : Integrable (fun y : ℝ =>
      Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) * g y))
    (hquot : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * ((x - u : ℝ) : ℂ))) *
                g (x - u) -
              Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (x : ℂ))) * g x))
      volume (-radius) radius)
    (hline : Integrable (fun v : ℝ =>
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral g
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I))) :
    Tendsto
      (fun R : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc (laplaceTransformBilateral g) s alpha R x)
      atTop
      (𝓝 ((ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (x : ℂ)) * g x)) := by
  apply tendsto_vonMangoldt_mul_fordJTrunc_of_inverse n
  exact tendsto_fordShiftedLaplaceInvTrunc hradius hg hquot hline

/-- The source-facing termwise limit for every natural index.  The indices
`0` and `1` are handled exactly by the vanishing von Mangoldt coefficient;
all positive logarithms use the proved local inversion theorem. -/
theorem tendsto_vonMangoldt_mul_fordJTrunc_F0
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (ha : alpha < s.re) (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2)
    (n : ℕ) :
    Tendsto
      (fun R : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc (fordLaplaceF0 f) s alpha R (Real.log n))
      atTop
      (𝓝 ((ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ)) *
          fordLaplaceRemainder f (Real.log n))) := by
  by_cases hn : 1 < n
  · apply tendsto_vonMangoldt_mul_fordJTrunc_of_inverse n
    exact tendsto_fordShiftedLaplaceInvTrunc_F0_log_nat
      hn ha heta hfcont hfdiff hFdiff hAbs hF₀
  · have hnle : n ≤ 1 := Nat.le_of_not_gt hn
    interval_cases n <;> simp

/-- Tannery's theorem for Ford's complete von Mangoldt right-line series.
The bound is the literal Cauchy envelope proved above, so it is independent
of the truncation height. -/
theorem tendsto_tsum_vonMangoldt_mul_fordJTrunc
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta : ℝ} {q : ℕ → ℂ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hlim : ∀ n : ℕ, Tendsto
      (fun R : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n))
      atTop (𝓝 (q n))) :
    Tendsto
      (fun R : ℝ => ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n))
      atTop (𝓝 (∑' n : ℕ, q n)) := by
  let C : ℝ := (1 / (2 * Real.pi)) * D *
    ∫ u : ℝ, fordKRightEnvelope s alpha u
  let B : ℕ → ℝ := fun n =>
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (alpha : ℂ) n‖ * C
  have hSeries : LSeriesSummable
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (alpha : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using halpha)
  have hB : Summable B := hSeries.norm.mul_right C
  apply tendsto_tsum_of_dominated_convergence hB hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  intro n
  have h := norm_vonMangoldt_mul_fordJTrunc_le
    ha hD heta hR hdiff hF₀ n
  dsimp only [B, C]
  convert h using 1
  all_goals ring

/-- Ford's finite right vertical line is the sum of the normalized
inverse-Laplace terms. -/
theorem fordK_rightLine_eq_tsum_fordJTrunc
    {F₀ : ℂ → ℂ} {s : ℂ} {alpha D eta R : ℝ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    VIntegral' (fordKSurrogateIntegrand s F₀) alpha (-R) R =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n) := by
  have hsum := hasSum_integral_fordKRightSeriesTerm (R := R)
    halpha ha hD heta hdiff hF₀
  have hscaled := hsum.mul_left (1 / (2 * Real.pi) : ℂ)
  have hterms : HasSum
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n))
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ u in (-R)..R,
          LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              ((alpha : ℂ) + (u : ℂ) * I) *
            F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))) := by
    refine HasSum.congr_fun hscaled (fun n => ?_)
    exact (normalized_integral_fordKRightSeriesTerm_eq
      F₀ s alpha R n).symm
  rw [hterms.tsum_eq]
  rw [VIntegral', VIntegral]
  simp only [smul_eq_mul]
  have hscalar :
      (1 / (2 * (Real.pi : ℂ) * I)) * I =
        1 / (2 * (Real.pi : ℂ)) := by
    field_simp [I_ne_zero, Real.pi_ne_zero]
  rw [← mul_assoc, hscalar]
  apply congrArg ((1 / (2 * Real.pi) : ℂ) * ·)
  apply intervalIntegral.integral_congr
  intro u _hu
  change fordKSurrogateIntegrand s F₀
      ((alpha : ℂ) + (u : ℂ) * I) =
    LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((alpha : ℂ) + (u : ℂ) * I) *
        F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))
  have hre : 1 < ((alpha : ℂ) + (u : ℂ) * I).re := by
    simpa using halpha
  rw [fordKSurrogateIntegrand_eq
    (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    (riemannZeta_ne_zero_of_one_lt_re hre)]
  rw [logDeriv_apply]
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre]
  ring

/-- The finite Ford right contour converges to the complete source series
once the pinned inverse-Laplace theorem has been verified at every
`log n`.  This theorem consumes both the exact finite contour identity and
the height-uniform Tannery bound. -/
theorem tendsto_fordK_rightLine_of_termwise_inverse
    {F₀ : ℂ → ℂ} {g : ℝ → ℂ} {s : ℂ} {alpha D eta : ℝ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hinv : ∀ n : ℕ, 1 < n → Tendsto
      (fun R : ℝ => fordShiftedLaplaceInvTrunc F₀ s alpha R (Real.log n))
      atTop (𝓝 (g (Real.log n)))) :
    Tendsto
      (fun R : ℝ => VIntegral' (fordKSurrogateIntegrand s F₀) alpha (-R) R)
      atTop
      (𝓝 (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ)) * g (Real.log n))) := by
  have hlim : ∀ n : ℕ, Tendsto
      (fun R : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        fordJTrunc F₀ s alpha R (Real.log n))
      atTop
      (𝓝 ((ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ)) * g (Real.log n))) := by
    intro n
    by_cases hn : 1 < n
    · exact tendsto_vonMangoldt_mul_fordJTrunc_of_inverse n (hinv n hn)
    · have hnle : n ≤ 1 := Nat.le_of_not_gt hn
      interval_cases n <;> simp
  have hsum := tendsto_tsum_vonMangoldt_mul_fordJTrunc
    halpha ha hD heta hdiff hF₀ hlim
  refine hsum.congr' ?_
  filter_upwards with R
  exact (fordK_rightLine_eq_tsum_fordJTrunc (R := R)
    halpha ha hD heta hdiff hF₀).symm

/-- Source-facing right-line limit in Ford's Lemma `K(s)`: the exact finite
contour tends to the von Mangoldt series with coefficient
`f(log n) - f(0)`. -/
theorem tendsto_fordK_rightLine_F0
    {f : ℝ → ℝ} {s : ℂ} {alpha D eta : ℝ}
    (halpha : 1 < alpha) (ha : alpha < s.re) (hD : 0 ≤ D)
    (heta : eta ≤ s.re - alpha)
    (hfcont : ContinuousOn f (Set.Ioi 0))
    (hfdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ f y)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ (fordLaplaceF0 f) z)
    (hAbs : ∀ z : ℂ, 0 < z.re → IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Set.Ioi 0))
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖fordLaplaceF0 f z‖ ≤ D / ‖z‖ ^ 2) :
    Tendsto
      (fun R : ℝ => VIntegral'
        (fordKSurrogateIntegrand s (fordLaplaceF0 f)) alpha (-R) R)
      atTop
      (𝓝 (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (-s * (Real.log n : ℂ)) *
          fordLaplaceRemainder f (Real.log n))) := by
  apply tendsto_fordK_rightLine_of_termwise_inverse
    halpha ha hD heta hFdiff hF₀
  intro n hn
  exact tendsto_fordShiftedLaplaceInvTrunc_F0_log_nat
    hn ha heta hfcont hfdiff hFdiff hAbs hF₀

end

end GafniTao
