import DongWangWangZhang2026.MeanValueFrequency
import Mathlib.Probability.Distributions.Cauchy

/-!
# Rightward maximum control for the actual Dirichlet series

The half-plane Poisson kernel is obtained from the Fourier transform of a
two-sided exponential. This supplies the analytic maximum-transport mechanism
of GS03 Lemma 2.2, with the original spectral phases retained.
-/

namespace DongWangWangZhang2026

open Complex MeasureTheory Filter
open scoped Topology FourierTransform NNReal

noncomputable section

/-- The positive, unit-mass Poisson kernel on a vertical line. -/
def poissonLineKernel (α u : ℝ) : ℝ := α / Real.pi / (α ^ 2 + u ^ 2)

theorem poissonLineKernel_nonneg {α : ℝ} (hα : 0 ≤ α) (u : ℝ) :
    0 ≤ poissonLineKernel α u := by unfold poissonLineKernel; positivity

theorem continuous_poissonLineKernel {α : ℝ} (hα : 0 < α) : Continuous (poissonLineKernel α) := by
  unfold poissonLineKernel
  exact continuous_const.div (by fun_prop)
    (fun u => ne_of_gt (by nlinarith [sq_pos_of_pos hα, sq_nonneg u]))

theorem poissonLineKernel_eq_cauchyPDF {α : ℝ} (hα : 0 ≤ α) :
    poissonLineKernel α = ProbabilityTheory.cauchyPDFReal 0 ⟨α, hα⟩ := by
  funext u
  change α / Real.pi / (α ^ 2 + u ^ 2) = Real.pi⁻¹ * α * ((u - 0) ^ 2 + α ^ 2)⁻¹
  rw [sub_zero]
  rw [add_comm (u ^ 2)]
  ring

theorem integrable_poissonLineKernel {α : ℝ} (hα : 0 < α) :
    Integrable (poissonLineKernel α) := by
  rw [poissonLineKernel_eq_cauchyPDF hα.le]
  exact ProbabilityTheory.integrable_cauchyPDFReal 0

theorem integral_poissonLineKernel {α : ℝ} (hα : 0 < α) :
    (∫ u : ℝ, poissonLineKernel α u) = 1 := by
  rw [poissonLineKernel_eq_cauchyPDF hα.le]
  apply ProbabilityTheory.integral_cauchyPDFReal_eq_one 0
  intro heq
  exact hα.ne' (congrArg (fun r : ℝ≥0 => (r : ℝ)) heq)

/-- The even exponential whose Fourier transform is the half-plane Poisson kernel. -/
def poissonExponential (α u : ℝ) : ℂ := (Real.exp (-2 * Real.pi * α * |u|) : ℂ)

theorem continuous_poissonExponential (α : ℝ) : Continuous (poissonExponential α) := by
  unfold poissonExponential
  fun_prop

theorem integrable_poissonExponential {α : ℝ} (hα : 0 < α) :
    Integrable (poissonExponential α) := by
  have hpos : IntegrableOn (fun u : ℝ => Real.exp (-2 * Real.pi * α * |u|)) (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a := -2 * Real.pi * α)
      (by nlinarith [mul_pos Real.pi_pos hα]) 0).congr_fun
      _ measurableSet_Ioi
    intro u hu
    dsimp only
    change 0 < u at hu
    rw [abs_of_pos hu]
  have hneg : IntegrableOn (fun u : ℝ => Real.exp (-2 * Real.pi * α * |u|)) (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic (a := 2 * Real.pi * α) (by positivity) 0).congr_fun
      _ measurableSet_Iic
    intro u hu
    dsimp only
    change u ≤ 0 at hu
    rw [abs_of_nonpos hu]
    congr 1
    ring
  have hreal := hneg.union hpos
  rw [Set.Iic_union_Ioi, integrableOn_univ] at hreal
  exact hreal.ofReal

/-- Fourier transform with Mathlib's exact `2π` convention. -/
theorem fourier_poissonExponential {α : ℝ} (hα : 0 < α) (ξ : ℝ) :
    𝓕 (poissonExponential α) ξ = (poissonLineKernel α ξ : ℂ) := by
  let G : ℝ → ℂ := fun u => Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * I) *
    poissonExponential α u
  have hG : Integrable G := by
    apply (integrable_poissonExponential hα).norm.mono'
    · exact ((by unfold G poissonExponential; fun_prop : Continuous G)).aestronglyMeasurable
    · filter_upwards with u
      dsimp only [G]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have heqPos : Set.EqOn G (fun u : ℝ =>
      Complex.exp ((-2 * Real.pi * ((α : ℂ) + (ξ : ℂ) * I)) * (u : ℂ))) (Set.Ioi 0) := by
    intro u hu
    change 0 < u at hu
    dsimp only [G, poissonExponential]
    rw [Complex.ofReal_exp, ← Complex.exp_add, abs_of_pos hu]
    congr 1
    push_cast
    ring
  have heqNeg : Set.EqOn G (fun u : ℝ =>
      Complex.exp ((2 * Real.pi * ((α : ℂ) - (ξ : ℂ) * I)) * (u : ℂ))) (Set.Iic 0) := by
    intro u hu
    change u ≤ 0 at hu
    dsimp only [G, poissonExponential]
    rw [Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonpos hu]
    congr 1
    push_cast
    ring
  have hrePos : (-2 * Real.pi * ((α : ℂ) + (ξ : ℂ) * I)).re < 0 := by
    simp
    positivity
  have hreNeg : 0 < (2 * Real.pi * ((α : ℂ) - (ξ : ℂ) * I)).re := by
    simp
    positivity
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ u : ℝ, G u) = _
  rw [← integral_add_compl measurableSet_Iic hG, Set.compl_Iic,
    setIntegral_congr_fun measurableSet_Iic heqNeg, setIntegral_congr_fun measurableSet_Ioi heqPos,
    integral_exp_mul_complex_Iic hreNeg, integral_exp_mul_complex_Ioi hrePos]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hnePos : (α : ℂ) + (ξ : ℂ) * I ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simpa using hα)
  have hneNeg : (α : ℂ) - (ξ : ℂ) * I ≠ 0 :=
    Complex.ne_zero_of_re_pos (by simpa using hα)
  have hden : (α : ℂ) ^ 2 + (ξ : ℂ) ^ 2 ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_add, Complex.ofReal_re]
    nlinarith [sq_nonneg ξ, sq_pos_of_pos hα]
  unfold poissonLineKernel
  push_cast
  field_simp [hnePos, hneNeg, hden, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  simp [Complex.I_sq]

/-- The oscillatory Poisson integral, with no totalized-integral shortcut. -/
theorem integral_poissonLineKernel_phase {α : ℝ} (hα : 0 < α) (v : ℝ) :
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) * Complex.exp (((v * u : ℝ) : ℂ) * I)) =
      (Real.exp (-α * |v|) : ℂ) := by
  have hfourier : 𝓕 (poissonExponential α) = fun ξ : ℝ => (poissonLineKernel α ξ : ℂ) :=
    funext (fourier_poissonExponential hα)
  have hint : Integrable (𝓕 (poissonExponential α)) := by
    rw [hfourier]
    exact (integrable_poissonLineKernel hα).ofReal
  have h := (integrable_poissonExponential hα).fourierInv_fourier_eq hint
    ((continuous_poissonExponential α).continuousAt (x := v / (2 * Real.pi)))
  rw [hfourier, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  have hexp (u : ℝ) : Complex.exp (((-2 * Real.pi * u * -(v / (2 * Real.pi)) : ℝ) : ℂ) * I) =
      Complex.exp (((v * u : ℝ) : ℂ) * I) := by
    congr 2
    congr 1
    field_simp
  have hvalue : poissonExponential α (v / (2 * Real.pi)) = (Real.exp (-α * |v|) : ℂ) := by
    unfold poissonExponential
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    congr 2
    field_simp
  simp_rw [smul_eq_mul, hexp] at h
  rw [hvalue] at h
  simpa only [mul_comm] using h

theorem integrable_poissonLineKernel_phase {α : ℝ} (hα : 0 < α) (v : ℝ) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      Complex.exp (((v * u : ℝ) : ℂ) * I)) := by
  apply (integrable_poissonLineKernel hα).mono'
  · exact ((Complex.continuous_ofReal.comp (continuous_poissonLineKernel hα)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le u)]

theorem continuous_tsum_logFrequency (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    Continuous (fun y : ℝ => ∑' n : ℕ, a n * zetaTerm (-y) n) := by
  refine continuous_tsum (f := fun n (y : ℝ) => a n * zetaTerm (-y) n) ?_ ha ?_
  · intro n
    by_cases hn : n = 0
    · simp only [hn, zetaTerm_zero, mul_zero]
      exact continuous_const
    · simp_rw [zetaTerm_eq_exp _ hn]
      fun_prop
  · intro n y
    by_cases hn : n = 0
    · simp [hn]
    · rw [norm_mul, norm_zetaTerm _ (Nat.pos_of_ne_zero hn), mul_one]

theorem norm_tsum_logFrequency_le (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (y : ℝ) :
    ‖∑' n : ℕ, a n * zetaTerm (-y) n‖ ≤ ∑' n : ℕ, ‖a n‖ := by
  have hs := (summable_logFrequencyTerms a ha y).norm
  apply (norm_tsum_le_tsum_norm hs).trans
  apply Summable.tsum_le_tsum _ hs ha
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [norm_mul, norm_zetaTerm _ (Nat.pos_of_ne_zero hn), mul_one]

theorem integral_poissonLineKernel_zetaTerm {α : ℝ} (hα : 0 < α) (y : ℝ) (n : ℕ) :
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) * zetaTerm (-(y + u)) n) =
      (((n : ℝ) ^ (-α) : ℝ) : ℂ) * zetaTerm (-y) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hphase (u : ℝ) : zetaTerm (-(y + u)) n =
      zetaTerm (-y) n * Complex.exp ((((-Real.log n) * u : ℝ) : ℂ) * I) := by
    rw [neg_add, zetaTerm_add, zetaTerm_eq_exp (-u) hn]
    congr 2
    congr 1
    congr 1
    ring
  simp_rw [hphase]
  have hfactor (u : ℝ) : (poissonLineKernel α u : ℂ) *
      (zetaTerm (-y) n * Complex.exp ((((-Real.log n) * u : ℝ) : ℂ) * I)) =
      zetaTerm (-y) n * ((poissonLineKernel α u : ℂ) *
        Complex.exp ((((-Real.log n) * u : ℝ) : ℂ) * I)) := by ring
  simp_rw [hfactor]
  rw [integral_const_mul, integral_poissonLineKernel_phase hα, abs_neg, abs_of_nonneg hlog,
    Real.rpow_def_of_pos hnR]
  rw [show -α * Real.log n = Real.log n * (-α) by ring, mul_comm]

theorem integrable_poissonLineKernel_zetaTerm {α : ℝ} (hα : 0 < α) (y : ℝ) (n : ℕ) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) * zetaTerm (-(y + u)) n) := by
  by_cases hn : n = 0
  · simp only [hn, zetaTerm_zero, mul_zero]
    exact integrable_zero _ _ _
  have heq (u : ℝ) : (poissonLineKernel α u : ℂ) * zetaTerm (-(y + u)) n =
      zetaTerm (-y) n * ((poissonLineKernel α u : ℂ) *
        Complex.exp ((((-Real.log n) * u : ℝ) : ℂ) * I)) := by
    rw [neg_add, zetaTerm_add, zetaTerm_eq_exp (-u) hn]
    have hphase : ((-u * Real.log n : ℝ) : ℂ) * I =
        (((-Real.log n) * u : ℝ) : ℂ) * I := by push_cast; ring
    rw [hphase]
    ring
  simp_rw [heq]
  exact (integrable_poissonLineKernel_phase hα _).const_mul _

/-- Exact Poisson reproduction for an absolutely convergent logarithmic-frequency
series. The rightward damping is proved term by term and exchanged with the integral. -/
theorem integral_poissonLineKernel_tsum (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    {α : ℝ} (hα : 0 < α) (y : ℝ) :
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      (∑' n : ℕ, a n * zetaTerm (-(y + u)) n)) =
        ∑' n : ℕ, a n * (((n : ℝ) ^ (-α) : ℝ) : ℂ) * zetaTerm (-y) n := by
  let F : ℕ → ℝ → ℂ := fun n u => a n * ((poissonLineKernel α u : ℂ) * zetaTerm (-(y + u)) n)
  have hF (n : ℕ) : Integrable (F n) := (integrable_poissonLineKernel_zetaTerm hα y n).const_mul _
  have hbound (n : ℕ) (u : ℝ) : ‖F n u‖ ≤ ‖a n‖ * poissonLineKernel α u := by
    by_cases hn : n = 0
    · simp only [F, hn, zetaTerm_zero, mul_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (poissonLineKernel_nonneg hα.le _)
    · dsimp only [F]
      rw [norm_mul, norm_mul, norm_zetaTerm _ (Nat.pos_of_ne_zero hn), mul_one,
        Complex.norm_real, Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le _)]
  have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖F n u‖) := by
    apply ha.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg (F n u)))
    intro n
    calc
      _ ≤ ∫ u : ℝ, ‖a n‖ * poissonLineKernel α u :=
        integral_mono (hF n).norm ((integrable_poissonLineKernel hα).const_mul _) (hbound n)
      _ = ‖a n‖ := by rw [integral_const_mul, integral_poissonLineKernel hα, mul_one]
  have heq (u : ℝ) : (poissonLineKernel α u : ℂ) *
      (∑' n : ℕ, a n * zetaTerm (-(y + u)) n) = ∑' n : ℕ, F n u := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [F]
    ring
  simp_rw [heq]
  rw [← integral_tsum_of_summable_integral_norm hF hsum]
  apply tsum_congr
  intro n
  dsimp only [F]
  rw [integral_const_mul, integral_poissonLineKernel_zetaTerm hα]
  ring

theorem integrable_poissonLineKernel_tsum (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    {α : ℝ} (hα : 0 < α) (y : ℝ) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      (∑' n : ℕ, a n * zetaTerm (-(y + u)) n)) := by
  apply ((integrable_poissonLineKernel hα).mul_const (∑' n : ℕ, ‖a n‖)).mono'
  · exact ((Complex.continuous_ofReal.comp (continuous_poissonLineKernel hα)).mul
      ((continuous_tsum_logFrequency a ha).comp
        (continuous_const.add continuous_id))).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le _)]
    exact mul_le_mul_of_nonneg_left (norm_tsum_logFrequency_le a ha _) (poissonLineKernel_nonneg hα.le _)

theorem poissonLineKernel_neg (α u : ℝ) : poissonLineKernel α (-u) = poissonLineKernel α u := by
  simp only [poissonLineKernel, neg_sq]

theorem integral_poissonLineKernel_far_le {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    (∫ u in {u : ℝ | T < |u|}, poissonLineKernel α u) ≤ 2 * α / (Real.pi * T) := by
  have hpos : (∫ u in Set.Ioi T, poissonLineKernel α u) ≤ α / (Real.pi * T) := by
    calc
      _ ≤ ∫ u in Set.Ioi T, (α / Real.pi) * u ^ (-2 : ℝ) := by
        apply setIntegral_mono_on (integrable_poissonLineKernel hα).integrableOn
          ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul _)
          measurableSet_Ioi
        intro u hu
        have hu0 := hT.trans hu
        rw [poissonLineKernel, Real.rpow_neg hu0.le, Real.rpow_two, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hu0)
          (by nlinarith [sq_nonneg α])
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
        norm_num
        rw [Real.rpow_neg_one]
        ring
  have hneg : (∫ u in Set.Iio (-T), poissonLineKernel α u) =
      ∫ u in Set.Ioi T, poissonLineKernel α u := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi T (poissonLineKernel α)]
    simp only [poissonLineKernel_neg]
  have hset : {u : ℝ | T < |u|} = Set.Iio (-T) ∪ Set.Ioi T := by
    ext u
    change T < |u| ↔ u < -T ∨ T < u
    rw [lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl h
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    apply Set.disjoint_left.mpr
    intro u hu₁ hu₂
    change u < -T at hu₁
    change T < u at hu₂
    linarith
  rw [hset, setIntegral_union hdisj measurableSet_Ioi
    (integrable_poissonLineKernel hα).integrableOn (integrable_poissonLineKernel hα).integrableOn,
    hneg]
  calc
    _ ≤ α / (Real.pi * T) + α / (Real.pi * T) := add_le_add hpos hpos
    _ = _ := by ring

/-- A local vertical-line maximum controls the Poisson average, with an explicit
error from the complementary frequencies. -/
theorem norm_poissonLine_average_le {f : ℝ → ℂ} (hf : Continuous f)
    {α T B M y : ℝ} (hα : 0 < α) (hT : 0 < T)
    (hglobal : ∀ u : ℝ, ‖f u‖ ≤ B)
    (hlocal : ∀ u : ℝ, |u| ≤ 2 * T → ‖f u‖ ≤ M) (hy : |y| ≤ T) :
    ‖∫ u : ℝ, (poissonLineKernel α u : ℂ) * f (y + u)‖ ≤
      M + B * (2 * α / (Real.pi * T)) := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hglobal 0)
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hlocal 0 (by simp; linarith))
  let E : Set ℝ := {u : ℝ | T < |u|}
  have hE : MeasurableSet E := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hnorm : Integrable (fun u : ℝ => poissonLineKernel α u * ‖f (y + u)‖) := by
    apply ((integrable_poissonLineKernel hα).mul_const B).mono'
    · exact ((continuous_poissonLineKernel hα).mul
        ((hf.comp (continuous_const.add continuous_id)).norm)).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_of_nonneg (mul_nonneg (poissonLineKernel_nonneg hα.le _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hglobal _) (poissonLineKernel_nonneg hα.le _)
  have hmajorant : Integrable (fun u : ℝ => poissonLineKernel α u * M +
      E.indicator (fun v => poissonLineKernel α v * B) u) :=
    ((integrable_poissonLineKernel hα).mul_const M).add
      (((integrable_poissonLineKernel hα).mul_const B).indicator hE)
  have hpoint (u : ℝ) : poissonLineKernel α u * ‖f (y + u)‖ ≤
      poissonLineKernel α u * M + E.indicator (fun v => poissonLineKernel α v * B) u := by
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      have h := mul_le_mul_of_nonneg_left (hglobal (y + u)) (poissonLineKernel_nonneg hα.le u)
      nlinarith [mul_nonneg (poissonLineKernel_nonneg hα.le u) hM]
    · rw [Set.indicator_of_notMem hu, add_zero]
      have huT : |u| ≤ T := le_of_not_gt hu
      apply mul_le_mul_of_nonneg_left _ (poissonLineKernel_nonneg hα.le u)
      exact hlocal (y + u) ((abs_add_le y u).trans (by linarith))
  calc
    _ ≤ ∫ u : ℝ, ‖(poissonLineKernel α u : ℂ) * f (y + u)‖ := norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, poissonLineKernel α u * ‖f (y + u)‖ := by
      simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le _)]
    _ ≤ ∫ u : ℝ, poissonLineKernel α u * M +
        E.indicator (fun v => poissonLineKernel α v * B) u := integral_mono hnorm hmajorant hpoint
    _ = M + (∫ u in E, poissonLineKernel α u) * B := by
      rw [integral_add ((integrable_poissonLineKernel hα).mul_const M)
        (((integrable_poissonLineKernel hα).mul_const B).indicator hE),
        integral_mul_const, integral_poissonLineKernel hα, one_mul, integral_indicator hE,
        integral_mul_const]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (integral_poissonLineKernel_far_le hα hT) hB
      dsimp only [E]
      nlinarith

theorem norm_tsum_logFrequency_rightward_le (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    {α T M y : ℝ} (hα : 0 < α) (hT : 0 < T)
    (hlocal : ∀ u : ℝ, |u| ≤ 2 * T → ‖∑' n : ℕ, a n * zetaTerm (-u) n‖ ≤ M)
    (hy : |y| ≤ T) :
    ‖∑' n : ℕ, a n * (((n : ℝ) ^ (-α) : ℝ) : ℂ) * zetaTerm (-y) n‖ ≤
      M + (∑' n : ℕ, ‖a n‖) * (2 * α / (Real.pi * T)) := by
  rw [← integral_poissonLineKernel_tsum a ha hα y]
  exact norm_poissonLine_average_le (continuous_tsum_logFrequency a ha) hα hT
    (norm_tsum_logFrequency_le a ha) hlocal hy

/-- The actual coefficients of the shifted zeta series on the real line at `σ`. -/
def zetaPhaseCoeff (σ t : ℝ) (n : ℕ) : ℂ := zetaTerm t n / (n : ℂ) ^ (σ : ℂ)

theorem summable_norm_zetaPhaseCoeff (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ‖zetaPhaseCoeff σ t n‖) :=
  (summable_zetaTerm_div_cpow t (s := (σ : ℂ)) (by simpa)).norm

theorem norm_zetaPhaseCoeff (σ t : ℝ) (n : ℕ) (hσ : 1 < σ) :
    ‖zetaPhaseCoeff σ t n‖ = (n : ℝ) ^ (-σ) := by
  by_cases hn : n = 0
  · simp [hn, zetaPhaseCoeff, Real.zero_rpow (by linarith : -σ ≠ 0)]
  · rw [zetaPhaseCoeff, norm_div, norm_zetaTerm _ (Nat.pos_of_ne_zero hn),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg n), one_div]

theorem tsum_norm_zetaPhaseCoeff_le (σ t : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ‖zetaPhaseCoeff σ t n‖) ≤ 1 + 1 / (σ - 1) := by
  simp_rw [norm_zetaPhaseCoeff σ t _ hσ]
  exact tsum_nat_rpow_neg_le hσ

theorem zetaPhaseCoeff_phase_eq (σ t y : ℝ) (n : ℕ) :
    zetaPhaseCoeff σ t n * zetaTerm (-y) n =
      zetaTerm t n / (n : ℂ) ^ ((σ : ℂ) + (y : ℂ) * I) := by
  by_cases hn : n = 0
  · simp [hn, zetaPhaseCoeff]
  have hcn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [zetaPhaseCoeff, div_mul_eq_mul_div, ← zetaTerm_add,
    zetaTerm_eq_cpow _ hn, zetaTerm_eq_cpow _ hn,
    ← Complex.cpow_sub _ _ hcn, ← Complex.cpow_sub _ _ hcn]
  congr 1
  push_cast
  ring

theorem tsum_zetaPhaseCoeff_phase (σ t y : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, zetaPhaseCoeff σ t n * zetaTerm (-y) n) =
      riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) := by
  simp_rw [zetaPhaseCoeff_phase_eq]
  rw [tsum_zetaTerm_div_cpow t (by simpa)]
  congr 1
  push_cast
  ring

theorem zetaPhaseCoeff_rightward (σ t α : ℝ) (n : ℕ) :
    zetaPhaseCoeff σ t n * (((n : ℝ) ^ (-α) : ℝ) : ℂ) = zetaPhaseCoeff (σ + α) t n := by
  by_cases hn : n = 0
  · simp [hn, zetaPhaseCoeff]
  have hcn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [zetaPhaseCoeff, zetaPhaseCoeff, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg, ← div_eq_mul_inv,
    div_div, ← Complex.cpow_add _ _ hcn, Complex.ofReal_add]

/-- Rightward maximum control for the actual zeta series. Its error is explicit
and uniform in the height; the local maximum is on the original vertical line. -/
theorem norm_shifted_zeta_rightward_le (σ t α T M y : ℝ)
    (hσ : 1 < σ) (hα : 0 < α) (hT : 0 < T)
    (hlocal : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I)‖ ≤ M) (hy : |y| ≤ T) :
    ‖riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ≤
      M + (1 + 1 / (σ - 1)) * (2 * α / (Real.pi * T)) := by
  have h := norm_tsum_logFrequency_rightward_le (zetaPhaseCoeff σ t)
    (summable_norm_zetaPhaseCoeff σ t hσ) hα hT
      (fun u hu => by rw [tsum_zetaPhaseCoeff_phase σ t u hσ]; exact hlocal u hu) hy
  simp_rw [zetaPhaseCoeff_rightward, tsum_zetaPhaseCoeff_phase (σ + α) t y (by linarith)] at h
  apply h.trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (tsum_norm_zetaPhaseCoeff_le σ t hσ)
    (by positivity))

/-- The maximizer used by the paper genuinely controls rightward shifts on the
half-sized frequency window, rather than being assumed to maximize there. -/
theorem exists_maximizingTwist_rightward_bound {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α → ∀ y : ℝ, |y| ≤ Real.log x / 2 →
        ‖riemannZeta ((((1 + 1 / Real.log x + α : ℝ) : ℂ)) + ((y - t : ℝ) : ℂ) * I)‖ ≤
          ‖riemannZeta (twistZetaPoint x t t₀)‖ +
            (1 + Real.log x) * (4 * α / (Real.pi * Real.log x)) := by
  obtain ⟨t₀, ht₀, hmax⟩ := exists_maximizingTwist hx t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  intro α hα y hy
  have hxlog := Real.log_pos hx
  have h := norm_shifted_zeta_rightward_le (1 + 1 / Real.log x) t α (Real.log x / 2)
    ‖riemannZeta (twistZetaPoint x t t₀)‖ y (by linarith [one_div_pos.mpr hxlog]) hα (by positivity)
      (fun u hu => hmax u (by linarith)) hy
  apply h.trans_eq
  congr 1
  field_simp
  ring

/-- Poisson reproduction for zeta itself, with absolute integrability stated
alongside the identity. Both the height and the displacement are arbitrary. -/
theorem poissonLine_zeta (σ t α y : ℝ) (hσ : 1 < σ) (hα : 0 < α) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I)) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I)) =
        riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I) := by
  have hi := integrable_poissonLineKernel_tsum (zetaPhaseCoeff σ t)
    (summable_norm_zetaPhaseCoeff σ t hσ) hα y
  have he := integral_poissonLineKernel_tsum (zetaPhaseCoeff σ t)
    (summable_norm_zetaPhaseCoeff σ t hσ) hα y
  simp_rw [tsum_zetaPhaseCoeff_phase σ t _ hσ] at hi he
  simp_rw [zetaPhaseCoeff_rightward, tsum_zetaPhaseCoeff_phase (σ + α) t y (by linarith)] at he
  exact ⟨hi, he⟩

/-- A single actual source-line maximizer controls the derivative mean square
on every line to its right, on the half-sized frequency window. -/
theorem exists_maximizingTwist_rightward_near_mean_square {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α →
        (∫ ξ in Set.Icc (-(Real.log x / (4 * Real.pi))) (Real.log x / (4 * Real.pi)),
          ‖deriv riemannZeta
            ((((1 + 1 / Real.log x + α : ℝ) : ℂ)) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
              ((((1 + 1 / Real.log x + α : ℝ) : ℂ)) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤
          (‖riemannZeta (twistZetaPoint x t t₀)‖ +
            (1 + Real.log x) * (4 * α / (Real.pi * Real.log x))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) := by
  obtain ⟨t₀, ht₀, hmax, hright⟩ := exists_maximizingTwist_rightward_bound hx t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  intro α hα
  have hlog := Real.log_pos hx
  have hp : 0 < 4 * Real.pi := by positivity
  have hnear := zeta_deriv_near_frequency_le t (Real.log x / (4 * Real.pi))
    (‖riemannZeta (twistZetaPoint x t t₀)‖ +
      (1 + Real.log x) * (4 * α / (Real.pi * Real.log x)))
    (σ := 1 + 1 / Real.log x + α) (by linarith [one_div_pos.mpr hlog]) (fun ξ hξ => by
      apply hright α hα
      rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
      have hb := (le_div_iff₀ hp).mp (abs_le.mpr hξ)
      linarith)
  convert hnear using 1
  congr 2
  ring

/-- Full spectral mean square assembled from the actual local maximum and the
sharp two-sided derivative tail. The Fourier scaling is explicit. -/
theorem zeta_deriv_quotient_mean_square_le (σ t T M : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T)
    (hmax : ∀ u : ℝ, |u| ≤ T →
      ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I)‖ ≤ M) :
    (∫ ξ : ℝ, ‖deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤
      M ^ 2 * (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) +
        (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
          (1 / T + 1 / ((σ - 1) ^ 3 * T ^ 2))) := by
  let F : ℝ → ℝ := fun y => ‖deriv riemannZeta
    ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2
  let E : Set ℝ := {y : ℝ | T < |y|}
  let R : ℝ := T / (2 * Real.pi)
  have hp : 0 < 2 * Real.pi := by positivity
  have hE : MeasurableSet E := (isOpen_lt continuous_const continuous_abs).measurableSet
  have heq (ξ : ℝ) :
      (Set.Icc (-R) R)ᶜ.indicator (fun z : ℝ => F (2 * Real.pi * z)) ξ =
        E.indicator F (2 * Real.pi * ξ) := by
    have hmem : ξ ∈ (Set.Icc (-R) R)ᶜ ↔ 2 * Real.pi * ξ ∈ E := by
      change ¬(-R ≤ ξ ∧ ξ ≤ R) ↔ T < |2 * Real.pi * ξ|
      rw [← abs_le, not_le, abs_mul, abs_of_pos hp]
      simpa only [R, mul_comm] using (div_lt_iff₀ hp : T / (2 * Real.pi) < |ξ| ↔ _)
    by_cases hξ : ξ ∈ (Set.Icc (-R) R)ᶜ
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem (hmem.mp hξ)]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (mt hmem.mpr hξ)]
  have hfarEq :
      (∫ ξ in (Set.Icc (-R) R)ᶜ, F (2 * Real.pi * ξ)) =
        (2 * Real.pi)⁻¹ * ∫ y in E, F y := by
    rw [← integral_indicator measurableSet_Icc.compl]
    simp_rw [heq]
    rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hp), smul_eq_mul,
      integral_indicator hE]
  have hnear := zeta_deriv_near_frequency_le t R M hσ (fun ξ hξ => by
    apply hmax
    rw [abs_mul, abs_of_pos hp]
    simpa only [mul_comm] using (le_div_iff₀ hp).mp (abs_le.mpr hξ))
  have hfar := (zeta_deriv_far_tail σ t T hσ hσ₂ hT).2
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc
    (integrable_zeta_deriv_quotient_sq t hσ)
  change (∫ ξ : ℝ, F (2 * Real.pi * ξ)) ≤ _
  rw [← hsplit, hfarEq]
  exact add_le_add hnear (mul_le_mul_of_nonneg_left hfar (inv_nonneg.mpr hp.le))

/-- The same source maximizer supplies a full weighted-summatory mean square
on every admissible line to its right. All near/far and coefficient inputs are
proved above; no shifted-line maximality is assumed. -/
theorem exists_maximizingTwist_weighted_mean_square {x : ℝ}
    (hx : 1 < x) (hxlog : 8 ≤ Real.log x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α → 1 / Real.log x + α ≤ 1 →
        (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
          ‖logZetaSum (Real.exp u) t‖ ^ 2) ≤
          (‖riemannZeta (twistZetaPoint x t t₀)‖ +
            (1 + Real.log x) * (4 * α / (Real.pi * Real.log x))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
            (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
              (2 / Real.log x + 4 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2))) := by
  obtain ⟨t₀, ht₀, hmax, hright⟩ := exists_maximizingTwist_rightward_bound hx t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  intro α hα hα₁
  have hlog := Real.log_pos hx
  have hσ : 1 < 1 + 1 / Real.log x + α := by linarith [one_div_pos.mpr hlog]
  have h := zeta_deriv_quotient_mean_square_le (1 + 1 / Real.log x + α) t
    (Real.log x / 2)
    (‖riemannZeta (twistZetaPoint x t t₀)‖ +
      (1 + Real.log x) * (4 * α / (Real.pi * Real.log x)))
    hσ (by linarith) (by linarith) (hright α hα)
  rw [integral_zeta_deriv_quotient_sq_eq_logSum_sq t hσ] at h
  rw [show 1 + 1 / Real.log x + α - 1 = 1 / Real.log x + α by ring] at h
  have hδ : 0 < 1 / Real.log x + α := add_pos (one_div_pos.mpr hlog) hα
  have htail : 1 / (Real.log x / 2) +
      1 / ((1 / Real.log x + α) ^ 3 * (Real.log x / 2) ^ 2) =
        2 / Real.log x + 4 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2) := by
    field_simp [hlog.ne', hδ.ne']
    ring
  rwa [htail] at h

/-- Poisson reproduction for an absolutely summable series with arbitrary real
frequencies. This also handles the shifted frequencies in the Lipschitz factor. -/
theorem poissonLine_frequency_series (a : ℕ → ℂ) (v : ℕ → ℝ)
    (ha : Summable (fun n => ‖a n‖)) {α : ℝ} (hα : 0 < α) (y : ℝ) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      ∑' n : ℕ, a n * Complex.exp (((-v n * (y + u) : ℝ) : ℂ) * I)) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      ∑' n : ℕ, a n * Complex.exp (((-v n * (y + u) : ℝ) : ℂ) * I)) =
        ∑' n : ℕ, a n * (Real.exp (-α * |v n|) : ℂ) *
          Complex.exp (((-v n * y : ℝ) : ℂ) * I) := by
  have hcont : Continuous (fun z : ℝ =>
      ∑' n : ℕ, a n * Complex.exp (((-v n * z : ℝ) : ℂ) * I)) := by
    refine continuous_tsum (f := fun n (z : ℝ) =>
      a n * Complex.exp (((-v n * z : ℝ) : ℂ) * I)) ?_ ha ?_
    · intro n
      fun_prop
    · intro n z
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hbound (z : ℝ) :
      ‖∑' n : ℕ, a n * Complex.exp (((-v n * z : ℝ) : ℂ) * I)‖ ≤ ∑' n : ℕ, ‖a n‖ := by
    have hnorm : Summable (fun n => ‖a n * Complex.exp (((-v n * z : ℝ) : ℂ) * I)‖) := by
      simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using ha
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using norm_tsum_le_tsum_norm hnorm
  constructor
  · apply ((integrable_poissonLineKernel hα).mul_const (∑' n : ℕ, ‖a n‖)).mono'
    · exact ((Complex.continuous_ofReal.comp (continuous_poissonLineKernel hα)).mul
        (hcont.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le _)]
      exact mul_le_mul_of_nonneg_left (hbound _) (poissonLineKernel_nonneg hα.le _)
  · let F : ℕ → ℝ → ℂ := fun n u =>
      (a n * Complex.exp (((-v n * y : ℝ) : ℂ) * I)) *
        ((poissonLineKernel α u : ℂ) * Complex.exp (((-v n * u : ℝ) : ℂ) * I))
    have hF (n : ℕ) : Integrable (F n) :=
      (integrable_poissonLineKernel_phase hα (-v n)).const_mul _
    have hn (n : ℕ) (u : ℝ) : ‖F n u‖ = ‖a n‖ * poissonLineKernel α u := by
      simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (poissonLineKernel_nonneg hα.le _)]
    have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖F n u‖) := by
      simp_rw [hn, integral_const_mul, integral_poissonLineKernel hα, mul_one]
      exact ha
    have heq (u : ℝ) : (poissonLineKernel α u : ℂ) *
        (∑' n : ℕ, a n * Complex.exp (((-v n * (y + u) : ℝ) : ℂ) * I)) =
          ∑' n : ℕ, F n u := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [show (((-v n * (y + u) : ℝ) : ℂ) * I) =
        (((-v n * y : ℝ) : ℂ) * I) + (((-v n * u : ℝ) : ℂ) * I) by push_cast; ring,
        Complex.exp_add]
      dsimp only [F]
      ring
    simp_rw [heq]
    rw [← integral_tsum_of_summable_integral_norm hF hsum]
    apply tsum_congr
    intro n
    dsimp only [F]
    rw [integral_const_mul, integral_poissonLineKernel_phase hα, abs_neg]
    ring

theorem zetaPhaseCoeff_modulated_series (σ t y b : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, zetaPhaseCoeff σ t n *
      Complex.exp (((-(Real.log n + b) * y : ℝ) : ℂ) * I)) =
        riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) *
          Complex.exp (((-b * y : ℝ) : ℂ) * I) := by
  have hterm (n : ℕ) : zetaPhaseCoeff σ t n *
      Complex.exp (((-(Real.log n + b) * y : ℝ) : ℂ) * I) =
        (zetaPhaseCoeff σ t n * zetaTerm (-y) n) *
          Complex.exp (((-b * y : ℝ) : ℂ) * I) := by
    by_cases hn : n = 0
    · simp [hn, zetaPhaseCoeff]
    · rw [zetaTerm_eq_exp _ hn, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_zetaPhaseCoeff_phase σ t y hσ]

/-- Poisson reproduction after a nonnegative frequency translation. Writing
`b=log w` gives the extra factor used by GS03 Lemma 2.2's Lipschitz version. -/
theorem poissonLine_modulated_zeta (σ t α y b : ℝ)
    (hσ : 1 < σ) (hα : 0 < α) (hb : 0 ≤ b) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I))) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I))) =
      riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I) *
        Complex.exp (((-α * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * I)) := by
  have h := poissonLine_frequency_series (zetaPhaseCoeff σ t) (fun n => Real.log n + b)
    (summable_norm_zetaPhaseCoeff σ t hσ) hα y
  simp_rw [zetaPhaseCoeff_modulated_series σ t _ b hσ] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hcoeff (n : ℕ) : zetaPhaseCoeff σ t n * (Real.exp (-α * |Real.log n + b|) : ℂ) =
      zetaPhaseCoeff (σ + α) t n * (Real.exp (-α * b) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, zetaPhaseCoeff]
    · rw [abs_of_nonneg (add_nonneg (Real.log_natCast_nonneg n) hb),
        show -α * (Real.log n + b) = Real.log n * (-α) + -α * b by ring,
        Real.exp_add, Complex.ofReal_mul, ← mul_assoc,
        ← Real.rpow_def_of_pos (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn),
        zetaPhaseCoeff_rightward]
  simp_rw [hcoeff]
  have hterm (n : ℕ) :
      (zetaPhaseCoeff (σ + α) t n * (Real.exp (-α * b) : ℂ)) *
        Complex.exp (((-(Real.log n + b) * y : ℝ) : ℂ) * I) =
      (zetaPhaseCoeff (σ + α) t n *
        Complex.exp (((-(Real.log n + b) * y : ℝ) : ℂ) * I)) *
          (Real.exp (-α * b) : ℂ) := by ring
  simp_rw [hterm]
  rw [tsum_mul_right, zetaPhaseCoeff_modulated_series (σ + α) t y b (by linarith),
    Complex.exp_add, Complex.ofReal_exp]
  ring

/-- Exact reproduction for the zeta difference factor, including integrability.
The nonnegative translation is essential to the rightward damping. -/
theorem poissonLine_zeta_difference (σ t α y b : ℝ) (c : ℂ)
    (hσ : 1 < σ) (hα : 0 < α) (hb : 0 ≤ b) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I)))) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I)))) =
      riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-α * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * I))) := by
  have hbase := poissonLine_zeta σ t α y hσ hα
  have hmod := poissonLine_modulated_zeta σ t α y b hσ hα hb
  have hmodI := hmod.1.const_mul c
  have heq (u : ℝ) : (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I))) =
      (poissonLineKernel α u : ℂ) * riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) -
        c * ((poissonLineKernel α u : ℂ) *
          (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
            Complex.exp (((-b * (y + u) : ℝ) : ℂ) * I))) := by ring
  simp_rw [heq]
  refine ⟨hbase.1.sub hmodI, ?_⟩
  rw [integral_sub hbase.1 hmodI, integral_const_mul, hbase.2, hmod.2]
  ring

/-- GS03's difference-factor maximum transport for the actual shifted zeta
series. The explicit error is uniform in the nonnegative translation `b`. -/
theorem norm_shifted_zeta_difference_rightward_le (σ t α T M y b : ℝ) (c : ℂ)
    (hσ : 1 < σ) (hα : 0 < α) (hT : 0 < T) (hb : 0 ≤ b) (hc : ‖c‖ ≤ 1)
    (hlocal : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * u : ℝ) : ℂ) * I))‖ ≤ M) (hy : |y| ≤ T) :
    ‖riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I) *
      (1 - c * Complex.exp (((-α * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * I)))‖ ≤
        M + (1 + 1 / (σ - 1)) * (4 * α / (Real.pi * T)) := by
  have hcont : Continuous (fun u : ℝ => riemannZeta
      ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I)) := by
    have h := continuous_tsum_logFrequency (zetaPhaseCoeff σ t)
      (summable_norm_zetaPhaseCoeff σ t hσ)
    simpa only [tsum_zetaPhaseCoeff_phase σ t _ hσ] using h
  have hglobal (u : ℝ) :
      ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I) *
        (1 - c * Complex.exp (((-b * u : ℝ) : ℂ) * I))‖ ≤ 2 * (1 + 1 / (σ - 1)) := by
    have hz : ‖riemannZeta ((σ : ℂ) + ((u - t : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / (σ - 1) := by
      rw [← tsum_zetaPhaseCoeff_phase σ t u hσ]
      exact (norm_tsum_logFrequency_le (zetaPhaseCoeff σ t)
        (summable_norm_zetaPhaseCoeff σ t hσ) u).trans (tsum_norm_zetaPhaseCoeff_le σ t hσ)
    have hd : ‖1 - c * Complex.exp (((-b * u : ℝ) : ℂ) * I)‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) (c * Complex.exp (((-b * u : ℝ) : ℂ) * I))
      rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at h
      linarith
    rw [norm_mul]
    have hB : 0 ≤ 1 + 1 / (σ - 1) := by positivity
    simpa only [mul_comm] using mul_le_mul hz hd (norm_nonneg _) hB
  rw [← (poissonLine_zeta_difference σ t α y b c hσ hα hb).2]
  have h := norm_poissonLine_average_le
    (hcont.mul (show Continuous (fun u : ℝ =>
      (1 : ℂ) - c * Complex.exp (((-b * u : ℝ) : ℂ) * I)) by fun_prop))
    hα hT hglobal hlocal hy
  convert h using 1
  ring

/-- The difference factor tied to the starting abscissa, as required by a
normalized summatory dilation. It retains the initial damping exactly. -/
theorem poissonLine_zeta_dilation_difference (σ t α y b : ℝ)
    (hσ : 1 < σ) (hα : 0 < α) (hb : 0 ≤ b) :
    Integrable (fun u : ℝ => (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        (1 - Complex.exp (((-(σ - 1) * b : ℝ) : ℂ) +
          (((-b * (y + u) : ℝ) : ℂ) * I))))) ∧
    (∫ u : ℝ, (poissonLineKernel α u : ℂ) *
      (riemannZeta ((σ : ℂ) + ((y + u - t : ℝ) : ℂ) * I) *
        (1 - Complex.exp (((-(σ - 1) * b : ℝ) : ℂ) +
          (((-b * (y + u) : ℝ) : ℂ) * I))))) =
      riemannZeta (((σ + α : ℝ) : ℂ) + ((y - t : ℝ) : ℂ) * I) *
        (1 - Complex.exp (((-(σ + α - 1) * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * I))) := by
  have h := poissonLine_zeta_difference σ t α y b
    (Complex.exp (((-(σ - 1) * b : ℝ) : ℂ))) hσ hα hb
  simp_rw [← Complex.exp_add] at h
  have heq : (((-(σ - 1) * b : ℝ) : ℂ)) +
      (((-α * b : ℝ) : ℂ) + (((-b * y : ℝ) : ℂ) * I)) =
        (((-(σ + α - 1) * b : ℝ) : ℂ)) + (((-b * y : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rwa [heq] at h

end
end DongWangWangZhang2026
