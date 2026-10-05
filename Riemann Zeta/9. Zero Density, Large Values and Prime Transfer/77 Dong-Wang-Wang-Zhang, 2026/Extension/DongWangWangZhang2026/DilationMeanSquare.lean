import DongWangWangZhang2026.TwoPointEuler
import DongWangWangZhang2026.MeanValueAssembly

/-!
# Weighted difference mean square at the actual maximizing twist

The dilation retains both original floor-cutoff sums. Translation in the
logarithmic variable gives genuine integrability and square integrability;
the Fourier consumer retains the exact initial damping.
-/

namespace DongWangWangZhang2026

open MeasureTheory Complex
open scoped FourierTransform ENNReal Topology

noncomputable section

/-- The damped difference of the actual logarithmically weighted sums. -/
def dampedLogZetaDifference (t σ b u : ℝ) : ℂ :=
  dampedLogZetaSum t σ u - (Real.exp (-(σ - 1) * b) : ℂ) *
    dampedLogZetaSum t σ (u - b)

theorem dampedLogZetaDifference_eq_actual (t σ b u : ℝ) :
    dampedLogZetaDifference t σ b u =
      (Real.exp (-σ * u) : ℂ) *
        (logZetaSum (Real.exp u) t - (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t) := by
  have hscale : Real.exp (-(σ - 1) * b) * Real.exp (-σ * (u - b)) =
      Real.exp (-σ * u) * Real.exp b := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [dampedLogZetaDifference, dampedLogZetaSum, ← mul_assoc, ← Complex.ofReal_mul]
  rw [hscale]
  push_cast
  ring

theorem integrable_dampedLogZetaDifference (t b : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (dampedLogZetaDifference t σ b) :=
  (integrable_dampedLogZetaSum t hσ).sub
    (((integrable_dampedLogZetaSum t hσ).comp_sub_right b).const_mul _)

theorem memLp_dampedLogZetaDifference_two (t b : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    MemLp (dampedLogZetaDifference t σ b) 2 := by
  have h := (memLp_dampedLogZetaSum_two t hσ).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) (-b))
  have hshift : MemLp (fun u : ℝ => dampedLogZetaSum t σ (u - b)) 2 := by
    simpa only [Function.comp_def, sub_eq_add_neg] using h
  exact (memLp_dampedLogZetaSum_two t hσ).sub (hshift.const_mul _)

/-- The frequency difference is the actual dilation factor, including its
dependence on the abscissa; no truncated series is substituted. -/
theorem fourier_dampedLogZetaDifference (t b ξ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    𝓕 (dampedLogZetaDifference t σ b) ξ =
      (-deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I)) := by
  let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_assoc (-2 * Real.pi)]
  have hkernel (u : ℝ) :
      Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) *
        dampedLogZetaDifference t σ b u =
          (logZetaSum (Real.exp u) t - (Real.exp b : ℂ) *
            logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u) := by
    rw [dampedLogZetaDifference_eq_actual, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add,
      mul_comm]
    congr 1
    congr 1
    dsimp only [s]
    push_cast
    ring
  have hi : (∫ u : ℝ, Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) •
      dampedLogZetaDifference t σ b u) =
      ∫ u : ℝ, (logZetaSum (Real.exp u) t - (Real.exp b : ℂ) *
        logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u) := by
    apply integral_congr_ae
    filter_upwards with u
    exact hkernel u
  rw [hi, (laplace_logZetaSum_dilation t b hs).2]
  have harg : s - (t : ℂ) * I =
      (σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I := by
    dsimp only [s]
    push_cast
    ring
  have hfactor : (1 - s) * (b : ℂ) =
      -(((σ - 1) * b : ℝ) : ℂ) + ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I := by
    dsimp only [s]
    push_cast
    ring
  rw [harg, hfactor]

/-- Parseval for the actual weighted difference, with every floor cutoff,
frequency normalization and initial damping retained. -/
theorem integral_zeta_deriv_dilation_sq_eq_logDifference_sq (t b : ℝ) {σ : ℝ}
    (hσ : 1 < σ) :
    (∫ ξ : ℝ, ‖(deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2) =
      ∫ u : ℝ, Real.exp (-2 * σ * u) *
        ‖logZetaSum (Real.exp u) t -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t‖ ^ 2 := by
  have hnorm (ξ : ℝ) :
      ‖(deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ =
              ‖𝓕 (dampedLogZetaDifference t σ b) ξ‖ := by
    simp only [fourier_dampedLogZetaDifference t b ξ hσ, neg_div, neg_mul, norm_neg]
  simp_rw [hnorm]
  rw [integral_norm_sq_fourier_of_integrable_memLp_two
    (integrable_dampedLogZetaDifference t b hσ) (memLp_dampedLogZetaDifference_two t b hσ)]
  apply integral_congr_ae
  filter_upwards with u
  rw [dampedLogZetaDifference_eq_actual, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem integrable_zeta_deriv_dilation_sq (t b : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖(deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2) := by
  have h := memLp_fourier_of_integrable_memLp_two
    (integrable_dampedLogZetaDifference t b hσ) (memLp_dampedLogZetaDifference_two t b hσ)
  have hint := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  simpa only [fourier_dampedLogZetaDifference t b _ hσ, neg_div, neg_mul, norm_neg] using hint

/-- The actual zeta dilation maximum controls the near-frequency weighted
difference integral through the proved logarithmic-derivative mean square. -/
theorem zeta_deriv_dilation_near_frequency_le (t b R M : ℝ) {σ : ℝ} (hσ : 1 < σ)
    (hmax : ∀ ξ ∈ Set.Icc (-R) R,
      ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) *
        (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
          ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ≤ M) :
    (∫ ξ in Set.Icc (-R) R, ‖(deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2) ≤
      M ^ 2 * (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) := by
  let G : ℝ → ℝ := fun ξ => ‖(-deriv riemannZeta
    ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I)) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2
  have hG := zeta_logDeriv_quotient_mean_square_le t hσ
  have hpoint (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-R) R) :
      ‖(deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2 ≤ M ^ 2 * G ξ := by
    let z : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I
    let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
    let F : ℂ := 1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
      ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I)
    have hz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa [z] using hσ)
    have hs : s ≠ 0 := Complex.ne_zero_of_one_lt_re (by simpa [s] using hσ)
    have hfactor : (deriv riemannZeta z / s) * F =
        -(riemannZeta z * F) * ((-deriv riemannZeta z / riemannZeta z) / s) := by
      field_simp [hz, hs]
    change ‖(deriv riemannZeta z / s) * F‖ ^ 2 ≤
      M ^ 2 * ‖(-deriv riemannZeta z / riemannZeta z) / s‖ ^ 2
    rw [hfactor, norm_mul, norm_neg, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hmax ξ hξ) 2) (sq_nonneg _)
  calc
    _ ≤ ∫ ξ in Set.Icc (-R) R, M ^ 2 * G ξ :=
      setIntegral_mono_on (integrable_zeta_deriv_dilation_sq t b hσ).integrableOn
        (hG.1.const_mul (M ^ 2)).integrableOn measurableSet_Icc hpoint
    _ = M ^ 2 * ∫ ξ in Set.Icc (-R) R, G ξ := integral_const_mul _ _
    _ ≤ M ^ 2 * ∫ ξ : ℝ, G ξ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hG.1 (Filter.Eventually.of_forall fun _ => sq_nonneg _)) (sq_nonneg M)
    _ ≤ M ^ 2 * ((Real.log 4 + 4) ^ 2 / (2 * (σ - 1))) :=
      mul_le_mul_of_nonneg_left hG.2 (sq_nonneg M)
    _ = _ := (mul_div_assoc _ _ _).symm

/-- Near/far assembly for the actual weighted dilation. The far-frequency
cost is at most four times the already proved full-series derivative tail. -/
theorem zeta_deriv_dilation_mean_square_le (σ t b T M : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hb : 0 ≤ b) (hT : 4 ≤ T)
    (hmax : ∀ y : ℝ, |y| ≤ T →
      ‖riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) *
        (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I))‖ ≤ M) :
    (∫ ξ : ℝ, ‖(deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
          (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
            ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2) ≤
      M ^ 2 * (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) +
        4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
          (1 / T + 1 / ((σ - 1) ^ 3 * T ^ 2)))) := by
  let F : ℝ → ℝ := fun y => ‖deriv riemannZeta
    ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2
  let D : ℝ → ℝ := fun ξ => ‖(deriv riemannZeta
    ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)) *
        (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) +
          ((-b * (2 * Real.pi * ξ) : ℝ) : ℂ) * I))‖ ^ 2
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
  have hdom (ξ : ℝ) : D ξ ≤ 4 * F (2 * Real.pi * ξ) := by
    have hd := (norm_damped_difference_factor_le
      (mul_nonneg (sub_nonneg.mpr hσ.le) hb) hb (2 * Real.pi * ξ)).trans (min_le_left _ _)
    have hd₂ := pow_le_pow_left₀ (norm_nonneg _) hd 2
    dsimp only [D, F]
    rw [norm_mul, mul_pow]
    have hm := mul_le_mul_of_nonneg_left hd₂
      (sq_nonneg ‖deriv riemannZeta
        ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖)
    nlinarith
  have hfar := setIntegral_mono_on (s := (Set.Icc (-R) R)ᶜ)
    (integrable_zeta_deriv_dilation_sq t b hσ).integrableOn
    ((integrable_zeta_deriv_quotient_sq t hσ).const_mul 4).integrableOn
      measurableSet_Icc.compl (fun ξ _ => hdom ξ)
  change (∫ ξ in (Set.Icc (-R) R)ᶜ, D ξ) ≤
    ∫ ξ in (Set.Icc (-R) R)ᶜ, 4 * F (2 * Real.pi * ξ) at hfar
  rw [integral_const_mul, hfarEq] at hfar
  have htail := (zeta_deriv_far_tail σ t T hσ hσ₂ hT).2
  have hfarBound := hfar.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hp.le)) (by norm_num : (0 : ℝ) ≤ 4))
  have hnear := zeta_deriv_dilation_near_frequency_le t b R M hσ (fun ξ hξ => by
    apply hmax
    rw [abs_mul, abs_of_pos hp]
    simpa only [mul_comm] using (le_div_iff₀ hp).mp (abs_le.mpr hξ))
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc
    (integrable_zeta_deriv_dilation_sq t b hσ)
  change (∫ ξ : ℝ, D ξ) ≤ _
  rw [← hsplit]
  exact add_le_add hnear hfarBound

/-- The proved two-frequency input is consumed by the actual weighted
summatory difference. No local zeta bound or mean square remains a premise. -/
theorem exists_maximizingTwist_weighted_dilation_mean_square (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → 1 / Real.log x + α ≤ 1 →
      (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
        ‖logZetaSum (Real.exp u) (t - t₀) -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) (t - t₀)‖ ^ 2) ≤
        (4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
          (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) +
            (1 + Real.log x) * (16 * α / (Real.pi * Real.log x))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
          4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
            (4 / Real.log x + 16 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2)))) := by
  obtain ⟨B, hB, hright⟩ := exists_maximizingTwist_dilation_rightward_bound A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b α hx hlog16 hscale hmax ht₀ hb hα hδ₁
  let L := Real.log x
  let M := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ ((A : ℝ)⁻¹))) / L) ^ (38 / 113 : ℝ) +
      (1 + L) * (16 * α / (Real.pi * L))
  have hL : 0 < L := Real.log_pos hx
  have hδ : 0 < 1 / L + α := add_pos (one_div_pos.mpr hL) hα
  have hσ : 1 < 1 + 1 / L + α := by linarith
  have hshift : 1 + 1 / L + α - 1 = 1 / L + α := by ring
  have hlocal (y : ℝ) (hy : |y| ≤ L / 4) :
      ‖riemannZeta (((1 + 1 / L + α : ℝ) : ℂ) + ((y - (t - t₀) : ℝ) : ℂ) * I) *
        (1 - Complex.exp (-(((1 + 1 / L + α - 1) * b : ℝ) : ℂ) +
          ((-b * y : ℝ) : ℂ) * I))‖ ≤ M := by
    rw [hshift]
    exact hright x t t₀ b α y hx hscale hmax ht₀ hb hα hy
  have h := zeta_deriv_dilation_mean_square_le (1 + 1 / L + α) (t - t₀) b (L / 4) M
    hσ (by dsimp only [L]; linarith) hb (by dsimp only [L]; linarith) hlocal
  rw [integral_zeta_deriv_dilation_sq_eq_logDifference_sq (t - t₀) b hσ, hshift] at h
  have htail : 1 / (L / 4) + 1 / ((1 / L + α) ^ 3 * (L / 4) ^ 2) =
      4 / L + 16 / ((1 / L + α) ^ 3 * L ^ 2) := by
    field_simp [hL.ne', hδ.ne']
    ring
  rw [htail] at h
  exact h

/-- The elementary series bound supplies the complementary branch of the
minimum used in damping-parameter integration. -/
theorem norm_zeta_dilation_le_four_div (σ t b y : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hb : 0 ≤ b) :
    ‖riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) *
      (1 - Complex.exp (-(((σ - 1) * b : ℝ) : ℂ) + ((-b * y : ℝ) : ℂ) * I))‖ ≤
        4 / (σ - 1) := by
  have hδ : 0 < σ - 1 := sub_pos.mpr hσ
  have hd := (norm_damped_difference_factor_le
    (mul_nonneg hδ.le hb) hb y).trans (min_le_left _ _)
  rw [norm_mul]
  calc
    _ ≤ (1 + 1 / (σ - 1)) * 2 := mul_le_mul
      (norm_shifted_zeta_le_reciprocal σ t y hσ) hd (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      apply (le_div_iff₀ hδ).mpr
      field_simp
      nlinarith

/-- A frequency-uniform cap is retained before parameter integration. Both
branches are proved for the same actual source maximizer and original sums. -/
theorem exists_maximizingTwist_weighted_dilation_mean_square_min (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b α : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → 0 < α → 1 / Real.log x + α ≤ 1 →
      (∫ u : ℝ, Real.exp (-2 * (1 + 1 / Real.log x + α) * u) *
        ‖logZetaSum (Real.exp u) (t - t₀) -
          (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) (t - t₀)‖ ^ 2) ≤
        (min (4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
          (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) + 16)
            (4 / (1 / Real.log x + α))) ^ 2 *
              (Real.log 4 + 4) ^ 2 / (2 * (1 / Real.log x + α)) +
          4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
            (4 / Real.log x + 16 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2)))) := by
  obtain ⟨B, hB, hright⟩ := exists_maximizingTwist_dilation_rightward_bound A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b α hx hlog16 hscale hmax ht₀ hb hα hδ₁
  let L := Real.log x
  let M := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ ((A : ℝ)⁻¹))) / L) ^ (38 / 113 : ℝ) + 16
  have hL : 0 < L := Real.log_pos hx
  have hL₁ : 1 ≤ L := by dsimp only [L]; linarith
  have hδ : 0 < 1 / L + α := add_pos (one_div_pos.mpr hL) hα
  have hσ : 1 < 1 + 1 / L + α := by linarith
  have hσ₂ : 1 + 1 / L + α ≤ 2 := by dsimp only [L]; linarith
  have hshift : 1 + 1 / L + α - 1 = 1 / L + α := by ring
  have herror : (1 + L) * (16 * α / (Real.pi * L)) ≤ 16 := by
    have hα₁ : α ≤ 1 := by linarith [one_div_pos.mpr hL]
    have hm := mul_le_mul_of_nonneg_left hα₁ (show 0 ≤ 1 + L by positivity)
    have hp := mul_le_mul_of_nonneg_right Real.two_le_pi hL.le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos Real.pi_pos hL)).mpr
    nlinarith
  have hlocal (y : ℝ) (hy : |y| ≤ L / 4) :
      ‖riemannZeta (((1 + 1 / L + α : ℝ) : ℂ) + ((y - (t - t₀) : ℝ) : ℂ) * I) *
        (1 - Complex.exp (-(((1 + 1 / L + α - 1) * b : ℝ) : ℂ) +
          ((-b * y : ℝ) : ℂ) * I))‖ ≤ min M (4 / (1 / L + α)) := by
    apply le_min
    · rw [hshift]
      exact (hright x t t₀ b α y hx hscale hmax ht₀ hb hα hy).trans
        (add_le_add le_rfl herror)
    · simpa only [hshift] using
        norm_zeta_dilation_le_four_div (1 + 1 / L + α) (t - t₀) b y hσ hσ₂ hb
  have h := zeta_deriv_dilation_mean_square_le (1 + 1 / L + α) (t - t₀) b (L / 4)
    (min M (4 / (1 / L + α))) hσ hσ₂ hb (by dsimp only [L]; linarith) hlocal
  rw [integral_zeta_deriv_dilation_sq_eq_logDifference_sq (t - t₀) b hσ, hshift] at h
  have htail : 1 / (L / 4) + 1 / ((1 / L + α) ^ 3 * (L / 4) ^ 2) =
      4 / L + 16 / ((1 / L + α) ^ 3 * L ^ 2) := by
    field_simp [hL.ne', hδ.ne']
    ring
  rw [htail] at h
  exact h

end
end DongWangWangZhang2026
