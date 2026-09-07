import GafniTao.FordKInfiniteRectangle
import Mathlib.MeasureTheory.Group.Integral

/-!
# Quantitative control of Ford's complete left edge

This file turns the literal translated Cauchy envelope on `Re w = -1/2`
into a uniform `O(1 + log(|t|+2))` bound.  The constants below are honest,
finite integrals; no bounded-weight placeholder is introduced.
-/

open Complex MeasureTheory

namespace GafniTao

noncomputable section

/-- The fixed logarithmic Cauchy mass used on Ford's left edge. -/
noncomputable def fordLeftLogMass : ℝ :=
  ∫ v : ℝ, Real.log (|v| + 2) / ((3 / 2 : ℝ) ^ 2 + v ^ 2)

/-- The fixed Cauchy mass used on Ford's left edge. -/
noncomputable def fordLeftCauchyMass : ℝ :=
  ∫ v : ℝ, 1 / ((3 / 2 : ℝ) ^ 2 + v ^ 2)

theorem integrable_fordLeftLogMass :
    Integrable (fun v : ℝ =>
      Real.log (|v| + 2) / ((3 / 2 : ℝ) ^ 2 + v ^ 2)) :=
  integrable_ford_log_quadratic (3 / 2) (by norm_num)

theorem integrable_fordLeftCauchyMass :
    Integrable (fun v : ℝ => 1 / ((3 / 2 : ℝ) ^ 2 + v ^ 2)) :=
  integrable_ford_inv_quadratic (3 / 2) (by norm_num)

theorem fordLeftLogMass_nonneg : 0 ≤ fordLeftLogMass := by
  apply integral_nonneg
  intro v
  exact div_nonneg (Real.log_nonneg (by linarith [abs_nonneg v])) (by positivity)

theorem fordLeftCauchyMass_nonneg : 0 ≤ fordLeftCauchyMass := by
  apply integral_nonneg
  intro v
  positivity

private theorem ford_const_sub_measurePreserving (t : ℝ) :
    MeasurePreserving (fun u : ℝ => t - u) volume volume := by
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_left volume t).comp
      (Measure.measurePreserving_neg volume)

private theorem ford_const_sub_measurableEmbedding (t : ℝ) :
    MeasurableEmbedding (fun u : ℝ => t - u) := by
  simpa only [sub_eq_add_neg] using
    (measurableEmbedding_addLeft t).comp measurableEmbedding_neg

theorem integral_ford_comp_const_sub (t : ℝ) (g : ℝ → ℝ) :
    (∫ u : ℝ, g (t - u)) = ∫ v : ℝ, g v := by
  exact (ford_const_sub_measurePreserving t).integral_comp
    (ford_const_sub_measurableEmbedding t) g

/-- The actual translated envelope is controlled by two fixed finite masses.
This is the qualitative-constant version of Ford's displayed calculation
following `(I2)`; it has precisely the logarithmic height dependence needed
by the zero detector. -/
theorem integral_ford_leftLine_envelope_le_masses
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    (∫ u : ℝ, Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2)) ≤
      fordLeftLogMass + Real.log (|t| + 2) * fordLeftCauchyMass := by
  let g : ℝ → ℝ := fun v =>
    Real.log (|v| + 2) / ((3 / 2 : ℝ) ^ 2 + v ^ 2) +
      Real.log (|t| + 2) * (1 / ((3 / 2 : ℝ) ^ 2 + v ^ 2))
  have hg : Integrable g := by
    exact integrable_fordLeftLogMass.add
      (integrable_fordLeftCauchyMass.const_mul (Real.log (|t| + 2)))
  have hgcomp : Integrable (fun u : ℝ => g (t - u)) := by
    exact ((ford_const_sub_measurePreserving t).integrable_comp_emb
      (ford_const_sub_measurableEmbedding t)).2 hg
  have hleft := integrable_ford_leftLine_envelope
    (sigma := sigma) (t := t) hsigma
  calc
    (∫ u : ℝ, Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2)) ≤
        ∫ u : ℝ, g (t - u) := by
      apply integral_mono hleft hgcomp
      intro u
      have hsquare : (3 / 2 : ℝ) ^ 2 ≤ (sigma + 1 / 2) ^ 2 := by
        nlinarith [sq_nonneg (sigma - 1)]
      have hden : 0 < (3 / 2 : ℝ) ^ 2 + (t - u) ^ 2 := by positivity
      have hden' : 0 < (sigma + 1 / 2) ^ 2 + (t - u) ^ 2 := by positivity
      have hlogu : 0 ≤ Real.log (|u| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg u])
      have hlogt : 0 ≤ Real.log (|t| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      have hprod : |u| + 2 ≤ (|t - u| + 2) * (|t| + 2) := by
        calc
          |u| + 2 = |t - (t - u)| + 2 := by ring_nf
          _ ≤ (|t - u| + |t|) + 2 := by
            linarith [abs_sub t (t - u)]
          _ ≤ (|t - u| + 2) * (|t| + 2) := by
            nlinarith [abs_nonneg (t - u), abs_nonneg t]
      have hlog : Real.log (|u| + 2) ≤
          Real.log (|t - u| + 2) + Real.log (|t| + 2) := by
        calc
          Real.log (|u| + 2) ≤
              Real.log ((|t - u| + 2) * (|t| + 2)) :=
            Real.log_le_log (by positivity) hprod
          _ = _ := Real.log_mul (by positivity) (by positivity)
      calc
        Real.log (|u| + 2) /
            ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2) ≤
            Real.log (|u| + 2) /
              ((3 / 2 : ℝ) ^ 2 + (t - u) ^ 2) :=
          div_le_div_of_nonneg_left hlogu hden
            (by linarith [sq_nonneg (t - u)])
        _ ≤ (Real.log (|t - u| + 2) + Real.log (|t| + 2)) /
              ((3 / 2 : ℝ) ^ 2 + (t - u) ^ 2) :=
          div_le_div_of_nonneg_right hlog hden.le
        _ = g (t - u) := by
          dsimp [g]
          ring
    _ = ∫ v : ℝ, g v := integral_ford_comp_const_sub t g
    _ = fordLeftLogMass + Real.log (|t| + 2) * fordLeftCauchyMass := by
      rw [integral_add integrable_fordLeftLogMass
        (integrable_fordLeftCauchyMass.const_mul (Real.log (|t| + 2))),
        integral_const_mul]
      rfl

/-- The complete left edge in Ford `(I2)` has uniform logarithmic height
growth.  The logarithmic-derivative input here is the already-proved global
left-line estimate, not a contour or final-zero-free assumption. -/
theorem norm_fordKLeftLineIntegral_le_masses
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta C : ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D) (hetaUpper : eta ≤ 3 / 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ → ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hlogDeriv : ∀ u : ℝ,
      ‖deriv riemannZeta (fordLeftLinePoint u) /
        riemannZeta (fordLeftLinePoint u)‖ ≤ C * Real.log (|u| + 2))
    (hC : 0 ≤ C) :
    ‖fordKLeftLineIntegral s F₀‖ ≤
      (C * D / (2 * Real.pi)) *
        (fordLeftLogMass + Real.log (|s.im| + 2) * fordLeftCauchyMass) := by
  have henv := integrable_ford_leftLine_envelope
    (sigma := s.re) (t := s.im) hs
  have hpoint : ∀ u : ℝ,
      ‖fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u)‖ ≤
        C * D * (Real.log (|u| + 2) /
          ((s.re + 1 / 2) ^ 2 + (s.im - u) ^ 2)) := by
    intro u
    have h := norm_fordLeftLine_logDeriv_mul_le
      (F₀ := F₀) (sigma := s.re) (t := s.im) (D := D) (eta := eta) (C := C)
      hs hetaUpper hF₀ hlogDeriv hC u
    have heq := fordKSurrogateIntegrand_eq
      (s := s) (w := fordLeftLinePoint u) (F₀ := F₀)
      (by intro hsw; have := congrArg Complex.re hsw; norm_num at this)
      (ford_leftLine_zeta_ne_zero u)
    rw [heq]
    simpa [logDeriv_apply, mul_div_assoc, mul_assoc] using h
  have hmajor : Integrable (fun u : ℝ =>
      C * D * (Real.log (|u| + 2) /
        ((s.re + 1 / 2) ^ 2 + (s.im - u) ^ 2))) := henv.const_mul (C * D)
  have hintegral := norm_integral_le_of_norm_le hmajor
    (Filter.Eventually.of_forall hpoint)
  have hscale : ‖(1 / (2 * Real.pi * I) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_I]
    norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [fordKLeftLineIntegral, norm_smul, norm_smul, hscale, norm_I, one_mul]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ u : ℝ, fordKSurrogateIntegrand s F₀ (fordLeftLinePoint u)‖ ≤
      (1 / (2 * Real.pi)) *
        ∫ u : ℝ, C * D * (Real.log (|u| + 2) /
          ((s.re + 1 / 2) ^ 2 + (s.im - u) ^ 2)) :=
      mul_le_mul_of_nonneg_left hintegral (by positivity)
    _ = (C * D / (2 * Real.pi)) *
        (∫ u : ℝ, Real.log (|u| + 2) /
          ((s.re + 1 / 2) ^ 2 + (s.im - u) ^ 2)) := by
      rw [integral_const_mul]
      ring
    _ ≤ (C * D / (2 * Real.pi)) *
        (fordLeftLogMass + Real.log (|s.im| + 2) * fordLeftCauchyMass) := by
      apply mul_le_mul_of_nonneg_left
        (integral_ford_leftLine_envelope_le_masses hs)
      positivity

/-- Existential-constant form used downstream in the Ford zero detector. -/
theorem exists_norm_fordKLeftLineIntegral_le_log
    {F₀ : ℂ → ℂ} {s : ℂ} {D eta : ℝ}
    (hs : 1 < s.re) (hD : 0 ≤ D) (hetaUpper : eta ≤ 3 / 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ → ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      ‖fordKLeftLineIntegral s F₀‖ ≤ C * D * (1 + Real.log (|s.im| + 2)) := by
  obtain ⟨C₀, hC₀, hlog⟩ := exists_norm_riemannZeta_logDeriv_ford_leftLine_le
  let C : ℝ := C₀ * (fordLeftLogMass + fordLeftCauchyMass + 1) /
    (2 * Real.pi)
  have hmass : 0 < fordLeftLogMass + fordLeftCauchyMass + 1 := by
    linarith [fordLeftLogMass_nonneg, fordLeftCauchyMass_nonneg]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hbase := norm_fordKLeftLineIntegral_le_masses hs hD hetaUpper hF₀
    (by simpa [fordLeftLinePoint] using hlog) hC₀.le
  have hL : 0 ≤ Real.log (|s.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hm0 := fordLeftLogMass_nonneg
  have hm1 := fordLeftCauchyMass_nonneg
  calc
    ‖fordKLeftLineIntegral s F₀‖ ≤
        (C₀ * D / (2 * Real.pi)) *
          (fordLeftLogMass + Real.log (|s.im| + 2) * fordLeftCauchyMass) := hbase
    _ ≤ C * D * (1 + Real.log (|s.im| + 2)) := by
      dsimp [C]
      have hpi : 0 < 2 * Real.pi := by positivity
      have hCD : 0 ≤ C₀ * D := mul_nonneg hC₀.le hD
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      rw [div_le_iff₀ hpi]
      field_simp [ne_of_gt hpi]
      nlinarith [mul_nonneg hm1 hL, mul_nonneg hm0 hL]

end

end GafniTao
