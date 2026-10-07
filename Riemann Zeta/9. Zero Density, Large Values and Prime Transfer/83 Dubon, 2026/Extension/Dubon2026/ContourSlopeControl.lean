import Dubon2026.RectangleRealParts
import Dubon2026.HorizontalArgumentBound

/-! # The actual zero count and the difference of vertical logarithmic-derivative means -/

namespace Dubon2026

open Complex MeasureTheory Set

/-- The real mean of the actual complex logarithmic derivative along a vertical segment. -/
noncomputable def verticalLogDerivMean (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) : ℝ :=
  (∫ t in -T..T, logDeriv (dirichletSum a N) ((σ : ℂ) + I * t)).re / (2 * T)

theorem abs_count_sub_vertical_integrals_le {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 ≤ T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0) :
    |2 * Real.pi * (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) -
      ((∫ t in -T..T, logDeriv (dirichletSum a N) ((u : ℂ) + I * t)).re -
        (∫ t in -T..T, logDeriv (dirichletSum a N) ((l : ℂ) + I * t)).re)| ≤
          2 * Real.pi * (2 : ℝ) ^ N := by
  have hi := rectangleIntegral_scaled_real (logDeriv (dirichletSum a N)) l u (-T) T
  rw [rectangleIntegral_logDeriv_eq_verticalZeroCount hN (ha.trans_ne one_ne_zero) hlu hT hb,
    natCast_re] at hi
  simp only [mul_comm I] at *
  have hbottom := abs_im_horizontal_logDeriv_integral_le hN ha (-T) hlu
    (fun x hx => hb _ (horizontal_bottom_mem_rectangleBorder hlu hx))
  have htop := abs_im_horizontal_logDeriv_integral_le hN ha T hlu
    (fun x hx => hb _ (horizontal_top_mem_rectangleBorder hlu hx))
  have hsum := (abs_sub (HIntegral (logDeriv (dirichletSum a N)) l u (-T)).im
    (HIntegral (logDeriv (dirichletSum a N)) l u T).im).trans
      (add_le_add (by simpa only [HIntegral, mul_comm I] using hbottom)
        (by simpa only [HIntegral, mul_comm I] using htop))
  have he : 2 * Real.pi * (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) -
      ((∫ t in -T..T, logDeriv (dirichletSum a N) ((u : ℂ) + t * I)).re -
        (∫ t in -T..T, logDeriv (dirichletSum a N) ((l : ℂ) + t * I)).re) =
      (HIntegral (logDeriv (dirichletSum a N)) l u (-T)).im -
        (HIntegral (logDeriv (dirichletSum a N)) l u T).im := by linarith
  rw [he]
  linarith

theorem abs_zeroDensity_sub_verticalLogDerivMean_le {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 < T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0) :
    |(verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T) -
      (verticalLogDerivMean a N u T - verticalLogDerivMean a N l T) / (2 * Real.pi)| ≤
        (2 : ℝ) ^ N / (2 * T) := by
  have hh := abs_count_sub_vertical_integrals_le hN ha hlu hT.le hb
  have hd : 0 < (2 * Real.pi) * (2 * T) := by positivity
  have he : (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) / (2 * T) -
      (verticalLogDerivMean a N u T - verticalLogDerivMean a N l T) / (2 * Real.pi) =
        (2 * Real.pi * (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) -
          ((∫ t in -T..T, logDeriv (dirichletSum a N) ((u : ℂ) + I * t)).re -
            (∫ t in -T..T, logDeriv (dirichletSum a N) ((l : ℂ) + I * t)).re)) /
              ((2 * Real.pi) * (2 * T)) := by
    unfold verticalLogDerivMean
    field_simp
  rw [he, abs_div, abs_of_pos hd]
  calc
    _ ≤ (2 * Real.pi * (2 : ℝ) ^ N) / ((2 * Real.pi) * (2 * T)) :=
      div_le_div_of_nonneg_right hh hd.le
    _ = (2 : ℝ) ^ N / (2 * T) := by
      field_simp

theorem verticalLogDerivMean_le_add {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u T : ℝ} (hlu : l ≤ u) (hT : 0 < T)
    (hb : ∀ s ∈ RectangleBorder (⟨l, -T⟩ : ℂ) (⟨u, T⟩ : ℂ), dirichletSum a N s ≠ 0) :
    verticalLogDerivMean a N l T ≤ verticalLogDerivMean a N u T +
      Real.pi * (2 : ℝ) ^ N / T := by
  have hh := (abs_le.mp (abs_count_sub_vertical_integrals_le hN ha hlu hT.le hb)).2
  have hc : 0 ≤ 2 * Real.pi *
      (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) := by positivity
  have hv : (∫ t in -T..T, logDeriv (dirichletSum a N) ((l : ℂ) + I * t)).re -
      (∫ t in -T..T, logDeriv (dirichletSum a N) ((u : ℂ) + I * t)).re ≤
        2 * Real.pi * (2 : ℝ) ^ N := by linarith
  apply sub_le_iff_le_add'.mp
  unfold verticalLogDerivMean
  rw [← sub_div]
  calc
    _ ≤ (2 * Real.pi * (2 : ℝ) ^ N) / (2 * T) :=
      div_le_div_of_nonneg_right hv (by positivity)
    _ = Real.pi * (2 : ℝ) ^ N / T := by ring

end Dubon2026
