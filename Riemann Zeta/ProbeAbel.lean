import RiemannZeta.GuthMaynard.DFIComplexLaplace

open Complex Set MeasureTheory Filter
open scoped Topology Interval
namespace RiemannZeta.GuthMaynard

theorem probe_damped_exp_integral
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) *
          cexp (-((ε : ℂ) * x)) * cexp (I * (a * x))) =
      ((ε : ℂ) - I * a) ^ (-s) * Gamma s := by
  have haRe : 0 < ((ε : ℂ) - I * a).re := by simp [hε]
  have h := dfiComplexLaplace_eq hs haRe
  unfold dfiComplexLaplace at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (I * ((a : ℂ) * x)) =
    (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) - I * a) * x))
  rw [show (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (I * ((a : ℂ) * x)) =
    (x : ℂ) ^ (s - 1) *
      (cexp (-((ε : ℂ) * x)) * cexp (I * ((a : ℂ) * x))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

theorem probe_damped_exp_neg_integral
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) *
          cexp (-((ε : ℂ) * x)) * cexp (-(I * (a * x)))) =
      ((ε : ℂ) + I * a) ^ (-s) * Gamma s := by
  have haRe : 0 < ((ε : ℂ) + I * a).re := by simp [hε]
  have h := dfiComplexLaplace_eq hs haRe
  unfold dfiComplexLaplace at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (-(I * ((a : ℂ) * x))) =
    (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) + I * a) * x))
  rw [show (x : ℂ) ^ (s - 1) * cexp (-((ε : ℂ) * x)) *
      cexp (-(I * ((a : ℂ) * x))) =
    (x : ℂ) ^ (s - 1) *
      (cexp (-((ε : ℂ) * x)) * cexp (-(I * ((a : ℂ) * x)))) by ring,
    ← Complex.exp_add]
  congr 2
  ring

theorem probe_damped_sin_integral
    {s : ℂ} (hs : 0 < s.re) {ε a : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) * Real.sin (a * x)) =
      (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) /
        (2 * I) * Gamma s := by
  have hp := probe_damped_exp_integral hs hε (a := a)
  have hm := probe_damped_exp_neg_integral hs hε (a := a)
  have hpi : (2 * I : ℂ) ≠ 0 := by simp
  let P : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) *
    cexp (-((ε : ℂ) * x)) * cexp (I * ((a : ℂ) * x))
  let M : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) *
    cexp (-((ε : ℂ) * x)) * cexp (-(I * ((a : ℂ) * x)))
  have hPInt : IntegrableOn P (Set.Ioi 0) := by
    have h := integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs
      (show 0 < ((ε : ℂ) - I * a).re by simp [hε])
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    dsimp [P]
    change (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) - I * a) * x)) = _
    rw [show -(((ε : ℂ) - I * a) * x) =
      -((ε : ℂ) * x) + I * ((a : ℂ) * x) by ring, Complex.exp_add]
    ring
  have hMInt : IntegrableOn M (Set.Ioi 0) := by
    have h := integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs
      (show 0 < ((ε : ℂ) + I * a).re by simp [hε])
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    dsimp [M]
    change (x : ℂ) ^ (s - 1) * cexp (-(((ε : ℂ) + I * a) * x)) = _
    rw [show -(((ε : ℂ) + I * a) * x) =
      -((ε : ℂ) * x) + -(I * ((a : ℂ) * x)) by ring, Complex.exp_add]
    ring
  calc
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Real.exp (-ε * x) * Real.sin (a * x)) =
      ∫ x : ℝ in Set.Ioi 0, (P x - M x) / (2 * I) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp [P, M]
      have hExp : ((Real.exp (-ε * x) : ℝ) : ℂ) =
          cexp (-((ε : ℂ) * x)) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [show (Real.sin (a * x) : ℂ) =
          (cexp (I * (a * x)) - cexp (-(I * (a * x)))) / (2 * I) by
        have hSin (y : ℝ) : (Real.sin y : ℂ) =
            (cexp (I * y) - cexp (-(I * y))) / (2 * I) := by
          rw [show I * (y : ℂ) = (y : ℂ) * I by ring,
            show -((y : ℂ) * I) = ((-y : ℝ) : ℂ) * I by push_cast; ring,
            Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg,
            Complex.cos_neg, Complex.sin_neg,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          push_cast
          field_simp
          ring
        simpa only [Complex.ofReal_mul] using hSin (a * x)]
      rw [hExp]
      ring
    _ = (∫ x : ℝ in Set.Ioi 0, P x - M x) / (2 * I) := by
      rw [MeasureTheory.integral_div]
    _ = ((∫ x : ℝ in Set.Ioi 0, P x) -
        ∫ x : ℝ in Set.Ioi 0, M x) / (2 * I) := by
      rw [MeasureTheory.integral_sub hPInt hMInt]
    _ = (((ε : ℂ) - I * a) ^ (-s) - ((ε : ℂ) + I * a) ^ (-s)) /
        (2 * I) * Gamma s := by
      rw [show (∫ x : ℝ in Set.Ioi 0, P x) =
          ((ε : ℂ) - I * a) ^ (-s) * Gamma s by exact hp,
        show (∫ x : ℝ in Set.Ioi 0, M x) =
          ((ε : ℂ) + I * a) ^ (-s) * Gamma s by exact hm]
      field_simp

end RiemannZeta.GuthMaynard
