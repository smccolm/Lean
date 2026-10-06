import DhimanKadiriQuesadaHerrera2026.KershnerBound

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The general curvature estimate has the exact 0.6715 normalization for the source exponential. -/
theorem kershner_monotone_global {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ)
    (hside : (∀ u ∈ Set.Icc a b, ν ≤ deriv f u) ∨ (∀ u ∈ Set.Icc a b, deriv f u ≤ ν)) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      0.6715 / Real.sqrt ℓ := by
  let g : ℝ → ℝ := fun u => -2 * Real.pi * (f u - ν * u)
  have hgd (u : ℝ) : HasDerivAt g (-2 * Real.pi * (deriv f u - ν)) u := by
    convert ((hf u).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν)).const_mul (-2 * Real.pi) using 1
    simp
  have hg : deriv g = fun u => -2 * Real.pi * (deriv f u - ν) := funext fun u => (hgd u).deriv
  have hgd' (u : ℝ) : HasDerivAt (deriv g) (-2 * Real.pi * deriv (deriv f) u) u := by
    rw [hg]
    exact ((hf' u).hasDerivAt.sub_const ν).const_mul _
  have h : ‖∫ u in a..b, Complex.exp ((g u : ℂ) * Complex.I)‖ ≤
      119 / (100 * Real.sqrt (2 * Real.pi * ℓ / 2)) := by
    rcases hside with hpos | hneg
    · apply norm_curvature_negative_slope hab (mul_pos Real.two_pi_pos hℓ)
        (fun u _ => (hgd u).differentiableAt) (fun u _ => (hgd' u).differentiableAt)
      · intro u hu
        rw [(hgd u).deriv]
        nlinarith [hpos u hu, Real.pi_pos]
      · intro u hu
        rw [(hgd' u).deriv]
        nlinarith [hcurv u hu, Real.pi_pos]
    · apply norm_curvature_positive_slope hab (mul_pos Real.two_pi_pos hℓ)
        (fun u _ => (hgd u).differentiableAt) (fun u _ => (hgd' u).differentiableAt)
      · intro u hu
        rw [(hgd u).deriv]
        nlinarith [hneg u hu, Real.pi_pos]
      · intro u hu
        rw [(hgd' u).deriv]
        nlinarith [hcurv u hu, Real.pi_pos]
  have he (u : ℝ) : Complex.exp ((g u : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    dsimp [g]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  simp_rw [he] at h
  have hi : (∫ u in a..b, (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)))) =
      (starRingEnd ℂ) (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) := by
    simp only [intervalIntegral, integral_conj, map_sub]
  rw [hi, Complex.norm_conj] at h
  apply h.trans
  rw [show 2 * Real.pi * ℓ / 2 = Real.pi * ℓ by ring, Real.sqrt_mul Real.pi_pos.le]
  have hc : (119 / 100 : ℝ) ≤ 0.6715 * Real.sqrt Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_d4]
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  apply (div_le_iff₀ (by positivity : 0 < 100 * (Real.sqrt Real.pi * Real.sqrt ℓ))).mpr
  have hm := mul_le_mul_of_nonneg_right hc hsℓ.le
  field_simp
  nlinarith

/-- The actual phase on a closed interval inherits 0.6715 without global regularity assumptions. -/
theorem kershner_monotone_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ)
    (hside : (∀ u ∈ Set.Icc a b, ν ≤ deriv f u) ∨ (∀ u ∈ Set.Icc a b, deriv f u ≤ ν)) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      0.6715 / Real.sqrt ℓ := by
  let F := extendedPhase f a b hab a
  have hFd : Differentiable ℝ F := fun u => (extendedPhase_hasDerivAt hab hfc a u).differentiableAt
  have hF : deriv F = extendedSlope f a b hab a := funext fun u => (extendedPhase_hasDerivAt hab hfc a u).deriv
  have hFd' : Differentiable ℝ (deriv F) := by
    rw [hF]
    exact fun u => (extendedSlope_hasDerivAt hab hfc a u).differentiableAt
  have h := kershner_monotone_global hab hℓ hFd hFd'
    (fun u hu => by
      rw [extendedPhase_second_deriv hab hfc a u, extendedCurvature_eq hab hu]
      exact hcurv u hu) ν (by
        have he (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv F u = deriv f u := by
          rw [hF]
          exact extendedSlope_eq hab (Set.left_mem_Icc.mpr hab) hu hf' hfc
        rcases hside with hp | hn
        · exact Or.inl (fun u hu => (he u hu).symm ▸ hp u hu)
        · exact Or.inr (fun u hu => (he u hu).symm ▸ hn u hu))
  have he : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))) =
      ∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    dsimp only [F]
    rw [extendedPhase_eq hab (Set.left_mem_Icc.mpr hab) hu hf hf' hfc]
  rw [he] at h
  exact h

/-- A nonnegative source slope gives the sharper 0.6715 bound for the actual zero frequency. -/
theorem kershner_zero_frequency {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b)) (hpos : 0 ≤ deriv f b)
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * (f u : ℂ))‖ ≤
      0.6715 / Real.sqrt ℓ := by
  have h := kershner_monotone_bound hab.le hℓ hf hf'
    (fun u hu => (hf'' u hu).continuousAt.continuousWithinAt)
    (stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower) 0
    (Or.inl (fun u hu => hpos.trans (hanti.antitoneOn hu (Set.right_mem_Icc.mpr hab.le) hu.2)))
  simpa only [zero_mul, sub_zero] using h

/-- Positivity of the source derivative tightens the actual two-boundary-integral error to 2.0145. -/
theorem kershner_boundary_positive {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b)) (hpos : 0 ≤ deriv f b)
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (M : ℕ) :
    ‖(∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      (∑ ν ∈ Finset.Icc 1 (M - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      2.0145 / Real.sqrt ℓ := by
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  have hz : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by
    simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using
      kershner_zero_frequency hab hℓ hf hf' hf'' hanti hpos hlower
  change ‖(∑ ν ∈ Finset.Icc 0 M, I ν) - ∑ ν ∈ Finset.Icc 1 (M - 1), I ν‖ ≤ _
  by_cases hM : M = 0
  · subst M
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.zero_sub, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty, sub_zero]
    exact hz.trans (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ℓ))
  · rw [frequency_boundary_decomposition I (by omega)]
    apply (norm_add_le _ _).trans
    have hM := kershner_integral_source hab hℓ hf hf' hf'' hanti hlower (M : ℝ)
    have h := add_le_add hz hM
    convert h using 1
    ring


end DhimanKadiriQuesadaHerrera2026
