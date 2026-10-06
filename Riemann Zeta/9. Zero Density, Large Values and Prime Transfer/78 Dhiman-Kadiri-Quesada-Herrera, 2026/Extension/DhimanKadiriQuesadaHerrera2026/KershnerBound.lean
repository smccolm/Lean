import DhimanKadiriQuesadaHerrera2026.CurvatureProjection
import DhimanKadiriQuesadaHerrera2026.StationarySource

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The general curvature estimate has the exact 1.343 normalization for the source exponential. -/
theorem kershner_integral_global {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt ℓ := by
  let g : ℝ → ℝ := fun u => -2 * Real.pi * (f u - ν * u)
  have hgd (u : ℝ) : HasDerivAt g (-2 * Real.pi * (deriv f u - ν)) u := by
    convert ((hf u).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν)).const_mul (-2 * Real.pi) using 1
    simp
  have hg : deriv g = fun u => -2 * Real.pi * (deriv f u - ν) := funext fun u => (hgd u).deriv
  have hgd' (u : ℝ) : HasDerivAt (deriv g) (-2 * Real.pi * deriv (deriv f) u) u := by
    rw [hg]
    exact ((hf' u).hasDerivAt.sub_const ν).const_mul _
  have h := norm_positive_curvature_integral (f := g) hab (mul_pos Real.two_pi_pos hℓ)
    (fun u _ => (hgd u).differentiableAt) (fun u _ => (hgd' u).differentiableAt)
    (fun u hu => by rw [(hgd' u).deriv]; nlinarith [hcurv u hu, Real.pi_pos])
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
  have hc : (119 / 50 : ℝ) ≤ 1.343 * Real.sqrt Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_d4]
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  apply (div_le_iff₀ (by positivity : 0 < 50 * (Real.sqrt Real.pi * Real.sqrt ℓ))).mpr
  have hm := mul_le_mul_of_nonneg_right hc hsℓ.le
  field_simp
  nlinarith

/-- The actual phase on a closed interval inherits 1.343 without global regularity assumptions. -/
theorem kershner_integral_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (ν : ℝ) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt ℓ := by
  let F := extendedPhase f a b hab a
  have hFd : Differentiable ℝ F := fun u => (extendedPhase_hasDerivAt hab hfc a u).differentiableAt
  have hF : deriv F = extendedSlope f a b hab a := funext fun u => (extendedPhase_hasDerivAt hab hfc a u).deriv
  have hFd' : Differentiable ℝ (deriv F) := by
    rw [hF]
    exact fun u => (extendedSlope_hasDerivAt hab hfc a u).differentiableAt
  have h := kershner_integral_global hab hℓ hFd hFd'
    (fun u hu => by
      rw [extendedPhase_second_deriv hab hfc a u, extendedCurvature_eq hab hu]
      exact hcurv u hu) ν
  have he : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))) =
      ∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    dsimp only [F]
    rw [extendedPhase_eq hab (Set.left_mem_Icc.mpr hab) hu hf hf' hfc]
  rw [he] at h
  exact h

/-- The paper's ordinary derivatives and decreasing slope discharge the signed curvature input. -/
theorem kershner_integral_source {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (ν : ℝ) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt ℓ :=
  kershner_integral_bound hab.le hℓ hf hf'
    (fun u hu => (hf'' u hu).continuousAt.continuousWithinAt)
    (stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower) ν

/-- Removing the two endpoint frequencies leaves exactly the interior frequency sum. -/
theorem frequency_boundary_decomposition (I : ℕ → ℂ) {M : ℕ} (hM : 1 ≤ M) :
    (∑ ν ∈ Finset.Icc 0 M, I ν) - (∑ ν ∈ Finset.Icc 1 (M - 1), I ν) = I 0 + I M := by
  have he : M = (M - 1) + 1 := by omega
  conv_lhs => lhs; rw [he, Finset.sum_Icc_succ_top (by omega)]
  have hs : Finset.Icc 0 (M - 1) = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.sum_insert (by simp), ← he]
  ring

/-- The source 2.686 bounds the actual removed integrals, including the zero-floor case. -/
theorem kershner_boundary_integrals {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) (M : ℕ) :
    ‖(∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      (∑ ν ∈ Finset.Icc 1 (M - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ)))‖ ≤
      2.686 / Real.sqrt ℓ := by
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  have hi (ν : ℕ) : ‖I ν‖ ≤ 1.343 / Real.sqrt ℓ :=
    kershner_integral_source hab hℓ hf hf' hf'' hanti hlower ν
  change ‖(∑ ν ∈ Finset.Icc 0 M, I ν) - ∑ ν ∈ Finset.Icc 1 (M - 1), I ν‖ ≤ _
  by_cases hM : M = 0
  · subst M
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.zero_sub, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty, sub_zero]
    apply (hi 0).trans
    exact div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ℓ)
  · rw [frequency_boundary_decomposition I (by omega)]
    apply (norm_add_le _ _).trans
    have h := add_le_add (hi 0) (hi M)
    convert h using 1
    ring

end DhimanKadiriQuesadaHerrera2026
