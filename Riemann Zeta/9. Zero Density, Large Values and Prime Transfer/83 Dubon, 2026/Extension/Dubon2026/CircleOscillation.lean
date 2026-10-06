import Dubon2026.CircleQuarter
import GuthMaynardExternal.PNT.ZetaAppendix

/-! # Cosine-phase tails from the existing foundation's nonstationary-phase estimate -/

namespace Dubon2026

open MeasureTheory Set

theorem deriv_cosine_phase (u t : ℝ) :
    deriv (fun θ : ℝ => u * Real.cos θ / (2 * Real.pi)) t =
      -u * Real.sin t / (2 * Real.pi) := by
  convert (((Real.hasDerivAt_cos t).const_mul u).div_const (2 * Real.pi)).deriv using 1
  ring

theorem norm_cosine_phase_tail {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ)
    (hδb : δ < Real.pi / 2) :
    ‖∫ θ in δ..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))‖ ≤
      2 / (u * Real.sin δ) := by
  let φ : ℝ → ℝ := fun θ => u * Real.cos θ / (2 * Real.pi)
  let g : ℝ → ℝ := fun θ => 1 / (-u * Real.sin θ / (2 * Real.pi))
  have hs (t : ℝ) (ht : t ∈ Icc δ (Real.pi / 2)) : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (hδ.trans_le ht.1) (by linarith [Real.pi_pos, ht.2])
  have hder (t : ℝ) : deriv φ t = -u * Real.sin t / (2 * Real.pi) :=
    deriv_cosine_phase u t
  have hne (t : ℝ) (ht : t ∈ Icc δ (Real.pi / 2)) : deriv φ t ≠ 0 := by
    rw [hder]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu.ne') (hs t ht).ne')
      (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have habs (t : ℝ) (ht : t ∈ Icc δ (Real.pi / 2)) :
      |g t| = (2 * Real.pi) / (u * Real.sin t) := by
    dsimp [g]
    rw [abs_div, abs_one, abs_div, abs_mul, abs_neg, abs_of_pos hu,
      abs_of_pos (hs t ht), abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp
  have hc : ContinuousOn g (Icc δ (Real.pi / 2)) := by
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.mul Real.continuous_sin.continuousOn).div_const _)
    intro t ht
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hu.ne') (hs t ht).ne')
      (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hm : AntitoneOn (fun t => |g t|) (Icc δ (Real.pi / 2)) := by
    intro t ht s hs' hts
    change |g s| ≤ |g t|
    rw [habs t ht, habs s hs']
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hu (hs t ht))
    exact mul_le_mul_of_nonneg_left
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ht.1, Real.pi_pos]) hs'.2 hts) hu.le
  have hb := ZetaAppendix.nonstationary_phase_integral_bound hδb φ
    (by dsimp [φ]; fun_prop) hne (fun _ => 1) g (fun t => by rw [hder]) hc hm
  have he (t : ℝ) : (1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (φ t : ℂ)) =
      Complex.exp (Complex.I * ((u * Real.cos t : ℝ) : ℂ)) := by
    rw [one_mul]
    congr 1
    dsimp [φ]
    push_cast
    field_simp
  change ‖∫ t in Icc δ (Real.pi / 2), (1 : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (φ t : ℂ))‖ ≤ |g δ| / Real.pi at hb
  simp_rw [he] at hb
  rw [habs δ ⟨le_rfl, hδb.le⟩] at hb
  rw [intervalIntegral.integral_of_le hδb.le, ← integral_Icc_eq_integral_Ioc]
  convert hb using 1
  field_simp

end Dubon2026
