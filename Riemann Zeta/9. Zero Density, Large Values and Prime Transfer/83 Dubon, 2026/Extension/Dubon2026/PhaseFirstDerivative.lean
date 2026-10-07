import Dubon2026.IntegratedFrequency
import GuthMaynardExternal.PNT.ZetaAppendix

/-! # First derivative bounds for an actual complex phase given by its frequency -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A unit initial phase with monotone negative frequency has the exact nonstationary integral bound. -/
theorem norm_phase_integral_le_of_negative_frequency {ν : ℝ → ℝ} {z : ℝ → ℂ}
    (hν : Continuous ν) (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t)
    (hz0 : ‖z 0‖ = 1) {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hslope : ∀ t ∈ Icc a b, ν t ≤ -lam) (hmono : AntitoneOn ν (Icc a b)) :
    ‖∫ t in a..b, z t‖ ≤ 2 / lam := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  let φ : ℝ → ℝ := fun t => integratedFrequency ν t / (2 * Real.pi)
  let g : ℝ → ℝ := fun t => 1 / (ν t / (2 * Real.pi))
  have hd (t : ℝ) : deriv φ t = ν t / (2 * Real.pi) :=
    ((hasDerivAt_integratedFrequency hν t).div_const _).deriv
  have hneg (t : ℝ) (ht : t ∈ Icc a b) : ν t < 0 := by linarith [hslope t ht]
  have hne (t : ℝ) (ht : t ∈ Icc a b) : deriv φ t ≠ 0 := by
    rw [hd]
    exact div_ne_zero (hneg t ht).ne (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have habs (t : ℝ) (ht : t ∈ Icc a b) : |g t| = (2 * Real.pi) / (-ν t) := by
    dsimp [g]
    rw [one_div_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_neg (hneg t ht)]
  have hc : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.div continuousOn_const (hν.continuousOn.div_const _)
    intro t ht
    exact div_ne_zero (hneg t ht).ne (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hm : AntitoneOn (fun t => |g t|) (Icc a b) := by
    intro t ht u hu htu
    change |g u| ≤ |g t|
    rw [habs u hu, habs t ht]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith [hneg t ht])
      (neg_le_neg (hmono ht hu htu))
  have hb := ZetaAppendix.nonstationary_phase_integral_bound hab' φ
    ((contDiff_integratedFrequency hν).div_const (2 * Real.pi)).contDiffOn hne
    (fun _ => 1) g (fun t => by rw [hd]) hc hm
  have he (t : ℝ) : z t = z 0 * Complex.exp (2 * Real.pi * I * (φ t : ℂ)) := by
    rw [phase_eq_initial_mul_exp_integratedFrequency hν hz t]
    congr 2
    dsimp [φ]
    push_cast
    field_simp
  have hi : ‖∫ t in a..b, z t‖ =
      ‖∫ t in Icc a b, (1 : ℂ) * Complex.exp (2 * Real.pi * I * (φ t : ℂ))‖ := by
    rw [intervalIntegral.integral_congr (fun t _ => he t)]
    rw [intervalIntegral.integral_const_mul, norm_mul, hz0, one_mul,
      intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    simp only [one_mul]
  rw [hi]
  apply hb.trans
  rw [habs a ⟨le_rfl, hab⟩]
  have hrec := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.pi) hlam
    (show lam ≤ -ν a by linarith [hslope a ⟨le_rfl, hab⟩])
  have hbound := div_le_div_of_nonneg_right hrec Real.pi_pos.le
  convert hbound using 1
  field_simp

/-- Reflection yields the same bound for monotone positive frequency, for the same genuine phase. -/
theorem norm_phase_integral_le_of_positive_frequency {ν : ℝ → ℝ} {z : ℝ → ℂ}
    (hν : Continuous ν) (hz : ∀ t : ℝ, HasDerivAt z (I * (ν t : ℂ) * z t) t)
    (hz0 : ‖z 0‖ = 1) {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hslope : ∀ t ∈ Icc a b, lam ≤ ν t) (hmono : AntitoneOn ν (Icc a b)) :
    ‖∫ t in a..b, z t‖ ≤ 2 / lam := by
  have hmem (t : ℝ) (ht : t ∈ Icc (-b) (-a)) : -t ∈ Icc a b := by
    constructor <;> linarith [ht.1, ht.2]
  have hz' (t : ℝ) : HasDerivAt (fun u => z (-u)) (I * ((-ν (-t) : ℝ) : ℂ) * z (-t)) t := by
    convert (hz (-t)).scomp t (hasDerivAt_neg t) using 1
    simp
  have hb := norm_phase_integral_le_of_negative_frequency
    (ν := fun t => -ν (-t)) (z := fun t => z (-t))
    (hν.comp continuous_neg).neg hz' (by simpa using hz0) (by linarith : -b ≤ -a) hlam
    (fun t ht => neg_le_neg (hslope (-t) (hmem t ht)))
    (fun t ht u hu htu => neg_le_neg (hmono (hmem u hu) (hmem t ht) (by linarith)))
  rw [intervalIntegral.integral_comp_neg] at hb
  simpa only [neg_neg] using hb

end
end Dubon2026
