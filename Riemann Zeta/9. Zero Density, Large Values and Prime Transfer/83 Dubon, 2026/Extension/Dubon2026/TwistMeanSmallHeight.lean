import Dubon2026.TwistCountStationarity
import Dubon2026.SlidingRadiusBound
import Mathlib.MeasureTheory.Integral.Prod

/-! # Haar mean zero counts in windows of small height -/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

theorem exists_integral_twistZeroCount_le_height {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H : ℝ, 0 ≤ H → H ≤ 1 →
      (∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N) ≤ K * H := by
  obtain ⟨K, hK⟩ := exists_uniform_twistZeroCount_bound hN ha l u 2
  refine ⟨K, Nat.cast_nonneg _, ?_⟩
  intro H hH hH₁
  let f : PrimeTorus N → ℝ → ℝ := fun z t =>
    (twistZeroCount a N hN ha l u H (z + primeTorusFlow N t) : ℝ)
  have hm : Measurable (Function.uncurry f) := by
    have hg : Measurable (fun z => (twistZeroCount a N hN ha l u H z : ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (measurable_twistZeroCount hN ha l u H)
    exact hg.comp ((continuous_fst.add ((continuous_primeTorusFlow N).comp continuous_snd)).measurable)
  have hbound (z : PrimeTorus N) : twistZeroCount a N hN ha l u H z ≤ K := by
    have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
    exact (verticalZeroCount_mono_height hN haz l u (by linarith : H ≤ 2)).trans (hK z)
  have hi : Integrable (Function.uncurry f)
      ((torusHaar N).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    apply (integrable_const (K : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with zt
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.uncurry, f]
    exact_mod_cast hbound (zt.1 + primeTorusFlow N zt.2)
  have he : (∫ z, (∫ t in Ioc (-1 : ℝ) 1, f z t) ∂torusHaar N) =
      2 * ∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N := by
    rw [integral_integral_swap hi]
    simp only [f, integral_twistZeroCount_add]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num)]
    norm_num
  have hb (z : PrimeTorus N) : (∫ t in Ioc (-1 : ℝ) 1, f z t) ≤ 2 * H * K := by
    have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
    have hh := integral_slidingZeroCount_le_radius (twistedCoefficients a N z) N hN haz
      l u (T := 1) (by norm_num) hH
    have hcount : (verticalZeroCount (twistedCoefficients a N z) N hN haz l u (1 + H) : ℝ) ≤ K := by
      exact_mod_cast (verticalZeroCount_mono_height hN haz l u
        (by linarith : 1 + H ≤ 2)).trans (hK z)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hh
    have htrans : (fun t : ℝ =>
        (slidingZeroCount (twistedCoefficients a N z) N hN haz l u H t : ℝ)) = f z := by
      funext t
      exact congrArg (fun n : ℕ => (n : ℝ))
        (slidingZeroCount_twisted a N hN ha l u H t z)
    rw [htrans] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hcount (by positivity))
  have hh := integral_mono hi.integral_prod_left (integrable_const (2 * H * (K : ℝ))) hb
  dsimp only [Function.uncurry] at hh
  rw [he] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  nlinarith

end

end Dubon2026
