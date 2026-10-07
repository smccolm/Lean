import Dubon2026.HorizontalZeroCount

/-! # Almost every phase has no zero on a prescribed horizontal segment -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

theorem measurable_horizontal_phase_count {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    Measurable (fun z : PrimeTorus N => (horizontalZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u : ℝ)) := by
  apply measurable_of_tendsto_metrizable' (𝓝[>] (0 : ℝ))
    (f := fun H z => (twistZeroCount a N hN ha l u H z : ℝ))
  · intro H
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_twistZeroCount hN ha l u H)
  · apply tendsto_pi_nhds.mpr
    intro z
    have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_small_count_eq_horizontal
      (twistedCoefficients a N z) N hN haz l u] with H hH
    exact congrArg (fun n : ℕ => (n : ℝ)) hH.symm

theorem integrable_horizontal_phase_count {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    Integrable (fun z : PrimeTorus N => (horizontalZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u : ℝ)) (torusHaar N) := by
  apply (integrable_twistZeroCount hN ha l u 1).mono'
    (measurable_horizontal_phase_count hN ha l u).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast horizontalZeroCount_le_vertical (twistedCoefficients a N z) N hN
    (by rwa [twistedCoefficients_one]) l u zero_lt_one

theorem integral_horizontal_phase_count_eq_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    (∫ z, (horizontalZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u : ℝ) ∂torusHaar N) = 0 := by
  obtain ⟨K, _, hK⟩ := exists_integral_twistZeroCount_le_height hN ha l u
  apply le_antisymm ?_ (integral_nonneg (fun _ => Nat.cast_nonneg _))
  have hlim : Tendsto (fun H : ℝ => K * H) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun H : ℝ => K * H) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_id.const_mul K).tendsto 0
    simpa only [mul_zero] using hh.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  have hsmall : ∀ᶠ H : ℝ in 𝓝[>] 0, H < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hsmall, self_mem_nhdsWithin] with H hH₁ hHp
  apply le_trans ?_ (hK H (le_of_lt hHp) hH₁.le)
  apply integral_mono (integrable_horizontal_phase_count hN ha l u)
    (integrable_twistZeroCount hN ha l u H)
  intro z
  dsimp only [twistZeroCount]
  exact_mod_cast horizontalZeroCount_le_vertical (twistedCoefficients a N z) N hN
    (by rwa [twistedCoefficients_one]) l u hHp

theorem ae_horizontal_phase_count_eq_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∀ᵐ z ∂torusHaar N, horizontalZeroCount (twistedCoefficients a N z) N hN
      (by rwa [twistedCoefficients_one]) l u = 0 := by
  have he := (integral_eq_zero_iff_of_nonneg (fun _ => Nat.cast_nonneg _)
    (integrable_horizontal_phase_count hN ha l u)).mp
      (integral_horizontal_phase_count_eq_zero hN ha l u)
  filter_upwards [he] with z hz
  simp only [Pi.zero_apply] at hz
  exact_mod_cast hz

end

end Dubon2026
