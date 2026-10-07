import Dubon2026.HorizontalPhaseNull

/-! # Almost-everywhere nonvanishing on horizontal boundaries -/

namespace Dubon2026

open MeasureTheory

theorem ae_horizontal_phase_ne_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∀ᵐ z ∂torusHaar N, ∀ s : ℂ, l < s.re → s.re < u → s.im = 0 →
      dirichletSum (twistedCoefficients a N z) N s ≠ 0 := by
  filter_upwards [ae_horizontal_phase_count_eq_zero hN ha l u] with z hz
  intro s hl hu ht hs
  have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  have hmem := (mem_horizontalZerosFinset (twistedCoefficients a N z) N hN haz l u s).mpr
    ⟨hl, hu, ht, hs⟩
  have hpos := (zeroMultiplicity_pos_iff hN haz s).mpr hs
  have hle : zeroMultiplicity (twistedCoefficients a N z) N s ≤
      horizontalZeroCount (twistedCoefficients a N z) N hN haz l u :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

theorem ae_horizontal_phase_height_ne_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u τ : ℝ) :
    ∀ᵐ z ∂torusHaar N, ∀ s : ℂ, l < s.re → s.re < u → s.im = τ →
      dirichletSum (twistedCoefficients a N z) N s ≠ 0 := by
  have he := (measurePreserving_add_right (torusHaar N) (primeTorusFlow N τ)).quasiMeasurePreserving.ae
    (ae_horizontal_phase_ne_zero hN ha l u)
  filter_upwards [he] with z hz
  intro s hl hu ht hs
  have hre : (s - Complex.I * τ).re = s.re := by simp
  have him : (s - Complex.I * τ).im = 0 := by simp [ht]
  apply hz (s - Complex.I * τ) (by simpa only [hre] using hl)
    (by simpa only [hre] using hu) him
  rw [← twistedCoefficients_twice, dirichletSum_twist_height, sub_add_cancel]
  exact hs

theorem ae_horizontal_phase_closed_segment_ne_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u τ : ℝ) :
    ∀ᵐ z ∂torusHaar N, ∀ s : ℂ, l ≤ s.re → s.re ≤ u → s.im = τ →
      dirichletSum (twistedCoefficients a N z) N s ≠ 0 := by
  filter_upwards [ae_horizontal_phase_height_ne_zero hN ha (l - 1) (u + 1) τ] with z hz
  intro s hl hu ht
  exact hz s (by linarith) (by linarith) ht

end Dubon2026
