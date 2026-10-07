import Dubon2026.TwistContourContinuity
import Dubon2026.InnerZeroRectangle
import Dubon2026.TwistCountFrequency
import Dubon2026.ZeroCountInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurability of the actual phase zero count

A zero-free inner rectangle retains every zero already in the open rectangle.
Its count is locally constant under phase variation, proving lower semicontinuity
and hence Borel measurability of the original multiplicity count. Almost-everywhere
continuity at arbitrary boundary atoms remains a distinct obligation.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem lowerSemicontinuous_twistZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) :
    LowerSemicontinuous (twistZeroCount a N hN ha l u H) := by
  intro z k hk
  have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  have hS : (zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN haz l u H).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hz : twistZeroCount a N hN ha l u H z = 0 := by
      simp only [twistZeroCount, verticalZeroCount, he, Finset.sum_empty]
    omega
  obtain ⟨s, hs⟩ := hS
  obtain ⟨hl, hu, ht, _⟩ := (mem_zerosInOpenRectangleFinset
    (twistedCoefficients a N z) N hN haz l u H s).mp hs
  obtain ⟨L, U, V, hL, hLU, hU, hVp, hV, hn, he⟩ :=
    exists_inner_zero_free_rectangle hN haz (hl.trans hu) ((abs_nonneg s.im).trans_lt ht)
  have hbase : twistZeroCount a N hN ha L U V z = twistZeroCount a N hN ha l u H z := by
    unfold twistZeroCount verticalZeroCount
    rw [he]
  have hloc := eventually_eq_twistZeroCount_of_boundary_ne_zero hN ha z hLU.le hVp.le hn
  filter_upwards [hloc] with w hw
  have haw : twistedCoefficients a N w 1 ≠ 0 := by rwa [twistedCoefficients_one]
  have hm : twistZeroCount a N hN ha L U V w ≤ twistZeroCount a N hN ha l u H w :=
    (verticalZeroCount_mono_height hN haw L U hV.le).trans
      (verticalZeroCount_mono_interval hN haw hL.le hU.le H)
  rw [hw, hbase] at hm
  exact hk.trans_le hm

theorem measurable_twistZeroCount {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) :
    Measurable (twistZeroCount a N hN ha l u H) :=
  (lowerSemicontinuous_twistZeroCount hN ha l u H).measurable

theorem tendsto_zeroDensity_of_twist_count_ae_continuous {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ)
    (hc : ∀ᵐ z ∂torusHaar N, ContinuousAt (twistZeroCount a N hN ha l u 1) z) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T))
      atTop (𝓝 ((∫ z, (twistZeroCount a N hN ha l u 1 z : ℝ) ∂torusHaar N) / 2)) :=
  tendsto_zeroDensity_of_twist_count_regular hN ha l u
    (measurable_twistZeroCount hN ha l u 1) hc

end

end Dubon2026
