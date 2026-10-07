import Dubon2026.TwistCountRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Convergence of the genuine finite-window count under exhaustion of an open strip -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem eventually_eq_verticalZeroCount_inner {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} {L U : ℕ → ℝ}
    (hL : ∀ n, l ≤ L n) (hU : ∀ n, U n ≤ u)
    (htL : Tendsto L atTop (𝓝 l)) (htU : Tendsto U atTop (𝓝 u)) (H : ℝ) :
    ∀ᶠ n in atTop, verticalZeroCount a N hN ha (L n) (U n) H =
      verticalZeroCount a N hN ha l u H := by
  classical
  let S := zerosInOpenRectangleFinset a N hN ha l u H
  have he : ∀ᶠ n in atTop, ∀ s ∈ S, L n < s.re ∧ s.re < U n := by
    apply S.eventually_all.mpr
    intro s hs
    obtain ⟨hl, hu, _, _⟩ := (mem_zerosInOpenRectangleFinset a N hN ha l u H s).mp hs
    exact (htL.eventually (Iio_mem_nhds hl)).and (htU.eventually (Ioi_mem_nhds hu))
  filter_upwards [he] with n hn
  have hs : zerosInOpenRectangleFinset a N hN ha (L n) (U n) H = S := by
    ext s
    constructor
    · intro hs
      rw [mem_zerosInOpenRectangleFinset] at hs
      exact (mem_zerosInOpenRectangleFinset a N hN ha l u H s).mpr
        ⟨(hL n).trans_lt hs.1, hs.2.1.trans_le (hU n), hs.2.2⟩
    · intro hs
      have hh := hn s hs
      have hm := (mem_zerosInOpenRectangleFinset a N hN ha l u H s).mp hs
      exact (mem_zerosInOpenRectangleFinset a N hN ha (L n) (U n) H s).mpr
        ⟨hh.1, hh.2, hm.2.2⟩
  exact congrArg (fun s => ∑ z ∈ s, zeroMultiplicity a N z) hs

theorem tendsto_integral_twistZeroCount_inner {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u : ℝ} {L U : ℕ → ℝ}
    (hL : ∀ n, l ≤ L n) (hU : ∀ n, U n ≤ u)
    (htL : Tendsto L atTop (𝓝 l)) (htU : Tendsto U atTop (𝓝 u)) (H : ℝ) :
    Tendsto (fun n => ∫ z, (twistZeroCount a N hN ha (L n) (U n) H z : ℝ) ∂torusHaar N)
      atTop (𝓝 (∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun z => (twistZeroCount a N hN ha l u H z : ℝ))
  · exact fun n => (integrable_twistZeroCount hN ha (L n) (U n) H).aestronglyMeasurable
  · exact integrable_twistZeroCount hN ha l u H
  · intro n
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast verticalZeroCount_mono_interval hN
      (by rwa [twistedCoefficients_one] : twistedCoefficients a N z 1 ≠ 0) (hL n) (hU n) H
  · filter_upwards with z
    have he := eventually_eq_verticalZeroCount_inner hN
      (by rwa [twistedCoefficients_one] : twistedCoefficients a N z 1 ≠ 0) hL hU htL htU H
    exact tendsto_const_nhds.congr' (he.mono fun _ h => congrArg Nat.cast h.symm)

theorem iUnion_inner_open_intervals {l u : ℝ} {L U : ℕ → ℝ}
    (hL : ∀ n, l ≤ L n) (hU : ∀ n, U n ≤ u)
    (htL : Tendsto L atTop (𝓝 l)) (htU : Tendsto U atTop (𝓝 u)) :
    (⋃ n, Ioo (L n) (U n)) = Ioo l u := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨(hL n).trans_lt hn.1, hn.2.trans_le (hU n)⟩
  · intro hx
    obtain ⟨n, hnL, hnU⟩ := ((htL.eventually (Iio_mem_nhds hx.1)).and
      (htU.eventually (Ioi_mem_nhds hx.2))).exists
    exact mem_iUnion.mpr ⟨n, hnL, hnU⟩

theorem tendsto_measure_inner_open_intervals (μ : Measure ℝ)
    {l u : ℝ} {L U : ℕ → ℝ} (hmL : Antitone L) (hmU : Monotone U)
    (hL : ∀ n, l ≤ L n) (hU : ∀ n, U n ≤ u)
    (htL : Tendsto L atTop (𝓝 l)) (htU : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun n => μ (Ioo (L n) (U n))) atTop (𝓝 (μ (Ioo l u))) := by
  rw [← iUnion_inner_open_intervals hL hU htL htU]
  apply tendsto_measure_iUnion_atTop
  intro n m hnm x hx
  exact ⟨(hmL hnm).trans_lt hx.1, hx.2.trans_le (hmU hnm)⟩

end

end Dubon2026
