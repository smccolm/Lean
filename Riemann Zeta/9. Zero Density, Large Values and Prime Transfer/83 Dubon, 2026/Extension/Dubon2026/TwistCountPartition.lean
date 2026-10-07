import Dubon2026.TorusPhaseRegularity
import Dubon2026.TwistCountMeasurable

/-! # Exact strip partitions and local constancy from boundary-line counts -/

namespace Dubon2026

open Filter Set MeasureTheory Complex
open scoped Topology

noncomputable section

theorem twistZeroCount_split_at_line {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u σ : ℝ} (hl : l < σ) (hu : σ < u)
    (H : ℝ) (z : PrimeTorus N) :
    twistZeroCount a N hN ha l u H z = twistZeroCount a N hN ha l σ H z +
      twistVerticalLineZeroCount a N hN ha l u H σ z + twistZeroCount a N hN ha σ u H z := by
  classical
  have haz : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  let S := zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN haz l u H
  have hleft : zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN haz l σ H =
      S.filter (fun s => s.re < σ) := by
    ext s
    simp only [S, Finset.mem_filter, mem_zerosInOpenRectangleFinset]
    constructor
    · rintro ⟨hs, ht, hh, hz⟩
      exact ⟨⟨hs, ht.trans hu, hh, hz⟩, ht⟩
    · rintro ⟨⟨hs, _, hh, hz⟩, ht⟩
      exact ⟨hs, ht, hh, hz⟩
  have hright : zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN haz σ u H =
      S.filter (fun s => σ < s.re) := by
    ext s
    simp only [S, Finset.mem_filter, mem_zerosInOpenRectangleFinset]
    constructor
    · rintro ⟨hs, ht, hh, hz⟩
      exact ⟨⟨hl.trans hs, ht, hh, hz⟩, hs⟩
    · rintro ⟨⟨_, ht, hh, hz⟩, hs⟩
      exact ⟨hs, ht, hh, hz⟩
  change (∑ s ∈ S, zeroMultiplicity (twistedCoefficients a N z) N s) = _
  unfold twistZeroCount verticalZeroCount twistVerticalLineZeroCount
  rw [hleft, hright]
  change (∑ s ∈ S, zeroMultiplicity (twistedCoefficients a N z) N s) =
    (∑ s ∈ S.filter (fun s => s.re < σ), zeroMultiplicity (twistedCoefficients a N z) N s) +
    (∑ s ∈ S.filter (fun s => s.re = σ), zeroMultiplicity (twistedCoefficients a N z) N s) +
    (∑ s ∈ S.filter (fun s => σ < s.re), zeroMultiplicity (twistedCoefficients a N z) N s)
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rcases lt_trichotomy s.re σ with h | h | h
  · simp only [if_pos h, if_neg h.ne, if_neg (not_lt_of_ge h.le), add_zero]
  · simp only [h, lt_self_iff_false, if_false, if_true, zero_add, add_zero]
  · simp only [if_neg (not_lt_of_ge h.le), if_neg h.ne', if_pos h, zero_add]

theorem lowerSemicontinuous_nat_eventually_le {X : Type*} [TopologicalSpace X]
    {f : X → ℕ} {x : X} (hf : LowerSemicontinuousAt f x) :
    ∀ᶠ y in 𝓝 x, f x ≤ f y := by
  by_cases hx : f x = 0
  · exact Filter.Eventually.of_forall fun _ => by rw [hx]; exact Nat.zero_le _
  · have hh := hf (f x - 1) (by omega)
    filter_upwards [hh] with y hy
    omega

/-- With a fixed total and fixed cut-line counts, lower semicontinuity forces each
open component count to be locally constant. -/
theorem eventually_eq_twistZeroCount_of_line_counts {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {L l u U H : ℝ}
    (hL : L < l) (hlu : l < u) (hU : u < U) (z : PrimeTorus N)
    (ht : ∀ᶠ w in 𝓝 z, twistZeroCount a N hN ha L U H w = twistZeroCount a N hN ha L U H z)
    (hl : ∀ᶠ w in 𝓝 z, twistVerticalLineZeroCount a N hN ha L U H l w =
      twistVerticalLineZeroCount a N hN ha L U H l z)
    (hu : ∀ᶠ w in 𝓝 z, twistVerticalLineZeroCount a N hN ha L U H u w =
      twistVerticalLineZeroCount a N hN ha L U H u z) :
    ∀ᶠ w in 𝓝 z, twistZeroCount a N hN ha l u H w = twistZeroCount a N hN ha l u H z := by
  have h₁ := lowerSemicontinuous_nat_eventually_le
    (lowerSemicontinuous_twistZeroCount hN ha L l H z)
  have h₂ := lowerSemicontinuous_nat_eventually_le
    (lowerSemicontinuous_twistZeroCount hN ha l u H z)
  have h₃ := lowerSemicontinuous_nat_eventually_le
    (lowerSemicontinuous_twistZeroCount hN ha u U H z)
  have he (v : PrimeTorus N) : twistZeroCount a N hN ha L U H v =
      twistZeroCount a N hN ha L l H v + twistVerticalLineZeroCount a N hN ha L U H l v +
      twistZeroCount a N hN ha l u H v + twistVerticalLineZeroCount a N hN ha L U H u v +
      twistZeroCount a N hN ha u U H v := by
    rw [twistZeroCount_split_at_line hN ha hL (hlu.trans hU),
      twistZeroCount_split_at_line hN ha hlu hU,
      twistVerticalLineZeroCount_eq_of_bounds hN ha hlu hU (hL.trans hlu) hU]
    omega
  filter_upwards [ht, hl, hu, h₁, h₂, h₃] with w htw hlw huw h₁w h₂w h₃w
  have hw := he w
  have hz := he z
  omega

end

end Dubon2026
