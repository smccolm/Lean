import TaoTrudgianYang2025.ExponentPairLocalLargeValues
import TaoTrudgianYang2025.LargeValueSubdivisionBounds
import TaoTrudgianYang2025.ClassicalMeanSquareBound

/-! Closing the local-height endpoint before the actual subdivision step. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem IsLargeValueBound.subdivision_max {σ τ τ' B : ℝ}
    (h : IsLargeValueBound σ τ B) :
    IsLargeValueBound σ τ' (B+max 0 (τ'-τ)) := by
  by_cases ht : τ' ≤ τ
  · simpa only [max_eq_left (show τ'-τ ≤ 0 by linarith),add_zero] using h.of_height_le ht
  · simpa only [max_eq_right (show 0 ≤ τ'-τ by linarith)] using h.subdivision (by linarith)

theorem ExponentPair.closed_local_largeValueBound {k l σ c : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hc : 0 < c)
    (hscale : k*c = 2*σ-1-l+k) :
    IsLargeValueBound σ c (2-2*σ) := by
  intro ε hε
  let a := min (c/2) (ε/4)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hac : a ≤ c/2 := min_le_left _ _
  have hae : a ≤ ε/4 := min_le_right _ _
  have hlocal : IsLargeValueBound σ (c-a) (2-2*σ) := by
    apply hpair.local_largeValueBound (by linarith)
    have hka : 0 < k*a := mul_pos hk ha
    nlinarith
  have hsub := hlocal.subdivision (show c-a ≤ c by linarith)
  obtain ⟨C,hC,δ,hδ,hbound⟩ := hsub (ε/2) (by linarith)
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hN hTl hTu hVl hVu
  apply (hbound P hN hTl hTu hVl hVu).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
    (by linarith)

theorem ExponentPair.largeValueBound_of_positive_cutoff {k l σ τ c : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hc : 0 < c)
    (hscale : k*c = 2*σ-1-l+k) :
    IsLargeValueBound σ τ ((2-2*σ)+max 0 (τ-c)) :=
  (hpair.closed_local_largeValueBound hk hc hscale).subdivision_max

theorem ExponentPair.largeValueBound {k l σ τ : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ
      ((2-2*σ)+max 0 (τ-(2*σ-1-l+k)/k)) := by
  let c := (2*σ-1-l+k)/k
  by_cases hc : 0 < c
  · apply hpair.largeValueBound_of_positive_cutoff hk hc
    dsimp [c]
    field_simp
  · apply (obvious_largeValueBound σ hτ).mono
    have hmax := le_max_right 0 (τ-c)
    change τ ≤ (2-2*σ)+max 0 (τ-c)
    linarith

end TaoTrudgianYang2025
