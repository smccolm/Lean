import TaoTrudgianYang2025.ExponentPairFiniteCorrelation

/-!
# Counting each nonzero shift distance at most twice

The row bounds retain the sum over correlations. Replacing that sum by
a uniform worst correlation would lose the small-shift cancellation
needed by the analytic A-process.
-/

noncomputable section

open Finset RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sum_lower_shift_distances_le (C : ℕ → ℝ) {H h : ℕ}
    (hh : h < H) (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if k < h then C (h-k) else 0) ≤
      ∑ r ∈ Icc 1 (H-1), C r := by
  let s := (range H).filter (fun k => k < h)
  have hinj : Set.InjOn (fun k => h-k) (s : Set ℕ) := by
    intro x hx y hy he
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    dsimp at he
    omega
  have hsub : s.image (fun k => h-k) ⊆ Icc 1 (H-1) := by
    intro r hr
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hr
    have hk' := (mem_filter.mp hk).2
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ s, C (h-k) := by simp only [s,sum_filter]
    _ = ∑ r ∈ s.image (fun k => h-k), C r := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => hC r hr)

theorem sum_upper_shift_distances_le (C : ℕ → ℝ) {H h : ℕ}
    (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if h < k then C (k-h) else 0) ≤
      ∑ r ∈ Icc 1 (H-1), C r := by
  let s := (range H).filter (fun k => h < k)
  have hinj : Set.InjOn (fun k => k-h) (s : Set ℕ) := by
    intro x hx y hy he
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    dsimp at he
    omega
  have hsub : s.image (fun k => k-h) ⊆ Icc 1 (H-1) := by
    intro r hr
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hr
    have hk' := mem_filter.mp hk
    have hkH := mem_range.mp hk'.1
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ s, C (k-h) := by simp only [s,sum_filter]
    _ = ∑ r ∈ s.image (fun k => k-h), C r := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => hC r hr)

theorem sum_shift_distance_row_le (C : ℕ → ℝ) (D : ℝ) {H h : ℕ}
    (hh : h < H) (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if h = k then D else C (shiftDistance h k)) ≤
      D+2*∑ r ∈ Icc 1 (H-1), C r := by
  have he (k : ℕ) :
      (if h = k then D else C (shiftDistance h k)) =
        (if k = h then D else 0)+
          (if k < h then C (h-k) else 0)+(if h < k then C (k-h) else 0) := by
    rcases lt_trichotomy h k with hk | hk | hk
    · simp [hk,ne_of_lt hk,ne_of_gt hk,not_lt_of_ge hk.le,
        shiftDistance,Nat.sub_eq_zero_of_le hk.le]
    · subst k
      simp
    · simp [hk,ne_of_lt hk,ne_of_gt hk,not_lt_of_ge hk.le,
        shiftDistance,Nat.sub_eq_zero_of_le hk.le]
  simp_rw [he]
  rw [sum_add_distrib,sum_add_distrib]
  have hdiag : (∑ k ∈ range H, if k = h then D else 0) = D := by
    simp [mem_range.mpr hh]
  rw [hdiag]
  linarith [sum_lower_shift_distances_le C hh hC,sum_upper_shift_distances_le (h := h) C hC]

end TaoTrudgianYang2025
