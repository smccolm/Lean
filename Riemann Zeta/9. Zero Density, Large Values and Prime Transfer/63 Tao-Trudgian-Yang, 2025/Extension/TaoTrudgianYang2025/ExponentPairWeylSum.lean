import TaoTrudgianYang2025.ExponentPairShiftDistanceSum

/-!
# Weyl differencing with the actual sum over nonzero correlations

The finite Cauchy--Schwarz expansion and the two-per-row distance count
give the factor 2H, rather than H squared times a worst correlation.
-/

noncomputable section

open Complex Finset RiemannZeta.GuthMaynard
open scoped BigOperators InnerProductSpace

namespace TaoTrudgianYang2025

theorem interval_weyl_differencing_sum
    (a : ℤ → ℂ) (N H : ℕ) (C : ℕ → ℝ)
    (ha : ∀ n ∈ Ico (0 : ℤ) N, ‖a n‖ ≤ 1)
    (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r)
    (hcorr : ∀ h ∈ range H, ∀ k ∈ range H, h ≠ k →
      ‖∑ n ∈ Ico (-(H : ℤ)) N,
        star (paddedShift a N n h)*paddedShift a N n k‖ ≤ C (shiftDistance h k)) :
    (H : ℝ)^2*‖∑ n ∈ Ico (0 : ℤ) N, a n‖^2 ≤
      ((N+H : ℕ) : ℝ)*((H : ℝ)*N+2*H*∑ r ∈ Icc 1 (H-1), C r) := by
  let s := Ico (-(H : ℤ)) (N : ℤ)
  let b : ℤ → ℕ → ℂ := fun n h => paddedShift a N n h
  let u : ℤ → ℂ := fun n => ∑ h ∈ range H, b n h
  let S : ℂ := ∑ n ∈ Ico (0 : ℤ) N, a n
  have hsum : ∑ n ∈ s, u n = H • S := by
    dsimp [u,b,s]
    rw [sum_comm]
    calc
      _ = ∑ _h ∈ range H, S := by
        apply sum_congr rfl
        intro h hh
        exact sum_paddedShift_eq a N H h (mem_range.mp hh)
      _ = _ := by simp
  have hdiag (h : ℕ) (hh : h ∈ range H) : ∑ n ∈ s, ‖b n h‖^2 ≤ (N : ℝ) := by
    dsimp [s,b]
    rw [sum_norm_sq_paddedShift_eq a N H h (mem_range.mp hh)]
    calc
      _ ≤ ∑ _n ∈ Ico (0 : ℤ) N, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        nlinarith [norm_nonneg (a n),ha n hn]
      _ = _ := by simp [Int.card_Ico]
  have hexpand : ∑ n ∈ s, ‖u n‖^2 =
      ∑ h ∈ range H, ∑ k ∈ range H, ∑ n ∈ s, ⟪b n h,b n k⟫_ℝ := by
    simp only [u,← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro h _
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro n _
    exact real_inner_comm _ _
  have hpair (h : ℕ) (hh : h ∈ range H) (k : ℕ) (hk : k ∈ range H) :
      ∑ n ∈ s, ⟪b n h,b n k⟫_ℝ ≤
        if h = k then (N : ℝ) else C (shiftDistance h k) := by
    by_cases he : h = k
    · subst k
      simp only [real_inner_self_eq_norm_sq]
      exact hdiag h hh
    · rw [if_neg he]
      let z := ∑ n ∈ s, star (b n h)*b n k
      have hre : (∑ n ∈ s, ⟪b n h,b n k⟫_ℝ) = z.re := by
        dsimp [z]
        simp only [Complex.re_sum]
        apply sum_congr rfl
        intro n _
        simp
        ring
      rw [hre]
      exact (Complex.re_le_norm z).trans (hcorr h hh k hk he)
  have hrow (h : ℕ) (hh : h ∈ range H) :
      (∑ k ∈ range H, ∑ n ∈ s, ⟪b n h,b n k⟫_ℝ) ≤
        (N : ℝ)+2*∑ r ∈ Icc 1 (H-1), C r := by
    exact (sum_le_sum fun k hk => hpair h hh k hk).trans
      (sum_shift_distance_row_le C N (mem_range.mp hh) hC)
  have htotal : (∑ h ∈ range H, ∑ k ∈ range H, ∑ n ∈ s, ⟪b n h,b n k⟫_ℝ) ≤
      (H : ℝ)*N+2*H*∑ r ∈ Icc 1 (H-1), C r := by
    calc
      _ ≤ ∑ _h ∈ range H, ((N : ℝ)+2*∑ r ∈ Icc 1 (H-1), C r) :=
        sum_le_sum hrow
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring
  have hcard : (s.card : ℝ) = ((N+H : ℕ) : ℝ) := by
    dsimp [s]
    norm_num [Int.card_Ico]
    norm_cast
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq s u
  rw [hsum,RCLike.norm_nsmul ℂ,nsmul_eq_mul,hexpand,hcard] at hcs
  calc
    _ = ((H : ℝ)*‖S‖)^2 := by ring
    _ ≤ ((N+H : ℕ) : ℝ)*
        (∑ h ∈ range H, ∑ k ∈ range H, ∑ n ∈ s, ⟪b n h,b n k⟫_ℝ) := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg _)

end TaoTrudgianYang2025
