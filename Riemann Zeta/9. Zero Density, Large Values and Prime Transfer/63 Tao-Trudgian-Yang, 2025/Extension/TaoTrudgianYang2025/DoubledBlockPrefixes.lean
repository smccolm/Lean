import TaoTrudgianYang2025.TruncatedDyadicPartition

/-! Full doubled-interval control of arbitrary prefixes.
Odd endpoints cost one coefficient; no truncated dyadic block is substituted. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem norm_prefix_le_doubled_blocks (a : ℕ → ℂ) (H J N : ℕ)
    (ha0 : a 0 = 0) (hNH : N ≤ H) (hNJ : N ≤ 2^J)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ n < H, ‖a n‖ ≤ A)
    (hb : ∀ k : ℕ, 0 < k → 2*k ≤ H →
      ‖∑ j ∈ Finset.range k, a (k+j)‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n‖ ≤ (J:ℝ)*(A+B) := by
  induction J generalizing N with
  | zero =>
    have hn : N = 0 ∨ N = 1 := by
      simp only [pow_zero] at hNJ
      omega
    rcases hn with hn | hn <;> subst N <;> simp [ha0]
  | succ J ih =>
    by_cases hsmall : N ≤ 1
    · have hn : N = 0 ∨ N = 1 := by omega
      rcases hn with hn | hn <;> subst N <;> simp only [Finset.range_zero,
        Finset.sum_empty,Finset.sum_range_one,ha0,norm_zero]
      all_goals positivity
    · let k := N/2
      have hk : 0 < k := by dsimp [k]; omega
      have hkH : k ≤ H := by dsimp [k]; omega
      have h2kH : 2*k ≤ H := by dsimp [k]; omega
      have hkJ : k ≤ 2^J := by
        rw [pow_succ] at hNJ
        dsimp [k]
        omega
      have hip := ih k hkH hkJ
      have htail : ‖∑ j ∈ Finset.range (N%2), a (k+k+j)‖ ≤ A := by
        have hr : N%2 = 0 ∨ N%2 = 1 := by omega
        rcases hr with hr | hr
        · simp only [hr,Finset.range_zero,Finset.sum_empty,norm_zero]
          exact hA
        · simp only [hr,Finset.sum_range_one,add_zero]
          apply ha
          dsimp [k]
          omega
      have he : (∑ n ∈ Finset.range N, a n) =
          ((∑ n ∈ Finset.range k, a n)+∑ j ∈ Finset.range k, a (k+j))+
            ∑ j ∈ Finset.range (N%2), a (k+k+j) := by
        have hNk : N = k+k+N%2 := by dsimp [k]; omega
        calc
          _ = ∑ n ∈ Finset.range (k+k+N%2), a n :=
            congrArg (fun L => ∑ n ∈ Finset.range L, a n) hNk
          _ = _ := by rw [Finset.sum_range_add,Finset.sum_range_add]
      rw [he]
      calc
        _ ≤ (‖∑ n ∈ Finset.range k, a n‖+
            ‖∑ j ∈ Finset.range k, a (k+j)‖)+
            ‖∑ j ∈ Finset.range (N%2), a (k+k+j)‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ ((J:ℝ)*(A+B)+B)+A :=
          add_le_add (add_le_add hip (hb k hk h2kH)) htail
        _ = _ := by push_cast; ring

end TaoTrudgianYang2025
