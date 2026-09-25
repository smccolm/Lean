import TaoTrudgianYang2025.ContinuousThirdDerivative

/-! Second-derivative bounds for arbitrary finite prefix lengths and either fixed sign. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem continuous_second_derivative_range_bound
    (F F' F'' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), α ≤ F'' x)
    (hhi : ∀ x ∈ Icc A (A+N), F'' x ≤ C*α) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      12*(C*N*Real.sqrt α+2/Real.sqrt α) := by
  cases N with
  | zero =>
      simp only [Finset.sum_range_zero,norm_zero,Nat.cast_zero,mul_zero,zero_mul,zero_add]
      positivity
  | succ N =>
      have hF0 : ∀ x ∈ Icc A (A+N+1), HasDerivAt F (F' x) x := by
        simpa only [Nat.cast_succ,add_assoc] using hF
      have hF1 : ∀ x ∈ Icc A (A+N+1), HasDerivAt F' (F'' x) x := by
        simpa only [Nat.cast_succ,add_assoc] using hF'
      have hl : ∀ x ∈ Icc A (A+N+1), α ≤ F'' x := by
        simpa only [Nat.cast_succ,add_assoc] using hlo
      have hu : ∀ x ∈ Icc A (A+N+1), F'' x ≤ C*α := by
        simpa only [Nat.cast_succ,add_assoc] using hhi
      have hb := continuous_second_derivative_bound F F' F'' A N hC hα hα1 hF0 hF1 hl hu
      have hs : 0 ≤ C*Real.sqrt α := by positivity
      push_cast
      nlinarith

theorem continuous_second_derivative_negative_range_bound
    (F F' F'' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), -(C*α) ≤ F'' x)
    (hhi : ∀ x ∈ Icc A (A+N), F'' x ≤ -α) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      12*(C*N*Real.sqrt α+2/Real.sqrt α) := by
  have hb := continuous_second_derivative_range_bound
    (fun x => -F x) (fun x => -F' x) (fun x => -F'' x) A N hC hα hα1
    (fun x hx => (hF x hx).neg) (fun x hx => (hF' x hx).neg)
    (fun x hx => by linarith [hhi x hx]) (fun x hx => by linarith [hlo x hx])
  rwa [norm_sum_fordAdditiveCharacter_neg_phase] at hb

end TaoTrudgianYang2025
