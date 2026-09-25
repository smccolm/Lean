import TaoTrudgianYang2025.ContinuousDerivativeBounds
import TaoTrudgianYang2025.SecondDerivativeScale
import GafniTao.FordTaylorPhase

/-! Explicit continuous second-derivative test for the actual additive character. -/

noncomputable section
open Set GafniTao RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem fordAdditiveCharacter_eq_unitaryPhase (x : ℝ) :
    fordAdditiveCharacter x = unitaryPhase (2*Real.pi*x) := by
  unfold fordAdditiveCharacter unitaryPhase
  congr 1
  push_cast
  ring

theorem continuous_second_derivative_bound
    (F F' F'' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N+1), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N+1), HasDerivAt F' (F'' x) x)
    (hlo : ∀ x ∈ Icc A (A+N+1), α ≤ F'' x)
    (hhi : ∀ x ∈ Icc A (A+N+1), F'' x ≤ C*α) :
    ‖∑ n ∈ Finset.range (N+1), fordAdditiveCharacter (F (A+n))‖ ≤
      12*(C*N*Real.sqrt α+2/Real.sqrt α) := by
  have hd (n : ℕ) (hn : n < N) :=
    continuous_second_difference_bounds F F' F''
      (x := A+n) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show A+(n:ℝ)+2 ≤ A+N+1 by
        have hn' : (n:ℝ)+1 ≤ N := by exact_mod_cast hn
        linarith)
      hF hF' hlo hhi
  have hlo' (n : ℕ) (hn : n < N) :
      2*Real.pi*α ≤
        (2*Real.pi*F (A+(n+2:ℕ))-2*Real.pi*F (A+(n+1:ℕ)))-
          (2*Real.pi*F (A+(n+1:ℕ))-2*Real.pi*F (A+n)) := by
    have hb := mul_le_mul_of_nonneg_left (hd n hn).1
      (show 0 ≤ 2*Real.pi by positivity)
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,← add_assoc,mul_sub] using hb
  have hhi' (n : ℕ) (hn : n < N) :
      (2*Real.pi*F (A+(n+2:ℕ))-2*Real.pi*F (A+(n+1:ℕ)))-
        (2*Real.pi*F (A+(n+1:ℕ))-2*Real.pi*F (A+n)) ≤ 2*Real.pi*(C*α) := by
    have hb := mul_le_mul_of_nonneg_left (hd n hn).2
      (show 0 ≤ 2*Real.pi by positivity)
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,← add_assoc,mul_sub] using hb
  simp_rw [fordAdditiveCharacter_eq_unitaryPhase]
  exact (vanDerCorput_second_derivative (fun n => 2*Real.pi*F (A+n)) N
    (2*Real.pi*α) (2*Real.pi*(C*α)) (Real.sqrt α)
    (by positivity) (Real.sqrt_pos.mpr hα) hlo' hhi').trans
      (second_derivative_scale_bound (Nat.cast_nonneg N) hC hα hα1)

end TaoTrudgianYang2025
