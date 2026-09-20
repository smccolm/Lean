import TaoTrudgianYang2025.EnergyPoweringLimits

/-! # Logarithmic calculus for positive physical quantities

These limits retain the scale variable and turn actual finite sums into
maxima of exponents. They do not postulate any analytic estimate.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

theorem tendsto_logb_mul
    {N X Y : ℕ → ℝ} {a b : ℝ}
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a))
    (hy : Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds b)) :
    Tendsto (fun n => Real.logb (N n) (X n * Y n)) atTop (nhds (a + b)) := by
  simpa only [Real.logb_mul (hX _).ne' (hY _).ne'] using hx.add hy

theorem tendsto_logb_pow
    {N X : ℕ → ℝ} {a : ℝ} (k : ℕ)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a)) :
    Tendsto (fun n => Real.logb (N n) (X n ^ k)) atTop (nhds ((k : ℝ) * a)) := by
  simpa only [Real.logb_pow] using hx.const_mul (k : ℝ)

theorem tendsto_logb_div
    {N X Y : ℕ → ℝ} {a b : ℝ}
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a))
    (hy : Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds b)) :
    Tendsto (fun n => Real.logb (N n) (X n / Y n)) atTop (nhds (a - b)) := by
  simpa only [Real.logb_div (hX _).ne' (hY _).ne'] using hx.sub hy

theorem tendsto_logb_rpow
    {N X : ℕ → ℝ} {a : ℝ} (k : ℝ) (hX : ∀ n, 0 < X n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a)) :
    Tendsto (fun n => Real.logb (N n) (X n ^ k)) atTop (nhds (k * a)) := by
  simpa only [Real.logb_rpow_eq_mul_logb_of_pos (hX _)] using hx.const_mul k

theorem tendsto_logb_max
    {N X Y : ℕ → ℝ} {a b : ℝ}
    (hN : ∀ n, 1 < N n) (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a))
    (hy : Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds b)) :
    Tendsto (fun n => Real.logb (N n) (max (X n) (Y n))) atTop (nhds (max a b)) := by
  apply (hx.max hy).congr
  intro n
  rcases le_total (X n) (Y n) with h | h
  · rw [max_eq_right h, max_eq_right ((Real.logb_le_logb (hN n) (hX n) (hY n)).2 h)]
  · rw [max_eq_left h, max_eq_left ((Real.logb_le_logb (hN n) (hY n) (hX n)).2 h)]

theorem tendsto_logb_add
    {N X Y : ℕ → ℝ} {a b : ℝ}
    (hN : ∀ n, 1 < N n) (hNtop : Tendsto N atTop atTop)
    (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a))
    (hy : Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds b)) :
    Tendsto (fun n => Real.logb (N n) (X n + Y n)) atTop (nhds (max a b)) := by
  apply tendsto_logb_of_const_mul_sandwich N (fun n => max (X n) (Y n))
    (fun n => X n + Y n) (max a b) 1 2 hN hNtop
    (fun n => (hX n).trans_le (le_max_left _ _)) zero_lt_one (by norm_num)
  · intro n
    constructor
    · rw [one_mul]
      exact max_le (by linarith [hY n]) (by linarith [hX n])
    · linarith [le_max_left (X n) (Y n), le_max_right (X n) (Y n)]
  · exact tendsto_logb_max hN hX hY hx hy

theorem tendsto_logb_min
    {N X Y : ℕ → ℝ} {a b : ℝ}
    (hN : ∀ n, 1 < N n) (hX : ∀ n, 0 < X n) (hY : ∀ n, 0 < Y n)
    (hx : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a))
    (hy : Tendsto (fun n => Real.logb (N n) (Y n)) atTop (nhds b)) :
    Tendsto (fun n => Real.logb (N n) (min (X n) (Y n))) atTop (nhds (min a b)) := by
  apply (hx.min hy).congr
  intro n
  rcases le_total (X n) (Y n) with h | h
  · rw [min_eq_left h, min_eq_left ((Real.logb_le_logb (hN n) (hX n) (hY n)).2 h)]
  · rw [min_eq_right h, min_eq_right ((Real.logb_le_logb (hN n) (hY n) (hX n)).2 h)]

end TaoTrudgianYang2025
