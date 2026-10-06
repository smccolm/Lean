import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! # Long interval averages from uniform unit-interval integral bounds -/

namespace Dubon2026

open MeasureTheory

theorem integral_nat_length_le {f : ℝ → ℝ}
    (hf : ∀ x y, IntervalIntegrable f volume x y) {B : ℝ}
    (hunit : ∀ x : ℝ, (∫ t in x..x + 1, f t) ≤ B) (x : ℝ) (n : ℕ) :
    (∫ t in x..x + n, f t) ≤ (n : ℝ) * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x + (n + 1 : ℕ) = (x + n) + 1 := by push_cast; ring
    rw [he, ← intervalIntegral.integral_add_adjacent_intervals (hf x (x + n)) (hf (x + n) (x + n + 1))]
    have hb := add_le_add ih (hunit (x + n))
    convert hb using 1
    push_cast
    ring

theorem symmetric_mean_le_two_of_unit_bound {f : ℝ → ℝ}
    (hf : ∀ x y, IntervalIntegrable f volume x y) (hn : 0 ≤ᵐ[volume] f)
    {B : ℝ} (hB : 0 ≤ B) (hunit : ∀ x : ℝ, (∫ t in x..x + 1, f t) ≤ B)
    {T : ℝ} (hT : 1 ≤ T) : (2 * T)⁻¹ * (∫ t in -T..T, f t) ≤ 2 * B := by
  let n := Nat.ceil (2 * T)
  have hnlo : 2 * T ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) ≤ 4 * T := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * T)).le.trans (by linarith)
  have hlarge := integral_nat_length_le hf hunit (-T) n
  have hmono : (∫ t in -T..T, f t) ≤ ∫ t in -T..(-T + n), f t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (ae_restrict_of_ae hn) (hf _ _)
  have hb : (∫ t in -T..T, f t) ≤ (4 * T) * B :=
    (hmono.trans hlarge).trans (mul_le_mul_of_nonneg_right hnhi hB)
  have htp : 0 < 2 * T := by linarith
  calc
    _ ≤ (2 * T)⁻¹ * ((4 * T) * B) := mul_le_mul_of_nonneg_left hb (inv_pos.mpr htp).le
    _ = 2 * B := by field_simp; ring

end Dubon2026
