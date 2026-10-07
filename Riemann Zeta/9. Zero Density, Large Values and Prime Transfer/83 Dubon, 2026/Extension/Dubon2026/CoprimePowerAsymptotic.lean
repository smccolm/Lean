import Dubon2026.CoprimeWeightSum
import Dubon2026.ScaledPowerSum

/-! # The exact totient-density leading term for coprime power sums -/

namespace Dubon2026

open Filter
open scoped Topology

theorem tendsto_coprime_power_sum_ratio {q : ℕ} (hq : q ≠ 0) {r : ℝ} (hr : -1 < r) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ r) /
        (N : ℝ) ^ (r + 1)) atTop (𝓝 (((q.totient : ℝ) / q) / (r + 1))) := by
  have hh := tendsto_finsetSum q.divisors (fun d hd =>
    (tendsto_scaled_power_sum (Nat.pos_of_mem_divisors hd) hr).const_mul
      (ArithmeticFunction.moebius d : ℝ))
  have hc : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
      (1 / ((d : ℝ) * (r + 1)))) = ((q.totient : ℝ) / q) / (r + 1) := by
    rw [← sum_moebius_div_eq_totient_div q hq, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [hc] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [sum_coprime_rpow_eq_moebius hq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem tendsto_coprime_power_sum_error {q : ℕ} (hq : q ≠ 0) {r : ℝ} (hr : -1 < r) :
    Tendsto (fun N : ℕ =>
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ r) -
        ((q.totient : ℝ) / q) * (N : ℝ) ^ (r + 1) / (r + 1)) /
          (N : ℝ) ^ (r + 1)) atTop (𝓝 0) := by
  have hh := (tendsto_coprime_power_sum_ratio hq hr).sub_const (((q.totient : ℝ) / q) / (r + 1))
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  field_simp [(Real.rpow_pos_of_pos hN0 (r + 1)).ne']

end Dubon2026
