import Dubon2026.CoprimeWeightSum
import Dubon2026.ScaledPowerSum
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The harmonic transition for coprime sums, including the bounded remainder -/

namespace Dubon2026

open Filter
open scoped Topology

theorem tendsto_harmonic_div_sub_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (harmonic (N / d) : ℝ) - Real.log N) atTop
      (𝓝 (Real.eulerMascheroniConstant - Real.log d)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hh := Real.tendsto_harmonic_sub_log.comp (tendsto_nat_div_fixed hd)
  have hl := (Real.continuousAt_log (div_pos zero_lt_one hdr).ne').tendsto.comp
    (tendsto_nat_div_natCast_ratio hd)
  have ht := hh.add hl
  rw [Real.log_div one_ne_zero hdr.ne', Real.log_one, zero_sub, ← sub_eq_add_neg] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hN
  have hk0 : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast Nat.div_pos hN hd
  simp only [Function.comp_apply]
  rw [Real.log_div hk0.ne' hN0.ne']
  ring

theorem coprime_harmonic_eq_moebius {q : ℕ} (hq : q ≠ 0) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ)⁻¹) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) / d) * (harmonic (N / d) : ℝ) := by
  simpa only [Real.rpow_neg_one, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, div_eq_mul_inv] using sum_coprime_rpow_eq_moebius hq N (-1)

theorem tendsto_coprime_harmonic_sub_log {q : ℕ} (hq : q ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ)⁻¹) -
        ((q.totient : ℝ) / q) * Real.log N) atTop
      (𝓝 (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) / d) *
        (Real.eulerMascheroniConstant - Real.log d))) := by
  have hh := tendsto_finsetSum q.divisors (fun d hd =>
    (tendsto_harmonic_div_sub_log (Nat.pos_of_mem_divisors hd)).const_mul
      ((ArithmeticFunction.moebius d : ℝ) / d))
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  dsimp only
  rw [coprime_harmonic_eq_moebius hq, ← sum_moebius_div_eq_totient_div q hq,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem eventually_coprime_harmonic_error_bounded {q : ℕ} (hq : q ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ)⁻¹) -
        ((q.totient : ℝ) / q) * Real.log N| ≤ C := by
  let c := ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) / d) *
    (Real.eulerMascheroniConstant - Real.log d)
  refine ⟨|c| + 1, by positivity, ?_⟩
  have hh := (tendsto_coprime_harmonic_sub_log hq).abs.eventually
    (gt_mem_nhds (lt_add_one |c|))
  filter_upwards [hh] with N hN
  exact hN.le

end Dubon2026
