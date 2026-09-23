import TaoTrudgianYang2025.FiniteSignSamples
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Exact second and bounded fourth moments of literal finite sign samples. -/

namespace TaoTrudgianYang2025

theorem finiteSignSamples_second_moment (v : List ℂ) :
    ((finiteSignSamples v).map Complex.normSq).sum =
      (2:ℝ)^v.length*(v.map Complex.normSq).sum := by
  induction v with
  | nil => simp [finiteSignSamples]
  | cons z v ih =>
    simp only [finiteSignSamples,List.map_append,List.map_map,List.sum_append]
    rw [← List.sum_map_add]
    simp_rw [Function.comp_def,complex_sign_second_pair]
    rw [List.sum_map_add,List.sum_map_mul_left,ih]
    simp only [List.map_const',List.sum_replicate,finiteSignSamples_length,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,List.length_cons,List.map_cons,List.sum_cons]
    rw [pow_succ]
    ring

theorem finiteSignSamples_fourth_moment (v : List ℂ) :
    ((finiteSignSamples v).map (fun w => Complex.normSq w^2)).sum ≤
      3*(2:ℝ)^v.length*((v.map Complex.normSq).sum)^2 := by
  induction v with
  | nil => simp [finiteSignSamples]
  | cons z v ih =>
    have hp : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
    have hpow : 0 ≤ (2:ℝ)^v.length := by positivity
    have hb :
        ((finiteSignSamples v).map (fun w =>
          Complex.normSq (w+z)^2+Complex.normSq (w-z)^2)).sum ≤
        ((finiteSignSamples v).map (fun w =>
          2*Complex.normSq w^2+12*Complex.normSq w*Complex.normSq z+
            2*Complex.normSq z^2)).sum := by
      apply List.sum_le_sum
      intro w _
      exact complex_sign_fourth_pair w z
    simp only [finiteSignSamples,List.map_append,List.map_map,List.sum_append]
    rw [← List.sum_map_add]
    simp only [Function.comp_def]
    calc
      _ ≤ _ := hb
      _ = 2*((finiteSignSamples v).map (fun w => Complex.normSq w^2)).sum+
          12*Complex.normSq z*((finiteSignSamples v).map Complex.normSq).sum+
          (2:ℝ)^v.length*(2*Complex.normSq z^2) := by
        simp only [List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_right,
          List.map_const',List.sum_replicate,finiteSignSamples_length,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        ring
      _ ≤ 3*(2:ℝ)^(z::v).length*(((z::v).map Complex.normSq).sum)^2 := by
        rw [finiteSignSamples_second_moment]
        simp only [List.length_cons,List.map_cons,List.sum_cons]
        rw [pow_succ (2:ℝ) v.length]
        nlinarith [mul_nonneg hpow (sq_nonneg (Complex.normSq z))]

end TaoTrudgianYang2025
