import Dubon2026.CoprimeMobius

/-! # Exact Möbius decomposition of arbitrary weighted coprime sums -/

namespace Dubon2026

theorem filter_dvd_Icc_eq_image {d N : ℕ} (hd : 0 < d) :
    (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (N / d)).image (fun n => d * n) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hn, hnN⟩, ⟨k, rfl⟩⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · by_contra hk
      have hk0 : k = 0 := by omega
      simp [hk0] at hn
    · exact (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hnN)
  · rintro ⟨k, ⟨hk, hkN⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkN

theorem sum_coprime_weight_eq_moebius {q : ℕ} (hq : q ≠ 0)
    (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), w n) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ∑ n ∈ Finset.Icc 1 (N / d), w (d * n) := by
  have hi (n : ℕ) : (if n.Coprime q then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
    have hh := congrArg (fun z : ℤ => (z : ℝ)) (sum_moebius_gcd_eq_coprimeIndicator q n)
    rw [divisors_gcd_eq_filter_dvd q n hq] at hh
    simpa only [Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero,
      Finset.sum_filter] using hh.symm
  rw [Finset.sum_filter]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, (if n.Coprime q then (1 : ℝ) else 0) * w n := by
      simp only [ite_mul, one_mul, zero_mul]
    _ = ∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ q.divisors, (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) * w n := by
      simp only [hi, Finset.sum_mul]
    _ = ∑ d ∈ q.divisors,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), (ArithmeticFunction.moebius d : ℝ) * w n := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter, ite_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [filter_dvd_Icc_eq_image hd0, Finset.sum_image]
      · rw [Finset.mul_sum]
      · intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left hd0 hab

theorem sum_coprime_rpow_eq_moebius {q : ℕ} (hq : q ≠ 0) (N : ℕ) (r : ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime q), (n : ℝ) ^ r) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ r *
        ∑ n ∈ Finset.Icc 1 (N / d), (n : ℝ) ^ r := by
  rw [sum_coprime_weight_eq_moebius hq]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    ← Finset.mul_sum, mul_assoc]

end Dubon2026
