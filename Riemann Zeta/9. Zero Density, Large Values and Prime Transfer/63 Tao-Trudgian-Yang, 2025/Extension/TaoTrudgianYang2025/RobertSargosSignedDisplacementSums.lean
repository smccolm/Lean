import TaoTrudgianYang2025.RobertSargosDisplacementSums

/-! Summation over actual signed displacements, with at most two integers
above each positive absolute value. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_integer_natAbs_le_twice
    (S : Finset ℤ) (f : ℕ → ℝ) {N : ℕ}
    (hf : ∀ n ∈ Finset.Icc 1 N, 0 ≤ f n)
    (hmem : ∀ d ∈ S, d.natAbs ∈ Finset.Icc 1 N) :
    (∑ d ∈ S, f d.natAbs) ≤ 2*∑ n ∈ Finset.Icc 1 N, f n := by
  classical
  have hcard : ∀ n : ℕ, (S.filter (fun d => d.natAbs = n)).card ≤ 2 := by
    intro n
    have hsub : S.filter (fun d => d.natAbs = n) ⊆ {(n:ℤ),-(n:ℤ)} := by
      intro d hd
      simpa only [Finset.mem_insert,Finset.mem_singleton] using
        Int.natAbs_eq_iff.mp (Finset.mem_filter.mp hd).2
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ _d ∈ S.filter (fun d => d.natAbs = n), f n :=
      (Finset.sum_fiberwise_of_maps_to' hmem f).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 2*f n := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n) (hf n hn)
    _ = _ := by rw [Finset.mul_sum]

theorem sum_signed_displacement_weight_le
    (S : Finset ℤ) {ε A : ℝ} {N : ℕ}
    (hε : 0 < ε) (hA : 0 ≤ A) (hN : 1 ≤ N)
    (hmem : ∀ d ∈ S, d.natAbs ∈ Finset.Icc 1 N) :
    (∑ d ∈ S, (d.natAbs:ℝ)^(ε/2)*(1+A/d.natAbs)) ≤
      2*(1+2/ε)*(N:ℝ)^ε*((N:ℝ)+A) := by
  calc
    _ ≤ 2*∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(ε/2)*(1+A/n) :=
      sum_integer_natAbs_le_twice S _ (fun _ _ => by positivity) hmem
    _ ≤ 2*((1+2/ε)*(N:ℝ)^ε*((N:ℝ)+A)) :=
      mul_le_mul_of_nonneg_left (sum_positive_displacement_weight_le hε hA hN)
        (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025
