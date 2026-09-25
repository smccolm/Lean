import TaoTrudgianYang2025.IntegerIntervalBoundary

/-! Exact integer-interval translation and finite averaging, including empty intervals. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_integer_interval_translate (w : ℤ → ℂ) (a b n : ℤ) :
    (∑ m ∈ Finset.Icc (a-n) (b-n), w (m+n)) = ∑ m ∈ Finset.Icc a b, w m := by
  apply Finset.sum_bij (fun m _ => m+n)
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  · intro m _ k _ he
    omega
  · intro m hm
    refine ⟨m-n,?_,by omega⟩
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  · intro m _
    rfl

theorem sum_integer_interval_average (w : ℤ → ℂ) (a b : ℤ) (N : ℕ) (hN : 0 < N) :
    (∑ m ∈ Finset.Icc a b, w m) =
      (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ Finset.Icc (a-n) (b-n), w (m+n) := by
  simp_rw [sum_integer_interval_translate]
  have hc : (Finset.Icc (1:ℤ) N).card = N := by rw [Int.card_Icc]; omega
  simp only [Finset.sum_const,hc,nsmul_eq_mul]
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end TaoTrudgianYang2025
