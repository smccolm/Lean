import TaoTrudgianYang2025.SargosSymmetricPositive

/-! Exact support and center-translation bridges for the padded symmetric products. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosPaddedSequence_symmetric_zero (a : ℤ → ℂ) (M : ℕ)
    {m : ℤ} (hm : m ∉ Finset.Ico (0:ℤ) M) (n : ℤ) :
    sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n) = 0 := by
  by_cases hp : m+n ∈ Finset.Ico (0:ℤ) M
  · have hn : m-n ∉ Finset.Ico (0:ℤ) M := by
      intro hn
      simp only [Finset.mem_Ico] at hp hn hm
      omega
    rw [sargosPaddedSequence_zero a M hn,mul_zero]
  · rw [sargosPaddedSequence_zero a M hp,zero_mul]

theorem sargos_supported_sum_shift {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (M L j : ℕ) (hj : j < L)
    (hf : ∀ n, n ∉ Finset.Ico (0:ℤ) M → f n = 0) :
    (∑ m ∈ Finset.Ico (-(L:ℤ)) M, f (m+j)) =
      ∑ m ∈ Finset.Ico (0:ℤ) M, f m := by
  classical
  calc
    _ = ∑ m ∈ Finset.Ico (-(L:ℤ)) M,
        if m+j ∈ Finset.Ico (0:ℤ) M then f (m+j) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs with h
      · rfl
      · exact hf _ h
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun m _ => m+(j:ℤ))
      · intro m hm
        exact (Finset.mem_filter.mp hm).2
      · intro m hm n hn he
        omega
      · intro n hn
        refine ⟨n-j,Finset.mem_filter.mpr ⟨?_,?_⟩,by omega⟩
        · have hn' := Finset.mem_Ico.mp hn
          apply Finset.mem_Ico.mpr
          constructor <;> omega
        · simpa using hn
      · intro m hm
        rfl

theorem sargos_symmetric_sum_shift (a : ℤ → ℂ) (M L j : ℕ) (hj : j < L)
    (S : Finset ℤ) :
    (∑ m ∈ Finset.Ico (-(L:ℤ)) M,
      ‖∑ n ∈ S, sargosPaddedSequence a M (m+j+n)*sargosPaddedSequence a M (m+j-n)‖) =
      ∑ m ∈ Finset.Ico (0:ℤ) M,
        ‖∑ n ∈ S, sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖ := by
  apply sargos_supported_sum_shift
    (fun m => ‖∑ n ∈ S, sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖)
    M L j hj
  intro m hm
  have he (n : ℤ) := sargosPaddedSequence_symmetric_zero a M hm n
  simp only [he,Finset.sum_const_zero,norm_zero]

theorem sargos_padded_diagonal (a : ℤ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M, ‖sargosPaddedSequence a M m‖^2) =
      ∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2 := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [sargosPaddedSequence_eq a M hm]

end TaoTrudgianYang2025
