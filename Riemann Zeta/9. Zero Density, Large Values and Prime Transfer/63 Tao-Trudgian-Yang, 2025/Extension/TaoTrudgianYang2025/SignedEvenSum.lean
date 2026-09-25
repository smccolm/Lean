import TaoTrudgianYang2025.TriangularShiftBounds

/-! Splitting an even signed sum without replacing it by individual norms. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_signed_even (f : ℤ → ℝ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ n, f (-n) = f n) :
    (∑ n ∈ Finset.Ioo (-(N:ℤ)) N, f n) =
      f 0+2*∑ n ∈ Finset.Ioo (0:ℤ) N, f n := by
  classical
  have he : Finset.Ioo (-(N:ℤ)) N =
      insert 0 (Finset.Ioo (-(N:ℤ)) 0 ∪ Finset.Ioo (0:ℤ) N) := by
    ext n
    simp only [Finset.mem_Ioo,Finset.mem_insert,Finset.mem_union]
    omega
  have hn : (0:ℤ) ∉ Finset.Ioo (-(N:ℤ)) 0 ∪ Finset.Ioo (0:ℤ) N := by
    simp only [Finset.mem_union,Finset.mem_Ioo]
    omega
  have hd : Disjoint (Finset.Ioo (-(N:ℤ)) 0) (Finset.Ioo (0:ℤ) N) := by
    apply Finset.disjoint_left.mpr
    intro n h₁ h₂
    have ha := Finset.mem_Ioo.mp h₁
    have hb := Finset.mem_Ioo.mp h₂
    omega
  have hneg : (∑ n ∈ Finset.Ioo (-(N:ℤ)) 0, f n) =
      ∑ n ∈ Finset.Ioo (0:ℤ) N, f n := by
    apply Finset.sum_bij (fun n _ => -n)
    · intro n hn'
      simp only [Finset.mem_Ioo] at hn' ⊢
      omega
    · intro n _ m _ he'
      omega
    · intro n hn'
      refine ⟨-n,?_,by omega⟩
      simp only [Finset.mem_Ioo] at hn' ⊢
      omega
    · intro n _
      exact (hf n).symm
  rw [he,Finset.sum_insert hn,Finset.sum_union hd,hneg]
  ring

end TaoTrudgianYang2025
