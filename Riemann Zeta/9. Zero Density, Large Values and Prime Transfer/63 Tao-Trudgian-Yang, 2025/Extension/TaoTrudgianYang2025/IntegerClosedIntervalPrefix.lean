import TaoTrudgianYang2025.ContinuousPhaseWeyl

/-! Literal closed integer intervals as a prefix plus their charged last endpoint. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_integer_Ico_eq_range (w : ℤ → ℂ) (a b : ℤ) :
    (∑ m ∈ Finset.Ico a b, w m) =
      ∑ n ∈ Finset.range (b-a).toNat, w (a+n) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => a+n)
  · intro n hn
    have hn' := Finset.mem_range.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  · intro n _ m _ he
    omega
  · intro m hm
    have hmi := Finset.mem_Ico.mp hm
    refine ⟨(m-a).toNat,Finset.mem_range.mpr (by omega),?_⟩
    have he := Int.toNat_of_nonneg (show 0 ≤ m-a by omega)
    omega
  · intro _ _
    rfl

theorem sum_integer_Icc_eq_range_add (w : ℤ → ℂ) (a b : ℤ) (hab : a ≤ b) :
    (∑ m ∈ Finset.Icc a b, w m) =
      (∑ n ∈ Finset.range (b-a).toNat, w (a+n))+w b := by
  have he : Finset.Icc a b = insert b (Finset.Ico a b) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_insert (by simp),sum_integer_Ico_eq_range]
  exact add_comm _ _

end TaoTrudgianYang2025
