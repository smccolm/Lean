import TaoTrudgianYang2025.IntegerFourierTails

/-!
# Exact symmetric-window decomposition around an integer core

The exterior blocks are the literal integer intervals. The reversed
left enumeration and forward right enumeration each include every
frequency once and retain the nearest exterior integer.
-/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sum_int_interval_three_parts (f : ℤ → ℂ)
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (∑ q ∈ Finset.Icc a d, f q) =
      (∑ q ∈ Finset.Ico a b, f q)+(∑ q ∈ Finset.Icc b c, f q)+
        ∑ q ∈ Finset.Ioc c d, f q := by
  have hs : Finset.Icc a d =
      (Finset.Ico a b ∪ Finset.Icc b c) ∪ Finset.Ioc c d := by
    ext q
    simp only [Finset.mem_Icc,Finset.mem_Ico,Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd₁ : Disjoint (Finset.Ico a b) (Finset.Icc b c) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_Ico,Finset.mem_Icc] at hq hq'
    omega
  have hd₂ : Disjoint (Finset.Ico a b ∪ Finset.Icc b c) (Finset.Ioc c d) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_union,Finset.mem_Ico,Finset.mem_Icc,Finset.mem_Ioc] at hq hq'
    omega
  rw [hs,Finset.sum_union hd₂,Finset.sum_union hd₁]

theorem sum_int_Ico_eq_reverse_range (f : ℤ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ico a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (b-((n+1 : ℕ) : ℤ)) := by
  have hlen : ((b-a).toNat : ℤ) = b-a := Int.toNat_of_nonneg (by omega)
  symm
  apply Finset.sum_bij (fun n _ => b-((n+1 : ℕ) : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ico,Nat.cast_add,Nat.cast_one]
    omega
  · intro n hn m hm h
    simp only [Nat.cast_add,Nat.cast_one] at h
    omega
  · intro q hq
    simp only [Finset.mem_Ico] at hq
    have hc : ((b-q-1).toNat : ℤ) = b-q-1 := Int.toNat_of_nonneg (by omega)
    refine ⟨(b-q-1).toNat,?_,?_⟩
    · simp only [Finset.mem_range]
      omega
    · simp only [Nat.cast_add,Nat.cast_one]
      omega
  · intro n hn
    rfl

theorem sum_int_Ioc_eq_forward_range (f : ℤ → ℂ) {a b : ℤ} (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, f q) =
      ∑ n ∈ Finset.range (b-a).toNat, f (a+((n+1 : ℕ) : ℤ)) := by
  have hlen : ((b-a).toNat : ℤ) = b-a := Int.toNat_of_nonneg (by omega)
  symm
  apply Finset.sum_bij (fun n _ => a+((n+1 : ℕ) : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ioc,Nat.cast_add,Nat.cast_one]
    omega
  · intro n hn m hm h
    simp only [Nat.cast_add,Nat.cast_one] at h
    omega
  · intro q hq
    simp only [Finset.mem_Ioc] at hq
    have hc : ((q-a-1).toNat : ℤ) = q-a-1 := Int.toNat_of_nonneg (by omega)
    refine ⟨(q-a-1).toNat,?_,?_⟩
    · simp only [Finset.mem_range]
      omega
    · simp only [Nat.cast_add,Nat.cast_one]
      omega
  · intro n hn
    rfl

end TaoTrudgianYang2025
