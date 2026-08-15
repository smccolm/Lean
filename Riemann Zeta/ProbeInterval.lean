import RiemannZeta.GuthMaynard.DFIEquation30

open Finset
open scoped BigOperators
open Classical

#check Finset.sum_union
#check Finset.sum_filter_add_sum_filter_not
#check Summable.sum_add_tsum_nat_add
#check Summable.sum_add_tsum_nat_add'
#check Equiv.tsum_eq
#check Equiv.hasSum_iff
#check Function.Injective.hasSum_iff
#check Function.Injective.summable_iff
#check tsum_subtype
#check tsum_subtype'
#check tsum_eq_tsum_of_hasSum_iff_hasSum
#check RiemannZeta.GuthMaynard.tsum_nat_add_one_rpow_neg_le
#check Real.summable_nat_rpow
#check Summable.tsum_le_tsum

example {M : Type} [AddCommMonoid M] (F : ℕ → M) (K L : ℕ) (hKL : K ≤ L) :
    (∑ q ∈ Finset.Icc 1 L, F q) =
      (∑ q ∈ Finset.Icc 1 K, F q) +
      (∑ q ∈ Finset.Ioc K L, F q) := by
  rw [← Finset.sum_union]
  · congr 1
    ext q
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
    omega

theorem sum_Icc_sub_tsum_eq_small_error_add_large_sub_tail
    (F G : ℕ → ℂ) (K L : ℕ) (hKL : K ≤ L)
    (hG : Summable G) (hG0 : G 0 = 0) :
    (∑ q ∈ Finset.Icc 1 L, F q) - ∑' q : ℕ, G q =
      (∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
      (∑ q ∈ Finset.Ioc K L, F q) -
      ∑' j : ℕ, G (j + (K + 1)) := by
  have hsplitF : (∑ q ∈ Finset.Icc 1 L, F q) =
      (∑ q ∈ Finset.Icc 1 K, F q) +
      (∑ q ∈ Finset.Ioc K L, F q) := by
    rw [← Finset.sum_union]
    · congr 1
      ext q
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
      omega
  have hprefixG : (∑ q ∈ Finset.range (K + 1), G q) =
      ∑ q ∈ Finset.Icc 1 K, G q := by
    rw [show Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) by
      ext q
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega]
    simp [hG0]
  have hsplitG := hG.sum_add_tsum_nat_add (K + 1)
  rw [hsplitF, ← hsplitG, hprefixG]
  rw [Finset.sum_sub_distrib]
  ring

theorem probe_tsum_if_gt_eq_tsum_add_one
    {M : Type} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (F : ℕ → M) (K : ℕ) :
    (∑' q : ℕ, if K < q then F q else 0) =
      ∑' j : ℕ, F (K + (j + 1)) := by
  let f : ℕ → M := fun q => if K < q then F q else 0
  let g : ℕ → ℕ := fun j => K + (j + 1)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    omega
  have hfOutside : ∀ q ∉ Set.range g, f q = 0 := by
    intro q hq
    dsimp [f]
    split_ifs with hKq
    · exfalso
      apply hq
      exact ⟨q - (K + 1), by dsimp [g]; omega⟩
    · rfl
  apply tsum_eq_tsum_of_hasSum_iff_hasSum
  intro x
  have hcomp : f ∘ g = fun j => F (K + (j + 1)) := by
    funext j
    dsimp [f, g]
    rw [if_pos]
    omega
  rw [← hcomp]
  exact (hg.hasSum_iff hfOutside).symm
