import GafniTao.HeathBrownBlockEnergy

/-!
# From block energy to Heath-Brown's close-pair count

This file uses the support of the literal triangular kernel.  Same-block
pairs outside `mathcal N_2` have zero weight, while every surviving weight
is at most one.  Thus the block energy is bounded by the exact finite
close-pair count, with no unspecified cutoff.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def heathBrownSameBlockPairs (N K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range K).biUnion (fun i =>
    (heathBrownBlock N K i).product (heathBrownBlock N K i))

theorem heathBrownBlockProducts_pairwiseDisjoint (N K : ℕ) :
    ((↑(Finset.range K) : Set ℕ).PairwiseDisjoint fun i =>
      (heathBrownBlock N K i).product (heathBrownBlock N K i)) := by
  intro i _hi j _hj hij
  change Disjoint
    ((heathBrownBlock N K i).product (heathBrownBlock N K i))
    ((heathBrownBlock N K j).product (heathBrownBlock N K j))
  rw [Finset.disjoint_left]
  intro p hpI hpJ
  have hmI := (Finset.mem_product.mp hpI).1
  have hmJ := (Finset.mem_product.mp hpJ).1
  have hidxI := (mem_heathBrownBlock.mp hmI).2.2
  have hidxJ := (mem_heathBrownBlock.mp hmJ).2.2
  exact hij (hidxI.symm.trans hidxJ)

theorem heathBrown_sameBlock_kernel_sum_eq
    (N K : ℕ) (B C : ℝ) (g₁ g₂ : ℕ → ℝ) :
    (∑ p ∈ heathBrownSameBlockPairs N K,
        heathBrownTriangularKernel B C
          (g₁ p.1 - g₁ p.2) (g₂ p.1 - g₂ p.2)) =
      ∑ i ∈ Finset.range K,
        ∑ m ∈ heathBrownBlock N K i,
          ∑ n ∈ heathBrownBlock N K i,
            heathBrownTriangularKernel B C
              (g₁ m - g₁ n) (g₂ m - g₂ n) := by
  unfold heathBrownSameBlockPairs
  rw [Finset.sum_biUnion (heathBrownBlockProducts_pairwiseDisjoint N K)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Finset.sum_product _ _ _

theorem heathBrownDistanceToInteger_lt_of_hat_pos
    {B x : ℝ} (hB : 0 < B) (hx : 0 < heathBrownHat B x) :
    heathBrownDistanceToInteger x < B := by
  by_contra hnot
  have hz := heathBrownHat_eq_zero_of_le_distance hB (le_of_not_gt hnot)
  linarith

theorem heathBrown_kernel_support
    {B C x y : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hphi : heathBrownTriangularKernel B C x y ≠ 0) :
    heathBrownDistanceToInteger x < B ∧
      heathBrownDistanceToInteger y < C := by
  have hphiPos : 0 < heathBrownTriangularKernel B C x y :=
    lt_of_le_of_ne (heathBrownTriangularKernel_nonneg B C x y) hphi.symm
  have hprod := (mul_pos_iff.mp hphiPos)
  rcases hprod with hpos | hneg
  · exact ⟨heathBrownDistanceToInteger_lt_of_hat_pos hB hpos.1,
      heathBrownDistanceToInteger_lt_of_hat_pos hC hpos.2⟩
  · exact False.elim ((not_lt_of_ge (heathBrownHat_nonneg B x)) hneg.1)

theorem heathBrown_sameBlock_mem_pairCountTwo_of_kernel_ne_zero
    {N k H K : ℕ} {f : ℝ → ℝ} {p : ℕ × ℕ}
    (hH : 0 < H)
    (hp : p ∈ heathBrownSameBlockPairs N K)
    (hkernel : heathBrownPairKernel k H f p ≠ 0) :
    p ∈ heathBrownPairCountTwo N k H K f := by
  unfold heathBrownSameBlockPairs at hp
  rw [Finset.mem_biUnion] at hp
  rcases hp with ⟨i, hi, hp⟩
  have hm := (Finset.mem_product.mp hp).1
  have hn := (Finset.mem_product.mp hp).2
  have hm' := mem_heathBrownBlock.mp hm
  have hn' := mem_heathBrownBlock.mp hn
  have hclose := heathBrownBlock_pair_source_distance hm hn
  unfold heathBrownPairKernel at hkernel
  have hwidth₁ : 0 < 4 * (((H : ℝ) ^ (k - 2))⁻¹) := by positivity
  have hwidth₂ : 0 < 4 * (((H : ℝ) ^ (k - 1))⁻¹) := by positivity
  have hsupp := heathBrown_kernel_support hwidth₁ hwidth₂ hkernel
  rw [mem_heathBrownPairCountTwo]
  exact ⟨hm'.1, hm'.2.1, hn'.1, hn'.2.1, hclose,
    hsupp.1.le, hsupp.2.le⟩

theorem heathBrown_sameBlock_kernel_sum_le_pairCountTwo
    {N k H K : ℕ} {f : ℝ → ℝ}
    (hH : 0 < H) :
    (∑ p ∈ heathBrownSameBlockPairs N K,
        heathBrownPairKernel k H f p) ≤
      ((heathBrownPairCountTwo N k H K f).card : ℝ) := by
  let S := heathBrownSameBlockPairs N K
  let T := heathBrownPairCountTwo N k H K f
  have hzero : ∀ p ∈ S, p ∉ T → heathBrownPairKernel k H f p = 0 := by
    intro p hpS hpT
    by_contra hne
    exact hpT (heathBrown_sameBlock_mem_pairCountTwo_of_kernel_ne_zero
      hH hpS hne)
  have hrestrict :
      (∑ p ∈ S, heathBrownPairKernel k H f p) =
        ∑ p ∈ S ∩ T, heathBrownPairKernel k H f p := by
    symm
    apply Finset.sum_subset
    · exact Finset.inter_subset_left
    · intro p hpS hpNot
      exact hzero p hpS (by
        intro hpT
        exact hpNot (Finset.mem_inter.mpr ⟨hpS, hpT⟩))
  rw [hrestrict]
  calc
    (∑ p ∈ S ∩ T, heathBrownPairKernel k H f p) ≤
        ∑ p ∈ T, heathBrownPairKernel k H f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.inter_subset_right
      · intro p _hpT _hpNot
        exact heathBrownPairKernel_nonneg k H f p
    _ ≤ ∑ _p ∈ T, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      unfold heathBrownPairKernel
      exact heathBrownTriangularKernel_le_one (by positivity) (by positivity)
    _ = (T.card : ℝ) := by simp

/-- The finite localization conclusion in Heath-Brown Section 3.  The factor
four is the exact loss from the chosen half-width majorant. -/
theorem heathBrownPairCountOne_card_le_four_mul_block_mul_pairCountTwo
    {N k H K : ℕ} {f : ℝ → ℝ}
    (hH : 0 < H) (hK : 0 < K)
    (hwidth₁ : 4 * (((H : ℝ) ^ (k - 2))⁻¹) ≤ 1 / 2)
    (hwidth₂ : 4 * (((H : ℝ) ^ (k - 1))⁻¹) ≤ 1 / 2) :
    ((heathBrownPairCountOne N k H f).card : ℝ) ≤
      4 * K * (heathBrownPairCountTwo N k H K f).card := by
  let B : ℝ := 4 * (((H : ℝ) ^ (k - 2))⁻¹)
  let C : ℝ := 4 * (((H : ℝ) ^ (k - 1))⁻¹)
  let g₁ : ℕ → ℝ := fun n => heathBrownDerivativeCoordinate f (k - 2) n
  let g₂ : ℕ → ℝ := fun n => heathBrownDerivativeCoordinate f (k - 1) n
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hmajor := heathBrownPairCountOne_quarter_le_kernel_sum
    (N := N) (k := k) (f := f) hH
  have hblock := heathBrown_full_kernel_sum_le_blocks
    (N := N) (K := K) hK hB (by simpa [B] using hwidth₁)
      hC (by simpa [C] using hwidth₂) g₁ g₂
  have hsame := heathBrown_sameBlock_kernel_sum_le_pairCountTwo
    (N := N) (k := k) (H := H) (K := K) (f := f) hH
  have hsumEq := heathBrown_sameBlock_kernel_sum_eq N K B C g₁ g₂
  have hmajor' := hmajor.trans_eq
    (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
      (heathBrownPairKernel k H f))
  change ((heathBrownPairCountOne N k H f).card : ℝ) / 4 ≤
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      heathBrownTriangularKernel B C (g₁ m - g₁ n) (g₂ m - g₂ n) at hmajor'
  have hchain : ((heathBrownPairCountOne N k H f).card : ℝ) / 4 ≤
      (K : ℝ) * (heathBrownPairCountTwo N k H K f).card := by
    calc
      ((heathBrownPairCountOne N k H f).card : ℝ) / 4 ≤
          ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            heathBrownTriangularKernel B C
              (g₁ m - g₁ n) (g₂ m - g₂ n) := hmajor'
      _ ≤ (K : ℝ) *
          ∑ i ∈ Finset.range K,
            ∑ m ∈ heathBrownBlock N K i,
              ∑ n ∈ heathBrownBlock N K i,
                heathBrownTriangularKernel B C
                  (g₁ m - g₁ n) (g₂ m - g₂ n) := hblock
      _ = (K : ℝ) *
          ∑ p ∈ heathBrownSameBlockPairs N K,
            heathBrownPairKernel k H f p := by
        congr 1
        rw [← hsumEq]
        rfl
      _ ≤ (K : ℝ) * (heathBrownPairCountTwo N k H K f).card :=
        mul_le_mul_of_nonneg_left hsame (Nat.cast_nonneg K)
  nlinarith

#print axioms heathBrownBlockProducts_pairwiseDisjoint
#print axioms heathBrown_sameBlock_kernel_sum_eq
#print axioms heathBrownDistanceToInteger_lt_of_hat_pos
#print axioms heathBrown_kernel_support
#print axioms heathBrown_sameBlock_mem_pairCountTwo_of_kernel_ne_zero
#print axioms heathBrown_sameBlock_kernel_sum_le_pairCountTwo
#print axioms heathBrownPairCountOne_card_le_four_mul_block_mul_pairCountTwo

end

end GafniTao
