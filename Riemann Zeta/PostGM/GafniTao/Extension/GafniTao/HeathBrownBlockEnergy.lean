import GafniTao.HeathBrownKernelEnergy

/-!
# Block Cauchy inequality for the Heath-Brown energy

The full finite exponential sum is decomposed into the consecutive integer
blocks from `HeathBrownBlocks`.  Cauchy's inequality is applied at every
Fourier frequency, and absolute convergence permits summing the resulting
pointwise inequality.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrownFourierAtom_sum_eq_block_sums
    {N K : ℕ} (hK : 0 < K) (g₁ g₂ : ℕ → ℝ) (rs : ℤ × ℤ) :
    (∑ n ∈ Finset.Icc 1 N, heathBrownFourierAtom g₁ g₂ rs n) =
      ∑ i ∈ Finset.range K, ∑ n ∈ heathBrownBlock N K i,
        heathBrownFourierAtom g₁ g₂ rs n := by
  symm
  calc
    (∑ i ∈ Finset.range K, ∑ n ∈ heathBrownBlock N K i,
        heathBrownFourierAtom g₁ g₂ rs n) =
      ∑ i ∈ Finset.range K, ∑ n ∈ Finset.Icc 1 N,
        if heathBrownBlockIndex N K n = i
          then heathBrownFourierAtom g₁ g₂ rs n else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [heathBrown_block_sum_eq]
    _ = ∑ n ∈ Finset.Icc 1 N,
        heathBrownFourierAtom g₁ g₂ rs n :=
      heathBrown_sum_over_blocks hK _

theorem heathBrownFrequencyEnergy_le_block_energies
    {N K : ℕ} (hK : 0 < K)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (g₁ g₂ : ℕ → ℝ) (rs : ℤ × ℤ) :
    heathBrownFrequencyEnergy B C g₁ g₂ (Finset.Icc 1 N) rs ≤
      (K : ℝ) * ∑ i ∈ Finset.range K,
        heathBrownFrequencyEnergy B C g₁ g₂
          (heathBrownBlock N K i) rs := by
  let c := heathBrownTriangularFourierCoefficient B C rs.1 rs.2
  let V : ℕ → ℂ := fun i =>
    ∑ n ∈ heathBrownBlock N K i, heathBrownFourierAtom g₁ g₂ rs n
  have hc : 0 ≤ c :=
    heathBrownTriangularFourierCoefficient_nonneg hB hC rs.1 rs.2
  have hsplit := heathBrownFourierAtom_sum_eq_block_sums
    (N := N) (K := K) hK g₁ g₂ rs
  have hcs := ford_norm_sum_sq_le_card_mul_sum_norm_sq
    (Finset.range K) V
  simp only [Finset.card_range] at hcs
  calc
    heathBrownFrequencyEnergy B C g₁ g₂ (Finset.Icc 1 N) rs =
        c * ‖∑ i ∈ Finset.range K, V i‖ ^ 2 := by
      simp only [heathBrownFrequencyEnergy, c, V]
      rw [hsplit]
    _ ≤ c * ((K : ℝ) * ∑ i ∈ Finset.range K, ‖V i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hc
    _ = (K : ℝ) * ∑ i ∈ Finset.range K,
        heathBrownFrequencyEnergy B C g₁ g₂
          (heathBrownBlock N K i) rs := by
      simp only [heathBrownFrequencyEnergy, c, V]
      rw [show
        c * ((K : ℝ) * ∑ i ∈ Finset.range K, ‖V i‖ ^ 2) =
          (K : ℝ) * (c * ∑ i ∈ Finset.range K, ‖V i‖ ^ 2) by ring]
      congr 1
      rw [Finset.mul_sum]

theorem hasSum_heathBrownBlockFrequencyEnergy
    {N K : ℕ}
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2)
    (g₁ g₂ : ℕ → ℝ) :
    HasSum
      (fun rs : ℤ × ℤ =>
        ∑ i ∈ Finset.range K,
          heathBrownFrequencyEnergy B C g₁ g₂
            (heathBrownBlock N K i) rs)
      (∑ i ∈ Finset.range K,
        ∑ m ∈ heathBrownBlock N K i,
          ∑ n ∈ heathBrownBlock N K i,
            heathBrownTriangularKernel B C
              (g₁ m - g₁ n) (g₂ m - g₂ n)) := by
  simpa using hasSum_sum (s := Finset.range K)
    (fun i _hi => hasSum_heathBrownFrequencyEnergy
      hB hBHalf hC hCHalf g₁ g₂ (heathBrownBlock N K i))

/-- Exact source block-energy inequality before the kernel support is used. -/
theorem heathBrown_full_kernel_sum_le_blocks
    {N K : ℕ} (hK : 0 < K)
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2)
    (g₁ g₂ : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        heathBrownTriangularKernel B C
          (g₁ m - g₁ n) (g₂ m - g₂ n)) ≤
      (K : ℝ) *
        ∑ i ∈ Finset.range K,
          ∑ m ∈ heathBrownBlock N K i,
            ∑ n ∈ heathBrownBlock N K i,
              heathBrownTriangularKernel B C
                (g₁ m - g₁ n) (g₂ m - g₂ n) := by
  let fullEnergy : (ℤ × ℤ) → ℝ :=
    heathBrownFrequencyEnergy B C g₁ g₂ (Finset.Icc 1 N)
  let blockEnergy : (ℤ × ℤ) → ℝ := fun rs =>
    ∑ i ∈ Finset.range K,
      heathBrownFrequencyEnergy B C g₁ g₂
        (heathBrownBlock N K i) rs
  have hfull : HasSum fullEnergy
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        heathBrownTriangularKernel B C
          (g₁ m - g₁ n) (g₂ m - g₂ n)) :=
    hasSum_heathBrownFrequencyEnergy hB hBHalf hC hCHalf
      g₁ g₂ (Finset.Icc 1 N)
  have hblocks : HasSum blockEnergy
      (∑ i ∈ Finset.range K,
        ∑ m ∈ heathBrownBlock N K i,
          ∑ n ∈ heathBrownBlock N K i,
            heathBrownTriangularKernel B C
              (g₁ m - g₁ n) (g₂ m - g₂ n)) :=
    hasSum_heathBrownBlockFrequencyEnergy hB hBHalf hC hCHalf g₁ g₂
  have hscaled := hblocks.mul_left (K : ℝ)
  have hpoint : ∀ rs, fullEnergy rs ≤ (K : ℝ) * blockEnergy rs := by
    intro rs
    exact heathBrownFrequencyEnergy_le_block_energies hK hB.le hC.le
      g₁ g₂ rs
  have htsum := hfull.summable.tsum_le_tsum hpoint hscaled.summable
  rw [hfull.tsum_eq, hscaled.tsum_eq] at htsum
  exact htsum

#print axioms heathBrownFourierAtom_sum_eq_block_sums
#print axioms heathBrownFrequencyEnergy_le_block_energies
#print axioms hasSum_heathBrownBlockFrequencyEnergy
#print axioms heathBrown_full_kernel_sum_le_blocks

end

end GafniTao
