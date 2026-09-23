import TaoTrudgianYang2025.SargosSymmetricTriples

/-! Sixth-power control by the actual square-diagonal sextuple correlations. -/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

def sargosSquareDiagonal (H : ℕ) :
    Finset (SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :=
  Finset.univ.filter (fun q => sargosInitialTuplePower 2 q.1=sargosInitialTuplePower 2 q.2)

def sargosSymmetricSextupleCorrelation (a : ℤ → ℂ) (M H j : ℕ) : ℝ :=
  ∑ q ∈ sargosSquareDiagonal H,
    ‖∑ m ∈ Finset.Ico (0:ℤ) M,
      sargosSymmetricTriple a M H j m q.1*conj (sargosSymmetricTriple a M H j m q.2)‖

theorem sargosSymmetricSextupleCorrelation_nonneg (a : ℤ → ℂ) (M H j : ℕ) :
    0 ≤ sargosSymmetricSextupleCorrelation a M H j :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem sargosPositiveCorrelation_cube (a : ℤ → ℂ) (M H j : ℕ) :
    (sargosPositiveCorrelation a M H j)^3 ≤
      (M:ℝ)^2*∑ m ∈ Finset.Ico (0:ℤ) M,
        ‖∑ t : SargosInitialMomentTuple H 3, sargosSymmetricTriple a M H j m t‖ := by
  have h := pow_sum_le_card_mul_sum_pow
    (s := Finset.Ico (0:ℤ) M)
    (f := fun m => ‖∑ n ∈ sargosPositiveOffsets H j,
      sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖)
    (fun _ _ => norm_nonneg _) 2
  norm_num only [Nat.reduceAdd] at h
  simp_rw [← norm_pow,sargos_positive_symmetric_cube] at h
  simpa only [sargosPositiveCorrelation,Int.card_Ico,sub_zero,Int.toNat_natCast] using h

theorem sargosSymmetricTriple_grouped_second (a : ℤ → ℂ) (M H j : ℕ) :
    (∑ m ∈ Finset.Ico (0:ℤ) M,
      ‖∑ t : SargosInitialMomentTuple H 3, sargosSymmetricTriple a M H j m t‖)^2 ≤
      (M:ℝ)*((Finset.Icc (0:ℤ) (3*(H:ℤ)^2)).card:ℝ)*
        sargosSymmetricSextupleCorrelation a M H j := by
  have hv : ∀ t ∈ (Finset.univ : Finset (SargosInitialMomentTuple H 3)),
      sargosInitialTuplePower 2 t ∈ Finset.Icc (0:ℤ) (3*(H:ℤ)^2) := by
    intro t ht
    exact Finset.mem_Icc.mpr (sargosInitialTuple_square_bounds t)
  have h := sargos_grouped_second_moment
    (Finset.univ : Finset (SargosInitialMomentTuple H 3))
    (Finset.Icc (0:ℤ) (3*(H:ℤ)^2)) (Finset.Ico (0:ℤ) M)
    (sargosInitialTuplePower 2) hv (sargosSymmetricTriple a M H j)
  simpa only [sargosSymmetricSextupleCorrelation,sargosSquareDiagonal,
    Finset.univ_product_univ,Int.card_Ico,sub_zero,Int.toNat_natCast] using h

theorem sargosPositiveCorrelation_sixth (a : ℤ → ℂ) (M : ℕ) {H : ℕ}
    (hH : 1 ≤ H) (j : ℕ) :
    (sargosPositiveCorrelation a M H j)^6 ≤
      4*(M:ℝ)^5*(H:ℝ)^2*sargosSymmetricSextupleCorrelation a M H j := by
  have hc := sargosPositiveCorrelation_cube a M H j
  have hs := sargosSymmetricTriple_grouped_second a M H j
  have hk := sargos_square_frequency_card_le hH
  have hQ := sargosSymmetricSextupleCorrelation_nonneg a M H j
  calc
    _ = ((sargosPositiveCorrelation a M H j)^3)^2 := by ring
    _ ≤ ((M:ℝ)^2*∑ m ∈ Finset.Ico (0:ℤ) M,
        ‖∑ t : SargosInitialMomentTuple H 3, sargosSymmetricTriple a M H j m t‖)^2 :=
      pow_le_pow_left₀ (pow_nonneg (sargosPositiveCorrelation_nonneg a M H j) 3) hc 2
    _ = (M:ℝ)^4*(∑ m ∈ Finset.Ico (0:ℤ) M,
        ‖∑ t : SargosInitialMomentTuple H 3, sargosSymmetricTriple a M H j m t‖)^2 := by ring
    _ ≤ (M:ℝ)^4*((M:ℝ)*((Finset.Icc (0:ℤ) (3*(H:ℤ)^2)).card:ℝ)*
        sargosSymmetricSextupleCorrelation a M H j) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (M:ℝ)^4*((M:ℝ)*(4*(H:ℝ)^2)*sargosSymmetricSextupleCorrelation a M H j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity)) hQ
    _ = _ := by ring

end TaoTrudgianYang2025
