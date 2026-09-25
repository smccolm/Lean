import TaoTrudgianYang2025.RobertSargosCorrelationBoundary
import TaoTrudgianYang2025.RobertSargosZeroRFloorBudgets

/-! The actual zero-zero diagonal and its physical floor-scale cost. -/

noncomputable section
open GafniTao
namespace TaoTrudgianYang2025

theorem robertSargos_zero_zero_re (f : ℝ → ℝ) (M H : ℕ) :
    (robertSargosTrimmedCorrelation f M H 0 0).re =
      ∑ h ∈ robertSargosHOverlap H 0, ((robertSargosMOverlap M h 0 0).card:ℝ) := by
  simp [robertSargosTrimmedCorrelation,fordAdditiveCharacter]

theorem robertSargos_zero_zero_bound (f : ℝ → ℝ) (M H : ℕ) :
    (robertSargosTrimmedCorrelation f M H 0 0).re ≤ (M:ℝ)*H := by
  rw [robertSargos_zero_zero_re]
  have hm : ∀ h ∈ robertSargosHOverlap H 0, (robertSargosMOverlap M h 0 0).card ≤ M := by
    intro h hh
    have hh0 : 0 ≤ h := by
      have := ((mem_robertSargosHOverlap H h 0).mp hh).1
      simp only [Finset.mem_Ico] at this
      omega
    have hs : robertSargosMOverlap M h 0 0 ⊆ Finset.Icc (1:ℤ) M := by
      intro m hm
      simp only [robertSargosMOverlap,add_zero,sub_zero,max_self,min_self,Finset.mem_Icc] at hm ⊢
      omega
    have hc := Finset.card_le_card hs
    simpa only [Int.card_Icc,add_sub_cancel_right,Int.toNat_natCast] using hc
  calc
    _ ≤ ∑ _h ∈ robertSargosHOverlap H 0, (M:ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      exact_mod_cast hm h hh
    _ ≤ (M:ℝ)*H := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((robertSargosHOverlap H 0).card:ℝ) ≤ H := by
        exact_mod_cast robertSargos_h_overlap_card H 0
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg M)

theorem zero_zero_floor_scale {lam : ℝ} (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    {H : ℕ} (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    (H:ℝ)^2 ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) := by
  let T := lam^(-(1:ℝ)/13)
  have hT : 1 ≤ T := by
    have := (thirteenth_root_physical_scale hlam hsmall).1
    dsimp [T]
    linarith
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  obtain ⟨_,hQ,_⟩ := positive_floor_half_bounds
    (show 1 ≤ T^3 from one_le_pow₀ hT)
  obtain ⟨_,hR,_⟩ := positive_floor_half_bounds hT
  have hprod := mul_le_mul hQ hR (by positivity) (by positivity)
  have hh : (H:ℝ) ≤ T^2/2 := by rwa [h2]
  have hs := mul_self_le_mul_self (Nat.cast_nonneg H) hh
  rw [← h3]
  change (H:ℝ)^2 ≤ (⌊T^3⌋₊:ℝ)*(⌊T⌋₊:ℝ)
  nlinarith [hprod]

theorem robertSargos_zero_zero_physical_a_times_a (f : ℝ → ℝ) (M H : ℕ)
    {lam : ℝ} (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    (8*(M:ℝ)*H/((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)))*
      (robertSargosTrimmedCorrelation f M H 0 0).re ≤ 8*(M:ℝ)^2 := by
  let Q : ℝ := ⌊lam^(-(3:ℝ)/13)⌋₊
  let R : ℝ := ⌊lam^(-(1:ℝ)/13)⌋₊
  have hT := (thirteenth_root_physical_scale hlam hsmall).1
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (positive_floor_half_bounds (show 1 ≤ lam^(-(1:ℝ)/13) by linarith)).1
  have h3 : (lam^(-(1:ℝ)/13))^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have hQ : 0 < Q := by
    dsimp [Q]
    have h1 : 1 ≤ lam^(-(3:ℝ)/13) := by
      rw [← h3]
      exact one_le_pow₀ (by linarith)
    exact_mod_cast (positive_floor_half_bounds h1).1
  have hs : (H:ℝ)^2 ≤ Q*R := zero_zero_floor_scale hlam hsmall hHmax
  have hb := mul_le_mul_of_nonneg_left (robertSargos_zero_zero_bound f M H)
    (show 0 ≤ 8*(M:ℝ)*H/(Q*R) by positivity)
  change (8*(M:ℝ)*H/(Q*R))*_ ≤ _
  refine hb.trans ?_
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos hQ hR)).mpr
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*(M:ℝ)^2 by positivity)
  convert hm using 1; ring

end TaoTrudgianYang2025
