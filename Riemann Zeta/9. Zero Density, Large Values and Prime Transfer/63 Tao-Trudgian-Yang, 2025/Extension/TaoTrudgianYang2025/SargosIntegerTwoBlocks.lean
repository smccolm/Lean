import TaoTrudgianYang2025.SargosIntegerBlock

/-! Exact two-block control for any contiguous integer subinterval. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosInteger_intersection_le_two_prefixMaximum
    (n a b : ℤ) (H : ℕ) (f : ℤ → ℂ) :
    ‖∑ y ∈ (Finset.Icc a b) ∩ (Finset.Ioc n (n+H)), f y‖ ≤
      2*sargosIntegerPrefixMaximum (n+1) H f := by
  have he : (Finset.Icc a b) ∩ (Finset.Ioc n (n+H)) =
      Finset.Icc (max a (n+1)) (min b (n+H)) := by
    ext y
    simp only [Finset.mem_inter,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  rw [he]
  exact norm_sargosInteger_interval_le_two_prefixMaximum n _ _ H f (by omega) (by omega)

theorem norm_sargosInteger_intersection_two_dyadic (m : ℕ) (a b : ℤ) (f : ℤ → ℂ) :
    ‖∑ y ∈ (Finset.Icc a b) ∩ (Finset.Ioc (m:ℤ) (4*m)), f y‖ ≤
      2*sargosIntegerPrefixMaximum ((m:ℤ)+1) m f+
        2*sargosIntegerPrefixMaximum ((2*m:ℤ)+1) (2*m) f := by
  classical
  let S₁ := (Finset.Icc a b) ∩ (Finset.Ioc (m:ℤ) (2*m))
  let S₂ := (Finset.Icc a b) ∩ (Finset.Ioc (2*m:ℤ) (4*m))
  have he : (Finset.Icc a b) ∩ (Finset.Ioc (m:ℤ) (4*m)) = S₁ ∪ S₂ := by
    ext y
    simp only [S₁,S₂,Finset.mem_inter,Finset.mem_Icc,Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint S₁ S₂ := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    simp only [S₁,S₂,Finset.mem_inter,Finset.mem_Icc,Finset.mem_Ioc] at hy hz
    omega
  have h₁ : ‖∑ y ∈ S₁, f y‖ ≤ 2*sargosIntegerPrefixMaximum ((m:ℤ)+1) m f := by
    have h := norm_sargosInteger_intersection_le_two_prefixMaximum (m:ℤ) a b m f
    simpa only [S₁,show (m:ℤ)+(m:ℤ) = 2*m by omega] using h
  have h₂ : ‖∑ y ∈ S₂, f y‖ ≤ 2*sargosIntegerPrefixMaximum ((2*m:ℤ)+1) (2*m) f := by
    have h := norm_sargosInteger_intersection_le_two_prefixMaximum (2*m:ℤ) a b (2*m) f
    simpa only [S₂,Nat.cast_mul,Nat.cast_ofNat,show (2*m:ℤ)+(2*m:ℤ) = 4*m by omega] using h
  rw [he,Finset.sum_union hd]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

end TaoTrudgianYang2025
