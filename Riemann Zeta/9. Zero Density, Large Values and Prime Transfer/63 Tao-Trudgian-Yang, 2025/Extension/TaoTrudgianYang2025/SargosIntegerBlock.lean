import TaoTrudgianYang2025.SargosQuarticResidualAbel

/-! Exact integer prefix differences for contiguous subintervals of a dyadic block. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_Ioc_eq_integerPrefix (a : ℤ) (H : ℕ) (f : ℤ → ℂ) :
    (∑ y ∈ Finset.Ioc a (a+H), f y) = sargosIntegerPrefix (a+1) H f := by
  have he : Finset.Ioc a (a+H) = Finset.Icc (a+1) (a+H) := by
    ext y
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [he,sargos_sum_Icc_eq_range]
  have hlen : (a+(H:ℤ)+1-(a+1)).toNat = H := by omega
  rw [hlen]
  rfl

theorem norm_sargosInteger_interval_le_two_prefixMaximum (n a b : ℤ) (H : ℕ) (f : ℤ → ℂ)
    (hna : n < a) (hb : b ≤ n+H) :
    ‖∑ y ∈ Finset.Icc a b, f y‖ ≤ 2*sargosIntegerPrefixMaximum (n+1) H f := by
  have hB := sargosIntegerPrefixMaximum_nonneg (n+1) H f
  by_cases hab : a ≤ b
  · let L₀ := (a-1-n).toNat
    let L₁ := (b-n).toNat
    have he₀ : n+(L₀:ℤ) = a-1 := by dsimp [L₀]; omega
    have he₁ : n+(L₁:ℤ) = b := by dsimp [L₁]; omega
    have hL₀ : L₀ ≤ H := by dsimp [L₀]; omega
    have hL₁ : L₁ ≤ H := by dsimp [L₁]; omega
    have hdis : Disjoint (Finset.Ioc n (a-1)) (Finset.Ioc (a-1) b) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      simp only [Finset.mem_Ioc] at hy hz
      omega
    have hunion := Finset.Ioc_union_Ioc_eq_Ioc (show n ≤ a-1 by omega) (show a-1 ≤ b by omega)
    have hs := Finset.sum_union (f := f) hdis
    rw [hunion] at hs
    have he : Finset.Ioc (a-1) b = Finset.Icc a b := by
      ext y
      simp only [Finset.mem_Ioc,Finset.mem_Icc]
      omega
    have hp₀ : (∑ y ∈ Finset.Ioc n (a-1), f y) = sargosIntegerPrefix (n+1) L₀ f := by
      rw [← he₀]
      exact sargos_sum_Ioc_eq_integerPrefix n L₀ f
    have hp₁ : (∑ y ∈ Finset.Ioc n b, f y) = sargosIntegerPrefix (n+1) L₁ f := by
      rw [← he₁]
      exact sargos_sum_Ioc_eq_integerPrefix n L₁ f
    rw [he,hp₀,hp₁] at hs
    have hsum : (∑ y ∈ Finset.Icc a b, f y) =
        sargosIntegerPrefix (n+1) L₁ f-sargosIntegerPrefix (n+1) L₀ f := by
      linear_combination -hs
    rw [hsum]
    have h₀ := norm_sargosIntegerPrefix_le_maximum (n+1) H L₀ f hL₀
    have h₁ := norm_sargosIntegerPrefix_le_maximum (n+1) H L₁ f hL₁
    exact (norm_sub_le _ _).trans (by linarith)
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab),Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025

