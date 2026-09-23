import TaoTrudgianYang2025.SargosInitialMomentTransfer

/-! The actual initial-interval sixth moment on power-of-two scales. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosInitialQuartic_dyadic_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ K : ℕ, ∀ z : ℤ → ℂ,
      (∀ n ∈ Finset.Ioc (0:ℤ) (2^(K+1):ℕ), ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosInitialQuarticSum (2^(K+1)) z α γ‖^6) ≤
        C*((K:ℝ)+1)^6*
          (lambda*((2^(K+1):ℕ):ℝ)^(3+ε)+((2^(K+1):ℕ):ℝ)^ε) := by
  obtain ⟨C,hC,hMoment⟩ := sargosQuartic_sixth_moment ε hε
  refine ⟨32*(C+64),by linarith only [hC],?_⟩
  intro K z hz lambda hlambda c d
  let P : ℕ := 2^(K+1)
  let F : ℝ := lambda*(P:ℝ)^(3+ε)+(P:ℝ)^ε
  have hP₂ : 2 ≤ P := by
    dsimp [P]
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (by omega : 1 ≤ K+1))
  have hP₁ : (1:ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hlambdaF : lambda ≤ F := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.one_le_rpow hP₁ (by linarith only [hε] : 0 ≤ 3+ε)) hlambda.le
    have hp : 0 ≤ (P:ℝ)^ε := by positivity
    dsimp [F]
    nlinarith only [hh,hp]
  have hz₂ : ∀ n ∈ Finset.Ioc (0:ℤ) 2, ‖z n‖ ≤ 1 := by
    intro n hn
    apply hz n
    simp only [Finset.mem_Ioc] at hn ⊢
    have hp : (2:ℤ) ≤ P := by exact_mod_cast hP₂
    exact ⟨hn.1,hn.2.trans hp⟩
  have hbase : (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      ‖sargosInitialQuarticSum 2 z α γ‖^6) ≤ 64*F := by
    have ht := sargosInitialQuartic_power_rectangle_trivial 2 6 z hz₂ hlambda.le c d
    norm_num at ht
    nlinarith only [ht,hlambdaF]
  have hi : ∀ i ∈ Finset.range K,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosQuarticSum (2^(i+1)) z α γ‖^6) ≤ C*F := by
    intro i hi
    have hiK := Finset.mem_range.mp hi
    have hN : 2 ≤ (2^(i+1):ℕ) := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (by omega : 1 ≤ i+1))
    have htop : 2*(2^(i+1):ℕ) ≤ P := by
      dsimp [P]
      calc
        _ = 2^(i+1+1) := by rw [pow_succ]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNP : (2^(i+1):ℕ) ≤ P := by omega
    have hzN : ∀ n ∈ sargosSourceInterval (2^(i+1)), ‖z n‖ ≤ 1 := by
      intro n hn
      have hh : (0:ℤ) ≤ (2^(i+1):ℕ) := Int.natCast_nonneg _
      have hhP : (2:ℤ)*(2^(i+1):ℕ) ≤ P := by exact_mod_cast htop
      apply hz n
      simp only [sargosSourceInterval,Finset.mem_Ioc] at hn
      simp only [Finset.mem_Ioc]
      exact ⟨hh.trans_lt hn.1,hn.2.trans hhP⟩
    have ht := hMoment (2^(i+1)) hN z hzN lambda hlambda c d
    have hNP' : ((2^(i+1):ℕ):ℝ) ≤ P := by exact_mod_cast hNP
    have hpow₁ := Real.rpow_le_rpow (Nat.cast_nonneg _) hNP'
      (by linarith only [hε] : 0 ≤ 3+ε)
    have hpow₂ := Real.rpow_le_rpow (Nat.cast_nonneg _) hNP' hε.le
    exact ht.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hpow₁ hlambda.le) hpow₂)
      (by linarith only [hC]))
  have hs : (∑ i ∈ Finset.range K,
      ∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosQuarticSum (2^(i+1)) z α γ‖^6) ≤ (K:ℝ)*(C*F) := by
    simpa using Finset.sum_le_sum hi
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
  have hKpow : (K:ℝ)^6 ≤ ((K:ℝ)+1)^6 :=
    pow_le_pow_left₀ hK (by linarith) 6
  have hone : (1:ℝ) ≤ ((K:ℝ)+1)^6 := one_le_pow₀ (by linarith)
  have hcoef : 64+C*(K:ℝ)^6 ≤ (C+64)*((K:ℝ)+1)^6 := by
    have hc := mul_le_mul_of_nonneg_left hKpow (by linarith only [hC] : 0 ≤ C)
    nlinarith only [hc,hone]
  calc
    _ ≤ 32*((∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosInitialQuarticSum 2 z α γ‖^6)+
        (K:ℝ)^5*∑ i ∈ Finset.range K,
          ∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
            ‖sargosQuarticSum (2^(i+1)) z α γ‖^6) :=
      sargosInitialQuartic_dyadic_integral K z c d lambda
    _ ≤ 32*(64*F+(K:ℝ)^5*((K:ℝ)*(C*F))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hbase (mul_le_mul_of_nonneg_left hs (by positivity))) (by norm_num)
    _ = 32*((64+C*(K:ℝ)^6)*F) := by ring
    _ ≤ 32*((C+64)*((K:ℝ)+1)^6*F) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hF) (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025
