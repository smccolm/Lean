import TaoTrudgianYang2025.SargosInitialDyadicMoment
import TaoTrudgianYang2025.SargosInitialTruncation

/-! Uniform sixth moments for the actual integer interval 1 through N. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosInitialQuartic_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ z : ℤ → ℂ,
      (∀ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosInitialQuarticSum N z α γ‖^6) ≤
        C*(lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε) := by
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hMoment⟩ := sargosInitialQuartic_dyadic_sixth_moment (ε/2) hhalf
  let L : ℝ := ((1/Real.log 2)*(1+6/(ε/2)))^6
  let R : ℝ := (2:ℝ)^(3+ε)
  have hC₀ : 0 ≤ C := by linarith only [hC]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨C*L*R+1,by nlinarith only [mul_nonneg (mul_nonneg hC₀ hL) hR],?_⟩
  intro N hN z hz lambda hlambda c d
  obtain ⟨K,hNP,hPN⟩ := sargos_initial_dyadic_cover hN
  let P : ℕ := 2^(K+1)
  have hP : (0:ℝ) < P := by dsimp [P]; positivity
  have hN₀ : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hPN' : (P:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hPN
  have ht := hMoment K (sargosInitialCutoff N z)
    (sargosInitialCutoff_unit N (2^(K+1)) z hz) lambda hlambda c d
  simp_rw [sargosInitialQuarticSum_cutoff hNP] at ht
  have hcount := sargos_dyadic_count_six_le_rpow K hhalf
  have hF : 0 ≤ lambda*(P:ℝ)^(3+ε/2)+(P:ℝ)^(ε/2) := by positivity
  have hp₁ : (P:ℝ)^(ε/2)*(P:ℝ)^(3+ε/2) = (P:ℝ)^(3+ε) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  have hp₂ : (P:ℝ)^(ε/2)*(P:ℝ)^(ε/2) = (P:ℝ)^ε := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  have hmain : (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      ‖sargosInitialQuarticSum N z α γ‖^6) ≤
      C*L*(lambda*(P:ℝ)^(3+ε)+(P:ℝ)^ε) := by
    calc
      _ ≤ C*((K:ℝ)+1)^6*(lambda*(P:ℝ)^(3+ε/2)+(P:ℝ)^(ε/2)) := ht
      _ ≤ C*(L*(P:ℝ)^(ε/2))*(lambda*(P:ℝ)^(3+ε/2)+(P:ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hC₀) hF
      _ = C*L*(lambda*((P:ℝ)^(ε/2)*(P:ℝ)^(3+ε/2))+
          (P:ℝ)^(ε/2)*(P:ℝ)^(ε/2)) := by ring
      _ = _ := by rw [hp₁,hp₂]
  have hpow₁ : (P:ℝ)^(3+ε) ≤ R*(N:ℝ)^(3+ε) := by
    have hh := Real.rpow_le_rpow hP.le hPN' (by linarith only [hε] : 0 ≤ 3+ε)
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN₀] using hh
  have hpow₂ : (P:ℝ)^ε ≤ R*(N:ℝ)^ε := by
    have hh := Real.rpow_le_rpow hP.le hPN' hε.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN₀] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by linarith : ε ≤ 3+ε)) (by positivity))
  have hFN : 0 ≤ lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε := by positivity
  calc
    _ ≤ C*L*(lambda*(P:ℝ)^(3+ε)+(P:ℝ)^ε) := hmain
    _ ≤ C*L*(lambda*(R*(N:ℝ)^(3+ε))+R*(N:ℝ)^ε) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hpow₁ hlambda.le) hpow₂)
        (mul_nonneg hC₀ hL)
    _ = (C*L*R)*(lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hFN

end TaoTrudgianYang2025

