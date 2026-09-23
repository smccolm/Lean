import TaoTrudgianYang2025.SargosInitialMomentTuples

/-! Sargos's actual sextuple count, uniform in every translated fourth-power window. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosInitialSextupleWindow_card_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ B : ℝ, 0 < B → ∀ c : ℝ,
      ((sargosInitialSextupleWindow N c B).card : ℝ) ≤
        C*((N:ℝ)^3+B)*(N:ℝ)^ε := by
  obtain ⟨C,hC,hMoment⟩ := sargosInitialQuartic_sixth_moment ε hε
  refine ⟨64*C,by linarith only [hC],?_⟩
  intro N hN B hB c
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hμ : 0 < 1/B := by positivity
  have hc := sargosShiftedNearPairs_card_le_central
    (Finset.univ : Finset (SargosInitialMomentTuple N 3))
    (fun t => (sargosInitialTuplePower 2 t : ℝ))
    (fun t => (sargosInitialTuplePower 4 t : ℝ))
    (by norm_num : (0:ℝ) < 1) hμ 0 c
  simp only [one_div_one,one_div_one_div,one_mul] at hc
  simp_rw [← sargosInitialQuarticSum_norm_even_eq_tuple_norm_sq N 3] at hc
  have hsub : ((sargosInitialSextupleWindow N c B).card : ℝ) ≤
      ((sargosShiftedNearPairs Finset.univ
        (fun t : SargosInitialMomentTuple N 3 => (sargosInitialTuplePower 2 t : ℝ))
        (fun t => (sargosInitialTuplePower 4 t : ℝ)) 0 c 1 B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (sargosInitialSextupleWindow_subset_shifted N c B)
  have hm := hMoment N hN (fun _ => 1) (by intro n hn; norm_num) (1/B) hμ
    (-(1/2)) (-((1/B)/2))
  have hα : -(1/2:ℝ)+1 = 1/2 := by ring
  have hγ : -((1/B)/2)+1/B = (1/B)/2 := by ring
  rw [hα,hγ] at hm
  have he : (N:ℝ)^(3+ε) = (N:ℝ)^3*(N:ℝ)^ε := by
    rw [Real.rpow_add hNp]
    norm_num
  calc
    _ ≤ (64/(1/B))*(∫ α in Icc (-(1/2:ℝ)) (1/2),
        ∫ γ in Icc (-((1/B)/2)) ((1/B)/2),
          ‖sargosInitialQuarticSum N (fun _ => 1) α γ‖^6) := hsub.trans hc
    _ ≤ (64/(1/B))*(C*((1/B)*(N:ℝ)^(3+ε)+(N:ℝ)^ε)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      rw [he]
      field_simp

theorem sargos_initial_sextuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ,
      ((sargosInitialSextupleWindow N c ((N:ℝ)^3)).card : ℝ) ≤ C*(N:ℝ)^(3+ε) := by
  obtain ⟨C,hC,h⟩ := sargosInitialSextupleWindow_card_bound ε hε
  refine ⟨2*C,by linarith only [hC],?_⟩
  intro N hN c
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ht := h N hN ((N:ℝ)^3) (by positivity) c
  have he : (N:ℝ)^(3+ε) = (N:ℝ)^3*(N:ℝ)^ε := by
    rw [Real.rpow_add hNp]
    norm_num
  calc
    _ ≤ C*((N:ℝ)^3+(N:ℝ)^3)*(N:ℝ)^ε := ht
    _ = _ := by rw [he]; ring

end TaoTrudgianYang2025
