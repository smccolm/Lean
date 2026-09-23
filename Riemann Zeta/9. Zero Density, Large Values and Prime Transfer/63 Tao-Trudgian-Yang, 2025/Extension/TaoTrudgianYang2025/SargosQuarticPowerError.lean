import TaoTrudgianYang2025.SargosQuarticBTransform

/-! The N^(1/4) source error used in the large-source sixth-moment reduction. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_quarterPower_sq {N : ℝ} (hN : 0 ≤ N) :
    (N^((1:ℝ)/4))^2 = Real.sqrt N := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hN]
  norm_num

theorem sargos_source_inverse_sqrt_le_quarterPower {N α : ℝ}
    (hN : 1 ≤ N) (hα : 1/Real.sqrt N ≤ α) :
    1/Real.sqrt α ≤ N^((1:ℝ)/4) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hαp : 0 < α := (div_pos (by norm_num) hNs).trans_le hα
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hαp
  let P := N^((1:ℝ)/4)
  have hP : 0 ≤ P := Real.rpow_nonneg hNp.le _
  have hP2 : P^2 = Real.sqrt N := sargos_quarterPower_sq hNp.le
  have ha : 1 ≤ α*Real.sqrt N := (div_le_iff₀ hNs).mp hα
  have he : (Real.sqrt α*P)^2 = α*Real.sqrt N := by
    rw [mul_pow,Real.sq_sqrt hαp.le,hP2]
  have hh : 1 ≤ Real.sqrt α*P := by
    have hz : 0 ≤ Real.sqrt α*P := by positivity
    nlinarith only [ha,he,hz]
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hh]

theorem sargos_log_one_add_le_quarterPower {N : ℝ} (hN : 1 ≤ N) :
    Real.log (N+1) ≤ 1+4*N^((1:ℝ)/4) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh := Real.log_le_log (show 0 < N+1 by positivity) (show N+1 ≤ 2*N by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hNp.ne'] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hlog := Real.log_le_rpow_div hNp.le (by norm_num : (0:ℝ) < 1/4)
  nlinarith only [hh,htwo,hlog]

theorem sargosQuartic_source_B_transform_quarterPower :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
          sargosQuarticStationaryMainTerm N α γ y)‖ ≤ C*(N : ℝ)^((1:ℝ)/4) := by
  obtain ⟨M,hM,hsource⟩ := sargosQuartic_source_B_transform_logN
  refine ⟨7*M,by linarith,?_⟩
  intro N α γ hN hα hα₁ hγ
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have ha := sargos_source_inverse_sqrt_le_quarterPower hNr hα
  have hl := sargos_log_one_add_le_quarterPower hNr
  have hP : 1 ≤ (N : ℝ)^((1:ℝ)/4) :=
    Real.one_le_rpow hNr (by norm_num)
  apply (hsource N α γ hN hα hα₁ hγ).trans
  have hh := mul_le_mul_of_nonneg_left
    (show 1/Real.sqrt α+1+Real.log ((N : ℝ)+1) ≤ 7*(N : ℝ)^((1:ℝ)/4) by
      linarith only [ha,hl,hP]) (show 0 ≤ M by linarith)
  convert hh using 1
  ring

theorem sargosQuartic_source_le_stationary_quarterPower :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤
        ‖∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
          sargosQuarticStationaryMainTerm N α γ y‖+C*(N : ℝ)^((1:ℝ)/4) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_source_B_transform_quarterPower
  refine ⟨C,hC,?_⟩
  intro N α γ hN hα hα₁ hγ
  have hs := hsource N α γ hN hα hα₁ hγ
  let q := ∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
    sargosQuarticStationaryMainTerm N α γ y
  have hn := norm_add_le (sargosQuarticSum N (fun _ => 1) α γ-q) q
  rw [sub_add_cancel] at hn
  change ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤ ‖q‖+_
  linarith only [hs,hn]

end TaoTrudgianYang2025

