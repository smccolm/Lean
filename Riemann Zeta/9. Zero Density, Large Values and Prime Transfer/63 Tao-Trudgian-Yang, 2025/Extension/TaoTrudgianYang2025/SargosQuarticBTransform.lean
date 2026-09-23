import TaoTrudgianYang2025.SargosQuarticEndpointError

/-! The large-source-range quartic B-transform with its full closed stationary sum.
All cutoff, Fourier-window, tail and endpoint errors have been consumed. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuartic_source_B_transform_logN :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
          sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        M*(1/Real.sqrt α+1+Real.log ((N : ℝ)+1)) := by
  obtain ⟨M,hM,hsource⟩ := sargosQuartic_source_buffered_uniform_logN
  refine ⟨M+17,by linarith,?_⟩
  intro N α γ hN hα hα₁ hγ
  let η := sargosQuarticStationaryWidth N α
  let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
  let B := sargosQuarticPlateauUpper N α γ 2 η
  let p := ∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y
  let q := ∑ y ∈ sargosQuarticStationaryFrequencies N α γ, sargosQuarticStationaryMainTerm N α γ y
  have hs : ‖sargosQuarticSum N (fun _ => 1) α γ-p‖ ≤
      M*(1/Real.sqrt α+1+Real.log ((N : ℝ)+1)) := hsource N α γ hN hα hα₁ hγ
  have he : ‖q-p‖ ≤ 17*(1/Real.sqrt α+1) :=
    sargosQuarticStationary_endpoint_error_source hN hα hα₁ hγ
  have hn := norm_add_le (sargosQuarticSum N (fun _ => 1) α γ-p) (p-q)
  rw [sub_add_sub_cancel,norm_sub_rev p q] at hn
  have hl : 0 ≤ Real.log ((N : ℝ)+1) :=
    Real.log_nonneg (by have hh := Nat.cast_nonneg (α := ℝ) N; linarith)
  change ‖sargosQuarticSum N (fun _ => 1) α γ-q‖ ≤ _
  nlinarith only [hn,hs,he,hl]

theorem sargosQuartic_source_B_transform :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ sargosQuarticStationaryFrequencies N α γ,
          sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        M*(1/Real.sqrt α+1+Real.log (2+α*N)) := by
  obtain ⟨M,hM,hsource⟩ := sargosQuartic_source_B_transform_logN
  refine ⟨2*M,by linarith,?_⟩
  intro N α γ hN hα hα₁ hγ
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have ha := sargosQuartic_source_scale hNr hα
  have hαp : 0 < α := ha.1
  have hheight : (N : ℝ)+1 ≤ (2+α*N)^2 := by
    have hh := mul_le_mul_of_nonneg_left ha.2.2 hNp.le
    nlinarith [mul_nonneg hαp.le hNp.le]
  have hlog := Real.log_le_log (show (0:ℝ) < (N : ℝ)+1 by positivity) hheight
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs := hsource N α γ hN hα hα₁ hγ
  apply hs.trans
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ M by linarith)
  have hx : 0 ≤ M*(1/Real.sqrt α+1) := by positivity
  nlinarith only [hm,hx]

end TaoTrudgianYang2025
