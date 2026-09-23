import TaoTrudgianYang2025.SargosQuarticMorsePhysical
import TaoTrudgianYang2025.BetaPoissonBoundary

/-! Exact Poisson entry for the literal quartic source sum.
The cutoff is constructed from the source lattice, and the absolute series
and discarded endpoint error are proved without a model-phase hypothesis. -/

noncomputable section

open Set Filter MeasureTheory Expdb GafniTao
open scoped ContDiff Topology FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem sargos_ford_character_eq_fourier (x : ℝ) :
    fordAdditiveCharacter x = (𝐞 x : ℂ) := by
  rw [fordAdditiveCharacter,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

def sargosQuarticWeightedKernel (χ : ℝ → ℝ) (N α γ x : ℝ) : ℂ :=
  (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x) : ℂ)

def sargosQuarticFourierMode (χ : ℝ → ℝ) (N α γ m : ℝ) : ℂ :=
  ∫ x : ℝ, (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x-m*x) : ℂ)

theorem sargosQuarticWeightedKernel_contDiff {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (N α γ : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticWeightedKernel χ N α γ) := by
  unfold sargosQuarticWeightedKernel sargosQuarticPhase
  simp only [Real.fourierChar_apply]
  have hw : ContDiff ℝ ∞ (fun x : ℝ => χ (x/N)) := hχ.comp (contDiff_id.div_const N)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(α*x^2+γ*x^4)) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hw).mul
    (((Complex.ofRealCLM.contDiff.comp hp).mul contDiff_const).cexp)

theorem sargosQuarticWeightedKernel_zero_of_not_mem {χ : ℝ → ℝ} {N x : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (hx : x ∉ Icc N (2*N)) (α γ : ℝ) :
    sargosQuarticWeightedKernel χ N α γ x = 0 := by
  have hnot : x/N ∉ tsupport χ := by
    intro h
    have hu := hs h
    apply hx
    exact ⟨by simpa only [one_mul] using ((lt_div_iff₀ hN).mp hu.1).le,
      ((div_lt_iff₀ hN).mp hu.2).le⟩
  simp only [sargosQuarticWeightedKernel,image_eq_zero_of_notMem_tsupport hnot,
    Complex.ofReal_zero,zero_mul]

theorem sargosQuarticWeightedKernel_hasCompactSupport {χ : ℝ → ℝ} {N : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    HasCompactSupport (sargosQuarticWeightedKernel χ N α γ) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ hx => sargosQuarticWeightedKernel_zero_of_not_mem hs hN hx α γ)

def sargosQuarticWeightedSchwartz {χ : ℝ → ℝ} {N : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    SchwartzMap ℝ ℂ :=
  (sargosQuarticWeightedKernel_hasCompactSupport hs hN α γ).toSchwartzMap
    (sargosQuarticWeightedKernel_contDiff hχ N α γ)

theorem sargosQuarticWeightedSchwartz_apply {χ : ℝ → ℝ} {N : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ x : ℝ) :
    sargosQuarticWeightedSchwartz hχ hs hN α γ x = sargosQuarticWeightedKernel χ N α γ x := rfl

theorem sargosQuarticWeightedSchwartz_fourier {χ : ℝ → ℝ} {N : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ m : ℝ) :
    𝓕 (sargosQuarticWeightedSchwartz hχ hs hN α γ) m = sargosQuarticFourierMode χ N α γ m := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with x
  change 𝐞 (-(m*x)) • sargosQuarticWeightedKernel χ N α γ x =
    (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x-m*x) : ℂ)
  simp only [Circle.smul_def,smul_eq_mul,sargosQuarticWeightedKernel]
  rw [show sargosQuarticPhase α γ x-m*x = -(m*x)+sargosQuarticPhase α γ x by ring,
    AddChar.map_add_eq_mul,Circle.coe_mul]
  ring

theorem sargosQuartic_weighted_poisson {χ : ℝ → ℝ} {N : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    (∑' n : ℤ, sargosQuarticWeightedKernel χ N α γ n) =
      ∑' m : ℤ, sargosQuarticFourierMode χ N α γ m := by
  have h := SchwartzMap.tsum_eq_tsum_fourier (sargosQuarticWeightedSchwartz hχ hs hN α γ) 0
  simpa only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one,
    sargosQuarticWeightedSchwartz_fourier,sargosQuarticWeightedSchwartz_apply] using h

theorem summable_norm_sargosQuarticFourierMode {χ : ℝ → ℝ} {N : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    Summable (fun m : ℤ => ‖sargosQuarticFourierMode χ N α γ m‖) := by
  let f := sargosQuarticWeightedSchwartz hχ hs hN α γ
  have hdecay := (𝓕 f).isBigO_cocompact_rpow (-(2 : ℝ))
  have hsum := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (hdecay.comp_tendsto Int.tendsto_coe_cofinite)
  have h : Summable (fun m : ℤ => sargosQuarticFourierMode χ N α γ m) := by
    simpa only [f,Function.comp_def,Real.norm_eq_abs,sargosQuarticWeightedSchwartz_fourier] using hsum
  exact h.norm

theorem sargosQuarticSum_eq_fourier_interval (N : ℕ) (α γ : ℝ) :
    sargosQuarticSum N (fun _ => 1) α γ =
      ∑ n ∈ Finset.Icc ((N : ℤ)+1) (2*N), (𝐞 (sargosQuarticPhase α γ n) : ℂ) := by
  rw [sargosQuarticSum_eq_phase]
  simp only [one_mul,sargos_ford_character_eq_fourier]
  have hI : sargosSourceInterval N = Finset.Icc ((N : ℤ)+1) (2*N) := by
    ext n
    simp only [sargosSourceInterval,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [hI]

theorem sargosQuartic_source_poisson {N : ℕ} (hN : 1 ≤ N) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Ioo 1 2 ∧ HasCompactSupport χ ∧
      (∀ x : ℝ, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ n : ℤ, χ ((n : ℝ)/N) =
        if n ∈ modelPhaseInteriorIndices N ((N : ℤ)+1) (2*N) then 1 else 0) ∧
      ∀ α γ : ℝ, Summable (fun m : ℤ => ‖sargosQuarticFourierMode χ N α γ m‖) ∧
        ‖sargosQuarticSum N (fun _ => 1) α γ-
          ∑' m : ℤ, sargosQuarticFourierMode χ N α γ m‖ ≤ 2 := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨χ,hχ,hs,hcompact,hrange,hvalues⟩ :=
    exists_modelPhase_interior_cutoff hNp ((N : ℤ)+1) (2*N)
  refine ⟨χ,hχ,hs,hcompact,hrange,hvalues,?_⟩
  intro α γ
  refine ⟨summable_norm_sargosQuarticFourierMode hχ hs hNp α γ,?_⟩
  have hsource : (∑' n : ℤ, sargosQuarticWeightedKernel χ N α γ n) =
      ∑ n ∈ modelPhaseInteriorIndices N ((N : ℤ)+1) (2*N),
        (𝐞 (sargosQuarticPhase α γ n) : ℂ) := by
    rw [tsum_eq_sum (s := modelPhaseInteriorIndices N ((N : ℤ)+1) (2*N)) (fun n hn => by
      simp only [sargosQuarticWeightedKernel,hvalues n,if_neg hn,Complex.ofReal_zero,zero_mul])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [sargosQuarticWeightedKernel,hvalues n,if_pos hn,Complex.ofReal_one,one_mul]
  rw [← sargosQuartic_weighted_poisson hχ hs hNp α γ,hsource,sargosQuarticSum_eq_fourier_interval]
  let F : ℝ → ℝ := fun u => sargosQuarticPhase α γ ((N : ℝ)*u)
  have he (n : ℤ) : (1:ℝ)*F ((n : ℝ)/N) = sargosQuarticPhase α γ n := by
    dsimp only [F,one_mul]
    field_simp
  have hb := norm_modelPhase_full_sub_interior_le_two F 1
    (N := (N : ℝ)) (a := (N : ℤ)+1) (b := 2*N)
    (by push_cast; linarith) (by push_cast; rfl)
  simpa only [he] using hb


end TaoTrudgianYang2025
