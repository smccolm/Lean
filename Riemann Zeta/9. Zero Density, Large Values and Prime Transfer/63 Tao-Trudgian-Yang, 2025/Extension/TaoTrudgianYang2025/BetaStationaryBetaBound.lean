import TaoTrudgianYang2025.BetaAmplitudePartialSummation

/-!
# Actual source beta bounds deweight the stationary main block

A fixed canonical chart is constructed before epsilon and the source F.
Its model condition, slope image, amplitude variation and prefix bounds
are all derived. The only analytic bound supplied is the strictly
upstream unweighted source exponent-sum bound at the dual scale.
This is a main-term theorem, not a Fourier-integral approximation.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators NNReal

namespace TaoTrudgianYang2025

theorem stationaryMain_bound_of_exponentSumBound
    {α : ℝ≥0} {β σ l r : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    (hl : (2 : ℝ)^(-σ) < l) (hlr : l ≤ r) (hr : r < 1) (hratio : r < 2*l) :
    ∃ A : ℝ, 0 < A ∧ A < l ∧ r < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ v ∈ Icc l r, χ v = 1) ∧
        ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
          ∀ (T N : ℝ) (F : ℝ → ℝ) (a L : ℕ),
            0 < T → 0 < N →
            IsApproximateModelPhaseFunction F σ P δ →
            C ≤ modelPhaseDualParameter σ A T →
            (modelPhaseDualParameter σ A T)^((α : ℝ)-δ) ≤ modelPhaseDualScale A T N →
            modelPhaseDualScale A T N ≤ (modelPhaseDualParameter σ A T)^((α : ℝ)+δ) →
            (∀ i : ℕ, i ≤ L → ((a : ℝ)+i)*N/T ∈ Icc l r) →
            ‖modelPhaseStationaryBlock F T N a L‖ ≤
              2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
                C*(modelPhaseDualParameter σ A T)^(β+ε) := by
  obtain ⟨A,hA,hAl,hrA,χ,hχ,hcompact,hplateau,hchart⟩ :=
    modelPhaseLegendreDual_canonical_extension hσ hl hlr hr hratio
  refine ⟨A,hA,hAl,hrA,χ,hχ,hcompact,hplateau,?_⟩
  intro ε hε
  obtain ⟨dβ,hdβ,Q,hQ,C,hC,hbound⟩ := hβ ε hε σ⁻¹ (inv_pos.mpr hσ)
  obtain ⟨η,hη,_,hmodel⟩ := hchart Q dβ hdβ
  let d := min (modelPhaseAmplitudeTolerance σ) (min η dβ)
  let P := max 2 (legendreFiniteInputOrder (Q+1))
  have hd : 0 < d := lt_min (modelPhaseAmplitudeTolerance_pos hσ) (lt_min hη hdβ)
  have hdamp : d ≤ modelPhaseAmplitudeTolerance σ := min_le_left _ _
  have hdη : d ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hddβ : d ≤ dβ := (min_le_right _ _).trans (min_le_right _ _)
  have hlpos : 0 < l :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ)).trans hl
  refine ⟨d,hd,P,le_max_left _ _,C,hC,?_⟩
  intro T N F a L hT hN hF hTC hlow hhigh hwindow
  have hF₂ : IsApproximateModelPhaseFunction F σ 2 d :=
    approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  obtain ⟨hslope,hK,hretain⟩ := hmodel F
    (approximateModelPhase_mono hF (le_max_right _ _) hdη)
  have hNd : 0 < modelPhaseDualScale A T N := modelPhaseDualScale_pos hA hT hN
  have hTd : 1 ≤ modelPhaseDualParameter σ A T := hC.trans hTC
  have haN : modelPhaseDualScale A T N ≤ (a : ℝ) := by
    have h := (hretain _ (hwindow 0 (Nat.zero_le L))).1.1
    simp only [Nat.cast_zero,add_zero] at h
    rw [← modelPhaseDualScale_coordinate hA.ne' hT.ne' hN.ne' (a : ℝ)] at h
    exact ((one_lt_div hNd).mp h).le
  have hbN : ((a+L : ℕ) : ℝ) ≤ 2*modelPhaseDualScale A T N := by
    have h := (hretain _ (hwindow L le_rfl)).1.2
    rw [← modelPhaseDualScale_coordinate hA.ne' hT.ne' hN.ne' ((a : ℝ)+L)] at h
    simpa only [Nat.cast_add] using ((div_lt_iff₀ hNd).mp h).le
  have hlowβ : (modelPhaseDualParameter σ A T)^((α : ℝ)-dβ) ≤
      modelPhaseDualScale A T N :=
    (Real.rpow_le_rpow_of_exponent_le hTd (by linarith : (α : ℝ)-dβ ≤ α-d)).trans hlow
  have hhighβ : modelPhaseDualScale A T N ≤
      (modelPhaseDualParameter σ A T)^((α : ℝ)+dβ) :=
    hhigh.trans (Real.rpow_le_rpow_of_exponent_le hTd (by linarith : (α : ℝ)+d ≤ α+dβ))
  have hmax : exponentialSumAtPrefixMax (canonicalLegendrePhase χ F σ A l)
      (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) a L ≤
        C*(modelPhaseDualParameter σ A T)^(β+ε) := by
    apply exponentialSumAtPrefixMax_le
    intro j hj
    apply hbound (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N)
      (canonicalLegendrePhase χ F σ A l) a (a+j)
    refine ⟨hTC,hlowβ,hhighβ,hK,haN,?_⟩
    exact (show ((a+j : ℕ) : ℝ) ≤ ((a+L : ℕ) : ℝ) by
      exact_mod_cast Nat.add_le_add_left hj a).trans hbN
  have hmain := norm_modelPhaseStationaryBlock_le_prefixMax hσ hdamp hF₂
    hA hlpos hT hN a L
    (fun i hi => hslope (hwindow i hi))
    (fun i hi => hlpos.trans_le (hwindow i hi).1)
    (fun i hi => hplateau _ (hwindow i hi))
  apply hmain.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmax
    (by positivity : 0 ≤ 2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹))

end TaoTrudgianYang2025
