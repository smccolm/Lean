import TaoTrudgianYang2025.BetaTaylorStationaryMain

/-!
# Upstream beta bounds on each original stationary chart

All chart membership, slope-image, moving-plateau and natural-interval
hypotheses are derived from the original model phase and source endpoints.
The only supplied sum estimate is the upstream nonasymptotic beta bound.
Physical dual power windows remain explicit for later scale transfer.
-/

noncomputable section

open Set Expdb
open scoped BigOperators NNReal

namespace TaoTrudgianYang2025

theorem sourceStationaryChart_bound_of_exponentSumBound
    {α : ℝ≥0} {β σ : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    (j : ℕ) (hj : j ∈ positiveSlopeChartIndices (modelPhaseSlopeMesh σ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
          0 < T → 0 < N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
          (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
          IsApproximateModelPhaseFunction F σ P δ →
          let A := positiveSlopeChartScale (modelPhaseSlopeMesh σ) j
          C ≤ modelPhaseDualParameter σ A T →
          (modelPhaseDualParameter σ A T)^((α : ℝ)-δ) ≤ modelPhaseDualScale A T N →
          modelPhaseDualScale A T N ≤ (modelPhaseDualParameter σ A T)^((α : ℝ)+δ) →
          ‖∑ q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
              (modelPhaseSlopeMesh σ) N T j, modelPhaseStationaryMainTerm F T N q‖ ≤
            2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹) *
              C*(modelPhaseDualParameter σ A T)^(β+ε) := by
  classical
  let A := positiveSlopeChartScale (modelPhaseSlopeMesh σ) j
  have hAbounds := positiveSlopeChartScale_bounds (modelPhaseSlopeMesh_pos σ) hj
  have hA : 0 < A := hAbounds.1
  have hA₂ : A ≤ 2 := hAbounds.2.trans (by norm_num)
  obtain ⟨dβ,hdβ,Q,_hQ,C,hC,hbound⟩ := hβ ε hε σ⁻¹ (inv_pos.mpr hσ)
  obtain ⟨η,hη,hsmall,hpos,hcanonical⟩ :=
    modelPhase_source_canonicalTaylorPhase hσ hA hA₂ Q hdβ
  let d := min (modelPhaseAmplitudeTolerance σ) (min η dβ)
  let P := max 2 (legendreFiniteInputOrder (Q+2))
  have hd : 0 < d := lt_min (modelPhaseAmplitudeTolerance_pos hσ) (lt_min hη hdβ)
  have hdamp : d ≤ modelPhaseAmplitudeTolerance σ := min_le_left _ _
  have hdη : d ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hddβ : d ≤ dβ := (min_le_right _ _).trans (min_le_right _ _)
  have hdsmall := hdη.trans hsmall
  have hdpos := hdη.trans hpos
  refine ⟨d,hd,hdsmall,hdpos,P,le_max_left _ _,C,hC,?_⟩
  intro T N F a b hT hN ha hb hlong hF
  dsimp only
  intro hTC hlow hhigh
  have hF₂ : IsApproximateModelPhaseFunction F σ 2 d :=
    approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hF₁ : IsApproximateModelPhaseFunction F σ 1 d :=
    approximateModelPhase_mono hF₂ (by norm_num) le_rfl
  let w := deriv F ((3 : ℝ)/2)
  let h := modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹)
  have hK := (hcanonical F
    (approximateModelPhase_mono hF (le_max_right _ _) hdη)
    N T a b hN hT ha hb hlong).1
  have hwmem : w ∈ modelPhaseSlopeRange F :=
    ⟨(3 : ℝ)/2,by constructor <;> norm_num,rfl⟩
  have hw : 0 < w :=
    (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
      (modelPhaseSlopeRange_positive_window hσ hdpos hF₁ hwmem).1
  have hh : 0 < h := modelPhaseTaylorWidth_pos hσ (by positivity)
  have hNd : 0 < modelPhaseDualScale A T N := modelPhaseDualScale_pos hA hT hN
  have hTd : 1 ≤ modelPhaseDualParameter σ A T := hC.trans hTC
  have hlowβ : (modelPhaseDualParameter σ A T)^((α : ℝ)-dβ) ≤
      modelPhaseDualScale A T N :=
    (Real.rpow_le_rpow_of_exponent_le hTd (by linarith : (α : ℝ)-dβ ≤ α-d)).trans hlow
  have hhighβ : modelPhaseDualScale A T N ≤
      (modelPhaseDualParameter σ A T)^((α : ℝ)+dβ) :=
    hhigh.trans (Real.rpow_le_rpow_of_exponent_le hTd (by linarith : (α : ℝ)+d ≤ α+dβ))
  let s := positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
    (modelPhaseSlopeMesh σ) N T j
  by_cases hne : s.Nonempty
  · obtain ⟨c,L,hinterval⟩ := modelPhaseSharpStationarySet_chart_natural_interval
      hσ hdsmall hdpos hF₁ hT hN ha hb hne
    have hmem : ∀ i : ℕ, i ≤ L → ((c+i : ℕ) : ℤ) ∈ s := by
      intro i hi
      rw [show s = _ from hinterval]
      apply Finset.mem_image.mpr
      exact ⟨c+i,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,rfl⟩
    have hsource : ∀ i : ℕ, i ≤ L →
        ((c+i : ℕ) : ℤ) ∈ modelPhaseSharpStationarySet F T N a b :=
      fun i hi => (mem_positiveSlopeChartFiber.mp (hmem i hi)).1
    have hcoord : ∀ i : ℕ, i ≤ L →
        (((c : ℝ)+i)*N/T)/A ∈ Ioo (1 : ℝ) 2 := by
      intro i hi
      simpa only [Int.cast_add,Int.cast_natCast,Nat.cast_add] using
        modelPhaseSharpStationarySet_chart_coordinate
          hσ hdsmall hdpos hF₁ hT hN ha hb (hmem i hi)
    have haN : modelPhaseDualScale A T N ≤ (c : ℝ) := by
      have hc := (hcoord 0 (Nat.zero_le L)).1
      simp only [Nat.cast_zero,add_zero] at hc
      rw [← modelPhaseDualScale_coordinate hA.ne' hT.ne' hN.ne' (c : ℝ)] at hc
      exact ((one_lt_div hNd).mp hc).le
    have hbN : ((c+L : ℕ) : ℝ) ≤ 2*modelPhaseDualScale A T N := by
      have hc := (hcoord L le_rfl).2
      rw [← modelPhaseDualScale_coordinate hA.ne' hT.ne' hN.ne' ((c : ℝ)+L)] at hc
      simpa only [Nat.cast_add] using ((div_lt_iff₀ hNd).mp hc).le
    have hmax : exponentialSumAtPrefixMax (canonicalTaylorLegendrePhase F σ A Q w h)
        (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N) c L ≤
          C*(modelPhaseDualParameter σ A T)^(β+ε) := by
      apply exponentialSumAtPrefixMax_le
      intro k hk
      apply hbound (modelPhaseDualParameter σ A T) (modelPhaseDualScale A T N)
        (canonicalTaylorLegendrePhase F σ A Q w h) c (c+k)
      refine ⟨hTC,hlowβ,hhighβ,hK,haN,?_⟩
      exact (show ((c+k : ℕ) : ℝ) ≤ ((c+L : ℕ) : ℝ) by
        exact_mod_cast Nat.add_le_add_left hk c).trans hbN
    have hslope : ∀ i : ℕ, i ≤ L → ((c : ℝ)+i)*N/T ∈ modelPhaseSlopeRange F := by
      intro i hi
      simpa only [Int.cast_add,Int.cast_natCast,Nat.cast_add] using
        (modelPhaseSharpStationarySet_critical_geometry hσ hdsmall hF₁ hT hN ha hb
          (hsource i hi)).1
    have hv : ∀ i : ℕ, i ≤ L → 0 < ((c : ℝ)+i)*N/T := by
      intro i hi
      exact (show 0 < (2 : ℝ)^(-σ)/2 by positivity).trans_le
        (modelPhaseSlopeRange_positive_window hσ hdpos hF₁ (hslope i hi)).1
    have hplateau : ∀ i : ℕ, i ≤ L → ((c : ℝ)+i)*N/T ∈ Icc
        (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h) := by
      intro i hi
      simpa only [Int.cast_add,Int.cast_natCast,Nat.cast_add] using
        modelPhaseSharpStationarySet_taylor_plateau hσ hdsmall hF₁ hT hN ha hb
          (hsource i hi)
    have hsum : (∑ q ∈ s, modelPhaseStationaryMainTerm F T N q) =
        modelPhaseStationaryBlock F T N c L := by
      rw [show s = _ from hinterval,Finset.sum_image]
      · simp only [Int.cast_natCast,modelPhaseStationaryBlock]
      · intro n _ m _ he
        change (n : ℤ) = (m : ℤ) at he
        exact_mod_cast he
    change ‖∑ q ∈ s, modelPhaseStationaryMainTerm F T N q‖ ≤ _
    rw [hsum]
    apply (norm_modelPhaseStationaryBlock_le_taylor_prefixMax Q hσ hdamp hF₂
      hA hw hh hT hN c L hslope hv hplateau).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmax
      (by positivity : 0 ≤ 2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹))
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change ‖∑ q ∈ s, modelPhaseStationaryMainTerm F T N q‖ ≤ _
    rw [hempty,Finset.sum_empty,norm_zero]
    positivity

end TaoTrudgianYang2025
