import TaoTrudgianYang2025.BetaSourceChartPhysical

/-!
# Assembly of the entire original stationary main sum

A common positive model tolerance, finite derivative order and threshold
are chosen over the fixed finite chart set before any source data.
The exact chart partition then assembles every retained integer.
-/

noncomputable section

open Set Expdb
open scoped NNReal BigOperators

namespace TaoTrudgianYang2025

theorem sourceStationaryMain_physical_bound
    {α : ℝ≥0} {β σ : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
          C ≤ T → 0 < N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
          T^(1-(α : ℝ)-δ) ≤ N → N ≤ T^(1-(α : ℝ)+δ) →
          (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖∑ q ∈ modelPhaseSharpStationarySet F T N a b,
              modelPhaseStationaryMainTerm F T N q‖ ≤
            C*(N/Real.sqrt T)*T^(β+ε) := by
  classical
  let J := positiveSlopeChartIndices (modelPhaseSlopeMesh σ)
  have hdmesh := modelPhaseSlopeMesh_pos σ
  have hpow : (2 : ℝ)^(-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hfour : 4 ∈ J := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl,Nat.le_floor ?_⟩
    apply (le_div_iff₀ hdmesh).mpr
    unfold modelPhaseSlopeMesh
    norm_num
    linarith
  let i₀ : {j : ℕ // j ∈ J} := ⟨4,hfour⟩
  have hne : J.attach.Nonempty := ⟨i₀,Finset.mem_attach _ _⟩
  choose d hd hsmall hpos P hP C hC hall using
    fun i : {j : ℕ // j ∈ J} =>
      sourceStationaryChart_physical_bound hβ hσ i.val i.property hε
  let δ := J.attach.inf' hne d
  let Pall := J.attach.sup P
  let Cmax := J.attach.sup' hne C
  let K := max Cmax ((J.card : ℝ)*Cmax)
  have hδ : 0 < δ := (Finset.lt_inf'_iff hne).mpr (fun i _ => hd i)
  have hδi (i : {j : ℕ // j ∈ J}) : δ ≤ d i :=
    Finset.inf'_le d (Finset.mem_attach _ _)
  have hPi (i : {j : ℕ // j ∈ J}) : P i ≤ Pall :=
    Finset.le_sup (Finset.mem_attach _ _)
  have hCi (i : {j : ℕ // j ∈ J}) : C i ≤ Cmax :=
    Finset.le_sup' C (Finset.mem_attach _ _)
  have hPall : 2 ≤ Pall := (hP i₀).trans (hPi i₀)
  have hCmax : 1 ≤ Cmax := (hC i₀).trans (hCi i₀)
  have hK : 1 ≤ K := hCmax.trans (le_max_left _ _)
  have hδsmall := (hδi i₀).trans (hsmall i₀)
  have hδpos := (hδi i₀).trans (hpos i₀)
  refine ⟨δ,hδ,hδsmall,hδpos,Pall,hPall,K,hK,?_⟩
  intro T N F a b hTK hN ha hb hlow hhigh hlong hF
  have hT₁ : 1 ≤ T := hK.trans hTK
  have hT : 0 < T := zero_lt_one.trans_le hT₁
  have hF₁ : IsApproximateModelPhaseFunction F σ 1 δ :=
    approximateModelPhase_mono hF (le_trans (by norm_num) hPall) le_rfl
  have hchart : ∀ j ∈ J,
      ‖∑ q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
          (modelPhaseSlopeMesh σ) N T j, modelPhaseStationaryMainTerm F T N q‖ ≤
        Cmax*(N/Real.sqrt T)*T^(β+ε) := by
    intro j hj
    let i : {j : ℕ // j ∈ J} := ⟨j,hj⟩
    have hCT : C i ≤ T := (hCi i).trans ((le_max_left _ _).trans hTK)
    have hlowi : T^(1-(α : ℝ)-d i) ≤ N :=
      (Real.rpow_le_rpow_of_exponent_le hT₁ (by linarith [hδi i])).trans hlow
    have hhighi : N ≤ T^(1-(α : ℝ)+d i) :=
      hhigh.trans (Real.rpow_le_rpow_of_exponent_le hT₁ (by linarith [hδi i]))
    apply (hall i T N F a b hCT hN ha hb hlowi hhighi hlong
      (approximateModelPhase_mono hF (hPi i) (hδi i))).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCi i) (by positivity)) (Real.rpow_nonneg hT.le _)
  rw [← modelPhaseSharpStationarySet_chart_partition hσ hδsmall hδpos hF₁
    hT hN ha hb (fun q => modelPhaseStationaryMainTerm F T N q)]
  calc
    _ ≤ ∑ j ∈ J, ‖∑ q ∈ positiveSlopeChartFiber
        (modelPhaseSharpStationarySet F T N a b) (modelPhaseSlopeMesh σ) N T j,
          modelPhaseStationaryMainTerm F T N q‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, Cmax*(N/Real.sqrt T)*T^(β+ε) := Finset.sum_le_sum hchart
    _ = ((J.card : ℝ)*Cmax)*(N/Real.sqrt T)*T^(β+ε) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ K*(N/Real.sqrt T)*T^(β+ε) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        (Real.rpow_nonneg hT.le _)

end TaoTrudgianYang2025
