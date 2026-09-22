import TaoTrudgianYang2025.BetaLegendreAllOrders

/-!
# Common compact slope domains and finite-order dual-phase uniformity

A fixed closed interval strictly inside (2^(-sigma),1) belongs to every
sufficiently accurate model phase's actual slope image. The final consumer
derives that inclusion and all requested derivative errors with one tolerance.
Canonical-domain extension and the transformed-sum theorem remain separate.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem modelPhaseSlopeRange_contains_compact_model_interval
    {σ δ a b : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hδ : δ ≤ min ((a-(2 : ℝ)^(-σ))/4) ((1-b)/4))
    (hF : IsApproximateModelPhaseFunction F σ P δ) :
    Icc a b ⊆ modelPhaseSlopeRange F := by
  let l := ((2 : ℝ)^(-σ)+a)/2
  let r := (b+1)/2
  have hp : 0 < (2 : ℝ)^(-σ) := Real.rpow_pos_of_pos (by norm_num) _
  have hl : l ∈ Ioo ((2 : ℝ)^(-σ)) 1 := by dsimp [l]; constructor <;> linarith
  have hr : r ∈ Ioo ((2 : ℝ)^(-σ)) 1 := by dsimp [r]; constructor <;> linarith
  have hlr : l ≤ r := by dsimp [l,r]; linarith
  have hlu := reciprocal_modelPhase_mem hσ hl
  have hru := reciprocal_modelPhase_mem hσ hr
  have huOrder : r^(-σ⁻¹) ≤ l^(-σ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos (hp.trans hl.1) hlr (neg_nonpos.mpr (inv_nonneg.mpr hσ.le))
  have hleft : (l^(-σ⁻¹))^(-σ) = l :=
    reciprocal_modelPhase_identity hσ (hp.trans hl.1).le
  have hright : (r^(-σ⁻¹))^(-σ) = r :=
    reciprocal_modelPhase_identity hσ (hp.trans hr.1).le
  intro v hv
  apply modelPhaseSlopeRange_contains_trimmed_model_interval hF hru.1 huOrder hlu.2
  rw [hleft,hright]
  have hd₁ := hδ.trans (min_le_left _ _)
  have hd₂ := hδ.trans (min_le_right _ _)
  dsimp [l,r]
  constructor <;> linarith [hv.1,hv.2]

def legendreFiniteInputOrder (Q : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (Q+1), (inversePhaseOrder (inversePhaseDerivativeExpression n)+1)

def legendreFiniteErrorConstant (σ : ℝ) (Q : ℕ) : ℝ :=
  1+∑ n ∈ Finset.range (Q+1), legendreModelErrorConstant σ n

theorem legendreFiniteInputOrder_le {Q n : ℕ} (hn : n ≤ Q) :
    inversePhaseOrder (inversePhaseDerivativeExpression n)+1 ≤ legendreFiniteInputOrder Q := by
  unfold legendreFiniteInputOrder
  exact Finset.single_le_sum (fun k _ => Nat.zero_le
    (inversePhaseOrder (inversePhaseDerivativeExpression k)+1))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))

theorem legendreFiniteErrorConstant_pos {σ : ℝ} (hσ : 0 < σ) (Q : ℕ) :
    0 < legendreFiniteErrorConstant σ Q := by
  have h := Finset.sum_nonneg (s := Finset.range (Q+1))
    (fun n _ => legendreModelErrorConstant_nonneg hσ n)
  unfold legendreFiniteErrorConstant
  linarith

theorem legendreModelErrorConstant_le_finite {σ : ℝ} (hσ : 0 < σ)
    {Q n : ℕ} (hn : n ≤ Q) :
    legendreModelErrorConstant σ n ≤ legendreFiniteErrorConstant σ Q := by
  have h := Finset.single_le_sum (s := Finset.range (Q+1))
    (fun k _ => legendreModelErrorConstant_nonneg hσ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))
  unfold legendreFiniteErrorConstant
  linarith

theorem modelPhaseLegendreDual_finiteOrder_model_error
    {σ δ : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F)
    (hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1) {n : ℕ} (hn : n ≤ Q) :
    |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
      iteratedDeriv n (modelPhase σ⁻¹) v| ≤ legendreFiniteErrorConstant σ Q * δ :=
  (modelPhaseLegendreDual_iteratedDeriv_model_error n hσ hδ
    (approximateModelPhase_mono hF (legendreFiniteInputOrder_le hn) le_rfl) hv hm).trans
    (mul_le_mul_of_nonneg_right (legendreModelErrorConstant_le_finite hσ hn)
      (approximateModelPhase_tolerance_nonneg hF))

theorem modelPhaseLegendreDual_compact_uniformity
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      ∀ F : ℝ → ℝ,
        IsApproximateModelPhaseFunction F σ (legendreFiniteInputOrder Q) δ →
      ∀ v ∈ Icc a b, v ∈ modelPhaseSlopeRange F ∧
        ∀ n ≤ Q, |iteratedDeriv (n+1) (modelPhaseLegendreDual F) v -
          iteratedDeriv n (modelPhase σ⁻¹) v| ≤ ε := by
  let η := min ((a-(2 : ℝ)^(-σ))/4) ((1-b)/4)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  let δ := min (min (modelPhaseCurvatureLower σ) 1)
    (min η (ε/legendreFiniteErrorConstant σ Q))
  have hC := legendreFiniteErrorConstant_pos hσ Q
  have hd : 0 < δ := lt_min (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
    (lt_min hη (div_pos hε hC))
  refine ⟨δ,hd,min_le_left _ _,?_⟩
  intro F hF v hv
  have hδ := min_le_left (min (modelPhaseCurvatureLower σ) 1)
    (min η (ε/legendreFiniteErrorConstant σ Q))
  have hδη : δ ≤ η :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/legendreFiniteErrorConstant σ Q :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hvJ := modelPhaseSlopeRange_contains_compact_model_interval hσ ha hab hb hδη hF hv
  refine ⟨hvJ,?_⟩
  intro n hn
  have hm : v ∈ Ioo ((2 : ℝ)^(-σ)) 1 :=
    ⟨ha.trans_le hv.1, hv.2.trans_lt hb⟩
  have he := modelPhaseLegendreDual_finiteOrder_model_error Q hσ hδ hF hvJ hm hn
  have hcδ : legendreFiniteErrorConstant σ Q*δ ≤ ε := by
    have h := (le_div_iff₀ hC).mp hδε
    nlinarith
  exact he.trans hcδ

end TaoTrudgianYang2025
