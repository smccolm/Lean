import TaoTrudgianYang2025.BetaBufferedSharpCore

/-!
# Original source expansion with sharp stationary error

The actual Poisson source and its finite original slope-envelope core
are consumed. Main terms are the literal interior plateau frequencies.
Every omitted mode is estimated, and no eta^-3 stationary loss remains.
The far-tail radius and all finite harmonic lengths remain explicit.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhase_buffered_source_sharp_expansion
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N η : ℝ) (a b : ℕ),
        0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        (a : ℝ)/N+4*η < (b : ℝ)/N →
        ∀ (F : ℝ → ℝ) (δ T ε : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
          0 < T → 0 < ε →
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let L := modelPhaseBufferedSupportLower F ((b : ℝ)/N) η T N
          let U := modelPhaseBufferedSupportUpper F ((a : ℝ)/N) η T N
          let P := modelPhaseBufferedPlateauLower F ((b : ℝ)/N) η T N
          let Q := modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) η T N
          let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            (∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q)‖ ≤
            4*N*η+2+ε+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(1+Real.log ((Q-P-1).toNat : ℝ))+
              (2*(T/N)*(σ+1)*η+6)*E*N/Real.sqrt T+
              (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
  obtain ⟨C,hC,hsource⟩ := modelPhase_buffered_poisson_core_precision hσ
  obtain ⟨D,hD,E,hE,hsharp⟩ := modelPhaseBufferedSharpCore_error hσ
  refine ⟨C,hC,D,hD,E,hE,?_⟩
  intro N η a b hN hη hη₁ ha hb hflat F δ T ε hδ hF hT hε A B L U P Q R
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hs := (hsource N η a b hN hη hη₁ ha hb F δ T ε hδ hF₁ hT hε).2.2.2
  have hc := hsharp ((a : ℝ)/N) ((b : ℝ)/N) η
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb) hη hflat
    F δ T N hδ hF hT hN
  let core := ∑ q ∈ Finset.Icc A B,
    modelPhaseFourierMode (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q
  let main := ∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q
  have he : exponentialSumAt F T N a b-main =
      (exponentialSumAt F T N a b-core)+(core-main) := by abel
  change ‖exponentialSumAt F T N a b-main‖ ≤ _
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hs hc)).trans_eq (by ring)

theorem bufferedTransitionCost_eq {T N : ℝ} (hN : 0 < N) (σ D η : ℝ) :
    (2*(T/N)*(σ+1)*η+6)*D*N/Real.sqrt T =
      2*D*(σ+1)*η*Real.sqrt T+6*D*N/Real.sqrt T := by
  calc
    _ = 2*D*(σ+1)*η*(T/Real.sqrt T)+6*D*N/Real.sqrt T := by
      field_simp
    _ = _ := by rw [Real.div_sqrt]

theorem bufferedTransitionCost_inverse_sqrt {T N : ℝ} (hT : 0 < T) (hN : 0 < N) (σ D : ℝ) :
    (2*(T/N)*(σ+1)*(Real.sqrt T)⁻¹+6)*D*N/Real.sqrt T =
      2*D*(σ+1)+6*D*N/Real.sqrt T := by
  rw [bufferedTransitionCost_eq hN]
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  field_simp

theorem modelPhase_buffered_source_inverse_sqrt_expansion
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N T : ℝ) (a b : ℕ),
        0 < N → 1 ≤ T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
        (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
        ∀ (F : ℝ → ℝ) (δ : ℝ),
          δ ≤ min (modelPhaseCurvatureLower σ) 1 →
          IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
          let η := (Real.sqrt T)⁻¹
          let A := modelPhaseCoreLower σ δ T N
          let B := modelPhaseCoreUpper δ T N
          let L := modelPhaseBufferedSupportLower F ((b : ℝ)/N) η T N
          let U := modelPhaseBufferedSupportUpper F ((a : ℝ)/N) η T N
          let P := modelPhaseBufferedPlateauLower F ((b : ℝ)/N) η T N
          let Q := modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) η T N
          let R : ℕ := ⌈C*T*(1+T)^2/N⌉₊+A.natAbs+B.natAbs+1
          ‖exponentialSumAt F T N a b-
            (∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q)‖ ≤
            (4+6*E)*N/Real.sqrt T+3+2*E*(σ+1)+
              (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
                Real.log (((R : ℤ)-B).toNat : ℝ))+
              D*(1+Real.log ((Q-P-1).toNat : ℝ))+
              (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+Real.log ((B-U).toNat : ℝ)) := by
  obtain ⟨C,hC,D,hD,E,hE,hsource⟩ := modelPhase_buffered_source_sharp_expansion hσ
  refine ⟨C,hC,D,hD,E,hE,?_⟩
  intro N T a b hN hT ha hb hflat F δ hδ hF η A B L U P Q R
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hs₁ : 1 ≤ Real.sqrt T := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hη : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr hs
  have hη₁ : (Real.sqrt T)⁻¹ ≤ 1 := (inv_le_one₀ hs).mpr hs₁
  have h := hsource N ((Real.sqrt T)⁻¹) a b hN hη hη₁ ha hb hflat
    F δ T 1 hδ hF hTpos (by norm_num)
  dsimp only at h
  simp only [inv_inv,Real.sq_sqrt hTpos.le,abs_of_pos hTpos,mul_one] at h
  rw [bufferedTransitionCost_inverse_sqrt hTpos hN] at h
  exact h.trans_eq (by ring)

theorem norm_exponentialSumAt_le_buffered_short
    {N η : ℝ} (hN : 0 < N) (hη : 0 ≤ η)
    (F : ℝ → ℝ) (T : ℝ) (a b : ℕ)
    (hshort : (b : ℝ)/N ≤ (a : ℝ)/N+4*η) :
    ‖exponentialSumAt F T N a b‖ ≤ 4*N*η+1 := by
  apply (norm_exponentialSumAt_le_card F T N a b).trans
  by_cases hab : a ≤ b
  · rw [Nat.card_Icc,Nat.cast_sub (by omega : a ≤ b+1),Nat.cast_add,Nat.cast_one]
    have hw := mul_le_mul_of_nonneg_right hshort hN.le
    have he (x : ℝ) : (x/N)*N = x := div_mul_cancel₀ x hN.ne'
    rw [add_mul,he,he] at hw
    nlinarith
  · have hs : Finset.Icc a b = ∅ := by
      ext n
      simp only [Finset.mem_Icc,Finset.notMem_empty,iff_false]
      omega
    rw [hs,Finset.card_empty,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025
