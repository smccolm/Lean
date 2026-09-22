import TaoTrudgianYang2025.BetaBufferedLogBudget

/-!
# Uniform sharp-source error after controlling every logarithmic length

The prescribed radius, rounded endpoints, and three interior/core lengths
are consumed explicitly. Constants precede the phase and physical scales.
A separate faithful short-interval bound handles the complementary case.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem modelPhase_buffered_source_uniform_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (N T : ℝ) (a b : ℕ),
      1 ≤ N → 1 ≤ T → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
      ∀ (F : ℝ → ℝ) (δ : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        ‖exponentialSumAt F T N a b-
          (∑ q ∈ Finset.Ioo
            (modelPhaseBufferedPlateauLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N)
            (modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N),
            modelPhaseStationaryMainTerm F T N q)‖ ≤
          M*(N/Real.sqrt T+1+Real.log (T+1)) := by
  obtain ⟨C,hC,D,hD,E,hE,hsource⟩ := modelPhase_buffered_source_inverse_sqrt_expansion hσ
  let K := C+6
  let F₀ := D+16/Real.pi
  let A₀ := 4+6*E
  let B₀ := 3+2*E*(σ+1)+F₀*(1+Real.log K)
  let M := max 1 (max A₀ (max B₀ (3*F₀)))
  have hM₁ : 1 ≤ M := le_max_left _ _
  have hMA : A₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMB : B₀ ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hMF : 3*F₀ ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨M,hM₁,?_⟩
  intro N T a b hN hT ha hb hflat F δ hδ hF
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hη : 0 < (Real.sqrt T)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hTpos)
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  have hs := hsource N T a b hNpos hT ha hb hflat F δ hδ hF
  let A := modelPhaseCoreLower σ δ T N
  let B := modelPhaseCoreUpper δ T N
  let L := modelPhaseBufferedSupportLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N
  let U := modelPhaseBufferedSupportUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N
  let P := modelPhaseBufferedPlateauLower F ((b : ℝ)/N) ((Real.sqrt T)⁻¹) T N
  let Q := modelPhaseBufferedPlateauUpper F ((a : ℝ)/N) ((Real.sqrt T)⁻¹) T N
  let R : ℕ := ⌈C*T*(1+T)^2/N⌉₊+A.natAbs+B.natAbs+1
  let G := Real.log K+3*Real.log (T+1)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hfar := modelPhaseSharpFarLengths_le_polynomial hσ.le
    (approximateModelPhase_tolerance_nonneg hF) (hδ.trans (min_le_right _ _))
    hTpos.le hN (zero_le_one.trans hC)
  have hinner := modelPhaseBufferedInnerLengths_le hσ hδ hF₁ hTpos hNpos hη
    ((one_le_div hNpos).mpr ha) ((div_le_iff₀ hNpos).mpr hb) hflat
  have hscale := three_scale_le_polynomial_budget (zero_le_one.trans hC) hTpos.le hN
  have hlogA : Real.log ((A+(R : ℤ)).toNat : ℝ) ≤ G :=
    log_nat_le_polynomial_budget hK hTpos.le hfar.1
  have hlogB : Real.log (((R : ℤ)-B).toNat : ℝ) ≤ G :=
    log_nat_le_polynomial_budget hK hTpos.le hfar.2
  have hlogL : Real.log ((L-A).toNat : ℝ) ≤ G :=
    log_nat_le_polynomial_budget hK hTpos.le (hinner.1.trans hscale)
  have hlogU : Real.log ((B-U).toNat : ℝ) ≤ G :=
    log_nat_le_polynomial_budget hK hTpos.le (hinner.2.1.trans hscale)
  have hlogI : Real.log ((Q-P-1).toNat : ℝ) ≤ G :=
    log_nat_le_polynomial_budget hK hTpos.le (hinner.2.2.trans hscale)
  have hfarlog : (4/Real.pi)*(2+Real.log ((A+(R : ℤ)).toNat : ℝ)+
      Real.log (((R : ℤ)-B).toNat : ℝ)) ≤ (8/Real.pi)*(1+G) := by
    calc
      _ ≤ (4/Real.pi)*(2+G+G) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have houterlog : (4/Real.pi)*(2+Real.log ((L-A).toNat : ℝ)+
      Real.log ((B-U).toNat : ℝ)) ≤ (8/Real.pi)*(1+G) := by
    calc
      _ ≤ (4/Real.pi)*(2+G+G) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hmidlog : D*(1+Real.log ((Q-P-1).toNat : ℝ)) ≤ D*(1+G) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hlogI) (zero_le_one.trans hD)
  have hbound :
      ‖exponentialSumAt F T N a b-
        (∑ q ∈ Finset.Ioo P Q, modelPhaseStationaryMainTerm F T N q)‖ ≤
      A₀*(N/Real.sqrt T)+B₀+3*F₀*Real.log (T+1) := by
    apply hs.trans
    have hh := add_le_add (add_le_add (add_le_add
      (show (4+6*E)*N/Real.sqrt T+3+2*E*(σ+1) ≤
        (4+6*E)*N/Real.sqrt T+3+2*E*(σ+1) from le_rfl) hfarlog) hmidlog) houterlog
    convert hh using 1
    dsimp [A₀,B₀,F₀,G,K]
    ring
  apply hbound.trans
  have hx : 0 ≤ N/Real.sqrt T := by positivity
  have hy : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  calc
    _ ≤ M*(N/Real.sqrt T)+M+M*Real.log (T+1) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hMA hx) hMB)
        (mul_le_mul_of_nonneg_right hMF hy)
    _ = _ := by ring

end TaoTrudgianYang2025
