import TaoTrudgianYang2025.IvicSixthExcessConvolution

/-! Uniform absorption of the actual restricted-moment threshold. -/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem eventually_ivicSixth_threshold_log {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop,
      (4*T)^(11/72+η)*zetaMomentLogLoss T ≤ T^(11/72+3*η) := by
  have hlog : ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T ≤ T^η := by
    simpa only [Real.rpow_one] using
      eventually_zetaMomentLogLoss_rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hη
  have hc := (tendsto_rpow_atTop hη).eventually
    (eventually_ge_atTop ((4:ℝ)^(11/72+η)))
  filter_upwards [hlog,hc,eventually_gt_atTop (0:ℝ)] with T hl hc hT
  rw [Real.mul_rpow (by norm_num) hT.le]
  calc
    _ ≤ (T^η*T^(11/72+η))*T^η :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hl
        (zetaMomentLogLoss_pos T).le (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hT,← Real.rpow_add hT]
      congr 1
      ring

theorem exists_ivicSixth_truncation_threshold {C η τ σ δ : ℝ}
    (hC : 0 < C) (hη : 0 < η) (hheight : 1 ≤ τ-δ)
    (hgap : 1/2+η+(τ+δ)*(11/72+3*η) ≤ σ-δ) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
      2*(C*P.N^(1/2:ℝ))*(4*P.T)^(11/72+η)*zetaMomentLogLoss P.T ≤ P.V := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_ivicSixth_threshold_log hη)
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (2*C)))
  refine ⟨max 1 (max A B),le_max_left _ _,?_⟩
  intro P hN hTl hTu hV
  have hN0 : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT0 : 0 < P.T := P.T_pos
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTl
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hheight
  have hAP : A ≤ P.T :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN)).trans hNT
  have hBP : B ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hTp : P.T^(11/72+3*η) ≤ P.N^((τ+δ)*(11/72+3*η)) := by
    have hh := Real.rpow_le_rpow P.T_pos.le hTu (by linarith : 0 ≤ 11/72+3*η)
    rw [← Real.rpow_mul hN0.le] at hh
    exact hh
  calc
    _ = (2*C)*P.N^(1/2:ℝ)*
        ((4*P.T)^(11/72+η)*zetaMomentLogLoss P.T) := by ring
    _ ≤ (2*C)*P.N^(1/2:ℝ)*P.T^(11/72+3*η) :=
      mul_le_mul_of_nonneg_left (hA P.T hAP) (by positivity)
    _ ≤ (P.N^η*P.N^(1/2:ℝ))*P.N^((τ+δ)*(11/72+3*η)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hB P.N hBP) (by positivity)) hTp
        (by positivity) (by positivity)
    _ = P.N^(1/2+η+(τ+δ)*(11/72+3*η)) := by
      rw [← Real.rpow_add hN0,← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ P.N^(σ-δ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hgap
    _ ≤ _ := hV

theorem exists_ivicSixth_pattern_moment {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ P : ZetaLargeValuePattern, T₀ ≤ P.T →
      ∀ C : ℝ, 0 < C →
      (∀ t ∈ P.ordinates, P.V ≤ C*P.N^(1/2:ℝ)*zetaMomentConvolution P.T t) →
      2*(C*P.N^(1/2:ℝ))*(4*P.T)^(11/72+η)*zetaMomentLogLoss P.T ≤ P.V →
      (P.ordinates.card : ℝ)*P.V^6 ≤ (2*C)^6*P.N^3*P.T^(1+3*η) := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_ivicSixthExcess_source_log_moment hη)
  refine ⟨max 1 A,le_max_left _ _,?_⟩
  intro P hT C hC hEntry hsmall
  have hN0 : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hf := P.ivicSixth_truncated_cardinality hC
    (Real.rpow_nonneg (by linarith [P.T_pos] : 0 ≤ 4*P.T) _) hEntry hsmall
  calc
    _ ≤ (2*C)^6*P.N^3*(zetaMomentLogLoss P.T^6*
        ∫ u in P.T/2..3*P.T, ivicSixthExcess ((4*P.T)^(11/72+η)) u^6) := by
      simpa only [mul_assoc] using hf
    _ ≤ _ := mul_le_mul_of_nonneg_left (hA P.T ((le_max_right _ _).trans hT))
      (by positivity)

end TaoTrudgianYang2025
