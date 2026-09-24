import TaoTrudgianYang2025.ZetaReflectionSourceLossWindow

/-! Actual normalized reflection with every logarithmic loss absorbed in an arbitrary source power. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem exists_zetaReflection_power_loss_pattern {τ ε : ℝ}
    (hτ : 1 < τ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N → ∀ σ : ℝ, 1/2 ≤ σ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
          P.ordinates.Nonempty →
            ∃ u ∈ Icc (-(2*P.T)) (2*P.T), ∃ Q : ZetaLargeValuePattern,
              Q.ordinates.Nonempty ∧ Q.ordinates ⊆ P.ordinates.image (fun t => t+u) ∧
              P.T/(4*Real.pi*P.N)/2 ≤ Q.N ∧
              Q.N ≤ 4*(P.T/(4*Real.pi*P.N)) ∧
              P.T/2 ≤ Q.T ∧ Q.T ≤ 2*P.T ∧
              P.V*Real.sqrt P.T/(P.N*P.N^ε) ≤ Q.V ∧
              (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/(P.N*P.N^ε) ≤
                Q.V*(Q.ordinates.card : ℝ) := by
  obtain ⟨r,hr,M₀,hM₀,hentry⟩ := exists_zetaReflection_normalized_pattern hτ
  obtain ⟨δ,hδ,hδr,L₀,hL₀,hloss⟩ := exists_reflection_source_loss_window hτ hε hr
  refine ⟨δ,hδ,max M₀ L₀,hM₀.trans (le_max_left _ _),?_⟩
  intro P hN σ hσ hTL hTU hV hne
  have hNpos := zero_lt_one.trans P.one_lt_N
  have hVpos := P.V_pos
  have hK := zetaReflectionConvolutionConstant_pos
  have hL := zetaMomentLogLoss_pos P.T
  have hA := zetaReflectionValueFloor_pos P
  have hTLr : P.N^(τ-r) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTL
  have hTUr : P.T ≤ P.N^(τ+r) := hTU.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hVr : P.N^(σ-r) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  obtain ⟨_hscale,hsmall⟩ := hloss P ((le_max_right _ _).trans hN) σ hσ hTL hTU hV
  obtain ⟨u,hu,j,_hj,Q,hQne,hQsub,hQNl,hQNu,hQTl,hQTu,hQV,hQmass,_hQdata⟩ :=
    hentry P ((le_max_left _ _).trans hN) σ hσ hTLr hTUr hVr hne
  let J := reflectionBandCount (zetaReflectionCommonInterval P.T P.N) (zetaReflectionValueFloor P)
  let D := 216*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T*(J : ℝ)
  have hJ : (1 : ℝ) ≤ J := by
    exact_mod_cast (show 1 ≤ J from reflectionBandCount_pos _ _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDs : D ≤ P.N^ε := hsmall
  have h24 : 24*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hJ
      (show 0 ≤ 216*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T by positivity)]
  have hnum : 0 ≤ P.V*Real.sqrt P.T := mul_nonneg P.V_pos.le (Real.sqrt_nonneg _)
  have hfloor : P.V*Real.sqrt P.T/(P.N*P.N^ε) ≤ zetaReflectionValueFloor P/3 := by
    calc
      _ ≤ P.V*Real.sqrt P.T/
          (P.N*(24*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T)) :=
        div_le_div_of_nonneg_left hnum (by positivity)
          (mul_le_mul_of_nonneg_left (h24.trans hDs) hNpos.le)
      _ = _ := by unfold zetaReflectionValueFloor; ring
  have hband : zetaReflectionValueFloor P/3 ≤ Q.V := by
    rw [hQV]
    have hp : (1 : ℝ) ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp hA.le]
  refine ⟨u,hu,Q,hQne,hQsub,hQNl,hQNu,hQTl,hQTu,hfloor.trans hband,?_⟩
  calc
    _ ≤ (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/(P.N*D) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hNpos hD)
        (mul_le_mul_of_nonneg_left hDs hNpos.le)
    _ = (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/
        (216*zetaReflectionConvolutionConstant*P.N*zetaMomentLogLoss P.T*(J : ℝ)) := by
      dsimp [D]
      ring
    _ ≤ _ := hQmass

end TaoTrudgianYang2025
