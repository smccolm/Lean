import TaoTrudgianYang2025.ZetaReflectionHeightLoss

/-! One physical radius makes the actual reflection loss subpower in the source scale. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem exists_reflection_source_loss_window {τ ε r : ℝ}
    (hτ : 1 < τ) (hε : 0 < ε) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N → ∀ σ : ℝ, 1/2 ≤ σ →
        P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
          4 ≤ P.T/(4*Real.pi*P.N) ∧
          216*zetaReflectionConvolutionConstant*zetaMomentLogLoss P.T*
            (reflectionBandCount (zetaReflectionCommonInterval P.T P.N)
              (zetaReflectionValueFloor P) : ℝ) ≤ P.N^ε := by
  obtain ⟨d,hd,M₀,hM₀,hscale⟩ := exists_reflection_dual_scale_window hτ
  let η := ε/(τ+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T₀,hT₀,hloss⟩ := exists_zetaReflection_height_loss_subpower hη
  let δ := min r (min d (min (1/4) ((τ-1)/2)))
  have hδ : 0 < δ := lt_min hr (lt_min hd (lt_min (by norm_num) (by linarith)))
  have hδr : δ ≤ r := min_le_left _ _
  have hδd : δ ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hδquarter : δ ≤ 1/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδgap : δ ≤ (τ-1)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,hδ,hδr,max M₀ T₀,hM₀.trans (le_max_left _ _),?_⟩
  intro P hN σ hσ hTL hTU hV
  have hNpos := zero_lt_one.trans P.one_lt_N
  have hTd : P.N^(τ-d) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTL
  have hM := hscale P.N ((le_max_left _ _).trans hN) P.one_lt_N P.T hTd
  have hNT : P.N ≤ P.T := by
    calc
      _ = P.N^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P.N^(τ-δ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
      _ ≤ _ := hTL
  have hTlarge : T₀ ≤ P.T := ((le_max_right _ _).trans hN).trans hNT
  have hV1 : 1 ≤ P.V :=
    (Real.one_le_rpow P.one_lt_N.le (show 0 ≤ σ-δ by linarith)).trans hV
  have hL := hloss P hTlarge hV1 (by linarith : 1 ≤ P.T/(4*Real.pi*P.N))
  have hTU' : P.T ≤ P.N^(τ+1) := hTU.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  refine ⟨hM,hL.trans ?_⟩
  calc
    _ ≤ (P.N^(τ+1))^η := Real.rpow_le_rpow P.T_pos.le hTU' hη.le
    _ = P.N^ε := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      dsimp [η]
      field_simp

end TaoTrudgianYang2025
