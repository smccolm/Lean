import TaoTrudgianYang2025.ZetaReflectionNormalizedFamily

/-! Uniform extraction of a genuine normalized reflected zeta pattern from actual source data. -/

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem exists_reflection_dual_scale_window {τ : ℝ} (hτ : 1 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → 1 < N → ∀ T : ℝ,
        N^(τ-δ) ≤ T → 4 ≤ T/(4*Real.pi*N) := by
  let δ := (τ-1)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlarge := (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (16*Real.pi))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlarge
  refine ⟨δ,hδ,max 1 N₀,le_max_left _ _,?_⟩
  intro N hN hN1 T hT
  have hNp : 0 < N := zero_lt_one.trans hN1
  have hpow := hN₀ N ((le_max_right _ _).trans hN)
  have he : N^δ*N = N^(τ-δ) := by
    calc
      N^δ*N = N^(δ+1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hNp δ 1).symm
      _ = N^(τ-δ) := by congr 1; dsimp [δ]; ring
  have h := mul_le_mul_of_nonneg_right hpow hNp.le
  rw [he] at h
  apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi*N)).2
  nlinarith [h.trans hT]

theorem exists_zetaReflection_normalized_pattern {τ : ℝ} (hτ : 1 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
        ∀ σ : ℝ, 1/2 ≤ σ →
          P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
            P.ordinates.Nonempty →
              ∃ u ∈ Icc (-(2*P.T)) (2*P.T),
                ∃ j ∈ Finset.range (reflectionBandCount
                    (zetaReflectionCommonInterval P.T P.N) (zetaReflectionValueFloor P)),
                  ∃ Q : ZetaLargeValuePattern,
                    Q.ordinates.Nonempty ∧ Q.ordinates ⊆ P.ordinates.image (fun t => t+u) ∧
                    P.T/(4*Real.pi*P.N)/2 ≤ Q.N ∧
                    Q.N ≤ 4*(P.T/(4*Real.pi*P.N)) ∧
                    P.T/2 ≤ Q.T ∧ Q.T ≤ 2*P.T ∧
                    Q.V = zetaReflectionValueFloor P*(2 : ℝ)^j/3 ∧
                    (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/
                        (216*zetaReflectionConvolutionConstant*P.N*zetaMomentLogLoss P.T*
                          (reflectionBandCount (zetaReflectionCommonInterval P.T P.N)
                            (zetaReflectionValueFloor P) : ℝ)) ≤
                      Q.V*(Q.ordinates.card : ℝ) ∧
                    ∃ i k : Fin 3,
                      Q.N = ((2^i.val*Nat.floor (P.T/(4*Real.pi*P.N)) : ℕ) : ℝ) ∧
                      Q.T = reflectionHeightScale P.T k ∧
                      Q.active = reflectionDyadicBlock
                        (Nat.floor (P.T/(4*Real.pi*P.N)))
                        (Nat.ceil (4*(P.T/(4*Real.pi*P.N)))) i := by
  obtain ⟨δ₁,hδ₁,N₁,hN₁,hfamily⟩ := exists_zetaReflection_value_family hτ
  obtain ⟨δ₂,hδ₂,N₂,hN₂,hscale⟩ := exists_reflection_dual_scale_window hτ
  let δ := min δ₁ δ₂
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ,lt_min hδ₁ hδ₂,max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro P hN σ hσ hTL hTU hV hne
  have hTL1 : P.N^(τ-δ₁) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTL
  have hTU1 : P.T ≤ P.N^(τ+δ₁) := hTU.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hV1 : P.N^(σ-δ₁) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hV
  have hTL2 : P.N^(τ-δ₂) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTL
  have hM := hscale P.N ((le_max_right _ _).trans hN) P.one_lt_N P.T hTL2
  obtain ⟨u,hu,j,hj,U,hUne,hUsub,hUsep,hUheight,hUvalues,hUmass⟩ :=
    hfamily P ((le_max_left _ _).trans hN) σ hσ hTL1 hTU1 hV1 hne
  have hA : 0 < zetaReflectionValueFloor P*(2 : ℝ)^j :=
    mul_pos (zetaReflectionValueFloor_pos P) (pow_pos (by norm_num) _)
  have hlarge : ∀ t ∈ U, zetaReflectionValueFloor P*(2 : ℝ)^j ≤
      ‖∑ n ∈ Finset.Icc (Nat.floor (P.T/(4*Real.pi*P.N))+1)
        (Nat.ceil (4*(P.T/(4*Real.pi*P.N)))), dirichletPhase n t‖ := by
    intro t ht
    simpa only [zetaReflectionCommonInterval_eq_scaled] using (hUvalues t ht).1
  obtain ⟨Q,hQne,hQsub,hQNl,hQNu,hQTl,hQTu,hQV,_hQcard,hQmass,hQdata⟩ :=
    exists_reflection_normalized_family hM P.T_pos hA U hUne hUsep hUheight hlarge
  refine ⟨u,hu,j,hj,Q,hQne,hQsub.trans hUsub,hQNl,hQNu,hQTl,hQTu,hQV,?_,hQdata⟩
  have h := (div_le_div_of_nonneg_right hUmass (by norm_num : (0 : ℝ) ≤ 27)).trans hQmass
  convert h using 1
  ring

end TaoTrudgianYang2025
