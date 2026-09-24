import TaoTrudgianYang2025.ZetaReflectionErrorThreshold

/-! Uniform actual-pattern common convolution after all error absorption. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

def zetaReflectionConvolutionConstant : ℝ :=
  1+32*Real.pi*zetaCutoffDerivativeMass 1

theorem zetaReflectionConvolutionConstant_pos : 0 < zetaReflectionConvolutionConstant := by
  unfold zetaReflectionConvolutionConstant
  have := zetaCutoffDerivativeMass_nonneg 1
  positivity

theorem exists_zetaReflectionConvolution_uniform_entry {τ : ℝ} (hτ : 1 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
      ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
        ∀ σ : ℝ, 1/2 ≤ σ →
          P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
            ∀ t ∈ P.ordinates,
              P.V*Real.sqrt P.T/P.N ≤ zetaReflectionConvolutionConstant*
                zetaReflectionConvolution (zetaReflectionCommonInterval P.T P.N) P.T t := by
  obtain ⟨ε,hε,hthreshold⟩ := exists_reflection_remainders_absorbed hτ
  obtain ⟨C,hC,hraw⟩ := zetaPattern_uniform_localized_reflection hε
  obtain ⟨j,δ,hδ,N₀,hN₀,habsorb⟩ := hthreshold C (zero_le_one.trans hC)
  refine ⟨δ,hδ,N₀,hN₀,?_⟩
  intro P hN σ hσ hTL hTU hV t ht
  obtain ⟨hTmin,hscale,herrors⟩ := habsorb P hN σ hσ hTL hTU hV
  have hsource := hraw P hTmin hscale t ht j
  have herr := herrors t ht
  let B := zetaReflectionConvolution (zetaReflectionCommonInterval P.T P.N) P.T t
  have hB : 0 ≤ B := zetaReflectionConvolution_nonneg _ _ _
  have hD : 0 ≤ zetaCutoffDerivativeMass 1 := zetaCutoffDerivativeMass_nonneg 1
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htime : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hcentral : P.V/2 ≤ Real.sqrt (t/(2*Real.pi))*
      ((4*zetaCutoffDerivativeMass 1/(P.T/(4*Real.pi*P.N)))*B) := by
    dsimp [B]
    nlinarith
  have hcentral' : P.V/2 ≤ Real.sqrt P.T*
      ((4*zetaCutoffDerivativeMass 1/(P.T/(4*Real.pi*P.N)))*B) := hcentral.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (reflection_scaled_height_bounds P.T_pos htime).2.1) (by positivity))
  have hsqrt : (Real.sqrt P.T)^2 = P.T := Real.sq_sqrt P.T_pos.le
  calc
    _ = (2*Real.sqrt P.T/P.N)*(P.V/2) := by ring
    _ ≤ (2*Real.sqrt P.T/P.N)*(Real.sqrt P.T*
        ((4*zetaCutoffDerivativeMass 1/(P.T/(4*Real.pi*P.N)))*B)) :=
      mul_le_mul_of_nonneg_left hcentral' (by positivity)
    _ = (32*Real.pi*zetaCutoffDerivativeMass 1*B)*(Real.sqrt P.T)^2/P.T := by
      field_simp
      ring
    _ = 32*Real.pi*zetaCutoffDerivativeMass 1*B := by
      rw [hsqrt]
      field_simp [P.T_pos.ne']
    _ ≤ _ := by
      change 32*Real.pi*zetaCutoffDerivativeMass 1*B ≤ zetaReflectionConvolutionConstant*B
      unfold zetaReflectionConvolutionConstant
      nlinarith

end TaoTrudgianYang2025
