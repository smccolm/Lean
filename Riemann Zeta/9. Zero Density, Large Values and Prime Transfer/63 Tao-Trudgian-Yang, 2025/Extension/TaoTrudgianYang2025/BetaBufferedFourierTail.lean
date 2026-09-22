import TaoTrudgianYang2025.BetaBufferedFourierDecay
import TaoTrudgianYang2025.IntegerFourierTails
import TaoTrudgianYang2025.BetaBufferedBoundary

/-!
# Quantitative far tails and finite Poisson entry from the actual source

The inverse-square mode estimate is summed over both integer signs.
The finite source consumer pays both original endpoint smoothing and
the actual omitted Fourier tail.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def modelPhaseBufferedFarTail (l r η : ℝ) (F : ℝ → ℝ) (T N : ℝ) (R : ℕ) : ℂ :=
  ∑' q : ℤ, if R < q.natAbs then
    modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q else 0

theorem modelPhaseBufferedFarTail_uniform
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (F : ℝ → ℝ) (δ T N : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < N →
        ∀ R : ℕ, 0 < R →
          ‖modelPhaseBufferedFarTail l r η F T N R‖ ≤
            C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_inverse_square_bound hσ
  refine ⟨2*C,by linarith,?_⟩
  intro l r η hl hr hη hη₁ F δ T N hδ hF hN R hR
  have hs := summable_norm_modelPhaseFourierMode
    (modelPhaseBufferedCutoff_contDiff l r η)
    (modelPhaseBufferedCutoff_tsupport_model hη hl hr) hF hN T
  have hb : ∀ q : ℤ, q ≠ 0 →
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
        (C*(η⁻¹)^2*(1+|T|)^2/N)/(q : ℝ)^2 := by
    intro q hq
    convert hmode l r η hl hr hη hη₁ F δ T N q hδ hF hN
      (by exact_mod_cast hq) using 1
    ring
  have h := norm_integer_far_tail_le_of_inverse_square
    (by positivity : 0 ≤ C*(η⁻¹)^2*(1+|T|)^2/N) hs hb hR
  convert h using 1
  ring

theorem modelPhase_buffered_poisson_truncated
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ →
        ∀ R : ℕ, 0 < R →
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) := by
  obtain ⟨C,hC,htail⟩ := modelPhaseBufferedFarTail_uniform hσ
  refine ⟨C,hC,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T hδ hF R hR
  let χ := modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η
  have hsource := modelPhase_buffered_poisson hF hN hη ha hb T
  have hsplit := tsum_int_eq_sum_Icc_add_far hsource.1.of_norm R
  have hfar := htail ((a : ℝ)/N) ((b : ℝ)/N) η
    ((one_le_div hN).mpr ha) ((div_le_iff₀ hN).mpr hb) hη hη₁ F δ T N hδ hF hN R hR
  have hdiff : ‖(∑' q : ℤ, modelPhaseFourierMode χ F T N q)-
      ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), modelPhaseFourierMode χ F T N q‖ ≤
        C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) := by
    rw [hsplit]
    simpa only [χ,add_sub_cancel_left,modelPhaseBufferedFarTail] using hfar
  calc
    _ = ‖(exponentialSumAt F T N a b-(∑' q : ℤ, modelPhaseFourierMode χ F T N q))+
        ((∑' q : ℤ, modelPhaseFourierMode χ F T N q)-
          ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), modelPhaseFourierMode χ F T N q)‖ := by
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsource.2 hdiff)

theorem modelPhase_buffered_poisson_truncated_precision
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N η : ℝ) (a b : ℕ),
      0 < N → 0 < η → η ≤ 1 → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ∀ (F : ℝ → ℝ) (δ T ε : ℝ), δ ≤ 1 →
        IsApproximateModelPhaseFunction F σ 1 δ → 0 < ε →
        let R : ℕ := ⌈C*(η⁻¹)^2*(1+|T|)^2/(N*ε)⌉₊+1
        0 < R ∧
          ‖exponentialSumAt F T N a b-
            ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              modelPhaseFourierMode
                (modelPhaseBufferedCutoff ((a : ℝ)/N) ((b : ℝ)/N) η) F T N q‖ ≤
            4*N*η+2+ε := by
  obtain ⟨C,hC,htrunc⟩ := modelPhase_buffered_poisson_truncated hσ
  refine ⟨C,hC,?_⟩
  intro N η a b hN hη hη₁ ha hb F δ T ε hδ hF hε R
  have hR : 0 < R := Nat.succ_pos _
  refine ⟨hR,?_⟩
  have hR₀ : 0 < (R : ℝ) := by exact_mod_cast hR
  have hceil : C*(η⁻¹)^2*(1+|T|)^2/(N*ε) ≤ (R : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      dsimp [R]
      rw [Nat.cast_add,Nat.cast_one]
      linarith)
  have hbudget : C*(η⁻¹)^2*(1+|T|)^2/(N*(R : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hN hR₀)).mpr
    have h := (div_le_iff₀ (mul_pos hN hε)).mp hceil
    nlinarith
  exact (htrunc N η a b hN hη hη₁ ha hb F δ T hδ hF R hR).trans
    (add_le_add le_rfl hbudget)

end TaoTrudgianYang2025
