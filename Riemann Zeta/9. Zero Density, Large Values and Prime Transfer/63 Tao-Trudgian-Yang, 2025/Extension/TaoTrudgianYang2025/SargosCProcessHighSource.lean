import TaoTrudgianYang2025.SargosFiniteClosedProcess
import TaoTrudgianYang2025.SargosCProcessBoundBudget
import TaoTrudgianYang2025.SargosCProcessTargetBudget
import TaoTrudgianYang2025.SargosCProcessTrivialBranches

/-! The optimized high-height estimate consumes the actual original source sum and integer length. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sargos_high_height_source_bound {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ),
        N₀ ≤ N → N ≤ T → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N →
        N^(sargosCProcessThreshold k l) ≤ T →
        IsApproximateModelPhaseFunction F σ P δ →
        ‖exponentialSumAt F T N a (a+M)‖^12 ≤
          K*((T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε))^12 := by
  obtain ⟨δ,hδ,P,hP,η,hη,C,hC,hfinite⟩ := sargos_finite_closed_model_process hkl hσ hε
  obtain ⟨N₀,hN₀,hadm⟩ := sargosCProcessScale_high_admissibility hkl.inTriangle hη
  let D := modelPhaseJetCoefficient σ 4
  have hD : 0 < D := modelPhaseJetCoefficient_pos hσ 4
  let B := 2+D^(k+ε)+2/D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCB : 0 ≤ C*B := mul_nonneg (zero_le_one.trans hC) hB
  let K := 2*(3:ℝ)^12+4096+C*B
  have hK : 1 ≤ K := by dsimp [K]; nlinarith only [hCB]
  have hKsmall : 2*(3:ℝ)^12 ≤ K := by dsimp [K]; linarith only [hCB]
  have hKshort : 4096 ≤ K := by dsimp [K]; nlinarith only [hCB]
  have hKmain : C*B ≤ K := by dsimp [K]; norm_num
  refine ⟨δ,hδ,P,hP,N₀,hN₀,K,hK,?_⟩
  intro F T N a M hN hNT ha hb hhigh hF
  have hN1 := hN₀.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hTp : 0 < T := hNp.trans_le hNT
  have hMN : (M:ℝ) ≤ N := by linarith
  let R := sargosCProcessScale k l T N
  let Y := (T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε)
  have hR : 0 < R := sargosCProcessScale_pos hTp hNp
  have hcost : N^12/R ≤ Y^12 := sargosCProcess_cost_le_target hkl.inTriangle.1 hε.le hN1 hNT
  by_cases hR2 : 2 ≤ R
  · by_cases hRM : R ≤ (M:ℝ)
    · obtain ⟨hsmall,hsecondary⟩ := hadm T N hN hhigh
      obtain ⟨H,hH,hHM,hHL,hHR,hscale,hsec⟩ :=
        sargosCProcess_integer_choice hR2 hRM hTp hsmall hsecondary
      have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
      have hHN : (H:ℝ) ≤ N := (by exact_mod_cast hHM : (H:ℝ) ≤ M).trans hMN
      have hf := hfinite H M a F T N hH hHM hN1 ha hb hTp hF hscale
      have hbudget := sargosCProcess_finite_budget hkl.inTriangle.1 hε.le hD
        hN1 hNT hHp hHR hHN hHL hsec
      have hstep := mul_le_mul_of_nonneg_left hbudget (zero_le_one.trans hC)
      have hs : ‖exponentialSumAt F T N a (a+M)‖^12 ≤
          (C*B)*(N^12/R)*(T/N)^ε*N^(2*ε) := by
        dsimp [D] at hstep
        dsimp [B,D,R]
        nlinarith only [hf,hstep]
      have hz : (N^12/R)*(T/N)^ε*N^(2*ε) ≤ Y^12 :=
        sargosCProcess_cost_error_le_target hkl.inTriangle.1 hε.le hN1 hNT
      calc
        _ ≤ (C*B)*((N^12/R)*(T/N)^ε*N^(2*ε)) := by nlinarith only [hs]
        _ ≤ (C*B)*Y^12 := mul_le_mul_of_nonneg_left hz hCB
        _ ≤ K*Y^12 := mul_le_mul_of_nonneg_right hKmain (by positivity)
    · have hshort := sargos_short_source_twelfth_bound F T N a M
        (show 1 ≤ R by linarith) (le_of_not_ge hRM)
        (sargosCProcessScale_high_thirteenth hkl.inTriangle hN1 hhigh)
      calc
        _ ≤ 4096*(N^12/R) := hshort
        _ ≤ 4096*Y^12 := mul_le_mul_of_nonneg_left hcost (by norm_num)
        _ ≤ K*Y^12 := mul_le_mul_of_nonneg_right hKshort (by positivity)
  · have hs := sargos_bounded_optimum_twelfth_bound F T N a M hN1 hb hR (le_of_not_ge hR2)
    calc
      _ ≤ (2*(3:ℝ)^12)*(N^12/R) := hs
      _ ≤ (2*(3:ℝ)^12)*Y^12 := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ ≤ K*Y^12 := mul_le_mul_of_nonneg_right hKsmall (by positivity)

end TaoTrudgianYang2025
