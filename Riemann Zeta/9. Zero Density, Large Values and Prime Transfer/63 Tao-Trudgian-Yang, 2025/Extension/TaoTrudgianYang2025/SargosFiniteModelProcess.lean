import TaoTrudgianYang2025.SargosFiniteProcessAlgebra

/-! A finite C-process inequality for the actual one-based source model sum. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_finite_model_process {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M a : ℕ) (F : ℝ → ℝ) (T N : ℝ),
        1 ≤ H → H ≤ M → 1 ≤ N → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N → 0 < T →
        IsApproximateModelPhaseFunction F σ P δ → (H:ℝ)^3/N^2 ≤ η →
        ‖∑ m ∈ Finset.Ioc (0:ℤ) M,
          fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m)‖^12 ≤
          C*(N^12/(H:ℝ)+
            N^11*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)+
            N^16/(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4))*(H:ℝ)^ε := by
  obtain ⟨δ,hδ,P,hP,η,hη,K,hK,hcorr⟩ := sargos_model_interior_correlation_bound hkl hσ hε
  obtain ⟨D,hD,hdiff⟩ := sargos_character_interior_differencing ε hε
  refine ⟨δ,hδ,P,hP,η,hη,1492992+382205952*K+D,by linarith,?_⟩
  intro H M a F T N hH hHM hN ha hb hT hF hsmall
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0:ℝ) < H := zero_lt_one.trans_le hHr
  have hMN : (M:ℝ) ≤ N := by linarith
  have hHMreal : (H:ℝ) ≤ M := by exact_mod_cast hHM
  have hHN := hHMreal.trans hMN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hD4 := modelPhaseJetCoefficient_pos hσ 4
  let A := (modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)
  let B := N^5/(modelPhaseJetCoefficient σ 4*T)
  let E := (H:ℝ)^ε
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 1 ≤ E := Real.one_le_rpow hHr hε.le
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have h3 : (H:ℝ)^(3+ε) = (H:ℝ)^3*E := by
    rw [Real.rpow_add hHp]
    norm_num [E]
  have h4 : (H:ℝ)^(4+ε) = (H:ℝ)^4*E := by
    rw [Real.rpow_add hHp]
    norm_num [E]
  have hc := hcorr H M a F T N hH hHM hN ha hb hT hF hsmall
  have hcN : sargosInteriorSextupleCorrelation (heathBrownPhysicalPhase F T N a 1) M H ≤
      K*(N*(H:ℝ)^3*E+(H:ℝ)^4*E*A+B*E) := by
    rw [h3,h4] at hc
    calc
      _ ≤ K*((M:ℝ)*(H:ℝ)^3*E+(H:ℝ)^4*E*A+B*E) := by
        convert hc using 1
        dsimp [A,B,E]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        gcongr
  have hh := hdiff H hH M hHM (heathBrownPhysicalPhase F T N a 1)
  have hdiag :
      ((M:ℝ)/(H:ℝ))^6*(M:ℝ)^6 ≤ (N/(H:ℝ))^6*N^6 := by gcongr
  have hfac : 382205952*(M:ℝ)^11/(H:ℝ)^4 ≤ 382205952*N^11/(H:ℝ)^4 := by gcongr
  have hc0 := sargosInteriorSextupleCorrelation_nonneg (heathBrownPhysicalPhase F T N a 1) M H
  have hmid := mul_le_mul hfac hcN hc0 (by positivity : 0 ≤ 382205952*N^11/(H:ℝ)^4)
  have herr : D*(M:ℝ)^11*E ≤ D*N^11*E := by gcongr
  calc
    _ ≤ 1492992*((M:ℝ)/(H:ℝ))^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*
          sargosInteriorSextupleCorrelation (heathBrownPhysicalPhase F T N a 1) M H+
        D*(M:ℝ)^11*E := hh
    _ ≤ 1492992*(N/(H:ℝ))^6*N^6+
        (382205952*N^11/(H:ℝ)^4)*(K*(N*(H:ℝ)^3*E+(H:ℝ)^4*E*A+B*E))+
        D*N^11*E := by
      have hd := mul_le_mul_of_nonneg_left hdiag (show (0:ℝ) ≤ 1492992 by norm_num)
      nlinarith only [hd,hmid,herr]
    _ ≤ (1492992+382205952*K+D)*(N^12/(H:ℝ)+N^11*A+N^11*B/(H:ℝ)^4)*E :=
      sargos_finite_process_algebra hHr hHN hE hA hB hD
    _ = _ := by
      dsimp [A,B,E]
      congr 2
      field_simp

end TaoTrudgianYang2025
