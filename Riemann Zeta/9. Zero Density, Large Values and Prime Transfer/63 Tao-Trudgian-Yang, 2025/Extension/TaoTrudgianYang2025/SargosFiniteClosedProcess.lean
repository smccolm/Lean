import TaoTrudgianYang2025.SargosFiniteModelProcess

/-! The finite C-process estimate enters the exact original closed natural source sum. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_closed_source_twelfth_le (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    ‖exponentialSumAt F T N a (a+M)‖^12 ≤
      2048*(1+‖∑ m ∈ Finset.Ioc (0:ℤ) M,
        fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m)‖^12) := by
  have he := sargos_exponentialSumAt_le_source F T N a M
  have hp := pow_le_pow_left₀ (norm_nonneg _) he 12
  have ha := add_pow_le (show (0:ℝ) ≤ 1 by norm_num)
    (norm_nonneg (∑ m ∈ Finset.Ioc (0:ℤ) M,
      fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m))) 12
  norm_num at ha
  exact hp.trans ha

theorem sargos_finite_closed_model_process {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M a : ℕ) (F : ℝ → ℝ) (T N : ℝ),
        1 ≤ H → H ≤ M → 1 ≤ N → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N → 0 < T →
        IsApproximateModelPhaseFunction F σ P δ → (H:ℝ)^3/N^2 ≤ η →
        ‖exponentialSumAt F T N a (a+M)‖^12 ≤
          C*(N^12/(H:ℝ)+
            N^11*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)+
            N^16/(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4))*(H:ℝ)^ε := by
  obtain ⟨δ,hδ,P,hP,η,hη,C,hC,hprocess⟩ := sargos_finite_model_process hkl hσ hε
  refine ⟨δ,hδ,P,hP,η,hη,4096*C,by linarith,?_⟩
  intro H M a F T N hH hHM hN ha hb hT hF hsmall
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0:ℝ) < H := zero_lt_one.trans_le hHr
  have hMN : (M:ℝ) ≤ N := by linarith
  have hHMreal : (H:ℝ) ≤ M := by exact_mod_cast hHM
  have hHN := hHMreal.trans hMN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hD4 := modelPhaseJetCoefficient_pos hσ 4
  let R := N^12/(H:ℝ)+
    N^11*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)+
    N^16/(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4)
  have hbase : 1 ≤ N^12/(H:ℝ) := by
    apply (le_div_iff₀ hHp).mpr
    simpa only [one_mul] using hHN.trans (le_self_pow₀ hN (show 12 ≠ 0 by norm_num))
  have hR : 1 ≤ R := by
    have hm : 0 ≤ N^11*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε) :=
      by positivity
    have hs : 0 ≤ N^16/(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4) := by positivity
    dsimp [R]
    linarith only [hbase,hm,hs]
  have hpow : 1 ≤ (H:ℝ)^ε := Real.one_le_rpow hHr hε.le
  have hbudget : 1 ≤ C*R*(H:ℝ)^ε :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hR) hpow
  have hs := hprocess H M a F T N hH hHM hN ha hb hT hF hsmall
  have hc := sargos_closed_source_twelfth_le F T N a M
  change ‖exponentialSumAt F T N a (a+M)‖^12 ≤ (4096*C)*R*(H:ℝ)^ε
  change ‖∑ m ∈ Finset.Ioc (0:ℤ) M,
    fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m)‖^12 ≤ C*R*(H:ℝ)^ε at hs
  nlinarith only [hs,hc,hbudget]

end TaoTrudgianYang2025
