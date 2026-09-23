import TaoTrudgianYang2025.SargosRealSixthMomentTheorem
import TaoTrudgianYang2025.SargosRealQuarticEndpoints

/-! Robert--Sargos's real-scale source maximum, with physical coefficient hypotheses. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargos_source_maximal_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 2 ≤ M → ∀ z : ℤ → ℂ,
      (∀ n : ℤ, M < (n:ℝ) → (n:ℝ) ≤ 2*M → ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        (sargosRealEndpointMaximum M z α γ)^6) ≤
        C*(lambda*M^(3+ε)+M^ε) := by
  obtain ⟨C,hC,h⟩ := sargosRealQuartic_maximal_sixth_moment ε hε
  refine ⟨C,hC,?_⟩
  intro M hM z hz lambda hlambda c d
  have hMp : 0 < M := by linarith only [hM]
  have hcoeff : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1 := by
    intro n hn
    have hp := (mem_sargosRealSourceInterval M n).mp hn
    exact hz n hp.1 hp.2
  simp_rw [sargosRealEndpointMaximum_eq hMp z]
  exact h M hM z hcoeff lambda hlambda c d

end TaoTrudgianYang2025
