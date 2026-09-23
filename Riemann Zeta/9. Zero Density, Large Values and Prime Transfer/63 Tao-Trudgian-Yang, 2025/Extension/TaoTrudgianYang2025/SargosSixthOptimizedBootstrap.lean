import TaoTrudgianYang2025.SargosSixthLogAbsorption

/-! Optimizing the actual finite-scale bootstrap at a uniformly admissible parameter. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosSixthBaseMoment_optimized_bootstrap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β B : ℝ), 0 ≤ β → 0 ≤ B →
      (∀ M : ℕ, 1 ≤ M → sargosSixthBaseMoment M ≤ B*(M:ℝ)^β) →
      ∀ N : ℕ, 16 ≤ N →
        sargosSixthBaseMoment N ≤
          C*(4+B)*(1+Real.log N)^6*(N:ℝ)^(sargosSixthExponentStep β) := by
  obtain ⟨C,hC,h⟩ := sargosSixthBaseMoment_power_bootstrap
  refine ⟨C,hC,?_⟩
  intro β B hβ hB hbound N hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  let A := sargosSixthBootstrapParameter N β
  have hA := sargosSixthBootstrapParameter_bounds hNr hβ
  have hp := h β B hβ hB hbound N A hN hA.1 hA.2
  have hinv := sargosSixthBootstrapParameter_inverse (β := β) hNp
  have hpower := sargosSixthBootstrapParameter_power hNp hβ
  have hlog := Real.log_nonneg hNr
  have hL : 1 ≤ 1+Real.log (N:ℝ) := by linarith only [hlog]
  have h₅ : (1+Real.log (N:ℝ))^5 ≤ (1+Real.log (N:ℝ))^6 :=
    pow_le_pow_right₀ hL (by norm_num)
  have h₆ : (Real.log (N:ℝ))^6 ≤ (1+Real.log (N:ℝ))^6 :=
    pow_le_pow_left₀ hlog (by linarith) 6
  have hq : 0 ≤ (N:ℝ)^(sargosSixthExponentStep β) := by positivity
  have he : (1+Real.log (N:ℝ))^5/A =
      4*(1+Real.log N)^5*(N:ℝ)^(sargosSixthExponentStep β) := by
    change _/sargosSixthBootstrapParameter N β = _
    calc
      _ = (1+Real.log (N:ℝ))^5*(1/sargosSixthBootstrapParameter N β) := by ring
      _ = _ := by rw [hinv]; ring
  change (4*A*N)^β = (N:ℝ)^(sargosSixthExponentStep β) at hpower
  rw [he,hpower] at hp
  calc
    _ ≤ C*(4*(1+Real.log N)^5*(N:ℝ)^(sargosSixthExponentStep β)+
        B*(Real.log N)^6*(N:ℝ)^(sargosSixthExponentStep β)) := hp
    _ ≤ C*(4*(1+Real.log N)^6*(N:ℝ)^(sargosSixthExponentStep β)+
        B*(1+Real.log N)^6*(N:ℝ)^(sargosSixthExponentStep β)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith only [hC] : 0 ≤ C)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₅ (by norm_num : (0:ℝ) ≤ 4)) hq)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₆ hB) hq)
    _ = _ := by ring

end TaoTrudgianYang2025
