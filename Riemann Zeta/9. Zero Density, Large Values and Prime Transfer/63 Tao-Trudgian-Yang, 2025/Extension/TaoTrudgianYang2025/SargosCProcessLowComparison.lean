import TaoTrudgianYang2025.SargosClassicalLowHeight

/-! The actual classical exponent-pair estimate enters the low-height C-process branch. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sargosCProcess_classical_gap {k : ℝ} (hk : 0 ≤ k) :
    (1:ℝ)/30-sargosCProcessK k = (2+3*k)/(60*(1+4*k)) := by
  have hd : 0 < 1+4*k := by linarith
  unfold sargosCProcessK
  field_simp
  ring

theorem sargosCProcess_classical_threshold_identity {k l : ℝ} (hk : 0 ≤ k) :
    ((1:ℝ)/30-sargosCProcessK k)*(sargosCProcessThreshold k l-1)+
      (26/30-sargosCProcessL k l) = 0 := by
  have hd := sargosCProcess_denominators_pos hk
  have hd' : 0 < 1+4*k := by linarith
  unfold sargosCProcessK sargosCProcessL sargosCProcessThreshold
  field_simp
  ring

theorem sargosCProcess_low_height_power_comparison {k l T N ε : ℝ}
    (hkl : InExponentPairTriangle k l) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hlow : T ≤ N^(sargosCProcessThreshold k l)) :
    (T/N)^((1:ℝ)/30+ε)*N^(26/30+ε) ≤
      (T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := hNp.trans_le hNT
  have hr : 0 < T/N := by positivity
  have hgap : 0 ≤ (1:ℝ)/30-sargosCProcessK k := by
    rw [sargosCProcess_classical_gap hkl.1]
    have hd := sargosCProcess_denominators_pos hkl.1
    exact div_nonneg hd.2.le (mul_nonneg (by norm_num) (by linarith [hkl.1]))
  have ht := Real.log_le_log hTp hlow
  rw [Real.log_rpow hNp] at ht
  have hc := mul_le_mul_of_nonneg_left ht hgap
  have hz := congrArg (fun x : ℝ => x*Real.log N)
    (sargosCProcess_classical_threshold_identity (l := l) hkl.1)
  dsimp only at hz
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hr,Real.log_rpow hNp,
    Real.log_rpow hr,Real.log_rpow hNp,Real.log_div hTp.ne' hNp.ne']
  nlinarith only [hc,hz]

theorem sargos_low_height_model_bound {k l σ ε : ℝ}
    (hkl : InExponentPairTriangle k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
        IsExponentPairSetupAt σ δ P C T N F a b →
        T ≤ N^(sargosCProcessThreshold k l) →
        ‖exponentialSumAt F T N a b‖ ≤
          C*(T/N)^(sargosCProcessK k+ε)*N^(sargosCProcessL k l+ε) := by
  obtain ⟨δ,hδ,P,hP,C,hC,hbound⟩ := sargos_classical_aCubedB_nonAsymptotic ε hε σ hσ
  refine ⟨δ,hδ,P,hP,C,hC,?_⟩
  intro T N F a b hsetup hlow
  have hc := sargosCProcess_low_height_power_comparison (ε := ε)
    hkl hsetup.one_le_scale hsetup.scale_le_param hlow
  have hb := hbound T N F a b hsetup
  calc
    _ ≤ C*(T/N)^((1:ℝ)/30+ε)*N^(26/30+ε) := hb
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (zero_le_one.trans hC)

end TaoTrudgianYang2025
