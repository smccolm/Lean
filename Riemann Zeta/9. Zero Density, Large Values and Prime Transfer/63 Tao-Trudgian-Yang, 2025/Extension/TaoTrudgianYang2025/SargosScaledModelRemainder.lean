import TaoTrudgianYang2025.SargosScaledPhysicalRemainder
import TaoTrudgianYang2025.SargosModelRemainderJets

/-! Actual source-model jets control the constructed extension at the original real scale. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosModelPhysicalPhase_scale_jets {σ δ T N A : ℝ}
    {F : ℝ → ℝ} {P Q M : ℕ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hδ : δ ≤ 1) (hP : Q+6 ≤ P)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    {j : ℕ} (hj : j ≤ Q+1) {x : ℝ} (hx : x ∈ Ioo (1:ℝ) M) :
    |iteratedDeriv (j+6) (heathBrownPhysicalPhase F T N A 1) x| ≤
      (sargosModelJetBudget σ Q*|T|/N^6)/N^j := by
  have hx0 : x ∈ Ioo (0:ℝ) M := ⟨by linarith [hx.1],hx.2⟩
  have hu := heathBrownPhysicalPoint_mem_interior hN ha hb hx0
  have hjet : |iteratedDeriv (j+6) F ((A+x)/N)| ≤ sargosModelJetBudget σ Q := by
    have h := (approximateModelPhase_iteratedDeriv_abs_le hσ hF hu (j+5) (by omega)).trans
      (modelPhaseJetCoefficient_le_sargosBudget hδ (by omega : j+5 ≤ Q+6))
    simpa only [show j+5+1=j+6 by omega] using h
  rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hN ha hb hx0,
    one_mul,abs_mul,abs_div,abs_of_pos (pow_pos hN (j+6))]
  calc
    _ ≤ (|T|/N^(j+6))*sargosModelJetBudget σ Q :=
      mul_le_mul_of_nonneg_left hjet (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem sargosScaledModelRemainder_uniform (σ : ℝ) (hσ : 0 ≤ σ) (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M P : ℕ) (F : ℝ → ℝ) (δ T N A : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → Q+6 ≤ P → δ ≤ 1 → 0 < N → N ≤ A → A+(M:ℝ) ≤ 2*N →
      IsApproximateModelPhaseFunction F σ P δ →
      ContDiff ℝ ∞ (sargosScaledPhysicalRemainder
        (heathBrownPhysicalPhase F T N A 1) M N Q q) ∧
      (∀ m ∈ sargosSextupleInterior M q,
        sargosScaledPhysicalRemainder (heathBrownPhysicalPhase F T N A 1) M N Q q m =
          sargosSextupleRemainder (heathBrownPhysicalPhase F T N A 1) q m) ∧
      ∀ x ∈ Icc (-N) N, ∀ j ≤ Q,
        |iteratedDeriv j (sargosScaledPhysicalRemainder
          (heathBrownPhysicalPhase F T N A 1) M N Q q) x| ≤
            C * |T| * (H:ℝ)^6/(60*N^6*N^j) := by
  obtain ⟨C,hC,hjets⟩ := sargosScaledPhysicalRemainder_uniform_jets Q
  let D := sargosModelJetBudget σ Q
  have hD : 1 ≤ D := sargosModelJetBudget_one_le σ Q
  have hCD : 1 ≤ C*D := by nlinarith
  refine ⟨C*D,hCD,?_⟩
  intro H M P F δ T N A q hM hP hδ hN ha hb hF
  have hMN : (M:ℝ) ≤ N := by linarith
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hf : ∀ y ∈ Ioo (1:ℝ) M,
      ContDiffAt ℝ ∞ (heathBrownPhysicalPhase F T N A 1) y :=
    fun y hy => sargosModelPhysicalPhase_contDiffAt hF.1 hN ha hb hy T
  have hj := hjets H M N (heathBrownPhysicalPhase F T N A 1) (D*|T|/N^6)
    q hM hMN (by positivity) hf
    (fun j hj y hy => sargosModelPhysicalPhase_scale_jets hσ hF hδ hP hN ha hb hj hy)
  refine ⟨sargosScaledPhysicalRemainder_contDiff hN Q q hf,
    fun m hm => sargosScaledPhysicalRemainder_agrees _ hN Q q hm,?_⟩
  intro x hx j hjQ
  convert hj x hx j hjQ using 1
  ring

end TaoTrudgianYang2025
