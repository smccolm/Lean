import TaoTrudgianYang2025.SargosSmoothExtendedReduction
import TaoTrudgianYang2025.HeathBrownPhysicalPhase
import TaoTrudgianYang2025.BetaTaylorJets

/-! The actual closed model phase supplies the source remainder's original-jet family. -/

noncomputable section

open Set Expdb Filter
open scoped ContDiff BigOperators Topology

namespace TaoTrudgianYang2025

def sargosModelJetBudget (σ : ℝ) (Q : ℕ) : ℝ :=
  1+∑ p ∈ Finset.range (Q+7), modelPhaseJetCoefficient σ p

theorem sargosModelJetBudget_one_le (σ : ℝ) (Q : ℕ) :
    1 ≤ sargosModelJetBudget σ Q := by
  have h := Finset.sum_nonneg (fun p (_hp : p ∈ Finset.range (Q+7)) =>
    modelPhaseJetCoefficient_nonneg σ p)
  dsimp [sargosModelJetBudget]
  linarith

theorem modelPhaseJetCoefficient_le_sargosBudget {σ δ : ℝ} {Q p : ℕ}
    (hδ : δ ≤ 1) (hp : p ≤ Q+6) :
    modelPhaseJetCoefficient σ p+δ ≤ sargosModelJetBudget σ Q := by
  have h := Finset.single_le_sum
    (fun k (_hk : k ∈ Finset.range (Q+7)) => modelPhaseJetCoefficient_nonneg σ k)
    (show p ∈ Finset.range (Q+7) by simp only [Finset.mem_range]; omega)
  dsimp [sargosModelJetBudget]
  linarith

theorem sargosModelPhysicalPhase_contDiffAt {F : ℝ → ℝ} {N A x : ℝ} {M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    (hx : x ∈ Ioo (1:ℝ) M) (T : ℝ) :
    ContDiffAt ℝ ∞ (heathBrownPhysicalPhase F T N A 1) x := by
  have hx0 : x ∈ Ioo (0:ℝ) M := ⟨by linarith [hx.1],hx.2⟩
  have hc := heathBrownPhysicalPhase_contDiffOn hF hN ha hb T 1
  exact (hc x ⟨hx0.1.le,hx0.2.le⟩).contDiffAt
    (mem_of_superset (isOpen_Ioo.mem_nhds hx0) Ioo_subset_Icc_self)

theorem sargosModelPhysicalPhase_source_jets {σ δ T N A : ℝ}
    {F : ℝ → ℝ} {P Q M : ℕ}
    (hσ : 0 ≤ σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hδ : δ ≤ 1) (hP : Q+6 ≤ P) (hM : 1 ≤ M)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    {j : ℕ} (hj : j ≤ Q+1) {x : ℝ} (hx : x ∈ Ioo (1:ℝ) M) :
    |iteratedDeriv (j+6) (heathBrownPhysicalPhase F T N A 1) x| ≤
      (sargosModelJetBudget σ Q*|T|/N^6)/(M:ℝ)^j := by
  have hx0 : x ∈ Ioo (0:ℝ) M := ⟨by linarith [hx.1],hx.2⟩
  have hu := heathBrownPhysicalPoint_mem_interior hN ha hb hx0
  have hp : j+5 ≤ P := by omega
  have hjet : |iteratedDeriv (j+6) F ((A+x)/N)| ≤ sargosModelJetBudget σ Q := by
    have h := (approximateModelPhase_iteratedDeriv_abs_le hσ hF hu (j+5) hp).trans
      (modelPhaseJetCoefficient_le_sargosBudget hδ (by omega : j+5 ≤ Q+6))
    simpa only [show j+5+1=j+6 by omega] using h
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMN : (M:ℝ) ≤ N := by linarith
  have hD : 0 ≤ sargosModelJetBudget σ Q := zero_le_one.trans (sargosModelJetBudget_one_le σ Q)
  have hden : N^6*(M:ℝ)^j ≤ N^(j+6) := by
    rw [pow_add]
    calc
      _ = (M:ℝ)^j*N^6 := mul_comm _ _
      _ ≤ N^j*N^6 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0.le hMN j)
        (pow_nonneg hN.le 6)
  rw [heathBrownPhysicalPhase_iteratedDeriv hF.1 hN ha hb hx0,
    one_mul,abs_mul,abs_div,abs_of_pos (pow_pos hN (j+6))]
  calc
    _ ≤ (|T|/N^(j+6))*sargosModelJetBudget σ Q :=
      mul_le_mul_of_nonneg_left hjet (by positivity)
    _ = (sargosModelJetBudget σ Q*|T|)/N^(j+6) := by ring
    _ ≤ (sargosModelJetBudget σ Q*|T|)/(N^6*(M:ℝ)^j) :=
      div_le_div_of_nonneg_left (mul_nonneg hD (abs_nonneg T)) (by positivity) hden
    _ = _ := by ring

end TaoTrudgianYang2025
