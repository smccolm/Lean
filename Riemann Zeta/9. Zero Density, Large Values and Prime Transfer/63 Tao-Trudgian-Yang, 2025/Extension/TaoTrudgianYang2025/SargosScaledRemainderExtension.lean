import TaoTrudgianYang2025.SargosScaledRemainderGeometry
import TaoTrudgianYang2025.BetaTaylorPastedUniform

/-! Actual real-scale Taylor extension with jets on the fixed two-sided observation window. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosScaledExtendedRemainder {H : ℕ} (f : ℝ → ℝ) (M : ℕ) (N : ℝ) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ → ℝ :=
  if (sargosSextupleInterior M q).Nonempty then
    taylorPastedExtension (sargosScaledRemainder f N q) Q
      (sargosScaledRemainderLeft N q) (sargosScaledRemainderRight M N q)
      (sargosScaledRemainderWidth N)
  else fun _ => 0

theorem sargosScaledExtendedRemainder_contDiff {H M : ℕ} {N : ℝ} {f : ℝ → ℝ}
    (hN : 0 < N) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (sargosScaledExtendedRemainder f M N Q q) := by
  unfold sargosScaledExtendedRemainder
  split_ifs
  · exact taylorPastedExtension_contDiff
      (show 0 < sargosScaledRemainderWidth N from one_div_pos.mpr (by positivity))
      (fun x hx => sargosScaledRemainder_contDiffAt hN q hf hx) Q
  · exact contDiff_const

theorem sargosScaledExtendedRemainder_agrees {H M : ℕ} {N : ℝ} (f : ℝ → ℝ)
    (hN : 0 < N) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosScaledExtendedRemainder f M N Q q ((m:ℝ)/N) = sargosSextupleRemainder f q m := by
  rw [sargosScaledExtendedRemainder,if_pos ⟨m,hm⟩,
    taylorPastedExtension_agrees _ _
      (show 0 < sargosScaledRemainderWidth N from one_div_pos.mpr (by positivity))
      (sargosSextupleInterior_in_scaled_plateau hN q hm)]
  simp only [sargosScaledRemainder,mul_div_cancel₀ _ hN.ne']

theorem sargosScaledExtendedRemainder_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (N : ℝ) (f : ℝ → ℝ) (B : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → (M:ℝ) ≤ N → 0 ≤ B →
      (∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) →
      (∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M, |iteratedDeriv (j+6) f y| ≤ B/N^j) →
      ∀ x ∈ Icc (-1:ℝ) 1, ∀ j ≤ Q,
        |iteratedDeriv j (sargosScaledExtendedRemainder f M N Q q) x| ≤ C*(B*(H:ℝ)^6/60) := by
  obtain ⟨C,hC,hjets⟩ := taylorPastedExtension_uniform_jets Q (D := 2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro H M N f B q hM hMN hB hf hb x hx j hj
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : 1 ≤ N := hM1.trans hMN
  have hN : 0 < N := zero_lt_one.trans_le hN1
  by_cases hne : (sargosSextupleInterior M q).Nonempty
  · rw [sargosScaledExtendedRemainder,if_pos hne]
    have hh := sargosScaledRemainderWidth_bounds hN1
    have hg := (sargosScaledRemainder_interval_geometry hN hMN q hne).2.2
    have hd := sargosScaledRemainder_observation_distances hN hMN q hne hx
    exact hjets _ _ _ _ _ _ hh.1 hh.2 hg
      (fun y hy => sargosScaledRemainder_contDiffAt hN q hf hy)
      (fun y hy k hk => abs_iteratedDeriv_sargosScaledRemainder_le hN q hf hb hy hk)
      hd.1 hd.2 j hj
  · rw [sargosScaledExtendedRemainder,if_neg hne]
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    simpa only [iteratedDeriv_const,ite_self,abs_zero] using
      (show (0:ℝ) ≤ C*(B*(H:ℝ)^6/60) by positivity)

end TaoTrudgianYang2025
