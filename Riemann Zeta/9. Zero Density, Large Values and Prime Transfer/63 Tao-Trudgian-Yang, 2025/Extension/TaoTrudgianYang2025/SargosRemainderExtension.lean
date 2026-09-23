import TaoTrudgianYang2025.SargosRemainderGeometry
import TaoTrudgianYang2025.BetaTaylorPastedUniform

/-!
A constructed smooth extension of the actual sextuple remainder.
The zero branch is used only when its actual integer support is empty.
Uniform constants precede every physical parameter and source phase.
-/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosExtendedRemainder {H : ℕ} (f : ℝ → ℝ) (M Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℝ → ℝ :=
  if (sargosSextupleInterior M q).Nonempty then
    taylorPastedExtension (sargosNormalizedRemainder f M q) Q
      (sargosRemainderLeft M q) (sargosRemainderRight M q) (sargosRemainderWidth M)
  else fun _ => 0

theorem sargosExtendedRemainder_of_empty {H : ℕ} (f : ℝ → ℝ) (M Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (he : sargosSextupleInterior M q = ∅) :
    sargosExtendedRemainder f M Q q = fun _ => 0 := by
  simp only [sargosExtendedRemainder,he,Finset.not_nonempty_empty,↓reduceIte]

theorem sargosExtendedRemainder_contDiff {H M : ℕ} {f : ℝ → ℝ}
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (sargosExtendedRemainder f M Q q) := by
  unfold sargosExtendedRemainder
  split_ifs
  · exact taylorPastedExtension_contDiff (sargosRemainderWidth_bounds hM).1
      (fun x hx => sargosNormalizedRemainder_contDiffAt hM q hf hx) Q
  · exact contDiff_const

theorem sargosExtendedRemainder_agrees {H M : ℕ} (f : ℝ → ℝ)
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosExtendedRemainder f M Q q ((m:ℝ)/M) = sargosSextupleRemainder f q m := by
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [sargosExtendedRemainder,if_pos ⟨m,hm⟩,
    taylorPastedExtension_agrees _ _ (sargosRemainderWidth_bounds hM).1
      (sargosSextupleInterior_in_plateau hM q hm)]
  simp only [sargosNormalizedRemainder,mul_div_cancel₀ _ hM0]

theorem sargosExtendedRemainder_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (f : ℝ → ℝ) (B : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → 0 ≤ B →
      (∀ y ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f y) →
      (∀ j ≤ Q+1, ∀ y ∈ Ioo (1:ℝ) M,
        |iteratedDeriv (j+6) f y| ≤ B/(M:ℝ)^j) →
      ∀ x ∈ Icc (0:ℝ) 1, ∀ j ≤ Q,
        |iteratedDeriv j (sargosExtendedRemainder f M Q q) x| ≤ C*(B*(H:ℝ)^6/60) := by
  obtain ⟨C,hC,hjets⟩ := taylorPastedExtension_uniform_jets Q (D := 1) le_rfl
  refine ⟨C,hC,?_⟩
  intro H M f B q hM hB hf hb x hx j hj
  by_cases hne : (sargosSextupleInterior M q).Nonempty
  · rw [sargosExtendedRemainder,if_pos hne]
    have hh := sargosRemainderWidth_bounds hM
    have hg := (sargosRemainder_interval_geometry hM q hne).2.2
    have hd := sargosRemainder_observation_distances hM q hne hx
    exact hjets _ _ _ _ _ _ hh.1 hh.2 hg
      (fun y hy => sargosNormalizedRemainder_contDiffAt hM q hf hy)
      (fun y hy k hk => abs_iteratedDeriv_sargosNormalizedRemainder_le hM q hf hb hy hk)
      hd.1 hd.2 j hj
  · rw [sargosExtendedRemainder,if_neg hne]
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    simpa only [iteratedDeriv_const,ite_self,abs_zero] using
      (show (0:ℝ) ≤ C*(B*(H:ℝ)^6/60) by positivity)

end TaoTrudgianYang2025
