import TaoTrudgianYang2025.SargosFrequencyWindows

/-! Actual trivial inner-sum estimate and the small-frequency contribution. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosSextupleInterior_subset_source {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosSextupleInterior M q ⊆ Finset.Ioc (0:ℤ) M := by
  intro m hm
  have hi := Finset.mem_Ioo.mp hm
  have hr := (sargosSextupleRadius_bounds q).1
  exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩

theorem sargosSextupleInterior_card_le {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    (sargosSextupleInterior M q).card ≤ M := by
  have h := Finset.card_le_card (sargosSextupleInterior_subset_source M q)
  simpa using h

theorem sargos_sextuple_inner_norm_le {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    ‖∑ m ∈ sargosSextupleInterior M q,
      fordAdditiveCharacter (sargosSextuplePhase f q m)‖ ≤ (M:ℝ) := by
  calc
    _ ≤ ∑ m ∈ sargosSextupleInterior M q,
        ‖fordAdditiveCharacter (sargosSextuplePhase f q m)‖ := norm_sum_le _ _
    _ = ((sargosSextupleInterior M q).card:ℝ) := by simp [sargos_character_norm]
    _ ≤ _ := by exact_mod_cast sargosSextupleInterior_card_le M q

theorem sargos_small_frequency_contribution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ (M : ℕ) (f : ℝ → ℝ),
      (∑ q ∈ sargosSmallFrequencySextuples H,
        ‖∑ m ∈ sargosSextupleInterior M q,
          fordAdditiveCharacter (sargosSextuplePhase f q m)‖) ≤
        C*(M:ℝ)*(H:ℝ)^(3+ε) := by
  obtain ⟨C,hC,hcount⟩ := sargosSmallFrequencySextuples_card_bound ε hε
  refine ⟨C,hC,?_⟩
  intro H hH M f
  calc
    _ ≤ ∑ _q ∈ sargosSmallFrequencySextuples H, (M:ℝ) :=
      Finset.sum_le_sum (fun q hq => sargos_sextuple_inner_norm_le f M q)
    _ = (M:ℝ)*((sargosSmallFrequencySextuples H).card:ℝ) := by simp [mul_comm]
    _ ≤ (M:ℝ)*(C*(H:ℝ)^(3+ε)) :=
      mul_le_mul_of_nonneg_left (hcount H hH) (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
