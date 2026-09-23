import TaoTrudgianYang2025.SargosSextupleRadiusJets
import TaoTrudgianYang2025.SargosInitialSextupleCount

/-! A proved global count for the actual square-diagonal sextuples. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosInitialTuplePower_bounds {H : ℕ}
    (t : SargosInitialMomentTuple H 3) (k : ℕ) :
    0 ≤ sargosInitialTuplePower k t ∧ sargosInitialTuplePower k t ≤ 3*(H:ℤ)^k := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (Finset.mem_Ioc.mp (t i).property).1.le k
  · calc
      _ ≤ ∑ _i : Fin 3, (H:ℤ)^k := by
        apply Finset.sum_le_sum
        intro i hi
        have hn := Finset.mem_Ioc.mp (t i).property
        exact pow_le_pow_left₀ hn.1.le hn.2 k
      _ = _ := by simp

theorem sargosSquareDiagonal_subset_window (H : ℕ) :
    sargosSquareDiagonal H ⊆ sargosInitialSextupleWindow H (-3*(H:ℝ)^4) (6*(H:ℝ)^4) := by
  intro q hq
  have h1 := sargosInitialTuplePower_bounds q.1 4
  have h2 := sargosInitialTuplePower_bounds q.2 4
  have h1r : 0 ≤ (sargosInitialTuplePower 4 q.1:ℝ) ∧
      (sargosInitialTuplePower 4 q.1:ℝ) ≤ 3*(H:ℝ)^4 := by exact_mod_cast h1
  have h2r : 0 ≤ (sargosInitialTuplePower 4 q.2:ℝ) ∧
      (sargosInitialTuplePower 4 q.2:ℝ) ≤ 3*(H:ℝ)^4 := by exact_mod_cast h2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(Finset.mem_filter.mp hq).2,?_,?_⟩
  · push_cast
    linarith [h1r.1,h2r.2]
  · push_cast
    linarith [h1r.2,h2r.1]

theorem sargosSquareDiagonal_card_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
      ((sargosSquareDiagonal H).card:ℝ) ≤ C*(H:ℝ)^(4+ε) := by
  obtain ⟨C,hC,hcount⟩ := sargosInitialSextupleWindow_card_bound ε hε
  refine ⟨7*C,by linarith,?_⟩
  intro H hH
  have hHpos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hH1 : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hcube : (H:ℝ)^3 ≤ (H:ℝ)^4 := pow_le_pow_right₀ hH1 (by omega)
  have hcard : ((sargosSquareDiagonal H).card:ℝ) ≤
      ((sargosInitialSextupleWindow H (-3*(H:ℝ)^4) (6*(H:ℝ)^4)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (sargosSquareDiagonal_subset_window H)
  have h := hcount H hH (6*(H:ℝ)^4) (by positivity) (-3*(H:ℝ)^4)
  have hp : (H:ℝ)^4*(H:ℝ)^ε = (H:ℝ)^(4+ε) := by
    rw [Real.rpow_add hHpos]
    norm_num
  calc
    _ ≤ C*((H:ℝ)^3+6*(H:ℝ)^4)*(H:ℝ)^ε := hcard.trans h
    _ ≤ C*(7*(H:ℝ)^4)*(H:ℝ)^ε := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith only [hcube]
    _ = (7*C)*((H:ℝ)^4*(H:ℝ)^ε) := by ring
    _ = _ := by rw [hp]

end TaoTrudgianYang2025
