import TaoTrudgianYang2025.SargosFrequencyWindows

/-! A proved finite cover of every actual large quartic frequency by width-H-cubed windows. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosLargeFrequency_window_index {H : ℕ} (hH : 1 ≤ H)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosLargeFrequencySextuples H) :
    ∃ j ∈ Finset.Icc 1 (3*H),
      q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3) := by
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hc : (0:ℝ) < (H:ℝ)^3 := pow_pos hHp 3
  have h := Finset.mem_filter.mp hq
  let d := |(sargosQuarticDifference q:ℝ)|
  have hd : (H:ℝ)^3 ≤ d := by
    dsimp [d]
    nlinarith [h.2]
  let j : ℕ := ⌊d/(H:ℝ)^3⌋₊
  have hjp : 0 < j := Nat.floor_pos.mpr ((le_div_iff₀ hc).mpr (by simpa using hd))
  have hdup : d/(H:ℝ)^3 ≤ (3*H:ℕ) := by
    apply (div_le_iff₀ hc).mpr
    have hh := sargosQuarticDifference_abs_le q
    push_cast
    calc
      d ≤ 3*(H:ℝ)^4 := hh
      _ = _ := by ring
  have hju : j ≤ 3*H := Nat.floor_le_of_le hdup
  refine ⟨j,Finset.mem_Icc.mpr ⟨by omega,hju⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨h.1,?_,?_⟩
  · exact (le_div_iff₀ hc).mp (Nat.floor_le (by positivity : 0 ≤ d/(H:ℝ)^3))
  · have hh := Nat.lt_floor_add_one (d/(H:ℝ)^3)
    have he := (div_lt_iff₀ hc).mp hh
    change d ≤ (j:ℝ)*(H:ℝ)^3+(H:ℝ)^3
    dsimp [j] at *
    nlinarith only [he]

theorem sargosLargeFrequency_sum_le_windows {H : ℕ} (hH : 1 ≤ H)
    (w : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3 → ℝ)
    (hw : ∀ q, 0 ≤ w q) :
    ∑ q ∈ sargosLargeFrequencySextuples H, w q ≤
      ∑ j ∈ Finset.Icc 1 (3*H),
        ∑ q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3), w q := by
  classical
  calc
    _ ≤ ∑ q ∈ sargosLargeFrequencySextuples H,
        ∑ j ∈ Finset.Icc 1 (3*H),
          if q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3)
            then w q else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨j,hj,hwin⟩ := sargosLargeFrequency_window_index hH q hq
      have hs := Finset.single_le_sum
        (f := fun i : ℕ => if q ∈ sargosAbsoluteSextupleWindow H
          ((i:ℝ)*(H:ℝ)^3) ((H:ℝ)^3) then w q else 0)
        (fun i hi => by
          dsimp only
          split_ifs
          · exact hw q
          · exact le_rfl) hj
      simpa only [if_pos hwin] using hs
    _ = ∑ j ∈ Finset.Icc 1 (3*H),
        ∑ q ∈ (sargosLargeFrequencySextuples H).filter
          (fun q => q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3)), w q := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact (Finset.mem_filter.mp hq).2
      · intro q hq hnot
        exact hw q

theorem sargosAbsoluteWindow_reciprocal_bound {H j : ℕ} (hH : 1 ≤ H) (hj : 1 ≤ j) :
    ∑ q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3),
      12/|(sargosQuarticDifference q:ℝ)| ≤
        ((sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3)).card:ℝ)*
          (12/((j:ℝ)*(H:ℝ)^3)) := by
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hjp : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  calc
    _ ≤ ∑ _q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3),
        12/((j:ℝ)*(H:ℝ)^3) := by
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (Finset.mem_filter.mp hq).2.1
    _ = _ := by simp

end TaoTrudgianYang2025
