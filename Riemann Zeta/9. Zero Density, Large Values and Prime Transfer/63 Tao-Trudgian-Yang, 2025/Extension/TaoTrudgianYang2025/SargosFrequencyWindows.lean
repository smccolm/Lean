import TaoTrudgianYang2025.SargosLargeFrequencyModelBound

/-! Actual signed and absolute quartic windows, with all ordered sextuple multiplicities. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosAbsoluteSextupleWindow (H : ℕ) (c B : ℝ) :
    Finset (SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :=
  (sargosSquareDiagonal H).filter (fun q =>
    c ≤ |(sargosQuarticDifference q:ℝ)| ∧ |(sargosQuarticDifference q:ℝ)| ≤ c+B)

def sargosSmallFrequencySextuples (H : ℕ) :
    Finset (SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :=
  (sargosSquareDiagonal H).filter (fun q => |(sargosQuarticDifference q:ℝ)| ≤ 12*(H:ℝ)^3)

def sargosLargeFrequencySextuples (H : ℕ) :
    Finset (SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :=
  (sargosSquareDiagonal H).filter (fun q => 12*(H:ℝ)^3 < |(sargosQuarticDifference q:ℝ)|)

theorem sargosQuarticDifference_abs_le {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    |(sargosQuarticDifference q:ℝ)| ≤ 3*(H:ℝ)^4 := by
  have h1 := sargosInitialTuplePower_bounds q.1 4
  have h2 := sargosInitialTuplePower_bounds q.2 4
  have h1r : 0 ≤ (sargosInitialTuplePower 4 q.1:ℝ) ∧
      (sargosInitialTuplePower 4 q.1:ℝ) ≤ 3*(H:ℝ)^4 := by exact_mod_cast h1
  have h2r : 0 ≤ (sargosInitialTuplePower 4 q.2:ℝ) ∧
      (sargosInitialTuplePower 4 q.2:ℝ) ≤ 3*(H:ℝ)^4 := by exact_mod_cast h2
  unfold sargosQuarticDifference
  push_cast
  exact abs_le.mpr ⟨by linarith [h1r.1,h2r.2],by linarith [h1r.2,h2r.1]⟩

theorem sargosAbsoluteSextupleWindow_subset_signed (H : ℕ) (c B : ℝ) :
    sargosAbsoluteSextupleWindow H c B ⊆
      sargosInitialSextupleWindow H c B ∪ sargosInitialSextupleWindow H (-c-B) B := by
  intro q hq
  have h := Finset.mem_filter.mp hq
  have hd := (Finset.mem_filter.mp h.1).2
  have hl := h.2.1
  have hu := h.2.2
  by_cases hp : 0 ≤ (sargosQuarticDifference q:ℝ)
  · rw [abs_of_nonneg hp] at hl hu
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,hl,hu⟩
  · rw [abs_of_neg (lt_of_not_ge hp)] at hl hu
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hd,?_,?_⟩
    · change -c-B ≤ (sargosQuarticDifference q:ℝ)
      linarith
    · change (sargosQuarticDifference q:ℝ) ≤ -c-B+B
      linarith

theorem sargosAbsoluteSextupleWindow_card_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ c : ℝ,
      ((sargosAbsoluteSextupleWindow H c ((H:ℝ)^3)).card:ℝ) ≤ C*(H:ℝ)^(3+ε) := by
  obtain ⟨C,hC,hcount⟩ := sargos_initial_sextuple_count ε hε
  refine ⟨2*C,by linarith,?_⟩
  intro H hH c
  have hc : ((sargosAbsoluteSextupleWindow H c ((H:ℝ)^3)).card:ℝ) ≤
      ((sargosInitialSextupleWindow H c ((H:ℝ)^3)).card:ℝ)+
      ((sargosInitialSextupleWindow H (-c-(H:ℝ)^3) ((H:ℝ)^3)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card (sargosAbsoluteSextupleWindow_subset_signed H c
      ((H:ℝ)^3))).trans (Finset.card_union_le _ _)
  have h1 := hcount H hH c
  have h2 := hcount H hH (-c-(H:ℝ)^3)
  linarith

theorem sargosSmallFrequencySextuples_subset_window (H : ℕ) :
    sargosSmallFrequencySextuples H ⊆
      sargosInitialSextupleWindow H (-12*(H:ℝ)^3) (24*(H:ℝ)^3) := by
  intro q hq
  have h := Finset.mem_filter.mp hq
  have hd := (Finset.mem_filter.mp h.1).2
  have habs := abs_le.mp h.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hd,?_,?_⟩
  · change -12*(H:ℝ)^3 ≤ (sargosQuarticDifference q:ℝ)
    linarith [habs.1]
  · change (sargosQuarticDifference q:ℝ) ≤ -12*(H:ℝ)^3+24*(H:ℝ)^3
    linarith [habs.2]

theorem sargosSmallFrequencySextuples_card_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
      ((sargosSmallFrequencySextuples H).card:ℝ) ≤ C*(H:ℝ)^(3+ε) := by
  obtain ⟨C,hC,hcount⟩ := sargosInitialSextupleWindow_card_bound ε hε
  refine ⟨25*C,by linarith,?_⟩
  intro H hH
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hc : ((sargosSmallFrequencySextuples H).card:ℝ) ≤
      ((sargosInitialSextupleWindow H (-12*(H:ℝ)^3) (24*(H:ℝ)^3)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (sargosSmallFrequencySextuples_subset_window H)
  have hb := hcount H hH (24*(H:ℝ)^3) (by positivity) (-12*(H:ℝ)^3)
  have he : (H:ℝ)^(3+ε) = (H:ℝ)^3*(H:ℝ)^ε := by
    rw [Real.rpow_add hHp]
    norm_num
  calc
    _ ≤ C*((H:ℝ)^3+24*(H:ℝ)^3)*(H:ℝ)^ε := hc.trans hb
    _ = _ := by rw [he]; ring

theorem sargosFrequencySextuples_partition (H : ℕ) :
    sargosSmallFrequencySextuples H ∪ sargosLargeFrequencySextuples H = sargosSquareDiagonal H ∧
      Disjoint (sargosSmallFrequencySextuples H) (sargosLargeFrequencySextuples H) := by
  constructor
  · ext q
    simp only [sargosSmallFrequencySextuples,sargosLargeFrequencySextuples,
      Finset.mem_union,Finset.mem_filter]
    constructor
    · intro h
      rcases h with h|h
      · exact h.1
      · exact h.1
    · intro h
      rcases le_or_gt |(sargosQuarticDifference q:ℝ)| (12*(H:ℝ)^3) with hs|hl
      · exact Or.inl ⟨h,hs⟩
      · exact Or.inr ⟨h,hl⟩
  · apply Finset.disjoint_left.mpr
    intro q hs hl
    exact (not_lt_of_ge (Finset.mem_filter.mp hs).2) (Finset.mem_filter.mp hl).2

end TaoTrudgianYang2025
