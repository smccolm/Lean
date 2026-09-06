import GafniTao.Pintz2023Equation416

/-!
# Pintz (2023), sign localization on a height shell

The source applies its local-frequency estimates on one signed dyadic height
interval.  The formal detector initially returns both signs.  Splitting once
by sign costs a factor two and restores the essential bound
`|u-v| ≤ T` after detector displacement.
-/

open Finset

namespace GafniTao

noncomputable section

/-- A detected family in the absolute dyadic shell has a same-sign half whose
pairwise frequency differences are at most the original shell height. -/
theorem exists_pintz2023_sameSign_subfamily
    {W : Finset ℝ} {T lambda : ℝ}
    (hLower : ∀ u ∈ W, T / 4 < |u|)
    (hUpper : ∀ u ∈ W, |u| ≤ T + 2 * lambda)
    (hDisplacement : 2 * lambda ≤ T / 4) :
    ∃ W' ⊆ W, (W.card : ℝ) ≤ 2 * (W'.card : ℝ) ∧
      ∀ u ∈ W', ∀ v ∈ W', |v - u| ≤ T := by
  classical
  let Wpos := W.filter (fun u => 0 ≤ u)
  let Wneg := W.filter (fun u => u < 0)
  have hcover : W ⊆ Wpos ∪ Wneg := by
    intro u hu
    by_cases huSign : 0 ≤ u
    · exact Finset.mem_union_left Wneg (Finset.mem_filter.mpr ⟨hu, huSign⟩)
    · exact Finset.mem_union_right Wpos
        (Finset.mem_filter.mpr ⟨hu, lt_of_not_ge huSign⟩)
  have hcardCover : W.card ≤ Wpos.card + Wneg.card := by
    exact (Finset.card_le_card hcover).trans
      (Finset.card_union_le Wpos Wneg)
  by_cases hcard : Wneg.card ≤ Wpos.card
  · refine ⟨Wpos, ?_, ?_, ?_⟩
    · intro u hu
      exact (Finset.mem_filter.mp hu).1
    · exact_mod_cast (hcardCover.trans (by omega :
        Wpos.card + Wneg.card ≤ 2 * Wpos.card))
    · intro u hu v hv
      have huW := (Finset.mem_filter.mp hu).1
      have hvW := (Finset.mem_filter.mp hv).1
      have huSign := (Finset.mem_filter.mp hu).2
      have hvSign := (Finset.mem_filter.mp hv).2
      have huLower := hLower u huW
      have hvLower := hLower v hvW
      have huUpper := hUpper u huW
      have hvUpper := hUpper v hvW
      rw [abs_of_nonneg huSign] at huLower huUpper
      rw [abs_of_nonneg hvSign] at hvLower hvUpper
      rw [abs_le]
      constructor <;> linarith
  · have hcard' : Wpos.card ≤ Wneg.card := by omega
    refine ⟨Wneg, ?_, ?_, ?_⟩
    · intro u hu
      exact (Finset.mem_filter.mp hu).1
    · exact_mod_cast (hcardCover.trans (by omega :
        Wpos.card + Wneg.card ≤ 2 * Wneg.card))
    · intro u hu v hv
      have huW := (Finset.mem_filter.mp hu).1
      have hvW := (Finset.mem_filter.mp hv).1
      have huSign := (Finset.mem_filter.mp hu).2
      have hvSign := (Finset.mem_filter.mp hv).2
      have huLower := hLower u huW
      have hvLower := hLower v hvW
      have huUpper := hUpper u huW
      have hvUpper := hUpper v hvW
      rw [abs_of_neg huSign] at huLower huUpper
      rw [abs_of_neg hvSign] at hvLower hvUpper
      rw [abs_le]
      constructor <;> linarith

#print axioms exists_pintz2023_sameSign_subfamily

end

end GafniTao
