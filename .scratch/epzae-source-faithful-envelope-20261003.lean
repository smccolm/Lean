import TaoTrudgianYang2025.LiteratureDensity

/-! Exact regressions for the installed source-faithful envelope.
The stronger frozen printed endpoint contract remains separate. -/

noncomputable section
namespace TaoTrudgianYang2025.LiteratureTable

example {σ : ℝ} (h39 : σ ≠ 39/40) (h41 : σ ≠ 41/42) :
    sourceFaithfulFiniteDensityTable σ = printedFiniteDensityTable σ :=
  sourceFaithfulFinite_eq_printed h39 h41

example {σ : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ ≤ 59/60) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤
      ((sourceFaithfulFiniteDensityTable σ):EReal) :=
  zeroDensityExponent_le_sourceFaithfulFinite hlo hhi

example {σ : ℝ} (hlo : 59/60 < σ) (hhi : σ < 1) :
    ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ ∧
      σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1)) :=
  exists_sourceFaithful_tail_cell hlo hhi

example {σ : ℝ} (hlo : 59/60 < σ) (hhi : σ < 1) :
    6 ≤ sourceFaithfulTailIndex σ ∧
      1-1/(2*(sourceFaithfulTailIndex σ:ℝ)*((sourceFaithfulTailIndex σ:ℝ)-1)) < σ ∧
      σ ≤ 1-1/(2*(sourceFaithfulTailIndex σ:ℝ)*((sourceFaithfulTailIndex σ:ℝ)+1)) :=
  sourceFaithfulTailIndex_spec hlo hhi

example {σ : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ < 1) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤
      ((sourceFaithfulDensityTable σ):EReal) :=
  zeroDensityExponent_le_sourceFaithfulTable hlo hhi

example : sourceFaithfulDensityTable (39/40) = (1424/1649:ℝ) := by
  norm_num [sourceFaithfulDensityTable, sourceFaithfulFiniteDensityTable]

example : sourceFaithfulDensityTable (41/42) = (28/37:ℝ) := by
  norm_num [sourceFaithfulDensityTable, sourceFaithfulFiniteDensityTable]

example : sourceFaithfulDensityTable (59/60) = (9/13:ℝ) := by
  norm_num [sourceFaithfulDensityTable, sourceFaithfulFiniteDensityTable,
    printedFiniteDensityTable]

example : printedFiniteDensityTable (39/40) = (16/21:ℝ) ∧
    printedFiniteDensityTable (41/42) = (63/85:ℝ) := by
  norm_num [printedFiniteDensityTable]

example : (16/21:ℝ) < 1424/1649 ∧ (63/85:ℝ) < 28/37 ∧ (3/5:ℝ) < 9/13 := by
  norm_num

example {n : ℕ} {σ : ℝ} (hn : 6 ≤ n)
    (hleft : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ)
    (hright : σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    sourceFaithfulTailIndex σ = n := sourceFaithfulTailIndex_eq hn hleft hright

example {n : ℕ} {σ : ℝ} (hlo : 59/60 < σ) (hn : 6 ≤ n)
    (hleft : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < σ)
    (hright : σ ≤ 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    sourceFaithfulDensityTable σ = 3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) :=
  sourceFaithfulDensityTable_of_tail_cell hlo hn hleft hright

example {n : ℕ} (hn : 6 ≤ n) :
    sourceFaithfulDensityTable (1-1/(2*(n:ℝ)*((n:ℝ)-1))) =
      3*(n:ℝ)/((n:ℝ)^2-2*(n:ℝ)+2) := sourceFaithfulDensityTable_tail_lower hn

example : sourceFaithfulDensityTable (83/84) = (21/37:ℝ) := by
  have hh := sourceFaithfulDensityTable_tail_lower (n:=7) (by omega)
  norm_num at hh
  exact hh

example : sourceFaithfulDensityTable (111/112) = (12/25:ℝ) := by
  have hh := sourceFaithfulDensityTable_tail_lower (n:=8) (by omega)
  norm_num at hh
  exact hh

#print axioms sourceFaithfulFiniteDensityTable
#print axioms sourceFaithfulFinite_eq_printed
#print axioms zeroDensityExponent_le_sourceFaithfulFinite
#print axioms exists_sourceFaithful_tail_cell
#print axioms sourceFaithfulTailIndex
#print axioms sourceFaithfulTailIndex_spec
#print axioms sourceFaithfulDensityTable
#print axioms zeroDensityExponent_le_sourceFaithfulTable
#print axioms sourceFaithfulTailIndex_eq
#print axioms sourceFaithfulDensityTable_of_tail_cell
#print axioms sourceFaithfulDensityTable_tail_lower

end TaoTrudgianYang2025.LiteratureTable
