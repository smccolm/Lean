import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated

namespace RiemannZeta.GuthMaynard

/--
The classical local zero-density estimate:
The number of zeros in a unit interval [t, t+1] is bounded by O(log T)
for t ∈ [T, 2T].
-/
def LocalZeroCountHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∃ C > 0, ∀ (σ t T : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
    (zeroCountRect model σ 1 t (t + 1) : ℝ) ≤ C * Real.log T

/--
F-05: Extract separated ordinates.
For any `T ≥ 2` and `σ`, there exists a 1-separated set `W ⊂ [T, 2T]`
whose cardinality controls the number of relevant zeros in the dyadic slab.
-/
def ExtractSeparatedHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), T ≥ 2 →
    ∃ (W : Finset ℝ), IsSeparated 1 W ∧ InTargetInterval T W ∧
      ∃ C > 0, (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (W.card : ℝ) * Real.log T

/--
Intermediate combinatorial geometric hypothesis:
We can choose a set of representative ordinates `S` in `[T, 2T]` such that
there is at most 2 points per unit interval, and the total number of zeros
is bounded by `S.card` times the max local zero count.
-/
def RepresentativeSelectionHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T : ℝ), T ≥ 2 →
    ∃ (S : Finset ℝ),
      (∀ x ∈ S, x ∈ Set.Icc T (2 * T)) ∧
      (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ 2) ∧
      (∃ C > 0, (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (S.card : ℝ) * Real.log T)

theorem deduce_extract_separated
    (model : ZetaZeroCountModel)
    (hRep : RepresentativeSelectionHypothesis model)
    (hSep : SeparatedSelectionHypothesis) :
    ExtractSeparatedHypothesis model := by
  intro σ T hT
  rcases hRep σ T hT with ⟨S, hS_interval, hS_density, C, hC_pos, h_bound⟩
  rcases hSep S 2 hS_density with ⟨W, hW_sub, hW_sep, hW_card⟩
  use W
  refine ⟨hW_sep, ?_, ?_⟩
  · intro x hx
    exact hS_interval x (hW_sub hx)
  · use C * 4
    refine ⟨by linarith, ?_⟩
    have h1 : (S.card : ℝ) ≤ 4 * (W.card : ℝ) := by
      have h_card : S.card ≤ 4 * W.card := by
        calc S.card ≤ 2 * 2 * W.card := hW_card
             _ = 4 * W.card := by ring
      exact Nat.cast_le.mpr h_card
    have h2 : Real.log T ≥ 0 := by
      apply Real.log_nonneg
      linarith
    calc
      (zeroCountRect model σ 1 T (2 * T) : ℝ) ≤ C * (S.card : ℝ) * Real.log T := h_bound
      _ ≤ C * (4 * (W.card : ℝ)) * Real.log T := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · exact h1
          · exact le_of_lt hC_pos
        · exact h2
      _ = (C * 4) * (W.card : ℝ) * Real.log T := by ring

end RiemannZeta.GuthMaynard
