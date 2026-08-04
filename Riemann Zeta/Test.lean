import Mathlib
import RiemannZeta.GuthMaynard.ExtractSeparated

open Finset

namespace RiemannZeta.GuthMaynard

theorem representative_selection (model : ZetaZeroCountModel) (hLocal : LocalZeroCountHypothesis model) : RepresentativeSelectionHypothesis model := by
  intro σ T hT
  have ⟨C, hC_pos, hLocal_bound⟩ := hLocal
  let S := (Finset.range (⌊T⌋₊ + 1)).image (fun k => T + (k : ℝ))
  use S
  sorry
