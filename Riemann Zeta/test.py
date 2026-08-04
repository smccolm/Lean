import subprocess
import sys

def check(lean_code):
    with open('RiemannZeta/GuthMaynard/ExtractSeparated_scratch.lean', 'w', encoding='utf-8') as f:
        f.write(lean_code)
    res = subprocess.run(['lake', 'env', 'lean', 'RiemannZeta/GuthMaynard/ExtractSeparated_scratch.lean'], cwd='E:/Lean/Riemann Zeta', capture_output=True, text=True)
    return res.stdout + res.stderr

lean_code = """import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ExtractSeparated

open Complex
open Finset

namespace RiemannZeta.GuthMaynard

theorem representative_selection (model : ZetaZeroCountModel) (hLocal : LocalZeroCountHypothesis model) : RepresentativeSelectionHypothesis model := by
  intro σ T hT
  have ⟨C, hC_pos, hLocal_bound⟩ := hLocal
  let a := ⌊T⌋
  let b := ⌊2 * T⌋
  let S := (Finset.Icc a b).image (fun k : ℤ => max T (min (2 * T) (k : ℝ)))
  use S
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [S, Finset.mem_image, Finset.mem_Icc] at hx
    rcases hx with ⟨k, _, hk2⟩
    rw [← hk2]
    simp only [Set.mem_Icc]
    exact ⟨le_max_left T _, max_le (by linarith) (min_le_left _ _)⟩
  · intro x
    sorry
  · sorry
"""

print(check(lean_code))
