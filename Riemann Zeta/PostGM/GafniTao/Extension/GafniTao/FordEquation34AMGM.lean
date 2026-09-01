import GafniTao.FordResiduePartition

/-!
# Ford equation (3.4): the exact residue coefficient

This file assembles the Newton fibre bound, Cauchy--Schwarz, AM--GM, and the
partition of all residue tuples.  The result is the pointwise inequality
whose integration gives Ford's equation (3.4), with the exact coefficient
`d! p^(s-d) p^(s-1)` before the final maximum over `p` residue classes.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordResidueFiberProduct
    {p d s : ℕ} [NeZero p] (hds : d ≤ s)
    (g : ZMod p → ℂ) (v : Fin d → ZMod p) : ℂ :=
  ∑ c : FordBResidueClass p d s v,
    ∏ i, g (fordBJoin hds c.1 i)

/-- The fully summed Cauchy--AM--GM inequality underlying (3.4).  Notice
that the displayed power is `p^(s-1)`; only the subsequent sum-to-maximum
step contributes the final factor `p`. -/
theorem ford_equation_3_4_pointwise
    {p d s : ℕ} [NeZero p] (hs : 0 < s) (hds : d ≤ s)
    (hp : Nat.Prime p) (hdp : d < p) (g : ZMod p → ℂ) :
    ∑ v : Fin d → ZMod p, ‖fordResidueFiberProduct hds g v‖ ^ 2 ≤
      ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
        (p : ℝ) ^ (s - 1) *
          ∑ a : ZMod p, ‖g a‖ ^ (2 * s) := by
  let D : ℝ := ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ)
  have hv (v : Fin d → ZMod p) :
      (s : ℝ) * ‖fordResidueFiberProduct hds g v‖ ^ 2 ≤
        D * ∑ c : FordBResidueClass p d s v,
          ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
    exact ford_residue_fiber_cauchy_amgm hs hds hp hdp v g
  have hsum := Finset.sum_le_sum fun v (_hv : v ∈
      (Finset.univ : Finset (Fin d → ZMod p))) => hv v
  have hsum' :
      (s : ℝ) *
          ∑ v : Fin d → ZMod p, ‖fordResidueFiberProduct hds g v‖ ^ 2 ≤
        D *
          ∑ v : Fin d → ZMod p,
            ∑ c : FordBResidueClass p d s v,
              ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
    simpa only [Finset.mul_sum] using hsum
  rw [ford_sum_BResidueClass_coordinates hds
    (f := fun a => ‖g a‖ ^ (2 * s))] at hsum'
  have hsR : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  have hmul :
      (s : ℝ) *
          ∑ v : Fin d → ZMod p, ‖fordResidueFiberProduct hds g v‖ ^ 2 ≤
        (s : ℝ) *
          (D * (p : ℝ) ^ (s - 1) *
            ∑ a : ZMod p, ‖g a‖ ^ (2 * s)) := by
    calc
      (s : ℝ) *
          ∑ v : Fin d → ZMod p, ‖fordResidueFiberProduct hds g v‖ ^ 2 ≤
        D * ((s : ℝ) * (p : ℝ) ^ (s - 1) *
          ∑ a : ZMod p, ‖g a‖ ^ (2 * s)) := hsum'
      _ = (s : ℝ) *
          (D * (p : ℝ) ^ (s - 1) *
            ∑ a : ZMod p, ‖g a‖ ^ (2 * s)) := by ring
  exact le_of_mul_le_mul_left hmul hsR

#print axioms ford_equation_3_4_pointwise

end

end GafniTao
