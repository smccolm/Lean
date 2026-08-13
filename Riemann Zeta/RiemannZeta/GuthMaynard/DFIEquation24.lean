import RiemannZeta.GuthMaynard.DFIReducedModulus

/-!
# DFI equation (24): primitive-residue reassembly

This module begins the exact passage from the two-variable Voronoi expansion
in equation (23) to the complete exponential sums in equation (24).  The
first theorem reassembles equation (23) over the same primitive residue set
as equation (22); the second isolates the Ramanujan coefficient of the
double-main branch.  The inverse-frequency Kloosterman identifications are
proved subsequently, rather than included as hypotheses here.
-/

open Complex Finset
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- The equation-(22) primitive-residue sum after separating the two divisor
phases, but before applying the two Voronoi formulas. -/
noncomputable def dfiEquation24PreVoronoi
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) *
      dfiEquation23SourceLeft q a b d E

/-- The exact reduced-modulus expansion obtained by applying equation (23)
inside the primitive-residue sum. -/
noncomputable def dfiEquation24ReducedExpansion
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) *
      dfiEquation23ReducedGroupedRight
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))) E

/-- The exact first step of DFI equation (24): equation (23) may be summed
over every primitive residue because its source-facing theorem is uniform in
that residue. -/
theorem dfiEquation24_reassemble_equation23
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    dfiEquation24PreVoronoi q a b h
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
      dfiEquation24ReducedExpansion q a b h
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  unfold dfiEquation24PreVoronoi dfiEquation24ReducedExpansion
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [dfiEquation23Weight_source_grouped
    w hf hbox hφ a b ha hb h q hq d hd.2]

/-- The primitive-residue coefficient of the double-main branch. -/
noncomputable def dfiEquation24MainCoefficient
    (q : ℕ) [NeZero q] (h : ℤ) (I : ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) * I

/-- The first term of DFI equation (24): its complete exponential sum is
exactly the Ramanujan sum `S(-h,0;q)`. -/
theorem dfiEquation24MainCoefficient_eq_ramanujan
    (q : ℕ) [NeZero q] (hq : 0 < q) (h : ℤ) (I : ℂ) :
    dfiEquation24MainCoefficient q h I = ramanujanSumInt q (-h) * I := by
  unfold dfiEquation24MainCoefficient
  rw [ramanujanSumInt_eq_sum_coprime q hq (-h)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  congr 2
  push_cast
  ring

end RiemannZeta.GuthMaynard
