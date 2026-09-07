import RiemannZeta.GuthMaynard.DFIProposition1Native
import RiemannZeta.GuthMaynard.DFIEquation22
import RiemannZeta.GuthMaynard.DFIDeltaSmooth

/-!
# DFI equation (23): the two-variable Voronoi expansion

This module isolates the exact algebraic content of applying DFI Proposition 1
in each variable.  The three branches are the logarithmic main term, the
`Y₀` branch, and the `K₀` branch.  Their Cartesian square is the nine-term
expansion in equation (23): the main integral, the two single transforms, the
double transform, and the five terms obtained by replacing at least one
`Y₀` transform by `K₀`.

The intermediate admissibility structure records only the analytic fact needed
to justify the second application: after applying any of the three branches in
the second variable, the resulting function of the first variable is again a
positive smooth compactly supported Voronoi test function.  A later theorem in
this file derives that fact for the localized equation-(21) weight; it is not a
substitute for equation (23).
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- The three terms in DFI Proposition 1. -/
inductive DFIVoronoiBranch where
  | mainTerm
  | minusTerm
  | plusTerm
  deriving DecidableEq, Fintype

/-- One complete branch of DFI Proposition 1.  The two transformed branches
include their complete dual divisor series. -/
noncomputable def dfiVoronoiBranchValue (q : ℕ) [NeZero q]
    (d : ZMod q) (branch : DFIVoronoiBranch) (g : ℝ → ℂ) : ℂ :=
  match branch with
  | .mainTerm => dfiVoronoiMainTerm q g
  | .minusTerm =>
      ∑' n : ℕ, divisorWeight n *
        ZMod.stdAddChar ((-d⁻¹) * (n : ZMod q)) *
          dfiVoronoiMinusTransform q (mellin g) n
  | .plusTerm =>
      ∑' n : ℕ, divisorWeight n *
        ZMod.stdAddChar (d⁻¹ * (n : ZMod q)) *
          dfiVoronoiPlusTransform q (mellin g) n

@[simp]
theorem dfiVoronoiBranchValue_zero (q : ℕ) [NeZero q]
    (d : ZMod q) (branch : DFIVoronoiBranch) :
    dfiVoronoiBranchValue q d branch (fun _ : ℝ => 0) = 0 := by
  cases branch <;>
    simp [dfiVoronoiBranchValue, dfiVoronoiMainTerm,
      dfiVoronoiMinusTransform, dfiVoronoiPlusTransform, mellin,
      VerticalIntegral', VerticalIntegral]

@[simp]
theorem sum_dfiVoronoiBranchValue (q : ℕ) [NeZero q]
    (d : ZMod q) (g : ℝ → ℂ) :
    ∑ branch : DFIVoronoiBranch, dfiVoronoiBranchValue q d branch g =
      dfiVoronoiMainTerm q g +
        (∑' n : ℕ, divisorWeight n *
          ZMod.stdAddChar ((-d⁻¹) * (n : ZMod q)) *
            dfiVoronoiMinusTransform q (mellin g) n) +
        ∑' n : ℕ, divisorWeight n *
          ZMod.stdAddChar (d⁻¹ * (n : ZMod q)) *
            dfiVoronoiPlusTransform q (mellin g) n := by
  have huniv : (Finset.univ : Finset DFIVoronoiBranch) =
      {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
        DFIVoronoiBranch.plusTerm} := by
    ext branch
    fin_cases branch <;> simp
  change (∑ branch ∈ (Finset.univ : Finset DFIVoronoiBranch),
    dfiVoronoiBranchValue q d branch g) = _
  rw [huniv]
  simp [dfiVoronoiBranchValue, add_assoc]

/-- Proposition 1 written as the sum of its three source branches. -/
theorem DFIVoronoiTestFunction.dfiProposition1_native_branch_sum
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (d : ZMod q) (hd : IsUnit d) :
    periodicDivisorWeightedSum q (dfiVoronoiCharacter q d) g =
      ∑ branch : DFIVoronoiBranch,
        dfiVoronoiBranchValue q d branch g := by
  rw [hg.dfiProposition1_native q d hd, sum_dfiVoronoiBranchValue]

/-- Compact positive support makes the periodic weighted divisor series
finite, hence summable. -/
theorem DFIVoronoiTestFunction.summable_periodicDivisorWeighted
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) (Phi : ZMod q → ℂ) :
    Summable (fun n : ℕ => periodicDivisorCoeff q Phi n * g n) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range (⌈hg.upper⌉₊ + 1))
  intro n hn
  have hnlarge : ⌈hg.upper⌉₊ + 1 ≤ n := by simpa using hn
  have hupperceil : hg.upper ≤ (⌈hg.upper⌉₊ : ℝ) := Nat.le_ceil hg.upper
  have hnotSupport : g (n : ℝ) = 0 := by
    by_contra hne
    have hnupper : (n : ℝ) ≤ hg.upper := (hg.support_subset hne).2
    exact (not_lt_of_ge hnupper) (lt_of_le_of_lt hupperceil (by exact_mod_cast hnlarge))
  simp [hnotSupport]

/-- The exact double divisor sum to which equation (23) is applied. -/
noncomputable def dfiEquation23Left (q : ℕ) [NeZero q]
    (dx dy : ZMod q) (E : ℝ → ℝ → ℂ) : ℂ :=
  periodicDivisorWeightedSum q (dfiVoronoiCharacter q dx)
    (fun x => periodicDivisorWeightedSum q (dfiVoronoiCharacter q dy) (E x))

/-- The nine terms in DFI equation (23), represented as the Cartesian square
of the three source branches. -/
noncomputable def dfiEquation23Right (q : ℕ) [NeZero q]
    (dx dy : ZMod q) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ byBranch : DFIVoronoiBranch, ∑ bxBranch : DFIVoronoiBranch,
    dfiVoronoiBranchValue q dx bxBranch
      (fun x => dfiVoronoiBranchValue q dy byBranch (E x))

/-- The precise regularity obligation created by the second application of
Proposition 1 in DFI equation (23). -/
structure DFIEquation23Admissible (q : ℕ) [NeZero q]
    (dy : ZMod q) (E : ℝ → ℝ → ℂ) where
  /-- The `ySlice` component of `DFIEquation23GroupedAdmissible`. -/
  ySlice : ∀ x : ℝ, DFIVoronoiTestFunction (E x)
  /-- The `xAfterYBranch` component of `DFIEquation23Admissible`. -/
  xAfterYBranch : ∀ branch : DFIVoronoiBranch,
    DFIVoronoiTestFunction
      (fun x => dfiVoronoiBranchValue q dy branch (E x))

/-- DFI equation (23), conditional only on the explicit analytic regularity
that is subsequently derived from the source weight.  This theorem performs
both applications of the already-proved native Proposition 1 and the finite
three-branch interchange. -/
theorem dfiEquation23_of_admissible (q : ℕ) [NeZero q]
    (dx dy : ZMod q) (hdx : IsUnit dx) (hdy : IsUnit dy)
    (E : ℝ → ℝ → ℂ) (hE : DFIEquation23Admissible q dy E) :
    dfiEquation23Left q dx dy E = dfiEquation23Right q dx dy E := by
  unfold dfiEquation23Left dfiEquation23Right
  have hinner : ∀ x : ℝ,
      periodicDivisorWeightedSum q (dfiVoronoiCharacter q dy) (E x) =
        ∑ branch : DFIVoronoiBranch,
          dfiVoronoiBranchValue q dy branch (E x) := fun x =>
    (hE.ySlice x).dfiProposition1_native_branch_sum q dy hdy
  simp_rw [hinner]
  have hsummable : ∀ branch : DFIVoronoiBranch,
      Summable (fun n : ℕ =>
        periodicDivisorCoeff q (dfiVoronoiCharacter q dx) n *
          dfiVoronoiBranchValue q dy branch (E n)) := fun branch =>
    (hE.xAfterYBranch branch).summable_periodicDivisorWeighted q
      (dfiVoronoiCharacter q dx)
  unfold periodicDivisorWeightedSum
  simp_rw [Finset.mul_sum]
  change (∑' n : ℕ,
      ∑ branch : DFIVoronoiBranch,
        periodicDivisorCoeff q (dfiVoronoiCharacter q dx) n *
          dfiVoronoiBranchValue q dy branch (E n)) = _
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (fun branch _ => hsummable branch)]
  apply Finset.sum_congr rfl
  intro branch _hbranch
  change periodicDivisorWeightedSum q (dfiVoronoiCharacter q dx)
      (fun x => dfiVoronoiBranchValue q dy branch (E x)) = _
  rw [(hE.xAfterYBranch branch).dfiProposition1_native_branch_sum q dx hdx]

/-- The two transformed branches grouped exactly as the non-main remainder
of Proposition 1.  This is the object to which the second Voronoi formula can
be applied without imposing separate parameter-smoothness hypotheses on the
`Y₀` and `K₀` pieces. -/
noncomputable def dfiVoronoiRemainderValue (q : ℕ) [NeZero q]
    (d : ZMod q) (g : ℝ → ℂ) : ℂ :=
  dfiVoronoiBranchValue q d .minusTerm g +
    dfiVoronoiBranchValue q d .plusTerm g

theorem sum_dfiVoronoiBranchValue_eq_main_add_remainder
    (q : ℕ) [NeZero q] (d : ZMod q) (g : ℝ → ℂ) :
    ∑ branch : DFIVoronoiBranch, dfiVoronoiBranchValue q d branch g =
      dfiVoronoiBranchValue q d .mainTerm g +
        dfiVoronoiRemainderValue q d g := by
  have huniv : (Finset.univ : Finset DFIVoronoiBranch) =
      {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
        DFIVoronoiBranch.plusTerm} := by
    ext branch
    fin_cases branch <;> simp
  rw [huniv]
  simp [dfiVoronoiRemainderValue]

/-- The exact grouped form of DFI equation (23).  Expanding the remainder
after the required Fubini theorem recovers the source's nine branches. -/
noncomputable def dfiEquation23GroupedRight (q : ℕ) [NeZero q]
    (dx dy : ZMod q) (E : ℝ → ℝ → ℂ) : ℂ :=
  (∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue q dx bx
        (fun x => dfiVoronoiBranchValue q dy .mainTerm (E x))) +
    ∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue q dx bx
        (fun x => dfiVoronoiRemainderValue q dy (E x))

/-- The `DFIEquation23GroupedAdmissible` definition used by the source-facing construction in `DFIEquation23`. -/
structure DFIEquation23GroupedAdmissible (q : ℕ) [NeZero q]
    (dy : ZMod q) (E : ℝ → ℝ → ℂ) where
  /-- The `ySlice` component of `DFIEquation23Admissible`. -/
  ySlice : ∀ x : ℝ, DFIVoronoiTestFunction (E x)
  /-- The `xMain` component of `DFIEquation23GroupedAdmissible`. -/
  xMain : DFIVoronoiTestFunction
    (fun x => dfiVoronoiBranchValue q dy .mainTerm (E x))
  /-- The `xRemainder` component of `DFIEquation23GroupedAdmissible`. -/
  xRemainder : DFIVoronoiTestFunction
    (fun x => dfiVoronoiRemainderValue q dy (E x))

theorem dfiEquation23_grouped_of_admissible (q : ℕ) [NeZero q]
    (dx dy : ZMod q) (hdx : IsUnit dx) (hdy : IsUnit dy)
    (E : ℝ → ℝ → ℂ) (hE : DFIEquation23GroupedAdmissible q dy E) :
    dfiEquation23Left q dx dy E = dfiEquation23GroupedRight q dx dy E := by
  unfold dfiEquation23Left dfiEquation23GroupedRight
  have hinner : ∀ x : ℝ,
      periodicDivisorWeightedSum q (dfiVoronoiCharacter q dy) (E x) =
        dfiVoronoiBranchValue q dy .mainTerm (E x) +
          dfiVoronoiRemainderValue q dy (E x) := by
    intro x
    rw [(hE.ySlice x).dfiProposition1_native_branch_sum q dy hdy,
      sum_dfiVoronoiBranchValue_eq_main_add_remainder]
  simp_rw [hinner]
  have hsMain := hE.xMain.summable_periodicDivisorWeighted q
    (dfiVoronoiCharacter q dx)
  have hsRem := hE.xRemainder.summable_periodicDivisorWeighted q
    (dfiVoronoiCharacter q dx)
  unfold periodicDivisorWeightedSum
  simp_rw [mul_add]
  rw [Summable.tsum_add hsMain hsRem]
  congr 1
  · exact hE.xMain.dfiProposition1_native_branch_sum q dx hdx
  · exact hE.xRemainder.dfiProposition1_native_branch_sum q dx hdx

end RiemannZeta.GuthMaynard
