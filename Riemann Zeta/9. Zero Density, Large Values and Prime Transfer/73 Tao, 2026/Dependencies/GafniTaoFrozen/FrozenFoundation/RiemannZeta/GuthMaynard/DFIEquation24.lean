import RiemannZeta.GuthMaynard.DFIReducedModulus
import RiemannZeta.GuthMaynard.DFIBiMellin
import Mathlib.MeasureTheory.Integral.Prod

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
open scoped BigOperators ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

/-- The equation-(22) primitive-residue sum after separating the two divisor
phases, but before applying the two Voronoi formulas. -/
noncomputable def dfiEquation24PreVoronoi
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) *
      dfiEquation23SourceLeft q a b d E

/-- The exact reduced-modulus nine-branch expansion obtained by applying
the ungrouped equation (23) inside the primitive-residue sum. -/
noncomputable def dfiEquation24ReducedExpansion
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) *
      dfiEquation23ReducedRight
        (dfiReducedModulus a q).denominator
      (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))) E

/-- One of the literal nine branches in DFI equation (24), after the two
Voronoi formulas but before identifying the primitive-residue coefficient as
a Ramanujan or Kloosterman sum.  Keeping the branch pair explicit is the
source-ordered entry point for the eight error estimates in equations
(28)--(30). -/
noncomputable def dfiEquation24ReducedBranchContribution
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiBranch) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar (((-h) * (d : ℤ) : ℤ) : ZMod q) *
      dfiVoronoiBranchValue (dfiReducedModulus a q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)) xBranch
        (fun x =>
          dfiVoronoiBranchValue (dfiReducedModulus b q).denominator
            (-((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator))) yBranch (E x))

/-- Exact branchwise reindexing of the reduced equation-(24) expansion. -/
theorem dfiEquation24ReducedExpansion_eq_sum_branches
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) :
    dfiEquation24ReducedExpansion q a b h E =
      ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
        dfiEquation24ReducedBranchContribution
          q a b h xBranch yBranch E := by
  unfold dfiEquation24ReducedExpansion
    dfiEquation24ReducedBranchContribution dfiEquation23ReducedRight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro yBranch _hy
  rw [Finset.sum_comm]

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
  rw [dfiEquation23Weight_source_ungrouped
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

/-- The eight non-main branch pairs in DFI equation (24), in the same
`y`-then-`x` source order as the exact nine-branch expansion. -/
noncomputable def dfiEquation24ReducedError
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
    if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
      dfiEquation24ReducedBranchContribution
        q a b h xBranch yBranch E

/-- The main/main branch contribution is exactly the primitive Ramanujan
coefficient applied to the two Voronoi main terms. -/
theorem dfiEquation24ReducedBranchContribution_main_main
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) :
    dfiEquation24ReducedBranchContribution
        q a b h .mainTerm .mainTerm E =
      dfiEquation24MainCoefficient q h
        (dfiVoronoiMainTerm (dfiReducedModulus a q).denominator (fun x =>
          dfiVoronoiMainTerm (dfiReducedModulus b q).denominator (E x))) := by
  rfl

/-- Literal main-plus-eight-errors decomposition of DFI equation (24). -/
theorem dfiEquation24ReducedExpansion_eq_main_add_error
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) :
    dfiEquation24ReducedExpansion q a b h E =
      dfiEquation24MainCoefficient q h
          (dfiVoronoiMainTerm (dfiReducedModulus a q).denominator (fun x =>
            dfiVoronoiMainTerm (dfiReducedModulus b q).denominator (E x))) +
        dfiEquation24ReducedError q a b h E := by
  have huniv : (Finset.univ : Finset DFIVoronoiBranch) =
      {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
        DFIVoronoiBranch.plusTerm} := by
    ext branch
    fin_cases branch <;> simp
  rw [dfiEquation24ReducedExpansion_eq_sum_branches]
  rw [← dfiEquation24ReducedBranchContribution_main_main]
  unfold dfiEquation24ReducedError
  change (∑ yBranch ∈ (Finset.univ : Finset DFIVoronoiBranch),
      ∑ xBranch ∈ (Finset.univ : Finset DFIVoronoiBranch),
        dfiEquation24ReducedBranchContribution
          q a b h xBranch yBranch E) = _
  rw [huniv]
  simp
  ring

/-- Triangle-inequality reduction of the equation-(24) remainder to its
eight source branches.  Subsequent estimates may therefore treat each
single- or double-transform branch without losing or duplicating a term. -/
theorem norm_dfiEquation24ReducedError_le
    (q a b : ℕ) [NeZero q] (h : ℤ) (E : ℝ → ℝ → ℂ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
        if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
          ‖dfiEquation24ReducedBranchContribution
            q a b h xBranch yBranch E‖ := by
  unfold dfiEquation24ReducedError
  calc
    ‖∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
        if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
          dfiEquation24ReducedBranchContribution
            q a b h xBranch yBranch E‖ ≤
      ∑ yBranch : DFIVoronoiBranch,
        ‖∑ xBranch : DFIVoronoiBranch,
          if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
            dfiEquation24ReducedBranchContribution
              q a b h xBranch yBranch E‖ := norm_sum_le _ _
    _ ≤ ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
        if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
          ‖dfiEquation24ReducedBranchContribution
            q a b h xBranch yBranch E‖ := by
      apply Finset.sum_le_sum
      intro yBranch _hy
      calc
        ‖∑ xBranch : DFIVoronoiBranch,
            if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
              dfiEquation24ReducedBranchContribution
                q a b h xBranch yBranch E‖ ≤
          ∑ xBranch : DFIVoronoiBranch,
            ‖if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
              dfiEquation24ReducedBranchContribution
                q a b h xBranch yBranch E‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro xBranch _hx
          split_ifs <;> simp_all

/-- A primitive residue sum may be reindexed exactly by the units of
`ZMod q`.  This is the finite bridge used when the inverse frequencies in
DFI equation (23) are reassembled into the complete sums in equation (24). -/
theorem sum_range_coprime_eq_sum_zmod_units
    (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q), F (d : ZMod q) =
      ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  let s := (Finset.range q).filter (fun d => d.Coprime q)
  let toUnit : (d : ℕ) → d ∈ s → (ZMod q)ˣ := fun d hd =>
    ZMod.unitOfCoprime d (Finset.mem_filter.mp hd).2
  apply Finset.sum_bij toUnit
  · intro d hd
    exact Finset.mem_univ _
  · intro d₁ hd₁ d₂ hd₂ heq
    have hval := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q).val) heq
    have hd₁lt : d₁ < q := Finset.mem_range.mp (Finset.mem_filter.mp hd₁).1
    have hd₂lt : d₂ < q := Finset.mem_range.mp (Finset.mem_filter.mp hd₂).1
    simpa [toUnit, ZMod.val_natCast, Nat.mod_eq_of_lt hd₁lt,
      Nat.mod_eq_of_lt hd₂lt] using hval
  · intro u _hu
    refine ⟨(u : ZMod q).val, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩
    · apply Units.ext
      simp [toUnit]
  · intro d hd
    simp [toUnit]

/-- The exact primitive-residue coefficient occurring after multiplying the
outer delta-symbol phase by one or two inverse-frequency Voronoi phases. -/
noncomputable def dfiEquation24KloostermanCoefficient
    (q : ℕ) [NeZero q] (h : ℤ) (frequency : ZMod q) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar
      ((-h : ZMod q) * (d : ZMod q) + frequency * (d : ZMod q)⁻¹)

/-- The inverse-frequency primitive sum in DFI equation (24) is exactly the
standard complete Kloosterman sum, not merely bounded by one. -/
theorem dfiEquation24KloostermanCoefficient_eq
    (q : ℕ) [NeZero q] (h : ℤ) (frequency : ZMod q) :
    dfiEquation24KloostermanCoefficient q h frequency =
      kloostermanSumZMod q (-h : ZMod q) frequency := by
  rw [dfiEquation24KloostermanCoefficient]
  rw [sum_range_coprime_eq_sum_zmod_units q
    (fun d : ZMod q =>
      ZMod.stdAddChar ((-h : ZMod q) * d + frequency * d⁻¹))]
  unfold kloostermanSumZMod
  apply Finset.sum_congr rfl
  intro u _hu
  rw [ZMod.inv_coe_unit]

/-- One reduced inverse-frequency branch, including the outer delta-symbol
phase, reassembles to the corresponding modulus-`q` Kloosterman sum. -/
theorem dfiEquation24_reduced_inverse_coefficient_eq
    (a q dFrequency : ℕ) [NeZero q] (h : ℤ) :
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)⁻¹) *
            (dFrequency : ZMod (dfiReducedModulus a q).denominator))) =
      kloostermanSumZMod q (-h : ZMod q)
        (dfiLiftedInverseFrequency a q dFrequency) := by
  calc
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)⁻¹) *
            (dFrequency : ZMod (dfiReducedModulus a q).denominator))) =
      ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
        ZMod.stdAddChar
          ((-h : ZMod q) * (d : ZMod q) +
            dfiLiftedInverseFrequency a q dFrequency * (d : ZMod q)⁻¹) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [stdAddChar_reduced_inverse_eq_lifted a q d dFrequency
        (Finset.mem_filter.mp hd).2]
      exact (ZMod.stdAddChar.map_add_eq_mul _ _).symm
    _ = kloostermanSumZMod q (-h : ZMod q)
        (dfiLiftedInverseFrequency a q dFrequency) :=
      dfiEquation24KloostermanCoefficient_eq q h
        (dfiLiftedInverseFrequency a q dFrequency)

/-- Negative inverse-frequency version of the preceding coefficient
identity.  These two signs cover the `Y₀` and `K₀` Voronoi branches in the
paper's equation (23). -/
theorem dfiEquation24_reduced_neg_inverse_coefficient_eq
    (a q dFrequency : ℕ) [NeZero q] (h : ℤ) :
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (-(((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)⁻¹) *
            (dFrequency : ZMod (dfiReducedModulus a q).denominator)))) =
      kloostermanSumZMod q (-h : ZMod q)
        (-dfiLiftedInverseFrequency a q dFrequency) := by
  calc
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (-(((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)⁻¹) *
            (dFrequency : ZMod (dfiReducedModulus a q).denominator)))) =
      ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
        ZMod.stdAddChar
          ((-h : ZMod q) * (d : ZMod q) +
            (-dfiLiftedInverseFrequency a q dFrequency) * (d : ZMod q)⁻¹) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hpos := stdAddChar_reduced_inverse_eq_lifted
        a q d dFrequency (Finset.mem_filter.mp hd).2
      have hneg := congrArg Inv.inv hpos
      rw [← AddChar.map_neg_eq_inv
          (ZMod.stdAddChar : AddChar
            (ZMod (dfiReducedModulus a q).denominator) ℂ),
        ← AddChar.map_neg_eq_inv
          (ZMod.stdAddChar : AddChar (ZMod q) ℂ)] at hneg
      rw [hneg]
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    _ = kloostermanSumZMod q (-h : ZMod q)
        (-dfiLiftedInverseFrequency a q dFrequency) :=
      dfiEquation24KloostermanCoefficient_eq q h
        (-dfiLiftedInverseFrequency a q dFrequency)

/-- The two possible signs of an inverse-frequency Voronoi character. -/
inductive DFIVoronoiFrequencySign where
  | positive
  | negative
  deriving DecidableEq, Fintype

/-- Apply a Voronoi frequency sign in any additive group. -/
def dfiSignedFrequency {A : Type*} [AddGroup A]
    (sign : DFIVoronoiFrequencySign) (z : A) : A :=
  match sign with
  | .positive => z
  | .negative => -z

/-- The reduced inverse-frequency character lift is uniform in the two
Voronoi signs. -/
theorem stdAddChar_signed_reduced_inverse_eq_lifted
    (sign : DFIVoronoiFrequencySign)
    (a q d n : ℕ) [NeZero q] (hd : d.Coprime q) :
    ZMod.stdAddChar
        (dfiSignedFrequency sign
          (((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)⁻¹) *
            (n : ZMod (dfiReducedModulus a q).denominator))) =
      ZMod.stdAddChar
        (dfiSignedFrequency sign
          (dfiLiftedInverseFrequency a q n * (d : ZMod q)⁻¹)) := by
  cases sign
  · exact stdAddChar_reduced_inverse_eq_lifted a q d n hd
  · simp only [dfiSignedFrequency, AddChar.map_neg_eq_inv]
    exact congrArg Inv.inv (stdAddChar_reduced_inverse_eq_lifted a q d n hd)

/-- All four two-transform sign combinations in DFI equation (24) are one
complete Kloosterman sum whose second frequency is the signed sum of the two
fixed lifted frequencies. -/
theorem dfiEquation24_two_reduced_inverse_coefficients_eq
    (xSign ySign : DFIVoronoiFrequencySign)
    (a b q m n : ℕ) [NeZero q] (h : ℤ) :
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency xSign
            (((((dfiReducedModulus a q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus a q).denominator)⁻¹) *
              (m : ZMod (dfiReducedModulus a q).denominator))) *
        ZMod.stdAddChar
          (dfiSignedFrequency ySign
            (((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus b q).denominator)))) =
      kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
          dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) := by
  calc
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency xSign
            (((((dfiReducedModulus a q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus a q).denominator)⁻¹) *
              (m : ZMod (dfiReducedModulus a q).denominator))) *
        ZMod.stdAddChar
          (dfiSignedFrequency ySign
            (((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus b q).denominator)))) =
      ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
        ZMod.stdAddChar
          ((-h : ZMod q) * (d : ZMod q) +
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
                (d : ZMod q)⁻¹) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [stdAddChar_signed_reduced_inverse_eq_lifted
          xSign a q d m (Finset.mem_filter.mp hd).2,
        stdAddChar_signed_reduced_inverse_eq_lifted
          ySign b q d n (Finset.mem_filter.mp hd).2]
      rw [← ZMod.stdAddChar.map_add_eq_mul,
        ← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      cases xSign <;> cases ySign <;>
        simp only [dfiSignedFrequency, neg_mul] <;> ring
    _ = kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
          dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) :=
      dfiEquation24KloostermanCoefficient_eq q h _

/-! ## Exact nine-branch form -/

/-- Sign of the inverse frequency in the `x`-variable of DFI (23). -/
def DFIVoronoiDualBranch.xSign :
    DFIVoronoiDualBranch → DFIVoronoiFrequencySign
  | .minusTerm => .negative
  | .plusTerm => .positive

/-- Sign of the inverse frequency in the `y`-variable of DFI (23).
The source phase is `-bd/q`, so it is the reverse of the `x` sign. -/
def DFIVoronoiDualBranch.ySign :
    DFIVoronoiDualBranch → DFIVoronoiFrequencySign
  | .minusTerm => .positive
  | .plusTerm => .negative

/-- The residue-independent `n`th summand of a dual Voronoi branch. -/
noncomputable def dfiVoronoiDualTerm (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  divisorWeight n *
    match branch with
    | .minusTerm => dfiVoronoiMinusTransform q (mellin g) n
    | .plusTerm => dfiVoronoiPlusTransform q (mellin g) n

/-- A transformed Voronoi branch is its inverse additive character times a
residue-independent dual term, summed over the dual frequency. -/
theorem dfiVoronoiBranchValue_dual_eq
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) :
    dfiVoronoiBranchValue q d branch.toBranch g =
      ∑' n : ℕ,
        ZMod.stdAddChar
            (dfiSignedFrequency branch.xSign (d⁻¹ * (n : ZMod q))) *
          dfiVoronoiDualTerm q branch g n := by
  cases branch <;>
    simp only [DFIVoronoiDualBranch.toBranch,
      DFIVoronoiDualBranch.xSign, dfiSignedFrequency,
      dfiVoronoiBranchValue, dfiVoronoiDualTerm] <;>
    apply tsum_congr <;> intro n <;> ring_nf

/-- The main Voronoi branch is complex-linear in the test function. -/
theorem dfiVoronoiMainTerm_const_mul (q : ℕ) (c : ℂ) (g : ℝ → ℂ) :
    dfiVoronoiMainTerm q (fun x => c * g x) = c * dfiVoronoiMainTerm q g := by
  unfold dfiVoronoiMainTerm
  rw [show (fun x : ℝ =>
      ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (q : ℂ)) * (c * g x)) =
      fun x : ℝ => c *
        (((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant -
          2 * Complex.log (q : ℂ)) * g x) by funext x; ring,
    MeasureTheory.integral_const_mul]
  ring

/-- The Mellin transform is complex-linear in a constant multiple. -/
theorem mellin_const_mul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) :
    mellin (fun x => c * g x) z = c * mellin g z := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [show (fun x : ℝ => (x : ℂ) ^ (z - 1) * (c * g x)) =
      fun x : ℝ => c * ((x : ℂ) ^ (z - 1) * g x) by funext x; ring,
    MeasureTheory.integral_const_mul]

/-- Both Mellin--Barnes dual transforms are complex-linear in their test
function. -/
theorem dfiVoronoiDualTerm_const_mul (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (c : ℂ) (g : ℝ → ℂ) (n : ℕ) :
    dfiVoronoiDualTerm q branch (fun x => c * g x) n =
      c * dfiVoronoiDualTerm q branch g n := by
  cases branch
  · simp only [dfiVoronoiDualTerm]
    unfold dfiVoronoiMinusTransform
    simp_rw [mellin_const_mul]
    rw [show (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z *
          (c * mellin g z)) =
        fun z : ℂ => c * ((n : ℂ) ^ (-(1 - z)) *
          dfiVoronoiMinusMultiplier q z * mellin g z) by
          funext z; ring,
      verticalIntegral'_const_mul]
    ring
  · simp only [dfiVoronoiDualTerm]
    unfold dfiVoronoiPlusTransform
    simp_rw [mellin_const_mul]
    rw [show (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z *
          (c * mellin g z)) =
        fun z : ℂ => c * ((n : ℂ) ^ (-(1 - z)) *
          dfiVoronoiPlusMultiplier q z * mellin g z) by
          funext z; ring,
      verticalIntegral'_const_mul]
    ring

/-- Every source branch is complex-linear in its test function. -/
theorem dfiVoronoiBranchValue_const_mul (q : ℕ) [NeZero q]
    (d : ZMod q) (branch : DFIVoronoiBranch) (c : ℂ) (g : ℝ → ℂ) :
    dfiVoronoiBranchValue q d branch (fun x => c * g x) =
      c * dfiVoronoiBranchValue q d branch g := by
  cases branch
  · exact dfiVoronoiMainTerm_const_mul q c g
  · change dfiVoronoiBranchValue q d
        DFIVoronoiDualBranch.minusTerm.toBranch (fun x => c * g x) =
      c * dfiVoronoiBranchValue q d
        DFIVoronoiDualBranch.minusTerm.toBranch g
    rw [dfiVoronoiBranchValue_dual_eq,
      dfiVoronoiBranchValue_dual_eq]
    simp_rw [dfiVoronoiDualTerm_const_mul]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  · change dfiVoronoiBranchValue q d
        DFIVoronoiDualBranch.plusTerm.toBranch (fun x => c * g x) =
      c * dfiVoronoiBranchValue q d
        DFIVoronoiDualBranch.plusTerm.toBranch g
    rw [dfiVoronoiBranchValue_dual_eq,
      dfiVoronoiBranchValue_dual_eq]
    simp_rw [dfiVoronoiDualTerm_const_mul]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring

set_option maxHeartbeats 800000 in
/-- The two logarithmic Voronoi main operators commute on a smooth source
supported in a positive rectangle.  This is the Fubini identity needed to
turn the `x`-main/`y`-dual branches of DFI (24) into complete Kloosterman
sums; it is proved on the literal source integrals, not assumed as a
linearity interface. -/
theorem dfiVoronoiMainTerm_comm_of_rectangular_support
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) :
    dfiVoronoiMainTerm qx (fun x ↦ dfiVoronoiMainTerm qy (E x)) =
      dfiVoronoiMainTerm qy
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
  let Wx : ℝ → ℂ := fun x ↦
    (dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (qx : ℂ)
  let Wy : ℝ → ℂ := fun y ↦
    (dfiSafeLog C y : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (qy : ℂ)
  let K : ℝ × ℝ → ℂ := fun p ↦ Wx p.1 * Wy p.2 * E p.1 p.2
  have hWx : Continuous Wx := by
    dsimp [Wx]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hA)).add
      continuous_const |>.sub continuous_const
  have hWy : Continuous Wy := by
    dsimp [Wy]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hC)).add
      continuous_const |>.sub continuous_const
  have hKcont : Continuous K := by
    dsimp [K]
    exact ((hWx.comp continuous_fst).mul (hWy.comp continuous_snd)).mul
      hE.continuous
  have hKcomp : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc)
    intro p hp
    have hEne : E p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [K, hz])
    exact hSupport hEne
  have hswap := MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := fun x y ↦ K (x, y))
    (μ := MeasureTheory.volume.restrict (Set.Icc A B))
    (ν := MeasureTheory.volume.restrict (Set.Icc C D)) hKcont hKcomp
  have hySupport (x : ℝ) : Function.support (E x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2
  have hxSupport (y : ℝ) :
      Function.support (fun x ↦ E x y) ⊆ Set.Icc A B := by
    intro x hx
    exact (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hx)).1
  have hInnerXSupport : Function.support
      (fun x ↦ dfiVoronoiMainTerm qy (E x)) ⊆ Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change dfiVoronoiMainTerm qy (E x) ≠ 0 at hx
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hx
    exact hx rfl
  have hInnerYSupport : Function.support
      (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) ⊆ Set.Icc C D := by
    intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    change dfiVoronoiMainTerm qx (fun x ↦ E x y) ≠ 0 at hy
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hy
    exact hy rfl
  rw [dfiVoronoiMainTerm_eq_Icc hA qx hInnerXSupport,
    dfiVoronoiMainTerm_eq_Icc hC qy hInnerYSupport]
  simp_rw [dfiVoronoiMainTerm_eq_Icc hC qy (hySupport _),
    dfiVoronoiMainTerm_eq_Icc hA qx (hxSupport _)]
  have hKinner (x : ℝ) :
      (∫ y in Set.Icc C D, K (x, y)) =
        Wx x * ∫ y in Set.Icc C D, Wy y * E x y := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro y hy
    simp [K]
    ring
  have hKouter (y : ℝ) :
      (∫ x in Set.Icc A B, K (x, y)) =
        Wy y * ∫ x in Set.Icc A B, Wx x * E x y := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp [K]
    ring
  calc
    (qx : ℂ)⁻¹ * ∫ x in Set.Icc A B,
        Wx x *
          ((qy : ℂ)⁻¹ * ∫ y in Set.Icc C D,
            Wy y * E x y) =
        (qx : ℂ)⁻¹ * ((qy : ℂ)⁻¹ *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, K (x, y))) := by
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      rw [hKinner x]
      ring
    _ = (qx : ℂ)⁻¹ * (qy : ℂ)⁻¹ *
          (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, K (x, y)) := by
      ring
    _ = (qy : ℂ)⁻¹ * (qx : ℂ)⁻¹ *
          (∫ y in Set.Icc C D, ∫ x in Set.Icc A B, K (x, y)) := by
      rw [hswap]
      ring
    _ = (qy : ℂ)⁻¹ * ((qx : ℂ)⁻¹ *
          (∫ y in Set.Icc C D, ∫ x in Set.Icc A B, K (x, y))) := by
      ring
    _ = (qy : ℂ)⁻¹ * ∫ y in Set.Icc C D,
        Wy y *
          ((qx : ℂ)⁻¹ * ∫ x in Set.Icc A B,
            Wx x * E x y) := by
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simp only
      rw [hKouter y]
      ring

set_option maxHeartbeats 600000 in
/-- A compactly supported parameter integral commutes with the logarithmic
Voronoi main operator.  This is the reusable Fubini step behind the Mellin
and dual-branch commutation identities below. -/
theorem integral_Icc_mul_dfiVoronoiMainTerm_comm
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (w : ℝ → ℂ) (hw : Continuous w) (q : ℕ) :
    (∫ y in Set.Icc C D,
        w y * dfiVoronoiMainTerm q (fun x ↦ E x y)) =
      dfiVoronoiMainTerm q
        (fun x ↦ ∫ y in Set.Icc C D, w y * E x y) := by
  let Wq : ℝ → ℂ := fun x ↦
    (dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)
  let K : ℝ × ℝ → ℂ := fun p ↦ Wq p.1 * w p.2 * E p.1 p.2
  have hWq : Continuous Wq := by
    dsimp [Wq]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hA)).add
      continuous_const |>.sub continuous_const
  have hKcont : Continuous K := by
    dsimp [K]
    exact ((hWq.comp continuous_fst).mul (hw.comp continuous_snd)).mul
      hE.continuous
  have hKcomp : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc)
    intro p hp
    have hEne : E p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [K, hz])
    exact hSupport hEne
  have hswap := (MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := fun x y ↦ K (x, y))
    (μ := MeasureTheory.volume.restrict (Set.Icc A B))
    (ν := MeasureTheory.volume.restrict (Set.Icc C D))
    hKcont hKcomp).symm
  have hxSupport : ∀ y : ℝ,
      Function.support (fun x ↦ E x y) ⊆ Set.Icc A B := by
    intro y x hx
    exact (hSupport (show (x, y) ∈ Function.support (Function.uncurry E) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hx)).1
  have hIntegratedSupport : Function.support
      (fun x ↦ ∫ y in Set.Icc C D, w y * E x y) ⊆ Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : (fun y ↦ w y * E x y) = fun _ ↦ 0 := by
      funext y
      have hExy : E x y = 0 := by
        by_contra hne
        exact hnot (hSupport (show
          (x, y) ∈ Function.support (Function.uncurry E) by
            simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
      simp [hExy]
    change (∫ y in Set.Icc C D, w y * E x y) ≠ 0 at hx
    rw [hzero] at hx
    simp at hx
  rw [dfiVoronoiMainTerm_eq_Icc hA q hIntegratedSupport]
  simp_rw [dfiVoronoiMainTerm_eq_Icc hA q (hxSupport _)]
  have hKinner (y : ℝ) :
      (∫ x in Set.Icc A B, K (x, y)) =
        w y * ∫ x in Set.Icc A B, Wq x * E x y := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simp [K]
    ring
  have hKouter (x : ℝ) :
      (∫ y in Set.Icc C D, K (x, y)) =
        Wq x * ∫ y in Set.Icc C D, w y * E x y := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro y hy
    simp [K]
    ring
  calc
    (∫ y in Set.Icc C D,
        w y * ((q : ℂ)⁻¹ * ∫ x in Set.Icc A B, Wq x * E x y)) =
      (q : ℂ)⁻¹ *
        (∫ y in Set.Icc C D, ∫ x in Set.Icc A B, K (x, y)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simp only
      rw [hKinner y]
      ring
    _ = (q : ℂ)⁻¹ *
        (∫ x in Set.Icc A B, ∫ y in Set.Icc C D, K (x, y)) := by
      rw [hswap]
    _ = (q : ℂ)⁻¹ * ∫ x in Set.Icc A B,
        Wq x * ∫ y in Set.Icc C D, w y * E x y := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact hKouter x

/-- Compact positive support turns the Mellin transform into its literal
finite-interval integral. -/
theorem mellin_eq_Icc_of_support
    {g : ℝ → ℂ} {C D : ℝ} (hC : 0 < C)
    (hg : Function.support g ⊆ Set.Icc C D) (z : ℂ) :
    mellin g z = ∫ y in Set.Icc C D, (y : ℂ) ^ (z - 1) * g y := by
  unfold mellin
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro y hy
    exact hC.trans_le hy.1
  · intro y hy
    have hgy : g y = 0 := by
      by_contra hne
      exact hy.2 (hg hne)
    simp [hgy]

set_option maxHeartbeats 800000 in
/-- A compactly supported Mellin weight in the first variable and a
quadratically growing vertical weight in the second variable form an
absolutely integrable product kernel.  This is the Fubini input for taking
the Mellin transform of a parameterized dual Voronoi branch. -/
theorem integrable_mellinWeight_verticalMellinKernel
    {E : ℝ → ℝ → ℂ} {A B C D Cw σ : ℝ} {W : ℝ → ℂ} (z : ℂ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2) :
    MeasureTheory.Integrable
      (Function.uncurry (fun x u : ℝ ↦
        (((max A x : ℝ) : ℂ) ^ (z - 1) *
          (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)))))
      ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
        MeasureTheory.volume) := by
  let w : ℝ → ℂ := fun x ↦ ((max A x : ℝ) : ℂ) ^ (z - 1)
  let K : ℝ → ℝ → ℂ := fun x u ↦
    w x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))
  have hw : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (Complex.continuousAt_ofReal_cpow_const (max A x) (z - 1)
      (Or.inr (ne_of_gt (hA.trans_le (le_max_left A x))))).comp
        (continuousAt_const.max continuousAt_id)
  have hKmeas : MeasureTheory.StronglyMeasurable (Function.uncurry K) := by
    apply MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro u
      exact hw.mul
        (continuous_const.mul
          (contDiff_mellin_slice hE hC hSupport
            ((σ : ℂ) + (u : ℂ) * I)).continuous)
    · intro x
      exact (continuous_const.mul
        (hWcont.mul (by
          simpa only [iteratedDeriv_zero] using
            continuous_iteratedDeriv_mellin_vertical
              hE hC hCD hSupport 0 x σ))).stronglyMeasurable
  obtain ⟨Km, hKm, hDecay⟩ :=
    exists_uniform_iteratedDeriv_mellin_decay
      hE hC hCD hSupport 0 σ
  have hwInt : MeasureTheory.Integrable w
      (MeasureTheory.volume.restrict (Set.Icc A B)) :=
    hw.integrableOn_Icc
  have hTailInt : MeasureTheory.Integrable
      (fun u : ℝ ↦ Cw * Km * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using
      integrable_inv_one_add_sq.const_mul (Cw * Km)
  have hMajor : MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ ‖w p.1‖ *
        (Cw * Km * (1 + p.2 ^ 2)⁻¹))
      ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
        MeasureTheory.volume) :=
    hwInt.norm.mul_prod hTailInt
  change MeasureTheory.Integrable (Function.uncurry K)
    ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
      MeasureTheory.volume)
  apply hMajor.mono' hKmeas.aestronglyMeasurable
  filter_upwards with p
  change ‖w p.1 * (W p.2 *
      mellin (E p.1) ((σ : ℂ) + (p.2 : ℂ) * I))‖ ≤
    ‖w p.1‖ * (Cw * Km * (1 + p.2 ^ 2)⁻¹)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_mul_le_cauchy_of_quadratic_and_sixth_decay
    hCw hKm (hW p.2) (by
      simpa only [iteratedDeriv_zero] using hDecay p.1 p.2)

set_option maxHeartbeats 1000000 in
/-- Mellin transformation in the retained variable commutes with any
absolutely convergent vertical Mellin operator whose weight has the
quadratic growth occurring in the DFI Voronoi multipliers. -/
theorem mellin_verticalMellinIntegral_comm
    {E : ℝ → ℝ → ℂ} {A B C D Cw σ : ℝ} {W : ℝ → ℂ} (z : ℂ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2) :
    mellin (fun x ↦ ∫ u : ℝ,
        W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) z =
      ∫ u : ℝ, W u *
        dfiBiMellin E z ((σ : ℂ) + (u : ℂ) * I) := by
  let H : ℝ → ℂ := fun x ↦ ∫ u : ℝ,
    W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)
  let w : ℝ → ℂ := fun x ↦ ((max A x : ℝ) : ℂ) ^ (z - 1)
  have hHSupport : Function.support H ⊆ Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change H x ≠ 0 at hx
    have hIntegrandZero : (fun u : ℝ ↦
        W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) = fun _ ↦ 0 := by
      funext u
      rw [hzero]
      simp [mellin]
    rw [show H x = ∫ u : ℝ,
        W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I) by rfl,
      hIntegrandZero] at hx
    exact hx (by simp)
  have hSliceSupport (u : ℝ) : Function.support
      (fun x ↦ mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) ⊆
        Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change mellin (E x) ((σ : ℂ) + (u : ℂ) * I) ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp [mellin])
  have hwEq : ∀ x ∈ Set.Icc A B, w x = (x : ℂ) ^ (z - 1) := by
    intro x hx
    simp [w, max_eq_right hx.1]
  have hInt := integrable_mellinWeight_verticalMellinKernel
    (σ := σ) (W := W) z hE hA hC hCD hSupport hWcont hCw hW
  have hswap := MeasureTheory.integral_integral_swap hInt
  change mellin H z = _
  rw [mellin_eq_Icc_of_support hA hHSupport z]
  calc
    (∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) * H x) =
        ∫ x in Set.Icc A B, ∫ u : ℝ,
          w x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      change (x : ℂ) ^ (z - 1) * (∫ u : ℝ,
          W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) = _
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [hwEq x hx]
    _ = ∫ u : ℝ, ∫ x in Set.Icc A B,
          w x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) := by
      simpa [w] using hswap
    _ = ∫ u : ℝ, W u *
          dfiBiMellin E z ((σ : ℂ) + (u : ℂ) * I) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [show dfiBiMellin E z ((σ : ℂ) + (u : ℂ) * I) =
          ∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) *
            mellin (E x) ((σ : ℂ) + (u : ℂ) * I) by
        exact mellin_eq_Icc_of_support hA (hSliceSupport u) z]
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      rw [hwEq x hx]
      ring

set_option maxHeartbeats 800000 in
/-- Iterated Mellin transforms of a smooth function supported in a positive
rectangle commute exactly.  This is the source-order bridge used when the
two Voronoi transforms in DFI equation (24) are expanded successively. -/
theorem mellin_mellin_comm_of_rectangular_support
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (z w : ℂ) :
    mellin (fun x ↦ mellin (E x) w) z =
      mellin (fun y ↦ mellin (fun x ↦ E x y) z) w := by
  let wx : ℝ → ℂ := fun x ↦ ((max A x : ℝ) : ℂ) ^ (z - 1)
  let wy : ℝ → ℂ := fun y ↦ ((max C y : ℝ) : ℂ) ^ (w - 1)
  let K : ℝ × ℝ → ℂ := fun p ↦ wx p.1 * wy p.2 * E p.1 p.2
  have hwx : Continuous wx := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (Complex.continuousAt_ofReal_cpow_const (max A x) (z - 1)
      (Or.inr (ne_of_gt (hA.trans_le (le_max_left A x))))).comp
        (continuousAt_const.max continuousAt_id)
  have hwy : Continuous wy := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (Complex.continuousAt_ofReal_cpow_const (max C y) (w - 1)
      (Or.inr (ne_of_gt (hC.trans_le (le_max_left C y))))).comp
        (continuousAt_const.max continuousAt_id)
  have hKcont : Continuous K := by
    exact ((hwx.comp continuous_fst).mul (hwy.comp continuous_snd)).mul
      hE.continuous
  have hKcomp : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc)
    intro p hp
    have hEne : E p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [K, hz])
    exact hSupport hEne
  have hswap := MeasureTheory.integral_integral_swap_of_hasCompactSupport
    (f := fun x y ↦ K (x, y))
    (μ := MeasureTheory.volume.restrict (Set.Icc A B))
    (ν := MeasureTheory.volume.restrict (Set.Icc C D)) hKcont hKcomp
  have hySupport (x : ℝ) : Function.support (E x) ⊆ Set.Icc C D := by
    intro y hy
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2
  have hxSupport (y : ℝ) :
      Function.support (fun x ↦ E x y) ⊆ Set.Icc A B := by
    intro x hx
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hx)).1
  have hOuterX : Function.support (fun x ↦ mellin (E x) w) ⊆
      Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change mellin (E x) w ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp [mellin])
  have hOuterY : Function.support
      (fun y ↦ mellin (fun x ↦ E x y) z) ⊆ Set.Icc C D := by
    intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    change mellin (fun x ↦ E x y) z ≠ 0 at hy
    rw [hzero] at hy
    exact hy (by simp [mellin])
  rw [mellin_eq_Icc_of_support hA hOuterX z,
    mellin_eq_Icc_of_support hC hOuterY w]
  simp_rw [mellin_eq_Icc_of_support hC (hySupport _) w,
    mellin_eq_Icc_of_support hA (hxSupport _) z]
  have hwxEq : ∀ x ∈ Set.Icc A B, wx x = (x : ℂ) ^ (z - 1) := by
    intro x hx
    simp [wx, max_eq_right hx.1]
  have hwyEq : ∀ y ∈ Set.Icc C D, wy y = (y : ℂ) ^ (w - 1) := by
    intro y hy
    simp [wy, max_eq_right hy.1]
  calc
    (∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) *
        ∫ y in Set.Icc C D, (y : ℂ) ^ (w - 1) * E x y) =
      ∫ x in Set.Icc A B, ∫ y in Set.Icc C D, K (x, y) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x hx
        simp only
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro y hy
        simp only
        simp [K, hwxEq x hx, hwyEq y hy]
        ring
    _ = ∫ y in Set.Icc C D, ∫ x in Set.Icc A B, K (x, y) := hswap
    _ = ∫ y in Set.Icc C D, (y : ℂ) ^ (w - 1) *
        ∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) * E x y := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      simp only
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      simp [K, hwxEq x hx, hwyEq y hy]
      ring

/-- For a fixed Mellin point in the first variable, the resulting function
of the second variable is again an admissible compactly supported Voronoi
test function. -/
noncomputable def dfiMellinTransposeTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (z : ℂ) :
    DFIVoronoiTestFunction
      (fun y ↦ mellin (fun x ↦ E x y) z) := by
  let F : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    exact hE.comp (contDiff_snd.prodMk contDiff_fst)
  have hFSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hne : E p.2 p.1 ≠ 0 := by
      simpa [F, Function.mem_support, Function.uncurry_apply_pair] using hp
    have hs : (p.2, p.1) ∈ Function.support (Function.uncurry E) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
    exact ⟨(hSupport hs).2, (hSupport hs).1⟩
  refine {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := ?_
    support_subset := ?_ }
  · simpa [F] using contDiff_mellin_slice hF hA hFSupport z
  · intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    change mellin (fun x ↦ E x y) z ≠ 0 at hy
    rw [hzero] at hy
    exact hy (by simp [mellin])

/-- A normalized vertical Mellin--Barnes operator on the DFI line commutes
with Mellin transformation in the retained compactly supported variable. -/
theorem mellin_verticalIntegral'_comm_of_quadratic
    {E : ℝ → ℝ → ℂ} {A B C D Cw : ℝ} {F : ℂ → ℂ} (z : ℂ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hFcont : Continuous (fun u : ℝ ↦
      F (-(1 / 2 : ℂ) + (u : ℂ) * I)))
    (hCw : 0 ≤ Cw)
    (hFbound : ∀ u : ℝ,
      ‖F (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        Cw * (1 + |u|) ^ 2) :
    mellin (fun x ↦ VerticalIntegral' (fun s : ℂ ↦
        F s * mellin (E x) s) (-(1 / 2 : ℝ))) z =
      VerticalIntegral' (fun s : ℂ ↦
        F s * mellin (fun y ↦ mellin (fun x ↦ E x y) z) s)
        (-(1 / 2 : ℝ)) := by
  let W : ℝ → ℂ := fun u ↦ F (-(1 / 2 : ℂ) + (u : ℂ) * I)
  let c : ℂ := (1 / (2 * Real.pi * I) : ℂ) * I
  have hComm := mellin_verticalMellinIntegral_comm
    (σ := -(1 / 2 : ℝ)) (W := W) z hE hA hC hCD hSupport
      (by simpa [W] using hFcont) hCw (by simpa [W] using hFbound)
  have hComm' : mellin (fun x ↦ ∫ u : ℝ, W u *
      mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) z =
      ∫ u : ℝ, W u *
        dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using hComm
  have hBi (u : ℝ) :
      dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I) =
        mellin (fun y ↦ mellin (fun x ↦ E x y) z)
          (-(1 / 2 : ℂ) + (u : ℂ) * I) := by
    exact mellin_mellin_comm_of_rectangular_support
      hE hA hC hSupport z (-(1 / 2 : ℂ) + (u : ℂ) * I)
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one]
  have hLeft : mellin (fun x ↦
      (1 / (2 * Real.pi * I) : ℂ) *
        (I * ∫ u : ℝ, W u *
          mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I))) z =
      c * mellin (fun x ↦ ∫ u : ℝ, W u *
        mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) z := by
    rw [show (fun x ↦ (1 / (2 * Real.pi * I) : ℂ) *
        (I * ∫ u : ℝ, W u *
          mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I))) =
      fun x ↦ c * (∫ u : ℝ, W u *
        mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) by
          funext x
          dsimp [c]
          ring]
    exact mellin_const_mul c _ z
  change mellin (fun x ↦
      (1 / (2 * Real.pi * I) : ℂ) *
        (I * ∫ u : ℝ, W u *
          mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I))) z = _
  rw [hLeft, hComm']
  rw [show (∫ u : ℝ, W u *
      dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, W u *
        mellin (fun y ↦ mellin (fun x ↦ E x y) z)
          (-(1 / 2 : ℂ) + (u : ℂ) * I) by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [hBi u]]
  dsimp [c, W]
  ring

/-- The fixed-frequency Mellin--Barnes kernel occurring in either DFI
Voronoi transform commutes with Mellin transformation in the other
variable. -/
theorem mellin_dfiVoronoiKernelTransform_comm
    {E : ℝ → ℝ → ℂ} {A B C D Cw : ℝ} (z : ℂ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (M : ℂ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hMcont : Continuous (fun u : ℝ ↦
      M (-(1 / 2 : ℂ) + (u : ℂ) * I)))
    (hCw : 0 ≤ Cw)
    (hMbound : ∀ u : ℝ,
      ‖M (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        Cw * (1 + |u|) ^ 2) :
    mellin (fun x ↦ VerticalIntegral' (fun s : ℂ ↦
        (n : ℂ) ^ (-(1 - s)) * M s * mellin (E x) s)
        (-(1 / 2 : ℝ))) z =
      VerticalIntegral' (fun s : ℂ ↦
        (n : ℂ) ^ (-(1 - s)) * M s *
          mellin (fun y ↦ mellin (fun x ↦ E x y) z) s)
        (-(1 / 2 : ℝ)) := by
  let F : ℂ → ℂ := fun s ↦ (n : ℂ) ^ (-(1 - s)) * M s
  have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hPowCont : Continuous (fun u : ℝ ↦
      (n : ℂ) ^ (-(1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)))) := by
    have hExponent : Continuous (fun u : ℝ ↦
        -(1 - (-(1 / 2 : ℂ) + (u : ℂ) * I))) := by fun_prop
    exact hExponent.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hFcont : Continuous (fun u : ℝ ↦
      F (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
    exact hPowCont.mul hMcont
  have hPowNorm (u : ℝ) :
      ‖(n : ℂ) ^ (-(1 - (-(1 / 2 : ℂ) + (u : ℂ) * I)))‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    · norm_num
  have hFbound : ∀ u : ℝ,
      ‖F (-(1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        Cw * (1 + |u|) ^ 2 := by
    intro u
    rw [norm_mul]
    calc
      _ ≤ 1 * (Cw * (1 + |u|) ^ 2) :=
        mul_le_mul (hPowNorm u) (hMbound u) (norm_nonneg _)
          (by positivity)
      _ = _ := one_mul _
  simpa [F, mul_assoc] using
    mellin_verticalIntegral'_comm_of_quadratic z
      hE hA hC hCD hSupport hFcont hCw hFbound

/-- One residue-independent DFI dual-frequency term commutes exactly with
Mellin transformation in the other physical variable. -/
theorem mellin_dfiVoronoiDualTerm_family
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (n : ℕ) (z : ℂ) :
    mellin (fun x ↦ dfiVoronoiDualTerm q branch (E x) n) z =
      dfiVoronoiDualTerm q branch
        (fun y ↦ mellin (fun x ↦ E x y) z) n := by
  by_cases hn : n = 0
  · subst n
    simp [dfiVoronoiDualTerm, divisorWeight, mellin]
  have hScale : 0 ≤ 32 * (q : ℝ) * dfiArchimedeanScale q ^ 2 := by
    positivity
  cases branch with
  | minusTerm =>
      simp only [dfiVoronoiDualTerm]
      rw [show (fun x ↦ divisorWeight n *
          dfiVoronoiMinusTransform q (mellin (E x)) n) =
        fun x ↦ divisorWeight n *
          (VerticalIntegral' (fun s : ℂ ↦
            (n : ℂ) ^ (-(1 - s)) * dfiVoronoiMinusMultiplier q s *
              mellin (E x) s) (-(1 / 2 : ℝ))) by
            rfl]
      rw [mellin_const_mul]
      unfold dfiVoronoiMinusTransform
      congr 1
      exact mellin_dfiVoronoiKernelTransform_comm z
        hE hA hC hCD hSupport (dfiVoronoiMinusMultiplier q) n hn
        (continuous_dfiVoronoiMinusMultiplier_leftLine q) hScale
        (norm_dfiVoronoiMinusMultiplier_le q)
  | plusTerm =>
      simp only [dfiVoronoiDualTerm]
      rw [show (fun x ↦ divisorWeight n *
          dfiVoronoiPlusTransform q (mellin (E x)) n) =
        fun x ↦ divisorWeight n *
          (VerticalIntegral' (fun s : ℂ ↦
            (n : ℂ) ^ (-(1 - s)) * dfiVoronoiPlusMultiplier q s *
              mellin (E x) s) (-(1 / 2 : ℝ))) by
            rfl]
      rw [mellin_const_mul]
      unfold dfiVoronoiPlusTransform
      congr 1
      exact mellin_dfiVoronoiKernelTransform_comm z
        hE hA hC hCD hSupport (dfiVoronoiPlusMultiplier q) n hn
        (continuous_dfiVoronoiPlusMultiplier_leftLine q) hScale
        (norm_dfiVoronoiPlusMultiplier_le q)

set_option maxHeartbeats 1000000 in
/-- The Mellin transform in the first variable of an actual dual Voronoi
branch in the second variable is the absolutely convergent two-variable
Mellin integral.  This is the exact analytic bridge needed by the
double-dual terms of DFI equation (24). -/
theorem mellin_dfiVoronoiDualBranch_family
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) [NeZero q] (d : ZMod q)
    (branch : DFIVoronoiDualBranch) (z : ℂ) :
    mellin (fun x ↦ dfiVoronoiBranchValue q d branch.toBranch (E x)) z =
      ((1 / (2 * Real.pi * I) : ℂ) * I) *
        ∫ u : ℝ, dfiDualBranchVerticalWeight q d branch u *
          dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I) := by
  let G : ℝ → ℂ := fun x ↦
    dfiVoronoiBranchValue q d branch.toBranch (E x)
  let W : ℝ → ℂ := dfiDualBranchVerticalWeight q d branch
  let w : ℝ → ℂ := fun x ↦ ((max A x : ℝ) : ℂ) ^ (z - 1)
  let c : ℂ := (1 / (2 * Real.pi * I) : ℂ) * I
  have hGSupport : Function.support G ⊆ Set.Icc A B := by
    simpa [G] using
      (dfiEquation23_dualBranchTestFunction
        hE hA hAB hC hCD hSupport q d branch).support_subset
  have hwEq : ∀ x ∈ Set.Icc A B, w x = (x : ℂ) ^ (z - 1) := by
    intro x hx
    simp [w, max_eq_right hx.1]
  obtain ⟨Cw, hCw, hWeight⟩ :=
    exists_dfiDualBranchVerticalWeight_quadratic_bound q d branch
  have hInt := integrable_mellinWeight_verticalMellinKernel
    (σ := -(1 / 2 : ℝ)) (W := W) z
    hE hA hC hCD hSupport
      (by simpa [W] using
        continuous_dfiDualBranchVerticalWeight q d branch)
      hCw (by simpa [W] using hWeight)
  have hswap := MeasureTheory.integral_integral_swap hInt
  have hyTest (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := by
      intro y hy
      exact (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2 }
  have hSliceSupport (u : ℝ) : Function.support
      (fun x ↦ mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) ⊆
        Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I) ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp [mellin])
  have hPointwise (x : ℝ) : G x = c *
      (∫ u : ℝ, W u *
        mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
    change dfiVoronoiBranchValue q d branch.toBranch (E x) = _
    rw [(hyTest x).dualBranch_eq_weightedMellinIntegral q d branch]
    dsimp [c, W]
    ring
  change mellin G z = _
  rw [mellin_eq_Icc_of_support hA hGSupport z]
  change (∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) * G x) = _
  calc
    (∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) * G x) =
        c * ∫ x in Set.Icc A B, ∫ u : ℝ,
          w x * (W u *
            mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      rw [hPointwise x, hwEq x hx]
      rw [MeasureTheory.integral_const_mul]
      ring
    _ = c * ∫ u : ℝ, ∫ x in Set.Icc A B,
          w x * (W u *
            mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)) := by
      congr 1
      simpa [w, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one] using hswap
    _ = c * ∫ u : ℝ, W u *
          dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [show dfiBiMellin E z (-(1 / 2 : ℂ) + (u : ℂ) * I) =
          ∫ x in Set.Icc A B, (x : ℂ) ^ (z - 1) *
            mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I) by
        exact mellin_eq_Icc_of_support hA (hSliceSupport u) z]
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      simp only
      rw [hwEq x hx]
      ring

set_option maxHeartbeats 1000000 in
/-- Applying actual dual Voronoi branches in both variables gives the
source-ordered double vertical Mellin integral, with both `1/(2πi)`
normalizations explicit. -/
theorem dfiVoronoiDualBranch_dualBranch_eq_doubleVertical
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (dx : ZMod qx) (dy : ZMod qy)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    dfiVoronoiBranchValue qx dx xBranch.toBranch
        (fun x ↦ dfiVoronoiBranchValue qy dy yBranch.toBranch (E x)) =
      (((1 / (2 * Real.pi * I) : ℂ) * I) ^ 2) *
        ∫ u : ℝ, ∫ v : ℝ,
          dfiDualBranchVerticalWeight qx dx xBranch u *
            dfiDualBranchVerticalWeight qy dy yBranch v *
              dfiBiMellin E
                (-(1 / 2 : ℂ) + (u : ℂ) * I)
                (-(1 / 2 : ℂ) + (v : ℂ) * I) := by
  let G : ℝ → ℂ := fun x ↦
    dfiVoronoiBranchValue qy dy yBranch.toBranch (E x)
  let Wx : ℝ → ℂ := dfiDualBranchVerticalWeight qx dx xBranch
  let Wy : ℝ → ℂ := dfiDualBranchVerticalWeight qy dy yBranch
  let c : ℂ := (1 / (2 * Real.pi * I) : ℂ) * I
  have hGTest : DFIVoronoiTestFunction G :=
    dfiEquation23_dualBranchTestFunction
      hE hA hAB hC hCD hSupport qy dy yBranch
  rw [show dfiVoronoiBranchValue qx dx xBranch.toBranch G =
      (1 / (2 * Real.pi * I) : ℂ) *
        (I * ∫ u : ℝ, Wx u *
          mellin G (-(1 / 2 : ℂ) + (u : ℂ) * I)) by
    simpa [Wx] using
      hGTest.dualBranch_eq_weightedMellinIntegral qx dx xBranch]
  have hMellin (u : ℝ) :
      mellin G (-(1 / 2 : ℂ) + (u : ℂ) * I) =
        c * ∫ v : ℝ, Wy v *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (u : ℂ) * I)
            (-(1 / 2 : ℂ) + (v : ℂ) * I) := by
    simpa [G, Wy, c] using
      mellin_dfiVoronoiDualBranch_family
        hE hA hAB hC hCD hSupport qy dy yBranch
          (-(1 / 2 : ℂ) + (u : ℂ) * I)
  simp_rw [hMellin]
  have hPull : (∫ u : ℝ, Wx u *
      (c * ∫ v : ℝ, Wy v *
        dfiBiMellin E
          (-(1 / 2 : ℂ) + (u : ℂ) * I)
          (-(1 / 2 : ℂ) + (v : ℂ) * I))) =
      c * ∫ u : ℝ, ∫ v : ℝ,
        Wx u * Wy v *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (u : ℂ) * I)
            (-(1 / 2 : ℂ) + (v : ℂ) * I) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    calc
      Wx u * (c * ∫ v : ℝ, Wy v *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (u : ℂ) * I)
            (-(1 / 2 : ℂ) + (v : ℂ) * I)) =
        c * (Wx u * ∫ v : ℝ, Wy v *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (u : ℂ) * I)
              (-(1 / 2 : ℂ) + (v : ℂ) * I)) := by ring
      _ = c * ∫ v : ℝ, Wx u *
            (Wy v * dfiBiMellin E
              (-(1 / 2 : ℂ) + (u : ℂ) * I)
              (-(1 / 2 : ℂ) + (v : ℂ) * I)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = c * ∫ v : ℝ, Wx u * Wy v *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (u : ℂ) * I)
              (-(1 / 2 : ℂ) + (v : ℂ) * I) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with v
        ring
  rw [hPull]
  dsimp [c, Wx, Wy]
  ring

set_option maxHeartbeats 600000 in
/-- Mellin transformation in one variable commutes with the logarithmic
Voronoi main operator in the other variable.  The proof uses a globally
continuous positive-axis extension of the complex power and the preceding
compact Fubini theorem. -/
theorem mellin_dfiVoronoiMainTerm_comm_of_rectangular_support
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) (z : ℂ) :
    mellin (fun y ↦ dfiVoronoiMainTerm q (fun x ↦ E x y)) z =
      dfiVoronoiMainTerm q (fun x ↦ mellin (E x) z) := by
  let G : ℝ → ℂ := fun y ↦
    dfiVoronoiMainTerm q (fun x ↦ E x y)
  let w : ℝ → ℂ := fun y ↦ ((max C y : ℝ) : ℂ) ^ (z - 1)
  have hw : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (Complex.continuousAt_ofReal_cpow_const (max C y) (z - 1)
      (Or.inr (ne_of_gt (hC.trans_le (le_max_left C y))))).comp
        (continuousAt_const.max continuousAt_id)
  have hGSupport : Function.support G ⊆ Set.Icc C D := by
    intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    change dfiVoronoiMainTerm q (fun x ↦ E x y) ≠ 0 at hy
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hy
    exact hy rfl
  have hwEq : ∀ y ∈ Set.Icc C D, w y = (y : ℂ) ^ (z - 1) := by
    intro y hy
    simp [w, max_eq_right hy.1]
  calc
    mellin G z = ∫ y in Set.Icc C D, (y : ℂ) ^ (z - 1) * G y :=
      mellin_eq_Icc_of_support hC hGSupport z
    _ = ∫ y in Set.Icc C D, w y * G y := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      change (y : ℂ) ^ (z - 1) * G y = w y * G y
      rw [hwEq y hy]
    _ = dfiVoronoiMainTerm q
        (fun x ↦ ∫ y in Set.Icc C D, w y * E x y) := by
      exact integral_Icc_mul_dfiVoronoiMainTerm_comm
        hE hA hSupport w hw q
    _ = dfiVoronoiMainTerm q (fun x ↦ mellin (E x) z) := by
      congr 1
      funext x
      rw [mellin_eq_Icc_of_support hC (by
        intro y hy
        exact (hSupport (show
          (x, y) ∈ Function.support (Function.uncurry E) by
            simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2) z]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro y hy
      change w y * E x y = (y : ℂ) ^ (z - 1) * E x y
      rw [hwEq y hy]

set_option maxHeartbeats 800000 in
/-- The product kernel obtained by pairing a logarithmic Voronoi main
weight in the retained variable with one of the vertical Mellin kernels is
absolutely integrable.  This is the precise Tonelli input for commuting a
main branch with a dual branch in DFI equation (24). -/
theorem integrable_dfiVoronoiMain_verticalMellinKernel
    {E : ℝ → ℝ → ℂ} {A B C D Cw σ : ℝ} {W : ℝ → ℂ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2)
    (q : ℕ) :
    MeasureTheory.Integrable
      (Function.uncurry (fun x u : ℝ ↦
        (((dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
            2 * Complex.log (q : ℂ)) *
          (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)))))
      ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
        MeasureTheory.volume) := by
  let Wq : ℝ → ℂ := fun x ↦
    (dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)
  let K : ℝ → ℝ → ℂ := fun x u ↦
    Wq x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))
  have hWq : Continuous Wq := by
    dsimp [Wq]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hA)).add
      continuous_const |>.sub continuous_const
  have hKmeas : MeasureTheory.StronglyMeasurable (Function.uncurry K) := by
    apply MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro u
      exact hWq.mul
        (continuous_const.mul
          (contDiff_mellin_slice hE hC hSupport
            ((σ : ℂ) + (u : ℂ) * I)).continuous)
    · intro x
      exact (continuous_const.mul
        (hWcont.mul (by
          simpa only [iteratedDeriv_zero] using
            continuous_iteratedDeriv_mellin_vertical
              hE hC hCD hSupport 0 x σ))).stronglyMeasurable
  obtain ⟨Km, hKm, hDecay⟩ :=
    exists_uniform_iteratedDeriv_mellin_decay
      hE hC hCD hSupport 0 σ
  have hWqInt : MeasureTheory.Integrable Wq
      (MeasureTheory.volume.restrict (Set.Icc A B)) :=
    hWq.integrableOn_Icc
  have hTailInt : MeasureTheory.Integrable
      (fun u : ℝ ↦ Cw * Km * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using
      integrable_inv_one_add_sq.const_mul (Cw * Km)
  have hMajor : MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ ‖Wq p.1‖ *
        (Cw * Km * (1 + p.2 ^ 2)⁻¹))
      ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
        MeasureTheory.volume) :=
    hWqInt.norm.mul_prod hTailInt
  change MeasureTheory.Integrable (Function.uncurry K)
    ((MeasureTheory.volume.restrict (Set.Icc A B)).prod
      MeasureTheory.volume)
  apply hMajor.mono' hKmeas.aestronglyMeasurable
  filter_upwards with p
  change ‖Wq p.1 * (W p.2 *
      mellin (E p.1) ((σ : ℂ) + (p.2 : ℂ) * I))‖ ≤
    ‖Wq p.1‖ * (Cw * Km * (1 + p.2 ^ 2)⁻¹)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_mul_le_cauchy_of_quadratic_and_sixth_decay
    hCw hKm (hW p.2) (by
      simpa only [iteratedDeriv_zero] using hDecay p.1 p.2)

set_option maxHeartbeats 800000 in
/-- A convergent vertical Mellin integral in the second variable commutes
with the logarithmic Voronoi main operator in the first variable.  Both
orders are literal Bochner integrals, and their equality follows from the
absolute-integrability theorem above. -/
theorem verticalMellinIntegral_dfiVoronoiMainTerm_comm
    {E : ℝ → ℝ → ℂ} {A B C D Cw σ : ℝ} {W : ℝ → ℂ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2)
    (q : ℕ) :
    (∫ u : ℝ, W u * mellin
        (fun y ↦ dfiVoronoiMainTerm q (fun x ↦ E x y))
        ((σ : ℂ) + (u : ℂ) * I)) =
      dfiVoronoiMainTerm q (fun x ↦
        ∫ u : ℝ, W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) := by
  let Wq : ℝ → ℂ := fun x ↦
    (dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)
  let H : ℝ → ℂ := fun x ↦
    ∫ u : ℝ, W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)
  have hSliceSupport (u : ℝ) : Function.support
      (fun x ↦ mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) ⊆
        Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change mellin (E x) ((σ : ℂ) + (u : ℂ) * I) ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp [mellin])
  have hHSupport : Function.support H ⊆ Set.Icc A B := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change H x ≠ 0 at hx
    have hIntegrandZero : (fun u : ℝ ↦
        W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) = fun _ ↦ 0 := by
      funext u
      rw [hzero]
      simp [mellin]
    rw [show H x = ∫ u : ℝ,
        W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I) by rfl,
      hIntegrandZero] at hx
    exact hx (by simp)
  have hInt := integrable_dfiVoronoiMain_verticalMellinKernel
    (σ := σ) hE hA hC hCD hSupport hWcont hCw hW q
  have hswap := MeasureTheory.integral_integral_swap hInt
  have hPointwise (u : ℝ) :
      mellin (fun y ↦ dfiVoronoiMainTerm q (fun x ↦ E x y))
          ((σ : ℂ) + (u : ℂ) * I) =
        dfiVoronoiMainTerm q (fun x ↦
          mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) :=
    mellin_dfiVoronoiMainTerm_comm_of_rectangular_support
      hE hA hC hSupport q ((σ : ℂ) + (u : ℂ) * I)
  rw [dfiVoronoiMainTerm_eq_Icc hA q hHSupport]
  simp_rw [hPointwise]
  simp_rw [dfiVoronoiMainTerm_eq_Icc hA q (hSliceSupport _)]
  change (∫ u : ℝ, W u *
      ((q : ℂ)⁻¹ * ∫ x in Set.Icc A B,
        Wq x * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))) =
    (q : ℂ)⁻¹ * ∫ x in Set.Icc A B, Wq x * H x
  calc
    (∫ u : ℝ, W u *
        ((q : ℂ)⁻¹ * ∫ x in Set.Icc A B,
          Wq x * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))) =
      (q : ℂ)⁻¹ * ∫ u : ℝ, ∫ x in Set.Icc A B,
        Wq x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      have hRight : (∫ x in Set.Icc A B,
          Wq x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))) =
          W u * ∫ x in Set.Icc A B,
            Wq x * mellin (E x) ((σ : ℂ) + (u : ℂ) * I) := by
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x hx
        ring
      rw [hRight]
      ring
    _ = (q : ℂ)⁻¹ * ∫ x in Set.Icc A B, ∫ u : ℝ,
        Wq x * (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I)) := by
      rw [hswap]
    _ = (q : ℂ)⁻¹ * ∫ x in Set.Icc A B, Wq x * H x := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ u : ℝ, Wq x *
        (W u * mellin (E x) ((σ : ℂ) + (u : ℂ) * I))) = Wq x * H x
      rw [MeasureTheory.integral_const_mul]

/-- Applying a logarithmic Voronoi main operator in the first variable
preserves the exact test-function class in the second variable. -/
noncomputable def dfiVoronoiMainTermFamilyTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q : ℕ) :
    DFIVoronoiTestFunction
      (fun y ↦ dfiVoronoiMainTerm q (fun x ↦ E x y)) := by
  let Wq : ℝ → ℂ := fun x ↦
    (dfiSafeLog A x : ℂ) + 2 * Real.eulerMascheroniConstant -
      2 * Complex.log (q : ℂ)
  have hWq : Continuous Wq := by
    dsimp [Wq]
    exact (Complex.ofRealCLM.continuous.comp (continuous_dfiSafeLog hA)).add
      continuous_const |>.sub continuous_const
  have hxSupport (y : ℝ) :
      Function.support (fun x ↦ E x y) ⊆ Set.Icc A B := by
    intro x hx
    exact (hSupport (show
      (x, y) ∈ Function.support (Function.uncurry E) by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hx)).1
  have hEq : (fun y ↦ dfiVoronoiMainTerm q (fun x ↦ E x y)) =
      fun y ↦ (q : ℂ)⁻¹ * ∫ x in Set.Icc A B, Wq x * E x y := by
    funext y
    simpa [Wq] using dfiVoronoiMainTerm_eq_Icc hA q (hxSupport y)
  have hEswap : ContDiff ℝ ∞
      (Function.uncurry (fun y x ↦ E x y)) := by
    simpa only [Function.uncurry_apply_pair] using hE.comp
      (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.2, p.1)))
  refine {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := ?_
    support_subset := ?_ }
  · rw [hEq]
    exact contDiff_const.mul
      (contDiff_integral_Icc_right_mul_left hWq hEswap)
  · intro y hy
    by_contra hnot
    have hzero : (fun x ↦ E x y) = fun _ ↦ 0 := by
      funext x
      by_contra hne
      exact hnot (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    change dfiVoronoiMainTerm q (fun x ↦ E x y) ≠ 0 at hy
    rw [hzero, dfiVoronoiMainTerm_eq_zero] at hy
    exact hy rfl

set_option maxHeartbeats 800000 in
/-- A logarithmic main branch in one variable commutes exactly with either
dual Voronoi branch in the other variable.  This is the missing source
identity behind both mixed entries of the nine-term DFI equation (24). -/
theorem dfiVoronoiMainTerm_dualBranch_comm_of_rectangular_support
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy] (d : ZMod qy)
    (branch : DFIVoronoiDualBranch) :
    dfiVoronoiMainTerm qx (fun x ↦
        dfiVoronoiBranchValue qy d branch.toBranch (E x)) =
      dfiVoronoiBranchValue qy d branch.toBranch
        (fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)) := by
  have hxTest (x : ℝ) : DFIVoronoiTestFunction (E x) := {
    lower := C
    upper := D
    lower_pos := hC
    lower_le_upper := hCD
    smooth := hE.comp (contDiff_prodMk_right x)
    support_subset := by
      intro y hy
      exact (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy)).2 }
  let G : ℝ → ℂ := fun y ↦ dfiVoronoiMainTerm qx (fun x ↦ E x y)
  let H : ℝ → ℂ := fun x ↦ ∫ u : ℝ,
    dfiDualBranchVerticalWeight qy d branch u *
      mellin (E x) (-(1 / 2 : ℂ) + (u : ℂ) * I)
  let c : ℂ := 1 / (2 * Real.pi * I)
  obtain ⟨Cw, hCw, hWeight⟩ :=
    exists_dfiDualBranchVerticalWeight_quadratic_bound qy d branch
  have hComm : (∫ u : ℝ,
      dfiDualBranchVerticalWeight qy d branch u *
        mellin G (-(1 / 2 : ℂ) + (u : ℂ) * I)) =
      dfiVoronoiMainTerm qx H := by
    simpa [G, H, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one] using
      verticalMellinIntegral_dfiVoronoiMainTerm_comm
        (σ := -(1 / 2 : ℝ)) hE hA hC hCD hSupport
        (continuous_dfiDualBranchVerticalWeight qy d branch)
        hCw hWeight qx
  have hLeft :
      dfiVoronoiMainTerm qx (fun x ↦
          dfiVoronoiBranchValue qy d branch.toBranch (E x)) =
        (c * I) * dfiVoronoiMainTerm qx H := by
    have hFun : (fun x ↦
        dfiVoronoiBranchValue qy d branch.toBranch (E x)) =
        fun x ↦ (c * I) * H x := by
      funext x
      rw [(hxTest x).dualBranch_eq_weightedMellinIntegral qy d branch]
      change c * (I * H x) = (c * I) * H x
      ring
    rw [hFun, dfiVoronoiMainTerm_const_mul]
  have hGTest : DFIVoronoiTestFunction G := by
    exact dfiVoronoiMainTermFamilyTestFunction
      hE hA hC hCD hSupport qx
  have hRight :
      dfiVoronoiBranchValue qy d branch.toBranch G =
        (c * I) * dfiVoronoiMainTerm qx H := by
    rw [hGTest.dualBranch_eq_weightedMellinIntegral qy d branch]
    change c * (I * ∫ u : ℝ,
        dfiDualBranchVerticalWeight qy d branch u *
          mellin G (-(1 / 2 : ℂ) + (u : ℂ) * I)) =
      (c * I) * dfiVoronoiMainTerm qx H
    rw [hComm]
    ring
  exact hLeft.trans hRight.symm
/-- The normalized vertical integral is bounded by the integral of the
pointwise norm. -/
theorem norm_verticalIntegral'_le_integral_norm (f : ℂ → ℂ) (σ : ℝ) :
    ‖VerticalIntegral' f σ‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ∫ u : ℝ, ‖f ((σ : ℂ) + (u : ℂ) * I)‖ := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I, one_mul]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (f := fun u : ℝ => f ((σ : ℂ) + (u : ℂ) * I))) (norm_nonneg _)

/-- Absolute summability of either residue-independent dual Voronoi series.
This is the Tonelli input needed to interchange the primitive residue sum
with the dual frequency sum in equation (24). -/
theorem summable_norm_dfiVoronoiDualTerm (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) :
    Summable (fun n : ℕ => ‖dfiVoronoiDualTerm q branch g n‖) := by
  let Φ : ZMod q → ℂ := fun _ => 1
  let M : ℂ → ℂ := match branch with
    | .minusTerm => dfiVoronoiMinusMultiplier q
    | .plusTerm => dfiVoronoiPlusMultiplier q
  have hsum := summable_integral_norm_dfiVoronoiMellinTerm q Φ M g
  have hscaled : Summable (fun n : ℕ =>
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ∫ u : ℝ, ‖dfiVoronoiMellinTerm q Φ M g n u‖) :=
    hsum.mul_left _
  apply Summable.of_norm_bounded hscaled
  intro n
  rw [Real.norm_eq_abs, abs_norm]
  have hvertical := norm_verticalIntegral'_le_integral_norm
    (fun z : ℂ => LSeries.term (periodicDivisorCoeff q Φ) (1 - z) n *
      (M z * mellin g z)) (-(1 / 2 : ℝ))
  rw [verticalIntegral_dfiVoronoiMellinTerm q Φ M g n] at hvertical
  have hterm : periodicDivisorCoeff q Φ n *
      VerticalIntegral' (fun z : ℂ =>
        (n : ℂ) ^ (-(1 - z)) * M z * mellin g z) (-(1 / 2 : ℝ)) =
      dfiVoronoiDualTerm q branch g n := by
    cases branch <;>
      simp [Φ, M, periodicDivisorCoeff, divisorWeight,
        dfiVoronoiDualTerm, dfiVoronoiMinusTransform,
        dfiVoronoiPlusTransform]
  rw [hterm] at hvertical
  simpa [dfiVoronoiMellinTerm] using hvertical

/-- The single transformed `x`-branch before summing the primitive residue
in DFI equation (24). -/
noncomputable def dfiEquation24XDualContribution
    (q a : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
      dfiVoronoiBranchValue (dfiReducedModulus a q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)) branch.toBranch g

/-- The single transformed `x`-branch of equation (24), with the primitive
residue sum evaluated as the exact complete Kloosterman sum. -/
theorem dfiEquation24XDualContribution_eq
    (q a : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    dfiEquation24XDualContribution q a h branch g =
      ∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency branch.xSign
              (dfiLiftedInverseFrequency a q n)) *
          dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n := by
  unfold dfiEquation24XDualContribution
  simp_rw [dfiVoronoiBranchValue_dual_eq]
  simp_rw [← tsum_mul_left]
  let s := (Finset.range q).filter (fun d => d.Coprime q)
  have hsummable : ∀ d ∈ s, Summable (fun n : ℕ =>
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar
            (dfiSignedFrequency branch.xSign
              (((((dfiReducedModulus a q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus a q).denominator)⁻¹) *
                (n : ZMod (dfiReducedModulus a q).denominator))) *
          dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n)) := by
    intro d hd
    have hnorm := summable_norm_dfiVoronoiDualTerm
      (dfiReducedModulus a q).denominator branch g
    apply Summable.of_norm_bounded hnorm
    intro n
    simp
  change (∑ d ∈ s, ∑' n : ℕ,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar
            (dfiSignedFrequency branch.xSign
              (((((dfiReducedModulus a q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus a q).denominator)⁻¹) *
                (n : ZMod (dfiReducedModulus a q).denominator))) *
          dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n)) = _
  rw [← Summable.tsum_finsetSum hsummable]
  apply tsum_congr
  intro n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ d ∈ s,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency branch.xSign
            (((((dfiReducedModulus a q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus a q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus a q).denominator)))) =
      kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency branch.xSign
          (dfiLiftedInverseFrequency a q n)) by
      simpa [s, dfiLiftedInverseFrequency, dfiSignedFrequency] using
        dfiEquation24_two_reduced_inverse_coefficients_eq
          branch.xSign DFIVoronoiFrequencySign.positive
          a 0 q n 0 h]

/-- The `x`-dual/`y`-main member of the literal nine-branch expansion is
exactly the single-frequency contribution above.  This is the first of the
eight source error branches in DFI (24), with no estimate or interchange
hidden in the identification. -/
theorem dfiEquation24ReducedBranchContribution_dual_main
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (branch : DFIVoronoiDualBranch) (E : ℝ → ℝ → ℂ) :
    dfiEquation24ReducedBranchContribution
        q a b h branch.toBranch .mainTerm E =
      dfiEquation24XDualContribution q a h branch
        (fun x ↦ dfiVoronoiMainTerm
          (dfiReducedModulus b q).denominator (E x)) := by
  unfold dfiEquation24ReducedBranchContribution
    dfiEquation24XDualContribution
  apply Finset.sum_congr rfl
  intro d hd
  congr 2
  push_cast
  ring

/-- Negating the source additive phase reverses the two Voronoi frequency
signs.  This is the sign convention in the `y`-variable of DFI (23). -/
theorem dfiVoronoiDualBranch_negative_source_character
    (q : ℕ) [NeZero q] (d : ZMod q)
    (hd : IsUnit d) (branch : DFIVoronoiDualBranch) (n : ℕ) :
    ZMod.stdAddChar
        (dfiSignedFrequency branch.xSign ((-d)⁻¹ * (n : ZMod q))) =
      ZMod.stdAddChar
        (dfiSignedFrequency branch.ySign (d⁻¹ * (n : ZMod q))) := by
  have hinv : (-d)⁻¹ = -(d⁻¹) := by
    apply ZMod.inv_eq_of_mul_eq_one q
    calc
      (-d) * -(d⁻¹) = d * d⁻¹ := by ring
      _ = 1 := ZMod.mul_inv_of_unit d hd
  rw [hinv]
  cases branch <;>
    simp [DFIVoronoiDualBranch.xSign, DFIVoronoiDualBranch.ySign,
      dfiSignedFrequency]

/-- The single transformed `y`-branch before summing the primitive residue
in DFI equation (24). -/
noncomputable def dfiEquation24YDualContribution
    (q b : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) : ℂ :=
  ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
    ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
      dfiVoronoiBranchValue (dfiReducedModulus b q).denominator
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))) branch.toBranch g

/-- The single transformed `y`-branch of equation (24), with its reversed
source sign and exact complete Kloosterman coefficient. -/
theorem dfiEquation24YDualContribution_eq
    (q b : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    dfiEquation24YDualContribution q b h branch g =
      ∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency branch.ySign
              (dfiLiftedInverseFrequency b q n)) *
          dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n := by
  unfold dfiEquation24YDualContribution
  rw [show (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        dfiVoronoiBranchValue (dfiReducedModulus b q).denominator
          (-((((dfiReducedModulus b q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus b q).denominator))) branch.toBranch g) =
      ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
        ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
          ∑' n : ℕ,
            ZMod.stdAddChar
                (dfiSignedFrequency branch.ySign
                  (((((dfiReducedModulus b q).numerator * d : ℕ) :
                    ZMod (dfiReducedModulus b q).denominator)⁻¹) *
                    (n : ZMod (dfiReducedModulus b q).denominator))) *
              dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
                branch g n by
      apply Finset.sum_congr rfl
      intro d hd
      rw [dfiVoronoiBranchValue_dual_eq]
      congr 1
      apply tsum_congr
      intro n
      rw [dfiVoronoiDualBranch_negative_source_character
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))
        (dfiReducedModulus_frequency_isUnit b q d
          (Finset.mem_filter.mp hd).2) branch n]]
  simp_rw [← tsum_mul_left]
  let s := (Finset.range q).filter (fun d => d.Coprime q)
  have hsummable : ∀ d ∈ s, Summable (fun n : ℕ =>
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar
            (dfiSignedFrequency branch.ySign
              (((((dfiReducedModulus b q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus b q).denominator)⁻¹) *
                (n : ZMod (dfiReducedModulus b q).denominator))) *
          dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n)) := by
    intro d hd
    have hnorm := summable_norm_dfiVoronoiDualTerm
      (dfiReducedModulus b q).denominator branch g
    apply Summable.of_norm_bounded hnorm
    intro n
    simp
  change (∑ d ∈ s, ∑' n : ℕ,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        (ZMod.stdAddChar
            (dfiSignedFrequency branch.ySign
              (((((dfiReducedModulus b q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus b q).denominator)⁻¹) *
                (n : ZMod (dfiReducedModulus b q).denominator))) *
          dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n)) = _
  rw [← Summable.tsum_finsetSum hsummable]
  apply tsum_congr
  intro n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ d ∈ s,
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency branch.ySign
            (((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus b q).denominator)))) =
      kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency branch.ySign
          (dfiLiftedInverseFrequency b q n)) by
      simpa [s, dfiLiftedInverseFrequency, dfiSignedFrequency] using
        dfiEquation24_two_reduced_inverse_coefficients_eq
          DFIVoronoiFrequencySign.positive branch.ySign
          0 b q 0 n h]

/-- The `x`-main/`y`-dual member of the literal nine-branch expansion is
exactly the single-frequency `y` contribution.  The proof uses the genuine
main/dual Fubini theorem above for each primitive residue. -/
theorem dfiEquation24ReducedBranchContribution_main_dual
    {A B C D : ℝ} (q a b : ℕ) [NeZero q] (h : ℤ)
    (branch : DFIVoronoiDualBranch) (E : ℝ → ℝ → ℂ)
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    dfiEquation24ReducedBranchContribution
        q a b h .mainTerm branch.toBranch E =
      dfiEquation24YDualContribution q b h branch
        (fun y ↦ dfiVoronoiMainTerm
          (dfiReducedModulus a q).denominator (fun x ↦ E x y)) := by
  unfold dfiEquation24ReducedBranchContribution
    dfiEquation24YDualContribution
  apply Finset.sum_congr rfl
  intro d hd
  have hPhase : ZMod.stdAddChar
      (((-h) * (d : ℤ) : ℤ) : ZMod q) =
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) := by
    congr 1
    push_cast
    ring
  rw [hPhase]
  congr 1
  change dfiVoronoiMainTerm (dfiReducedModulus a q).denominator
      (fun x ↦ dfiVoronoiBranchValue
        (dfiReducedModulus b q).denominator
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator)))
        branch.toBranch (E x)) = _
  exact dfiVoronoiMainTerm_dualBranch_comm_of_rectangular_support
    hE hA hC hCD hSupport
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator
    (-((((dfiReducedModulus b q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus b q).denominator))) branch

/-- A finite rectangular truncation of one of the four double-transform
branches in DFI equation (24).  The amplitude is the iterated pair of
residue-independent Voronoi transforms; all primitive-residue dependence is
kept in the two displayed additive characters. -/
noncomputable def dfiEquation24FiniteDualDualContribution
    (q a b M N : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range N,
    ∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency xBranch.xSign
            (((((dfiReducedModulus a q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus a q).denominator)⁻¹) *
              (m : ZMod (dfiReducedModulus a q).denominator))) *
        ZMod.stdAddChar
          (dfiSignedFrequency yBranch.ySign
            (((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus b q).denominator))) *
      dfiVoronoiDualTerm (dfiReducedModulus a q).denominator xBranch
        (fun x => dfiVoronoiDualTerm
          (dfiReducedModulus b q).denominator yBranch (E x) n) m

/-- Exact finite double-transform part of DFI equation (24).  This proves
all four sign combinations at once and records the precise lifted frequency
`±ā m ± b̄ n` in the complete Kloosterman sum. -/
theorem dfiEquation24FiniteDualDualContribution_eq
    (q a b M N : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) (E : ℝ → ℝ → ℂ) :
    dfiEquation24FiniteDualDualContribution
        q a b M N h xBranch yBranch E =
      ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range N,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xBranch.xSign
                (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency yBranch.ySign
                (dfiLiftedInverseFrequency b q n)) *
          dfiVoronoiDualTerm (dfiReducedModulus a q).denominator xBranch
            (fun x => dfiVoronoiDualTerm
              (dfiReducedModulus b q).denominator yBranch (E x) n) m := by
  unfold dfiEquation24FiniteDualDualContribution
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_mul]
  rw [dfiEquation24_two_reduced_inverse_coefficients_eq]

/-! ## Infinite double-frequency reassembly -/

/-- The full, iterated dual-frequency contribution before the primitive
residue sum has been evaluated.  The order of the two `tsum`s is the source
order in DFI (24): the `y`-Voronoi frequency is introduced first and the
`x`-Voronoi frequency second. -/
noncomputable def dfiEquation24DualDualPrimitive
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ) : ℂ :=
  ∑' m : ℕ, ∑' n : ℕ,
    (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
      ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
        ZMod.stdAddChar
          (dfiSignedFrequency xSign
            (((((dfiReducedModulus a q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus a q).denominator)⁻¹) *
              (m : ZMod (dfiReducedModulus a q).denominator))) *
        ZMod.stdAddChar
          (dfiSignedFrequency ySign
            (((((dfiReducedModulus b q).numerator * d : ℕ) :
              ZMod (dfiReducedModulus b q).denominator)⁻¹) *
              (n : ZMod (dfiReducedModulus b q).denominator)))) *
      amplitude m n

/-- The full DFI-(24) double-frequency expression after evaluating the
primitive residue sum as one complete Kloosterman sum. -/
noncomputable def dfiEquation24DualDualKloosterman
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ) : ℂ :=
  ∑' m : ℕ, ∑' n : ℕ,
    kloostermanSumZMod q (-h : ZMod q)
        (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
          dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
      amplitude m n

/-- Exact infinite version of the finite Kloosterman reassembly above.
No convergence hypothesis is needed for this identity because no infinite
sum is reordered: both sides use the same source-ordered iterated sums and
the equality is proved term by term. -/
theorem dfiEquation24DualDualPrimitive_eq_kloosterman
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ) :
    dfiEquation24DualDualPrimitive q a b h xSign ySign amplitude =
      dfiEquation24DualDualKloosterman q a b h xSign ySign amplitude := by
  unfold dfiEquation24DualDualPrimitive dfiEquation24DualDualKloosterman
  apply tsum_congr
  intro m
  apply tsum_congr
  intro n
  calc
    _ = (∑ d ∈ (Finset.range q).filter (fun d => d.Coprime q),
        ZMod.stdAddChar ((-h : ZMod q) * (d : ZMod q)) *
          ZMod.stdAddChar
            (dfiSignedFrequency xSign
              (((((dfiReducedModulus a q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus a q).denominator)⁻¹) *
                (m : ZMod (dfiReducedModulus a q).denominator))) *
          ZMod.stdAddChar
            (dfiSignedFrequency ySign
              (((((dfiReducedModulus b q).numerator * d : ℕ) :
                ZMod (dfiReducedModulus b q).denominator)⁻¹) *
                (n : ZMod (dfiReducedModulus b q).denominator)))) *
        amplitude m n := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [dfiEquation24_two_reduced_inverse_coefficients_eq]

end RiemannZeta.GuthMaynard
