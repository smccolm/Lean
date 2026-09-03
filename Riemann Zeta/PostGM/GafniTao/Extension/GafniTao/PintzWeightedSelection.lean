import GafniTao.PintzGramBound
import GafniTao.LocalZeroCount
import RiemannZeta.GuthMaynard.LargeValuesFinal

/-!
# Multiplicity-safe selection for Pintz equation (4.11)

The source first displaces each zero ordinate by at most `2 lambda`, then
extracts a `5 lambda`-separated family.  The lemmas below perform those two
operations while retaining every input weight, so they can be applied to
analytic zero multiplicities rather than merely to distinct ordinates.
-/

open Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Weighted form of bounded-displacement reseparation.  The output is a
set of shifted ordinates; weights in every fibre are retained in the stated
cardinality loss. -/
theorem exists_oneSeparated_shifted_weighted
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate shift : α → ℝ)
    {H : ℝ} (L : ℕ)
    (hShift : ∀ x ∈ S, |ordinate x - shift x| ≤ H)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter
          (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L) :
    ∃ W ⊆ S.image shift, IsSeparated 1 W ∧
      ∑ x ∈ S, weight x ≤
        2 * ((2 * Nat.ceil H + 1) * L) * W.card := by
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ x ∈ S.filter (fun y => shift y = u), weight x
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (S.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1),
        shiftedWeight u ≤ (2 * Nat.ceil H + 1) * L := by
    intro z
    simpa only [shiftedWeight] using
      shifted_bin_weight_le_of_unit_bin_weight S weight ordinate shift H L
        hShift hLocal z
  obtain ⟨W, hW, hSep, hWeight⟩ :=
    weighted_separated_selection (S.image shift) shiftedWeight
      ((2 * Nat.ceil H + 1) * L) hLocalShifted
  have hAll : S.filter (fun x => shift x ∈ S.image shift) = S := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S (S.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ S.image shift, shiftedWeight u = ∑ x ∈ S, weight x := by
    simpa only [shiftedWeight] using hFiber
  refine ⟨W, hW, hSep, ?_⟩
  rw [← hTotal]
  exact hWeight

/-- Pintz equation (4.11) as a finite weighted selection theorem.  The first
factor is the displacement/local-zero loss and the second is the explicit
one-dimensional cost of passing from unit separation to `G` separation. -/
theorem exists_pintz_scaledSeparated_shifted_weighted
    {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate shift : α → ℝ)
    {H G : ℝ} (hG : 0 < G) (L : ℕ)
    (hShift : ∀ x ∈ S, |ordinate x - shift x| ≤ H)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter
          (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L) :
    ∃ W ⊆ S.image shift, IsSeparated G W ∧
      ∑ x ∈ S, weight x ≤
        (2 * ((2 * Nat.ceil H + 1) * L)) *
          (2 * (2 * Nat.ceil G + 1)) * W.card := by
  obtain ⟨U, hU, hUSep, hUWeight⟩ :=
    exists_oneSeparated_shifted_weighted S weight ordinate shift L
      hShift hLocal
  obtain ⟨W, hWU, hWSep, hUCard⟩ :=
    exists_dilated_separated_subset hG hUSep
  refine ⟨W, fun x hx => hU (hWU hx), hWSep, ?_⟩
  calc
    ∑ x ∈ S, weight x ≤
        2 * ((2 * Nat.ceil H + 1) * L) * U.card := hUWeight
    _ ≤ (2 * ((2 * Nat.ceil H + 1) * L)) *
        (2 * (2 * Nat.ceil G + 1) * W.card) := by
          gcongr
    _ = (2 * ((2 * Nat.ceil H + 1) * L)) *
          (2 * (2 * Nat.ceil G + 1)) * W.card := by ring

/-- Equation (4.11) specialized to the actual symmetric, multiplicity-weighted
zeta-zero set.  The selector may depend on the complete complex zero, so
zeros sharing an ordinate and multiple copies are not silently identified. -/
theorem exists_pintz_zero_selection
    {sigma T H G : ℝ} (shift : ℂ → ℝ)
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G)
    (hShift : ∀ rho ∈ zeroSet sigma T, |rho.im - shift rho| ≤ H) :
    ∃ W ⊆ (zeroSet sigma T).image shift, IsSeparated G W ∧
      zeroCount sigma T ≤
        (2 * ((2 * Nat.ceil H + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T))) *
        (2 * (2 * Nat.ceil G + 1)) * W.card := by
  let L : ℕ := Nat.ceil (globalLocalZeroLogConstant * Real.log T)
  have hLogNonneg : 0 ≤ Real.log T := by
    have hTone : 1 ≤ T := by
      calc
        (1 : ℝ) ≤ Real.exp 2 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by norm_num)
        _ ≤ max (Real.exp 2) 8 := le_max_left _ _
        _ ≤ T := hT
    exact Real.log_nonneg hTone
  have hMajorantNonneg :
      0 ≤ globalLocalZeroLogConstant * Real.log T :=
    mul_nonneg globalLocalZeroLogConstant_pos.le hLogNonneg
  have hLocal : ∀ z : ℤ,
      ∑ rho ∈ (zeroSet sigma T).filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho ≤ L := by
    intro z
    have hReal := zeroLocalUnitBin_multiplicity_le_global_log
      sigma T z hsigma hT
    have hCeil : globalLocalZeroLogConstant * Real.log T ≤ (L : ℝ) := by
      exact Nat.le_ceil _
    have hCast :
        ((∑ rho ∈ (zeroSet sigma T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact hReal.trans hCeil
    exact_mod_cast hCast
  obtain ⟨W, hW, hSep, hWeight⟩ :=
    exists_pintz_scaledSeparated_shifted_weighted
      (zeroSet sigma T) zeroMultiplicity Complex.im shift hG L hShift hLocal
  refine ⟨W, hW, hSep, ?_⟩
  rw [zeroCount_eq_weighted_sum]
  simpa only [L] using hWeight

#print axioms exists_oneSeparated_shifted_weighted
#print axioms exists_pintz_scaledSeparated_shifted_weighted
#print axioms exists_pintz_zero_selection

end

end GafniTao
