import GafniTao.Pintz2023VariableLocalization
import GafniTao.PintzWeightedSelection
import GafniTao.LocalZeroCount

/-!
# Pintz (2023), equations (4.9)--(4.12): dependent zero selection

This is the multiplicity-safe selection theorem for the source polynomial
whose real exponent depends on the detected zero.  A representative zero is
retained over every selected displaced ordinate, so the later Halasz argument
receives the actual distance `1-rho.re` rather than a fixed surrogate.
-/

open Finset

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Weighted, displaced, separated selection for the literal equation-(4.12)
polynomial with its zero-dependent real exponent. -/
theorem exists_pintz2023_zero_detected_variable_selection_subset
    {xi T H G V lambda : ℝ} {X Y : ℕ} (S : Finset ℂ)
    (hS : S ⊆ zeroSet (1 - xi) T)
    (hsigma : 0 ≤ 1 - xi)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G)
    (hDetected : ∀ rho ∈ S,
      ∃ u : ℝ, |rho.im - u| ≤ H ∧
        V ≤ ‖pintz2023TruncatedPolynomial X Y
          (1 - (1 - rho.re) + 1 / lambda) u‖) :
    ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
      IsSeparated G W ∧
      (∑ rho ∈ S, zeroMultiplicity rho) ≤
        (2 * ((2 * Nat.ceil H + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T))) *
        (2 * (2 * Nat.ceil G + 1)) * W.card ∧
      (∀ u ∈ W, etaAt u ∈ Set.Icc 0 xi) ∧
      (∀ u ∈ W, |u| ≤ T + H) ∧
      ∀ u ∈ W,
        V ≤ ‖pintz2023TruncatedPolynomial X Y
          (1 - etaAt u + 1 / lambda) u‖ := by
  classical
  let shift : ℂ → ℝ := fun rho =>
    if hrho : rho ∈ S then Classical.choose (hDetected rho hrho)
    else rho.im
  have hShift : ∀ rho ∈ S, |rho.im - shift rho| ≤ H := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hDetected rho hrho)).1
  have hLargeShift : ∀ rho ∈ S,
      V ≤ ‖pintz2023TruncatedPolynomial X Y
        (1 - (1 - rho.re) + 1 / lambda) (shift rho)‖ := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hDetected rho hrho)).2
  let L : ℕ := Nat.ceil (globalLocalZeroLogConstant * Real.log T)
  have hLocal : ∀ z : ℤ,
      ∑ rho ∈ S.filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho ≤ L := by
    intro z
    have hSub :
        S.filter (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) ⊆
          (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) := by
      intro rho hrho
      rw [Finset.mem_filter] at hrho ⊢
      exact ⟨hS hrho.1, hrho.2⟩
    have hSum :
        ∑ rho ∈ S.filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤
        ∑ rho ∈ (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSub
      intro rho hrho hnot
      exact Nat.zero_le _
    have hFullReal := zeroLocalUnitBin_multiplicity_le_global_log
      (1 - xi) T z hsigma hT
    change
      ((∑ rho ∈ (zeroSet (1 - xi) T).filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho : ℕ) : ℝ) ≤
        globalLocalZeroLogConstant * Real.log T at hFullReal
    have hCeil : globalLocalZeroLogConstant * Real.log T ≤ (L : ℝ) :=
      Nat.le_ceil _
    have hFull :
        ∑ rho ∈ (zeroSet (1 - xi) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤ L := by
      exact_mod_cast hFullReal.trans hCeil
    exact hSum.trans hFull
  obtain ⟨W, hW, hSep, hCount⟩ :=
    exists_pintz_scaledSeparated_shifted_weighted
      S zeroMultiplicity Complex.im shift hG L hShift hLocal
  have hPreimage : ∀ u ∈ W, ∃ rho ∈ S, shift rho = u := by
    intro u hu
    exact Finset.mem_image.mp (hW hu)
  let source : ℝ → ℂ := fun u =>
    if hu : u ∈ W then Classical.choose (hPreimage u hu) else 0
  let etaAt : ℝ → ℝ := fun u => 1 - (source u).re
  have hSourceMem : ∀ u ∈ W, source u ∈ S := by
    intro u hu
    dsimp only [source]
    rw [dif_pos hu]
    exact (Classical.choose_spec (hPreimage u hu)).1
  have hSourceShift : ∀ u ∈ W, shift (source u) = u := by
    intro u hu
    dsimp only [source]
    rw [dif_pos hu]
    exact (Classical.choose_spec (hPreimage u hu)).2
  have hEtaRange : ∀ u ∈ W, etaAt u ∈ Set.Icc 0 xi := by
    intro u hu
    have hrho := hS (hSourceMem u hu)
    change source u ∈ zerosInRect (1 - xi) 1 (-T) T at hrho
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrho
    dsimp only [etaAt]
    exact ⟨by linarith [hrho.1.2.1], by linarith [hrho.1.1]⟩
  have hHeight : ∀ u ∈ W, |u| ≤ T + H := by
    intro u hu
    have hrho := hS (hSourceMem u hu)
    change source u ∈ zerosInRect (1 - xi) 1 (-T) T at hrho
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrho
    have him : |(source u).im| ≤ T :=
      abs_le.mpr ⟨hrho.1.2.2.1, hrho.1.2.2.2⟩
    have hdisp := hShift (source u) (hSourceMem u hu)
    rw [hSourceShift u hu] at hdisp
    calc
      |u| = |(source u).im - ((source u).im - u)| := by ring_nf
      _ ≤ |(source u).im| + |(source u).im - u| := abs_sub _ _
      _ ≤ T + H := add_le_add him hdisp
  have hLarge : ∀ u ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y
        (1 - etaAt u + 1 / lambda) u‖ := by
    intro u hu
    have h := hLargeShift (source u) (hSourceMem u hu)
    rw [hSourceShift u hu] at h
    simpa only [etaAt] using h
  exact ⟨W, etaAt, hSep, hCount, hEtaRange, hHeight, hLarge⟩

#print axioms exists_pintz2023_zero_detected_variable_selection_subset

end

end GafniTao
