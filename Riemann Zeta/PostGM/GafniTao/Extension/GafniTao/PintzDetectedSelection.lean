import GafniTao.PintzZetaWindow

/-!
# Selecting Pintz-detected zeta zeros

This is the source-facing consumer of equations (4.9)--(4.11).  A detected
ordinate is chosen for every actual zeta zero, after which the weighted local
zero count and separation argument retain both the detector lower bound and
the analytic multiplicity of the original zero family.
-/

open Finset

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Multiplicity-safe assembly of the pointwise detector and Pintz's
separation step.  The hypothesis is the literal pointwise output of equation
(4.9), not a cardinality estimate or a copy of the conclusion. -/
theorem exists_pintz_zero_detected_selection
    {sigma T H G xi V : ℝ} {Y : ℕ}
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G)
    (hDetected : ∀ rho ∈ zeroSet sigma T,
      ∃ u : ℝ, |rho.im - u| ≤ H ∧
        V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖) :
    ∃ W : Finset ℝ, IsSeparated G W ∧
      zeroCount sigma T ≤
        (2 * ((2 * Nat.ceil H + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T))) *
        (2 * (2 * Nat.ceil G + 1)) * W.card ∧
      ∀ u ∈ W, V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖ := by
  let shift : ℂ → ℝ := fun rho =>
    if h : rho ∈ zeroSet sigma T then Classical.choose (hDetected rho h)
    else rho.im
  have hShift : ∀ rho ∈ zeroSet sigma T,
      |rho.im - shift rho| ≤ H := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hDetected rho hrho)).1
  have hLargeShift : ∀ rho ∈ zeroSet sigma T,
      V ≤ ‖pintzDetectedPolynomialIcc xi Y (shift rho)‖ := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hDetected rho hrho)).2
  obtain ⟨W, hW, hSep, hCount⟩ :=
    exists_pintz_zero_selection shift hsigma hT hG hShift
  refine ⟨W, hSep, hCount, ?_⟩
  intro u hu
  obtain ⟨rho, hrho, hrfl⟩ := Finset.mem_image.mp (hW hu)
  subst u
  exact hLargeShift rho hrho

/-- The same detected selection on an explicitly specified subset of the
physical zero set.  This is needed because Pintz's contour detector applies
away from a short central height interval, whose multiplicity is accounted
for separately rather than silently discarded. -/
theorem exists_pintz_zero_detected_selection_subset
    {sigma T H G xi V : ℝ} {Y : ℕ} (S : Finset ℂ)
    (hS : S ⊆ zeroSet sigma T)
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G)
    (hDetected : ∀ rho ∈ S,
      ∃ u : ℝ, |rho.im - u| ≤ H ∧
        V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖) :
    ∃ W : Finset ℝ, IsSeparated G W ∧
      ∑ rho ∈ S, zeroMultiplicity rho ≤
        (2 * ((2 * Nat.ceil H + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T))) *
        (2 * (2 * Nat.ceil G + 1)) * W.card ∧
      (∀ u ∈ W, V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖) ∧
      ∀ u ∈ W, |u| ≤ T + H := by
  let shift : ℂ → ℝ := fun rho =>
    if h : rho ∈ S then Classical.choose (hDetected rho h) else rho.im
  have hShift : ∀ rho ∈ S, |rho.im - shift rho| ≤ H := by
    intro rho hrho
    dsimp only [shift]
    rw [dif_pos hrho]
    exact (Classical.choose_spec (hDetected rho hrho)).1
  have hLargeShift : ∀ rho ∈ S,
      V ≤ ‖pintzDetectedPolynomialIcc xi Y (shift rho)‖ := by
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
          (zeroSet sigma T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) := by
      intro rho hrho
      rw [Finset.mem_filter] at hrho ⊢
      exact ⟨hS hrho.1, hrho.2⟩
    have hSum :
        ∑ rho ∈ S.filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤
        ∑ rho ∈ (zeroSet sigma T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSub
      intro rho _ _
      exact Nat.zero_le _
    have hFullReal := zeroLocalUnitBin_multiplicity_le_global_log
      sigma T z hsigma hT
    have hCeil : globalLocalZeroLogConstant * Real.log T ≤ (L : ℝ) :=
      Nat.le_ceil _
    have hCast :
        ((∑ rho ∈ (zeroSet sigma T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho : ℕ) : ℝ) ≤ (L : ℝ) :=
      hFullReal.trans hCeil
    have hFull :
        ∑ rho ∈ (zeroSet sigma T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤ L := by
      exact_mod_cast hCast
    exact hSum.trans hFull
  obtain ⟨W, hW, hSep, hCount⟩ :=
    exists_pintz_scaledSeparated_shifted_weighted
      S zeroMultiplicity Complex.im shift hG L hShift hLocal
  refine ⟨W, hSep, hCount, ?_, ?_⟩
  · intro u hu
    obtain ⟨rho, hrho, hrfl⟩ := Finset.mem_image.mp (hW hu)
    subst u
    exact hLargeShift rho hrho
  · intro u hu
    obtain ⟨rho, hrho, hrfl⟩ := Finset.mem_image.mp (hW hu)
    subst u
    have hrhoZero := hS hrho
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect sigma 1 (-T) T at hrhoZero
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrhoZero
    have hrect :=
      (RiemannZeta.GuthMaynard.mem_ZeroRectangle sigma 1 (-T) T rho).mp
        hrhoZero.1
    have him : |rho.im| ≤ T := abs_le.mpr ⟨hrect.2.2.1, hrect.2.2.2⟩
    calc
      |shift rho| = |rho.im - (rho.im - shift rho)| := by ring_nf
      _ ≤ |rho.im| + |rho.im - shift rho| := abs_sub _ _
      _ ≤ T + H := add_le_add him (hShift rho hrho)

#print axioms exists_pintz_zero_detected_selection
#print axioms exists_pintz_zero_detected_selection_subset

end

end GafniTao
