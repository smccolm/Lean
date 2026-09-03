import GafniTao.PintzDetectedSelection

/-!
# The finite Pintz zero-density inequality

This module is the first theorem in the Pintz chain whose conclusion is about
the actual multiplicity-weighted zeta-zero count.  It consumes the detected
selection, the exact equation-(4.12) Gram expansion, and the equation-(4.13)
off-diagonal absorption condition.
-/

open Finset Metric
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal integer loss in the weighted displacement and separation
step. -/
noncomputable def pintzSelectionLoss (H G T : ℝ) : ℕ :=
  (2 * ((2 * Nat.ceil H + 1) *
    Nat.ceil (globalLocalZeroLogConstant * Real.log T))) *
  (2 * (2 * Nat.ceil G + 1))

/-- Finite count form of Pintz equations (4.11)--(4.14).  Keeping `V^2` on
the left avoids any hidden division or nonemptiness assumption. -/
theorem pintz_finite_zero_density
    {sigma T H G xi V M : ℝ} {Y : ℕ}
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G) (hxi : 0 ≤ xi) (hV : 0 < V) (hM : 0 ≤ M)
    (hDetected : ∀ rho ∈ zeroSet sigma T,
      ∃ u : ℝ, |rho.im - u| ≤ H ∧
        V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖)
    (hGram : ∀ t u : ℝ, G ≤ dist t u →
      ‖pintzGramCorrelation xi Y t u‖ ≤ M)
    (hAbsorb : 2 * (harmonic Y : ℝ) * M ≤ V ^ 2) :
    (zeroCount sigma T : ℝ) * V ^ 2 ≤
      (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) *
          ((Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ))) := by
  obtain ⟨W, hSep, hCount, hLarge⟩ :=
    exists_pintz_zero_detected_selection hsigma hT hG hDetected
  let D : ℝ := (Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ)
  have hHarmonic : 0 ≤ (harmonic Y : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hOff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintzGramCorrelation xi Y t u‖ ≤ M := by
    intro t ht u hu htu
    exact hGram t u (hSep t ht u hu htu)
  have hDiag : ∀ t ∈ W,
      ‖pintzGramCorrelation xi Y t t‖ ≤ D := by
    intro t ht
    exact norm_pintzGramCorrelation_self_le hxi t
  have hOffDiagonalHalf :
      2 * (harmonic Y : ℝ) * (W.card : ℝ) ^ 2 * M ≤
        ((W.card : ℝ) * V) ^ 2 := by
    have hcardSq : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
    calc
      2 * (harmonic Y : ℝ) * (W.card : ℝ) ^ 2 * M =
          (W.card : ℝ) ^ 2 *
            (2 * (harmonic Y : ℝ) * M) := by ring
      _ ≤ (W.card : ℝ) ^ 2 * V ^ 2 :=
        mul_le_mul_of_nonneg_left hAbsorb hcardSq
      _ = ((W.card : ℝ) * V) ^ 2 := by ring
  have hCard := pintz_equation_4_14 hV hM hD hLarge hOff hDiag
    hOffDiagonalHalf
  have hCountReal :
      (zeroCount sigma T : ℝ) ≤
        (pintzSelectionLoss H G T : ℝ) * (W.card : ℝ) := by
    exact_mod_cast hCount
  calc
    (zeroCount sigma T : ℝ) * V ^ 2 ≤
        ((pintzSelectionLoss H G T : ℝ) * (W.card : ℝ)) * V ^ 2 := by
      exact mul_le_mul_of_nonneg_right hCountReal (sq_nonneg V)
    _ = (pintzSelectionLoss H G T : ℝ) *
        ((W.card : ℝ) * V ^ 2) := by ring
    _ ≤ (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) * D) := by
      gcongr
    _ = (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) *
          ((Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ))) := by rfl

/-- Equations (4.11)--(4.14) on a named subset of the physical zero set.
The left side is the literal analytic-multiplicity sum over that subset. -/
theorem pintz_finite_subset_density
    (S : Finset ℂ) {sigma T H G xi V M : ℝ} {Y : ℕ}
    (hS : S ⊆ zeroSet sigma T)
    (hsigma : 0 ≤ sigma) (hT : max (Real.exp 2) 8 ≤ T)
    (hG : 0 < G) (hxi : 0 ≤ xi) (hV : 0 < V) (hM : 0 ≤ M)
    (hDetected : ∀ rho ∈ S,
      ∃ u : ℝ, |rho.im - u| ≤ H ∧
        V ≤ ‖pintzDetectedPolynomialIcc xi Y u‖)
    (hGram : ∀ t u : ℝ, |t| ≤ T + H → |u| ≤ T + H →
      G ≤ dist t u →
      ‖pintzGramCorrelation xi Y t u‖ ≤ M)
    (hAbsorb : 2 * (harmonic Y : ℝ) * M ≤ V ^ 2) :
    ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) * V ^ 2 ≤
      (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) *
          ((Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ))) := by
  obtain ⟨W, hSep, hCount, hLarge, hHeight⟩ :=
    exists_pintz_zero_detected_selection_subset S hS hsigma hT hG hDetected
  let D : ℝ := (Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ)
  have hHarmonic : 0 ≤ (harmonic Y : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hOff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintzGramCorrelation xi Y t u‖ ≤ M := by
    intro t ht u hu htu
    exact hGram t u (hHeight t ht) (hHeight u hu)
      (hSep t ht u hu htu)
  have hDiag : ∀ t ∈ W,
      ‖pintzGramCorrelation xi Y t t‖ ≤ D := by
    intro t ht
    exact norm_pintzGramCorrelation_self_le hxi t
  have hOffDiagonalHalf :
      2 * (harmonic Y : ℝ) * (W.card : ℝ) ^ 2 * M ≤
        ((W.card : ℝ) * V) ^ 2 := by
    have hcardSq : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
    calc
      2 * (harmonic Y : ℝ) * (W.card : ℝ) ^ 2 * M =
          (W.card : ℝ) ^ 2 * (2 * (harmonic Y : ℝ) * M) := by ring
      _ ≤ (W.card : ℝ) ^ 2 * V ^ 2 :=
        mul_le_mul_of_nonneg_left hAbsorb hcardSq
      _ = ((W.card : ℝ) * V) ^ 2 := by ring
  have hCard := pintz_equation_4_14 hV hM hD hLarge hOff hDiag
    hOffDiagonalHalf
  have hCountReal :
      ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) ≤
        (pintzSelectionLoss H G T : ℝ) * (W.card : ℝ) := by
    exact_mod_cast hCount
  calc
    ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) * V ^ 2 ≤
        ((pintzSelectionLoss H G T : ℝ) * (W.card : ℝ)) * V ^ 2 := by
      exact mul_le_mul_of_nonneg_right hCountReal (sq_nonneg V)
    _ = (pintzSelectionLoss H G T : ℝ) *
        ((W.card : ℝ) * V ^ 2) := by ring
    _ ≤ (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) * D) := by
      gcongr
    _ = (pintzSelectionLoss H G T : ℝ) *
        (2 * (harmonic Y : ℝ) *
          ((Y : ℝ) ^ (2 * xi) * (harmonic Y : ℝ))) := by rfl

#print axioms pintz_finite_zero_density
#print axioms pintz_finite_subset_density

end

end GafniTao
