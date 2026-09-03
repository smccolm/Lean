import GafniTao.PintzGramUniform

/-!
# Pintz's finite inequality on the actual near-one zero set

The Gaussian contour detector requires the zero ordinate to lie outside a
short central interval.  We therefore partition the physical zero set, apply
the exact detector/Gram argument to the high part, and retain a separately
proved local-count term for the central part.
-/

open Finset Metric
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Zeros to which the two horizontal edges at distance `2 lambda` can be
applied without crossing the bounded-height zeta region. -/
noncomputable def pintzHighZeroSet (eta T lambda : ℝ) : Finset ℂ :=
  (zeroSet (1 - eta) T).filter
    (fun rho => 2 * lambda + 3 < |rho.im|)

/-- The complementary short central interval, kept with analytic
multiplicity. -/
noncomputable def pintzLowZeroSet (eta T lambda : ℝ) : Finset ℂ :=
  (zeroSet (1 - eta) T).filter
    (fun rho => ¬ 2 * lambda + 3 < |rho.im|)

theorem pintzHighZeroSet_subset (eta T lambda : ℝ) :
    pintzHighZeroSet eta T lambda ⊆ zeroSet (1 - eta) T := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

/-- Exact multiplicity partition into the detected and central pieces. -/
theorem zeroCount_eq_pintz_high_add_low (eta T lambda : ℝ) :
    zeroCount (1 - eta) T =
      (∑ rho ∈ pintzHighZeroSet eta T lambda, zeroMultiplicity rho) +
      ∑ rho ∈ pintzLowZeroSet eta T lambda, zeroMultiplicity rho := by
  rw [zeroCount_eq_weighted_sum]
  simpa only [pintzHighZeroSet, pintzLowZeroSet] using
    (Finset.sum_filter_add_sum_filter_not
      (zeroSet (1 - eta) T)
      (fun rho => 2 * lambda + 3 < |rho.im|)
      zeroMultiplicity).symm

/-- The central zeros occupy only explicitly many unit bins.  This is the
finite remainder that Pintz suppresses in asymptotic notation. -/
theorem pintz_low_zero_weight_le
    {eta T lambda : ℝ}
    (hetaUpper : eta ≤ 1)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ∑ rho ∈ pintzLowZeroSet eta T lambda, zeroMultiplicity rho ≤
      2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
        Nat.ceil (globalLocalZeroLogConstant * Real.log T)) := by
  let S := pintzLowZeroSet eta T lambda
  let L : ℕ := Nat.ceil (globalLocalZeroLogConstant * Real.log T)
  have hsigma : 0 ≤ 1 - eta := by linarith
  have hShift : ∀ rho ∈ S, |rho.im - (0 : ℝ)| ≤ 2 * lambda + 3 := by
    intro rho hrho
    have hlow := (Finset.mem_filter.mp hrho).2
    simpa only [sub_zero, not_lt] using hlow
  have hLocal : ∀ z : ℤ,
      ∑ rho ∈ S.filter
          (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
        zeroMultiplicity rho ≤ L := by
    intro z
    have hSub :
        S.filter (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) ⊆
          (zeroSet (1 - eta) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1) := by
      intro rho hrho
      rw [Finset.mem_filter] at hrho ⊢
      exact ⟨(Finset.mem_filter.mp hrho.1).1, hrho.2⟩
    have hSum :
        ∑ rho ∈ S.filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤
        ∑ rho ∈ (zeroSet (1 - eta) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSub
      intro rho _ _
      exact Nat.zero_le _
    have hFullReal := zeroLocalUnitBin_multiplicity_le_global_log
      (1 - eta) T z hsigma hT
    have hCeil : globalLocalZeroLogConstant * Real.log T ≤ (L : ℝ) :=
      Nat.le_ceil _
    have hCast :
        ((∑ rho ∈ (zeroSet (1 - eta) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho : ℕ) : ℝ) ≤ (L : ℝ) :=
      hFullReal.trans hCeil
    have hFull :
        ∑ rho ∈ (zeroSet (1 - eta) T).filter
            (fun w => (z : ℝ) ≤ w.im ∧ w.im < (z : ℝ) + 1),
          zeroMultiplicity rho ≤ L := by
      exact_mod_cast hCast
    exact hSum.trans hFull
  obtain ⟨W, hW, hSep, hWeight⟩ :=
    exists_oneSeparated_shifted_weighted S zeroMultiplicity Complex.im
      (fun _ => 0) L hShift hLocal
  have hImageSubset : S.image (fun _ => (0 : ℝ)) ⊆ {0} := by
    intro u hu
    simp only [Finset.mem_image] at hu
    obtain ⟨rho, hrho, rfl⟩ := hu
    simp
  have hWCard : W.card ≤ 1 := by
    have := Finset.card_le_card (hW.trans hImageSubset)
    simpa using this
  calc
    ∑ rho ∈ pintzLowZeroSet eta T lambda, zeroMultiplicity rho =
        ∑ rho ∈ S, zeroMultiplicity rho := by rfl
    _ ≤ 2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) * L) * W.card := hWeight
    _ ≤ 2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) * L) * 1 := by
      gcongr
    _ = 2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
        Nat.ceil (globalLocalZeroLogConstant * Real.log T)) := by simp [L]

/-- The high-zero part of Pintz's equations (4.8)--(4.14), with the actual
zeta zeros, multiplicities, detector, cutoff, and two-regime Gram envelope.
Only the displayed finite contour-error and off-diagonal absorption
inequalities remain to be discharged by explicit parameter selection. -/
theorem pintz_physical_high_density
    {eta T lambda : ℝ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hlambda : pintzMobiusLambdaThreshold ≤ lambda)
    (hLambdaHeight : 2 * lambda ≤ T)
    (hError : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      pintzEquation46ErrorBound (1 - rho.re) rho.im lambda
        (pintzPhysicalZetaMajorant eta T)
        (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4)
    (hAbsorb :
      2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          pintzPhysicalGramMajorant eta lambda T ≤
        pintzDetectedLowerBound eta lambda T ^ 2) :
    ((∑ rho ∈ pintzHighZeroSet eta T lambda,
        zeroMultiplicity rho : ℕ) : ℝ) *
        pintzDetectedLowerBound eta lambda T ^ 2 ≤
      (pintzSelectionLoss (2 * lambda) (5 * lambda) T : ℝ) *
        (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
            (harmonic (pintzMobiusCutoff lambda) : ℝ))) := by
  have hsigma : 0 ≤ 1 - eta := by linarith
  have hG : 0 < 5 * lambda := by
    have hthreshold := pintzMobiusLambdaThreshold_ge_eight.trans hlambda
    positivity
  have hlambdaPos : 0 < lambda := by
    have hthreshold := pintzMobiusLambdaThreshold_ge_eight.trans hlambda
    linarith
  have hV : 0 < pintzDetectedLowerBound eta lambda T := by
    unfold pintzDetectedLowerBound
    have hTQuarter : (1 / 2 : ℝ) ≤ T := by
      have hT8 : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hT
      linarith
    have hZ := pintzPhysicalZetaMajorant_pos
      (eta := eta) (T := T) hTQuarter
    apply one_div_pos.mpr
    exact mul_pos (mul_pos (by norm_num) hlambdaPos)
      (mul_pos (div_pos hZ heta) (Real.exp_pos _))
  have hTQuarter : (1 / 4 : ℝ) ≤ T := by
    have hT8 : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hT
    linarith
  have hM : 0 ≤ pintzPhysicalGramMajorant eta lambda T :=
    pintzPhysicalGramMajorant_nonneg
      (eta := eta) (lambda := lambda) (T := T) hTQuarter
  have hDetected : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      ∃ u : ℝ, |rho.im - u| ≤ 2 * lambda ∧
        pintzDetectedLowerBound eta lambda T ≤
          ‖pintzDetectedPolynomialIcc (2 * eta)
            (pintzMobiusCutoff lambda) u‖ := by
    intro rho hrho
    have hrhoFull := (Finset.mem_filter.mp hrho).1
    have hheight := (Finset.mem_filter.mp hrho).2
    exact exists_large_pintzDetectedPolynomial_of_mem_zeroSet
      heta (by linarith) hlambda hheight hLambdaHeight hrhoFull
        (hError rho hrho)
  have hGram : ∀ t u : ℝ,
      |t| ≤ T + 2 * lambda → |u| ≤ T + 2 * lambda →
      5 * lambda ≤ dist t u →
      ‖pintzGramCorrelation (2 * eta) (pintzMobiusCutoff lambda) t u‖ ≤
        pintzPhysicalGramMajorant eta lambda T := by
    intro t u ht hu hsep
    have hlambdaEight := pintzMobiusLambdaThreshold_ge_eight.trans hlambda
    have hsepAbs : 3 ≤ |u - t| := by
      rw [Real.dist_eq] at hsep
      rw [abs_sub_comm]
      linarith
    exact norm_pintzGramCorrelation_le_physicalMajorant
      heta.le hetaUpper hsepAbs ht hu hLambdaHeight
  have hfinite := pintz_finite_subset_density
    (pintzHighZeroSet eta T lambda)
    (pintzHighZeroSet_subset eta T lambda) hsigma hT hG
    (by positivity : 0 ≤ 2 * eta) hV hM hDetected hGram hAbsorb
  have hexponent : 2 * (2 * eta) = 4 * eta := by ring
  rw [hexponent] at hfinite
  exact hfinite

/-- Full finite Pintz inequality.  The first right-hand term is the explicit
central-height remainder; the second is the detected high-zero contribution.
-/
theorem pintz_physical_finite_density
    {eta T lambda : ℝ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 8)
    (hT : max (Real.exp 2) 8 ≤ T)
    (hlambda : pintzMobiusLambdaThreshold ≤ lambda)
    (hLambdaHeight : 2 * lambda ≤ T)
    (hError : ∀ rho ∈ pintzHighZeroSet eta T lambda,
      pintzEquation46ErrorBound (1 - rho.re) rho.im lambda
        (pintzPhysicalZetaMajorant eta T)
        (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4)
    (hAbsorb :
      2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          pintzPhysicalGramMajorant eta lambda T ≤
        pintzDetectedLowerBound eta lambda T ^ 2) :
    (zeroCount (1 - eta) T : ℝ) *
        pintzDetectedLowerBound eta lambda T ^ 2 ≤
      (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 +
      (pintzSelectionLoss (2 * lambda) (5 * lambda) T : ℝ) *
        (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
          ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
            (harmonic (pintzMobiusCutoff lambda) : ℝ))) := by
  have hlow := pintz_low_zero_weight_le
    (eta := eta) (T := T) (lambda := lambda) (by linarith) hT
  have hhigh := pintz_physical_high_density heta hetaUpper hT hlambda
    hLambdaHeight hError hAbsorb
  have hlowReal :
      ((∑ rho ∈ pintzLowZeroSet eta T lambda,
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℕ) := by
    exact_mod_cast hlow
  have hlowMul :
      ((∑ rho ∈ pintzLowZeroSet eta T lambda,
          zeroMultiplicity rho : ℕ) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 ≤
        ((2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℕ) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 :=
    mul_le_mul_of_nonneg_right hlowReal
      (sq_nonneg (pintzDetectedLowerBound eta lambda T))
  push_cast at hlowMul
  push_cast at hhigh
  rw [zeroCount_eq_pintz_high_add_low eta T lambda]
  push_cast
  calc
    (∑ x ∈ pintzHighZeroSet eta T lambda, (zeroMultiplicity x : ℝ) +
        ∑ x ∈ pintzLowZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 =
      (∑ x ∈ pintzHighZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 +
        (∑ x ∈ pintzLowZeroSet eta T lambda, (zeroMultiplicity x : ℝ)) *
          pintzDetectedLowerBound eta lambda T ^ 2 := by ring
    _ ≤ (pintzSelectionLoss (2 * lambda) (5 * lambda) T : ℝ) *
          (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
            ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
              (harmonic (pintzMobiusCutoff lambda) : ℝ))) +
        (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 :=
      add_le_add hhigh hlowMul
    _ = (2 * ((2 * Nat.ceil (2 * lambda + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta lambda T ^ 2 +
        (pintzSelectionLoss (2 * lambda) (5 * lambda) T : ℝ) *
          (2 * (harmonic (pintzMobiusCutoff lambda) : ℝ) *
            ((pintzMobiusCutoff lambda : ℝ) ^ (4 * eta) *
              (harmonic (pintzMobiusCutoff lambda) : ℝ))) := by
      ring

#print axioms pintz_low_zero_weight_le
#print axioms pintz_physical_high_density
#print axioms pintz_physical_finite_density

end

end GafniTao
