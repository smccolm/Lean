import GafniTao.FordShiftedZeroDetectorRemainderEnvelope
import GafniTao.FordCotangentPositivity

/-!
# Pole-corrected finite Ford detector inequality

This file performs the sign-sensitive step after the exact contour identity.
Zeros omitted from a chosen subset have nonpositive shifted contributions.
The zeta-pole term remains explicit.
-/

open Complex Set Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordCotKernel_neg (eta : ℝ) (z : ℂ) :
    fordCotKernel eta (-z) = -fordCotKernel eta z := by
  unfold fordCotKernel Complex.cot
  simp
  ring

theorem fordShiftedDetector_zeroContribution_nonpos
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) {rho : ℂ}
    (hrho : rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper) :
    ((analyticVanishingOrder riemannZeta rho : ℂ) *
      fordCotKernel eta
        (rho - fordShiftedDetectorCenter sigma t)).re ≤ 0 := by
  have hd := mem_fordShiftedDetectorPhysicalZeros_data hrho
  have hreLower : 0 ≤ sigma - rho.re := by
    have hz := (mem_fordShiftedDetectorPhysicalZeros_iff.mp hrho).1
    have hre := (mem_zeroSet_zero_data hz).2.1
    linarith
  have hreUpper : sigma - rho.re ≤ eta := by
    have hb := (abs_le.mp hd.2.1).1
    linarith
  have hkernel :
      0 ≤ (fordCotKernel eta
        (fordShiftedDetectorCenter sigma t - rho)).re := by
    apply fordCotKernel_re_nonneg heta
    · simpa [fordShiftedDetectorCenter] using hreLower
    · simpa [fordShiftedDetectorCenter] using hreUpper
  have hneg :
      fordCotKernel eta
          (rho - fordShiftedDetectorCenter sigma t) =
        -fordCotKernel eta
          (fordShiftedDetectorCenter sigma t - rho) := by
    rw [show rho - fordShiftedDetectorCenter sigma t =
      -(fordShiftedDetectorCenter sigma t - rho) by ring,
      fordCotKernel_neg]
  rw [hneg, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero, neg_re]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
    (neg_nonpos.mpr hkernel)

theorem sum_fordShiftedDetector_zeroContribution_le_subset
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) {S : Finset ℂ}
    (hS : S ⊆
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper) :
    (∑ rho ∈ fordShiftedDetectorPhysicalZeros
        sigma eta yLower yUpper,
      ((analyticVanishingOrder riemannZeta rho : ℂ) *
        fordCotKernel eta
          (rho - fordShiftedDetectorCenter sigma t)).re) ≤
      ∑ rho ∈ S,
        ((analyticVanishingOrder riemannZeta rho : ℂ) *
          fordCotKernel eta
            (rho - fordShiftedDetectorCenter sigma t)).re := by
  classical
  let Z := fordShiftedDetectorPhysicalZeros
    sigma eta yLower yUpper
  let f : ℂ → ℝ := fun rho =>
    ((analyticVanishingOrder riemannZeta rho : ℂ) *
      fordCotKernel eta
        (rho - fordShiftedDetectorCenter sigma t)).re
  have hsplit :
      (∑ rho ∈ Z, f rho) =
        (∑ rho ∈ S, f rho) + ∑ rho ∈ Z \ S, f rho := by
    rw [← sum_sdiff hS]
    ring
  have hrest : (∑ rho ∈ Z \ S, f rho) ≤ 0 := by
    apply Finset.sum_nonpos
    intro rho hrho
    exact fordShiftedDetector_zeroContribution_nonpos
      hsigma heta (Finset.mem_sdiff.mp hrho).1
  dsimp only [Z, f] at hsplit ⊢
  linarith

/-- Exact finite subset inequality.  It is valid before any limiting
argument and shows the additional positive pole correction explicitly as
the negative of the real kernel at the pole. -/
theorem fordShiftedDetector_finite_subset_inequality
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) {S : Finset ℂ}
    (hS : S ⊆
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper)
    (habel :
      (fordShiftedDetectorPhysicalResidueMass
          sigma eta t yLower yUpper).re =
        fordShiftedDetectorPhysicalVerticalBulk eta sigma t
            (eta : ℂ) yLower yUpper -
          fordShiftedDetectorPhysicalVerticalBulk eta sigma t
            (-eta : ℂ) yLower yUpper -
          (fordShiftedHorizontalRemainder
            sigma eta t (yLower - t)).re +
          (fordShiftedHorizontalRemainder
            sigma eta t (yUpper - t)).re) :
    -(fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter sigma t)).re ≤
      (∑ rho ∈ S,
        ((analyticVanishingOrder riemannZeta rho : ℂ) *
          fordCotKernel eta
            (rho - fordShiftedDetectorCenter sigma t)).re) -
      (fordCotKernel eta
        (1 - fordShiftedDetectorCenter sigma t)).re -
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (eta : ℂ) yLower yUpper +
      fordShiftedDetectorPhysicalVerticalBulk eta sigma t
        (-eta : ℂ) yLower yUpper +
      ‖fordShiftedHorizontalRemainder
        sigma eta t (yLower - t)‖ +
      ‖fordShiftedHorizontalRemainder
        sigma eta t (yUpper - t)‖ := by
  have hexpand :=
    re_fordShiftedDetectorPhysicalResidueMass_expanded
      sigma eta t yLower yUpper
  have hzero :=
    sum_fordShiftedDetector_zeroContribution_le_subset
      (t := t) hsigma heta hS
  have hremLower :
      (fordShiftedHorizontalRemainder
        sigma eta t (yLower - t)).re ≤
      ‖fordShiftedHorizontalRemainder
        sigma eta t (yLower - t)‖ :=
    Complex.re_le_norm _
  have hremUpper :
      -(fordShiftedHorizontalRemainder
        sigma eta t (yUpper - t)).re ≤
      ‖fordShiftedHorizontalRemainder
        sigma eta t (yUpper - t)‖ := by
    simpa only [Complex.neg_re, norm_neg] using
      (Complex.re_le_norm
        (-(fordShiftedHorizontalRemainder
          sigma eta t (yUpper - t))))
  rw [hexpand] at habel
  linarith

/-- Fully selected version of the finite subset inequality.  No contour
nonvanishing or boundary premise remains in the public interface. -/
theorem exists_fordShiftedDetector_selected_subset_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {sigma eta etaMax t T : ℝ}
        (_hsigma : 1 ≤ sigma)
        (_heta : 0 ≤ eta) (_hetaMax : eta < etaMax)
        (_hPole : sigma - 1 ≤ eta)
        (_hleftMax : -1 ≤ sigma - etaMax)
        (_ht : 0 < t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * etaMax / Real.pi ≤ T),
      ∃ eta' RUpper RLower : ℝ,
        eta < eta' ∧ eta' < etaMax ∧
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (∀ S : Finset ℂ, S ⊆
            fordShiftedDetectorPhysicalZeros
              sigma eta' (-RLower) RUpper →
          -(fordDetectorZetaLogDeriv
              (fordShiftedDetectorCenter sigma t)).re ≤
            (∑ rho ∈ S,
              ((analyticVanishingOrder riemannZeta rho : ℂ) *
                fordCotKernel eta'
                  (rho - fordShiftedDetectorCenter sigma t)).re) -
            (fordCotKernel eta'
              (1 - fordShiftedDetectorCenter sigma t)).re -
            fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (eta' : ℂ) (-RLower) RUpper +
            fordShiftedDetectorPhysicalVerticalBulk eta' sigma t
              (-eta' : ℂ) (-RLower) RUpper +
            ‖fordShiftedHorizontalRemainder
              sigma eta' t (-RLower - t)‖ +
            ‖fordShiftedHorizontalRemainder
              sigma eta' t (RUpper - t)‖) ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordShiftedHorizontalRemainder
            sigma eta' t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (-RLower - t) := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_fordShiftedDetector_selected_finite_abel
  refine ⟨C, hC, ?_⟩
  intro sigma eta etaMax t T _hsigma _heta _hetaMax _hPole
    _hleftMax _ht _hT _hTlarge
  obtain ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
      habel, hremUpper, hremLower⟩ :=
    hselected _hsigma _heta _hetaMax _hPole _hleftMax
      _ht _hT _hTlarge
  refine ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
    ?_, hremUpper, hremLower⟩
  intro S hS
  exact fordShiftedDetector_finite_subset_inequality
    _hsigma (lt_of_le_of_lt _heta heta') hS habel

end

end GafniTao
