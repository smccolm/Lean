import GafniTao.FordZeroDetectorSelectedAbel
import GafniTao.FordCotangentPositivity

/-!
# The zeta-pole term in Ford's cotangent detector

The general meromorphic detector counts the pole of `riemannZeta` at `1`
with multiplicity `-1`.  Its residue contribution is therefore
`-fordCotKernel eta (1 - z₀)`.  This term has zero real part for Ford's
unshifted centre `z₀ = 1 + it`; it is not definitionally absent for a centre
whose real part is greater than one.  The lemmas here record the exact
cancellation used by the source-valid `Re z₀ = 1` specialization.
-/

open Complex Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem re_fordCotKernel_pure_im_eq_zero (eta y : ℝ) :
    (fordCotKernel eta ((y : ℂ) * I)).re = 0 := by
  let c : ℝ := Real.pi / (2 * eta)
  have harg :
      ((c : ℂ) * ((y : ℂ) * I)) = ((c * y : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold fordCotKernel
  change (((c : ℝ) : ℂ) * Complex.cot
    (((c : ℝ) : ℂ) * ((y : ℂ) * I))).re = 0
  rw [harg, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show ((c * y : ℝ) : ℂ) * I =
      ((0 : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I by simp,
    ford_re_cot_formula]
  simp

theorem re_fordCotKernel_one_sub_center_eq_zero (eta t : ℝ) :
    (fordCotKernel eta (1 - fordDetectorCenter t)).re = 0 := by
  have hpoint :
      (1 : ℂ) - fordDetectorCenter t = ((-t : ℝ) : ℂ) * I := by
    unfold fordDetectorCenter
    push_cast
    ring
  rw [hpoint, re_fordCotKernel_pure_im_eq_zero]

/-- At Ford's physical centre `1+it`, the finite residue mass contains the
central logarithmic derivative and the multiplicity-weighted zero sum, while
the zeta-pole term has exactly zero real part. -/
theorem re_fordDetectorPhysicalResidueMass_eq_logDeriv_add_zeroSum
    (eta t yLower yUpper : ℝ) :
    (fordDetectorPhysicalResidueMass eta t yLower yUpper).re =
      (fordDetectorZetaLogDeriv (fordDetectorCenter t)).re +
        ∑ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
          ((analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta (rho - fordDetectorCenter t)).re := by
  classical
  unfold fordDetectorPhysicalResidueMass
  rw [Complex.add_re, Complex.sub_re,
    re_fordCotKernel_one_sub_center_eq_zero]
  simp

/-- The selected finite Abel identity, expanded so that the pole cancellation
and the actual multiplicity-weighted zeta-zero sum are visible in the public
statement. -/
theorem exists_fordDetector_selected_finite_abel_expanded :
    ∃ C : ℝ, 0 < C ∧
      ∀ {eta etaMax t T : ℝ}
        (_heta : 0 ≤ eta) (_hetaMax : eta < etaMax)
        (_hetaMaxUpper : etaMax ≤ 1) (_ht : 0 < t) (_hT : 8 ≤ T)
        (_hTlarge : t + 2 * etaMax / Real.pi ≤ T),
      ∃ eta' RUpper RLower : ℝ,
        eta < eta' ∧ eta' < etaMax ∧
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (fordDetectorZetaLogDeriv (fordDetectorCenter t)).re +
            ∑ rho ∈ fordDetectorPhysicalZeros eta' (-RLower) RUpper,
              ((analyticVanishingOrder riemannZeta rho : ℂ) *
                fordCotKernel eta' (rho - fordDetectorCenter t)).re =
          fordDetectorPhysicalVerticalBulk eta' t (eta' : ℂ)
              (-RLower) RUpper -
            fordDetectorPhysicalVerticalBulk eta' t (-eta' : ℂ)
              (-RLower) RUpper -
            (fordDetectorHorizontalRemainder eta' t (-RLower - t)).re +
            (fordDetectorHorizontalRemainder eta' t (RUpper - t)).re ∧
        ‖fordDetectorHorizontalRemainder eta' t (RUpper - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (RUpper - t) ∧
        ‖fordDetectorHorizontalRemainder eta' t (-RLower - t)‖ ≤
          fordDetectorHorizontalRemainderMajorant eta'
            (C * Real.log T ^ 2) (-RLower - t) := by
  obtain ⟨C, hC, hselected⟩ := exists_fordDetector_selected_finite_abel
  refine ⟨C, hC, ?_⟩
  intro eta etaMax t T _heta _hetaMax _hetaMaxUpper _ht _hT _hTlarge
  obtain ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL,
      habel, hremUpper, hremLower⟩ :=
    hselected _heta _hetaMax _hetaMaxUpper _ht _hT _hTlarge
  refine ⟨eta', RUpper, RLower, heta', heta'Max, hRU, hRL, ?_,
    hremUpper, hremLower⟩
  rw [← re_fordDetectorPhysicalResidueMass_eq_logDeriv_add_zeroSum]
  exact habel

end

end GafniTao
