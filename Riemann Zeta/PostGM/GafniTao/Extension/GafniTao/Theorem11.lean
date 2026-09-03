import GafniTao.AllIntervals
import GafniTao.CountableDiagonal

/-!
# Gafni--Tao Theorem 1.1

This file packages the two logically different conclusions of Theorem 1.1.
The almost-all conclusion uses one measurable exceptional set of ordinary
density zero, obtained by the countable diagonal argument; it is not merely a
collection of fixed-threshold dyadic estimates.
-/

open MeasureTheory Set

namespace GafniTao

noncomputable section

/-- The exact two-part conclusion of Gafni--Tao Theorem 1.1 for a uniform
ordinary zero-density coefficient `Azero`. -/
def GafniTaoTheorem11Conclusion (Azero : ℝ) : Prop :=
  (∀ theta : ℝ, 0 < theta → theta < 1 →
      1 - 1 / Azero < theta → AllShortIntervalsPNT theta) ∧
    (∀ theta : ℝ, 0 < theta → theta < 1 →
      1 - 2 / Azero < theta →
        ∃ E : Set ℝ,
          MeasurableSet E ∧ NaturalDensityZero E ∧
            ShortIntervalPNTOutside theta E)

/-- Source-faithful conditional form of Theorem 1.1.  Its hypotheses are the
actual analytic inputs used by the proof: the sharp explicit formula, the
near-one logarithmic density estimate, the Vinogradov--Korobov zero-free
region, and the uniform ordinary density envelope. -/
theorem gafniTaoTheorem11
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B Tzero c Tone Azero : ℝ}
    (hDensity : NearOneLogDensityBound C B Tzero)
    (hZeroFree : VinogradovKorobovCountVanishing c Tone)
    (hC : 0 < C) (hc : 0 < c) (hAzero : 0 < Azero)
    (hUpperHalf : UniformOrdinaryDensityExponent Azero)
    (hFullStrip : UniformNonnegativeOrdinaryDensityEnvelope Azero) :
    GafniTaoTheorem11Conclusion Azero := by
  constructor
  · intro theta htheta hthetaUpper hthreshold
    exact gafniTaoTheorem11_allIntervals hFormula hDensity hZeroFree hC hc
      hFullStrip htheta hthetaUpper hthreshold hAzero
  · intro theta htheta hthetaUpper hthreshold
    exact exists_densityZero_exceptionalSet_of_dyadic htheta.le
      (gafniTaoTheorem11_almostAll_dyadic hDensity hC hAzero htheta
        hthetaUpper hUpperHalf hthreshold)

/-- Native almost-all short-interval PNT obtained by consuming the frozen
Guth--Maynard density theorem and then performing the countable diagonal.
The returned set is a single measurable subset of the real endpoints and has
ordinary natural density zero. -/
theorem gafniTaoTheorem11_almostAll_guthMaynard_singleSet_native
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    ∃ E : Set ℝ,
      MeasurableSet E ∧ NaturalDensityZero E ∧
        ShortIntervalPNTOutside theta E := by
  exact exists_densityZero_exceptionalSet_of_dyadic (by linarith)
    (gafniTaoTheorem11_almostAll_guthMaynard_native htheta hthetaUpper)

/-- The complete native `A₀ = 30/13` specialization of Theorem 1.1. -/
theorem gafniTaoTheorem11_guthMaynard_native :
    GafniTaoTheorem11Conclusion (30 / 13) := by
  obtain ⟨c, Tzero, Tdensity, hc, hZeroFree, hDensity⟩ :=
    exists_pintz_nearOne_log_density_native
  exact gafniTaoTheorem11 sharpTruncatedExplicitFormulaBound_native hDensity
    hZeroFree pintzNearOneDensityCoefficient_pos hc (by norm_num)
    uniformOrdinaryDensityExponent_thirty_thirteenths
    uniformNonnegativeOrdinaryDensityEnvelope_thirty_thirteenths

/-- Direct projection of the all-interval native conclusion, retained as a
regression bridge to the earlier branch-specific theorem. -/
theorem gafniTaoTheorem11_guthMaynard_allIntervals_regression
    {theta : ℝ} (htheta : 17 / 30 < theta) (hthetaUpper : theta < 1) :
    AllShortIntervalsPNT theta := by
  apply gafniTaoTheorem11_guthMaynard_native.1 theta (by linarith)
    hthetaUpper
  simpa only [seventeen_thirtieths_eq_uniform_all_threshold] using htheta

/-- Direct projection of the one-set almost-all native conclusion. -/
theorem gafniTaoTheorem11_guthMaynard_almostAll_regression
    {theta : ℝ} (htheta : 2 / 15 < theta) (hthetaUpper : theta < 1) :
    ∃ E : Set ℝ,
      MeasurableSet E ∧ NaturalDensityZero E ∧
        ShortIntervalPNTOutside theta E := by
  apply gafniTaoTheorem11_guthMaynard_native.2 theta (by linarith)
    hthetaUpper
  simpa only [two_fifteenths_eq_uniform_almost_all_threshold] using htheta

end

end GafniTao
