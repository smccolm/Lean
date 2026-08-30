import GafniTao.RightEdgeStrip

/-!
# Complete finite equation-(2.7) consumer

This module closes the finite strip trichotomy using the exact near-one
density and Vinogradov--Korobov predicates.  Those two predicates remain the
published analytic inputs to be formalized; every downstream strip and
epsilon loss is discharged here.
-/

namespace GafniTao

/-- Complete fixed-`epsilon`, fixed-`J` equation-(2.7) bound.  It consumes the
literal right-edge mass theorem, the lower-half second moment, the refined
ordinary/additive-energy alternatives, and the nonadmissible small-`A`
branch. -/
theorem equation27FullZeroMeasure_epsilonBound_of_nearOne_inputs
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {J : ℕ} (hJ : 0 < J)
    {theta eps delta mu : ℝ}
    (hthetaLower : 0 < theta) (hthetaUpper : theta < 1)
    (heps : 0 < eps)
    (hthreshold : 0 < 1 / (1 - theta) - eps)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hJMargin : 1 / (J : ℝ) <
      eps * (1 - theta) * nearOneRightEdgeWidth C 2)
    (hfixed : refinedFixedEpsilonExponent theta eps < (mu : EReal)) :
    EpsilonExponentBound
      (fun X => equation27FullZeroMeasure J theta delta X)
      (max (1 - theta) mu + 4 / J) := by
  apply equation27FullZeroMeasure_epsilonBound_of_refinedFixedEpsilon_lt
    cutoff hJ hthetaUpper heps hthreshold hdelta hdeltaOne hJMargin hfixed
  intro j hj hAtRight
  exact equation27StripMeasure_epsilonBound_of_rightEdge
    hDensity hZeroFree hC hc hJ hthetaLower hthetaUpper hdelta hdeltaOne
      hAtRight.le

end GafniTao
