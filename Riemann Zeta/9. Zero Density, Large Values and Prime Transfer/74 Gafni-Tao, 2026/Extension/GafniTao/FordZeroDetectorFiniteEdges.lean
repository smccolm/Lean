import GafniTao.FordZeroDetectorFinite

/-!
# Oriented edges of Ford's finite zero detector

This is the exact finite-height rearrangement before integration by parts and
the horizontal-edge limit.  Both horizontal edges and both vertical edges
remain explicit, so no decay or logarithm-branch claim is hidden here.
-/

open Complex Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The right vertical detector edge equals the finite residue sum plus the
other three oriented edges. -/
theorem fordZetaDetector_rightEdge_eq_explicit_add_edges
    {eta t R : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hR : |t| < R)
    (hboundary : ∀ rho ∈ fordDetectorZeros eta t R,
      |rho.re - 1| < eta ∧ |rho.im - t| < R) :
    VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (1 + eta) (t - R) (t + R) =
      fordDetectorZetaLogDeriv (fordDetectorCenter t) -
          fordCotKernel eta (1 - fordDetectorCenter t) +
          ∑ rho ∈ fordDetectorZeros eta t R,
            (analyticVanishingOrder riemannZeta rho : ℂ) *
              fordCotKernel eta (rho - fordDetectorCenter t) -
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) (t - R) +
        HIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (1 + eta) (t + R) +
        VIntegral' (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
          (1 - eta) (t - R) (t + R) := by
  have hrect := fordZetaDetector_rectangleIntegral_eq_explicit_sum
    heta hetaUpper ht hR hboundary
  have hreLower : (fordDetectorLower eta t R).re = 1 - eta := by
    simp [fordDetectorLower]
  have hreUpper : (fordDetectorUpper eta t R).re = 1 + eta := by
    simp [fordDetectorUpper]
  have himLower : (fordDetectorLower eta t R).im = t - R := by
    simp [fordDetectorLower]
  have himUpper : (fordDetectorUpper eta t R).im = t + R := by
    simp [fordDetectorUpper]
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLower, hreUpper, himLower, himUpper] at hrect
  linear_combination hrect

end

end GafniTao
