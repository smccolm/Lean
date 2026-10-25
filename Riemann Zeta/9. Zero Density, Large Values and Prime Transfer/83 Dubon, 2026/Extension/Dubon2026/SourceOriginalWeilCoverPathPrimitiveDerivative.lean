import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The actual inverse coordinate and coefficient laws give the derivative
of a local path primitive along a real cell-coordinate curve. This is the
chain-rule input to the boundary-arc fundamental theorem of calculus. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

theorem cover_hasDerivAt_path_primitive :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ {θ : Ω[EE⁄ℂ]}, Q.differentialCoeff θ ∈ Q.toValuationSubring →
      ∀ {Φ : ℂ → ℂ}, HasDerivAt Φ (RD Q θ 0) 0 →
      ∀ {z : ℝ → ℂ} {v : ℂ} {t : ℝ}, HasDerivAt z v t → z t = ζ Q →
      HasDerivAt (Φ ∘ PC Q ∘ ζ.symm ∘ z) (CF ζ θ (z t) * v) t := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd θ hθ Φ hΦ z v t hz hzt
  let σ : ℂ → ℂ := PC Q ∘ ζ.symm
  have hσ : HasDerivAt σ (deriv σ (ζ Q)) (ζ Q) :=
    (cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd).1.differentiableAt.hasDerivAt
  have hσQ : σ (ζ Q) = 0 := by
    change PC Q (ζ.symm (ζ Q)) = 0
    rw [ζ.left_inv hQ, placeChart_self]
  have hcoeff := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd θ hθ).1.self_of_nhds
  change CF ζ θ (ζ Q) = RD Q θ (σ (ζ Q)) * deriv σ (ζ Q) at hcoeff
  rw [hσQ] at hcoeff
  have hσz : HasDerivAt (σ ∘ z) (deriv σ (ζ Q) * v) t := by
    apply HasDerivAt.comp t _ hz
    rwa [hzt]
  have hΦz : HasDerivAt Φ (RD Q θ 0) ((σ ∘ z) t) := by
    simpa only [Function.comp_apply, hzt, hσQ] using hΦ
  convert hΦz.comp t hσz using 1
  rw [hzt, hcoeff, mul_assoc]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
