import Dubon2026.SourceOriginalWeilCoverCellPuncturedCoefficient
import Dubon2026.SourceOriginalWeilCoverLogarithmicReading
import Dubon2026.SourceComplexSimplePolePullback

/-! DUB-17/18 -> cover Abel converse -> meromorphic generation and residue
reciprocity -> actual cell simple-pole coefficients. Reuse finite differential
support, the existing one-form law, inverse coordinates and logarithmic reading.
The generic simple-pole pullback theorem is reused unchanged. -/
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


theorem cover_coeff_simple_pole :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ θ : Ω[EE⁄ℂ], -1 ≤ Q.ordDifferential θ →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (ζ Q),
        CF ζ θ w = Q.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand Q)
          (Q.uniformizer * Q.differentialCoeff θ) / (w - ζ Q) + G w := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd θ hθ
  let σ : ℂ → ℂ := PC Q ∘ ζ.symm
  let r := Q.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand Q)
    (Q.uniformizer * Q.differentialCoeff θ)
  have hinv := cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd
  have hσ0 : σ (ζ Q) = 0 := by simp only [σ, Function.comp_apply, ζ.left_inv hQ, placeChart_self]
  have hσd : deriv σ (ζ Q) ≠ 0 := by rw [hinv.2.deriv]; exact inv_ne_zero hd
  obtain ⟨b, hb, hread⟩ := exists_cover_logarithmic_reading N n radicand baseDivisor hRadicand hOrders Q θ hθ r rfl
  obtain ⟨G, hGa, hmodel⟩ := CellGeometry.exists_simple_pole_pullback_remainder σ
    (chartRead N n radicand baseDivisor hRadicand hOrders Q b) (ζ Q) r hinv.1 hσ0 hσd
      (analyticAt_place_reading N n radicand baseDivisor hRadicand hOrders Q hb)
  have ht := cover_inverse_tendsto_punctured N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd
  refine ⟨G, hGa, ?_⟩
  filter_upwards [cover_coeff_eq_near_punctured N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd θ,
    ht.eventually hread, hmodel] with w hw hwr hwm
  rw [hw, hwr]
  exact (by simpa only [div_eq_mul_inv] using hwm)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
