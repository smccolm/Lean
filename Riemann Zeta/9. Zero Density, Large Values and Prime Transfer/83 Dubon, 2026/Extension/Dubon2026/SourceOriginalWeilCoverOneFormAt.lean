import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives

/-! DUB-17/18 -> cover reciprocity -> coordinate differential coefficients.
The already proved regular-at-a-place change law and actual chart inverse
identities give the one-form law at every regular point in a cover chart.
This avoids rebuilding the local Kaehler expression calculation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem cover_one_form_law_at (Q : Place ℂ EE) (θ : Ω[EE⁄ℂ]) {y : ℂ}
    (hy : y ∈ ball 0 (placeRadius N n radicand baseDivisor hRadicand hOrders Q))
    (hyr : (placeFamily N n radicand baseDivisor hRadicand hOrders Q y).differentialCoeff θ ∈
      (placeFamily N n radicand baseDivisor hRadicand hOrders Q y).toValuationSubring) :
    readDifferential N n radicand baseDivisor hRadicand hOrders Q θ y =
      readDifferential N n radicand baseDivisor hRadicand hOrders
        (placeFamily N n radicand baseDivisor hRadicand hOrders Q y) θ 0 *
      deriv (placeChart N n radicand baseDivisor hRadicand hOrders
        (placeFamily N n radicand baseDivisor hRadicand hOrders Q y) ∘
          placeFamily N n radicand baseDivisor hRadicand hOrders Q) y := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let Q' := placeFamily N n radicand baseDivisor hRadicand hOrders Q y
  let T : ℂ → ℂ := placeChart N n radicand baseDivisor hRadicand hOrders Q' ∘
    placeFamily N n radicand baseDivisor hRadicand hOrders Q
  let S := chartRead N n radicand baseDivisor hRadicand hOrders Q' Q.uniformizer
  have hQ' : Q' ∈ (placeChart N n radicand baseDivisor hRadicand hOrders Q).source := ⟨y, hy, rfl⟩
  have hTy : T y = 0 := placeChart_self N n radicand baseDivisor hRadicand hOrders Q'
  have hSa : AnalyticAt ℂ S 0 := analyticAt_place_reading N n radicand baseDivisor hRadicand hOrders Q'
    (uniformizer_regular_on_chart N n radicand baseDivisor hRadicand hOrders Q Q' hQ')
  have hsrc : y ∈ ((placeChart N n radicand baseDivisor hRadicand hOrders Q).symm.trans
      (placeChart N n radicand baseDivisor hRadicand hOrders Q')).source :=
    ⟨hy, mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q'⟩
  have hTa : AnalyticAt ℂ T y :=
    analyticOnNhd_placeChart_transition N n radicand baseDivisor hRadicand hOrders Q Q' y hsrc
  have hnear := (isOpen_placeChart_trans_source N n radicand baseDivisor hRadicand hOrders Q Q').mem_nhds hsrc
  have hid : S ∘ T =ᶠ[𝓝 y] id := by
    filter_upwards [hnear] with z hz
    rw [placeChart_trans_source] at hz
    change (placeChart N n radicand baseDivisor hRadicand hOrders Q)
      (placeFamily N n radicand baseDivisor hRadicand hOrders Q'
        (placeChart N n radicand baseDivisor hRadicand hOrders Q'
          (placeFamily N n radicand baseDivisor hRadicand hOrders Q z))) = z
    have hback : placeFamily N n radicand baseDivisor hRadicand hOrders Q'
        (placeChart N n radicand baseDivisor hRadicand hOrders Q'
          (placeFamily N n radicand baseDivisor hRadicand hOrders Q z)) =
        placeFamily N n radicand baseDivisor hRadicand hOrders Q z :=
      (placeChart N n radicand baseDivisor hRadicand hOrders Q').left_inv hz.2
    rw [hback]
    exact place_eval_uniformizer N n radicand baseDivisor hRadicand hOrders Q hz.1
  have hsd : HasDerivAt S (deriv S 0) (T y) := by
    rw [hTy]
    exact hSa.differentiableAt.hasDerivAt
  have hd : deriv S 0 * deriv T y = 1 := by
    rw [← (hsd.comp y hTa.differentiableAt.hasDerivAt).deriv, hid.deriv_eq, deriv_id]
  have hS0 : S 0 = y := by
    change (placeChart N n radicand baseDivisor hRadicand hOrders Q)
      (placeFamily N n radicand baseDivisor hRadicand hOrders Q' 0) = y
    rw [(place_spec N n radicand baseDivisor hRadicand hOrders Q').2.1]
    exact place_eval_uniformizer N n radicand baseDivisor hRadicand hOrders Q hy
  have he := (readDifferential_change_of_coeff_mem N n radicand baseDivisor hRadicand hOrders Q Q' θ hyr hQ').self_of_nhds
  change readDifferential N n radicand baseDivisor hRadicand hOrders Q' θ 0 =
    readDifferential N n radicand baseDivisor hRadicand hOrders Q θ (S 0) * deriv S 0 at he
  change readDifferential N n radicand baseDivisor hRadicand hOrders Q θ y =
    readDifferential N n radicand baseDivisor hRadicand hOrders Q' θ 0 * deriv T y
  rw [he, hS0, mul_assoc, hd, mul_one]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
