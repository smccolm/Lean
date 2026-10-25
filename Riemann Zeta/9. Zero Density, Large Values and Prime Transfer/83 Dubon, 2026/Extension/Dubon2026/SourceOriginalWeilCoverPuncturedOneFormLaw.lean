import Dubon2026.SourceOriginalWeilCoverOneFormLaw
import Dubon2026.SourceOriginalWeilCoverCellCoefficient

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


open Metric

theorem cover_eventually_differentialCoeff_mem_punctured (v : Place ℂ EE) (θ : Ω[EE⁄ℂ]) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ᶠ w in 𝓝[≠] v, w.differentialCoeff θ ∈ w.toValuationSubring := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  haveI : ∀ w : Place ℂ EE, w.DCoordGenerates := cover_place_dCoordGenerates N n radicand
  haveI : Nontrivial Ω[EE⁄ℂ] := cover_differentials_nontrivial N n radicand
  by_cases h0 : θ = 0
  · subst θ
    exact Eventually.of_forall fun w => by rw [w.differentialCoeff_zero]; exact zero_mem _
  have hfin : {w : Place ℂ EE | w.ordDifferential θ < 0}.Finite :=
    (finite_cover_differential_support N n radicand h0).subset fun _ hw => ne_of_lt hw
  filter_upwards [nhdsNE_le_cofinite v hfin.compl_mem_cofinite] with w hw
  exact w.mem_of_ord_nonneg (not_lt.mp hw)

theorem cover_placeFamily_tendsto_punctured (v : Place ℂ EE) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    Tendsto (PF v) (𝓝[≠] (0 : ℂ)) (𝓝[≠] v) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hc := placeFamily_continuousAt_zero N n radicand baseDivisor hRadicand hOrders v
  rw [ContinuousAt, (place_spec N n radicand baseDivisor hRadicand hOrders v).2.1] at hc
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hc.mono_left nhdsWithin_le_nhds)
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N n radicand baseDivisor hRadicand hOrders v) :=
    nhdsWithin_le_nhds (ball_mem_nhds _ (place_spec N n radicand baseDivisor hRadicand hOrders v).1)
  filter_upwards [hb, self_mem_nhdsWithin] with z hz hn
  intro he
  apply hn
  have he' := congrArg (PC v) he
  have hchart : PC v (PF v z) = z := (PC v).right_inv hz
  rw [hchart, placeChart_self] at he'
  exact he'

theorem cover_one_form_law_punctured (Q : Place ℂ EE) (θ : Ω[EE⁄ℂ]) :
    ∀ᶠ y in 𝓝[≠] (0 : ℂ), RD Q θ y = RD (PF Q y) θ 0 * deriv (PC (PF Q y) ∘ PF Q) y := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N n radicand baseDivisor hRadicand hOrders Q) :=
    nhdsWithin_le_nhds (ball_mem_nhds _ (place_spec N n radicand baseDivisor hRadicand hOrders Q).1)
  filter_upwards [hb, (cover_placeFamily_tendsto_punctured N n radicand baseDivisor hRadicand hOrders Q).eventually
    (cover_eventually_differentialCoeff_mem_punctured N n radicand baseDivisor hRadicand hOrders Q θ)] with y hy hyr
  exact cover_one_form_law_at N n radicand baseDivisor hRadicand hOrders Q θ hy hyr

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
