import Dubon2026.SourceOriginalWeilCoverDifferentialReadings

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel comparison.
Adapt the proved original-curve coordinate and primitive arguments to the
literal Kummer cover, using its constructed charts and finite coordinate.
The primitive gluing argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem chart_dCoord_order_zero (v : Place ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    (placeFamily N n r A hr hrA v z).ordDifferential v.dCoord = 0 := by
  have ho := (place_spec N n r A hr hrA v).2.2.2 z hz
  have h := cover_ordDifferential_D_eq_ord_sub_one N n r (placeFamily N n r A hr hrA v z)
    (f := v.uniformizer - algebraMap ℂ (EE) z)
    (by rw [ho]; exact one_ne_zero)
  rw [map_sub, Derivation.map_algebraMap, sub_zero, ho, sub_self] at h
  exact h

theorem chart_differentialCoeff_regular (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    v.differentialCoeff ω ∈ (placeFamily N n r A hr hrA v z).toValuationSubring := by
  haveI := cover_place_dCoordGenerates N n r v
  haveI := cover_place_dCoordGenerates N n r (placeFamily N n r A hr hrA v z)
  haveI : Nontrivial Ω[EE⁄ℂ] :=
    cover_differentials_nontrivial N n r
  by_cases hc : v.differentialCoeff ω = 0
  · rw [hc]
    exact zero_mem _
  have hd : (placeFamily N n r A hr hrA v z).differentialCoeff v.dCoord ≠ 0 := by
    intro he
    have h := (placeFamily N n r A hr hrA v z).differentialCoeff_smul_dCoord v.dCoord
    rw [he, zero_smul] at h
    exact v.dCoord_ne_zero h.symm
  have hs := (placeFamily N n r A hr hrA v z).ordDifferential_smul hc hd
  rw [v.differentialCoeff_smul_dCoord ω, chart_dCoord_order_zero N n r A hr hrA v hz, add_zero] at hs
  have hreg := (mem_cover_regularDifferentials_iff_ord_nonneg N n r ω).mp hω (placeFamily N n r A hr hrA v z)
  rw [hs] at hreg
  exact (placeFamily N n r A hr hrA v z).mem_of_ord_nonneg hreg

theorem analyticOnNhd_readDifferential (v : Place ℂ (EE))
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE)) :
    AnalyticOnNhd ℂ (readDifferential N n r A hr hrA v ω) (ball 0 (placeRadius N n r A hr hrA v)) := by
  intro z hz
  have ha : AnalyticAt ℂ (chartRead N n r A hr hrA v (v.differentialCoeff ω)) z :=
    (place_spec N n r A hr hrA v).2.2.1.analyticAt hz (chart_differentialCoeff_regular N n r A hr hrA v ω hω hz)
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with u hu
  exact (readDifferential_eq_coefficient N n r A hr hrA v ω hu).symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
