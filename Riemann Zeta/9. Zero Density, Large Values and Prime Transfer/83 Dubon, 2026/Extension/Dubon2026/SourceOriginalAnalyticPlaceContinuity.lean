import Dubon2026.SourceOriginalRamifiedPlaceContinuity

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual
analytic paths on the original curve. The stabilizer identifies the
chosen-root power pullback with the genuine analytic place map. The
already proved normalized-family continuity therefore descends through
the explicit centered coordinate, including elliptic points.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric EllipticCoordinate
open scoped Topology ComplexConjugate
variable (N : ℕ) [NeZero N]
attribute [local instance] OriginalChart.placeTopology

theorem originalRamifiedPlace_power_eventuallyEq (τ : ℍ) :
    (fun z : ℂ => originalRamifiedPlace N τ (z ^ originalAnalyticRamification N τ)) =ᶠ[𝓝 0]
      fun z => originalAnalyticPlace N (ofComplex (param τ z)) := by
  have hne : ∀ᶠ z : ℂ in 𝓝 0, z ≠ 1 := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨R, hR, hb⟩ := Metric.eventually_nhds_iff_ball.mp ((param_im_pos_eventually τ).and hne)
  filter_upwards [ball_mem_nhds (0 : ℂ) hR] with z hz
  let e := originalAnalyticRamification N τ
  let he := (originalAnalyticRamification_pos N τ).ne'
  let u := PowerDescent.root e he (z ^ e)
  have hu : u ∈ ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right, u, PowerDescent.norm_root_power] using hz
  obtain ⟨hpz, hnz⟩ := hb z hz
  obtain ⟨hpu, hnu⟩ := hb u hu
  change originalAnalyticPlace N (ofComplex (param τ u)) = _
  apply place_eq_of_coord_power_eq N τ
  simp only [ofComplex_apply_of_im_pos hpu, ofComplex_apply_of_im_pos hpz,
    UpperHalfPlane.coe_mk, coord_param τ hnu, coord_param τ hnz]
  exact PowerDescent.root_pow e he _

theorem originalAnalyticPlace_ofComplex_continuousAt (τ : ℍ) :
    ContinuousAt (fun z : ℂ => originalAnalyticPlace N (ofComplex z)) (τ : ℂ) := by
  let F := fun z : ℂ => originalAnalyticPlace N (ofComplex z)
  have hp : ContinuousAt (fun z : ℂ => z ^ originalAnalyticRamification N τ) 0 :=
    continuousAt_id.pow _
  have hr : ContinuousAt (originalRamifiedPlace N τ)
      ((0 : ℂ) ^ originalAnalyticRamification N τ) := by
    rw [zero_pow (originalAnalyticRamification_pos N τ).ne']
    exact OriginalChart.originalRamifiedPlace_continuousAt_zero N τ
  have hc : ContinuousAt (fun z : ℂ => F (param τ z)) 0 :=
    (hr.comp (f := fun z : ℂ => z ^ originalAnalyticRamification N τ) hp).congr
      (originalRamifiedPlace_power_eventuallyEq N τ)
  have hcoord : AnalyticAt ℂ (coord τ) (τ : ℂ) :=
    (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (upper_ne_conj τ τ))
  have hc' : ContinuousAt (fun z : ℂ => F (param τ z)) (coord τ τ) := by
    simpa only [coord, sub_self, zero_div] using hc
  apply (hc'.comp hcoord.continuousAt).congr
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  have he : param τ (coord τ z) = z := param_coord τ ⟨z, hz⟩
  change F (param τ (coord τ z)) = F z
  rw [he]

theorem originalAnalyticPlace_continuous : Continuous (originalAnalyticPlace N) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  have h := (originalAnalyticPlace_ofComplex_continuousAt N τ).comp
    UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

end
end Dubon2026.SourceFunctionField
