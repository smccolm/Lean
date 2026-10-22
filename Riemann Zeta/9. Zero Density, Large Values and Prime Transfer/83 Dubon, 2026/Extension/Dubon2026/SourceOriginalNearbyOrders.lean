import Dubon2026.SourceOriginalRamifiedMeromorphicOrder
import Dubon2026.SourceEllipticParameterLocal
import Dubon2026.SourcePowerDescentLocalBranch

/-! DUB-17/18 -> original torsion cardinality -> compatible finite
complex-place charts. Away from the center, the descended family is locally
the actual original evaluation along a noncritical analytic branch. Its
meromorphic order is the original normalized order times the ramification
at that nearby upper-half-plane point. Regular functions are analytic.
Removing this remaining nearby ramification factor is the next obligation.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter EllipticCoordinate
open scoped Topology

theorem originalRamifiedPlace_nearby_orders (N : ℕ) [NeZero N] (τ : ℍ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, z ≠ 0 →
      ‖PowerDescent.root (originalAnalyticRamification N τ)
        (originalAnalyticRamification_pos N τ).ne' z‖ < R →
      ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z =
          (((originalAnalyticRamification N (ofComplex (param τ (PowerDescent.root
            (originalAnalyticRamification N τ) (originalAnalyticRamification_pos N τ).ne' z))) : ℤ) *
            (originalRamifiedPlace N τ z).ord f : ℤ) : WithTop ℤ) ∧
        (f ∈ (originalRamifiedPlace N τ z).toValuationSubring →
          AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z) := by
  have hne : ∀ᶠ u in 𝓝 (0 : ℂ), u ≠ 1 := isOpen_ne.mem_nhds zero_ne_one
  obtain ⟨R, hR, hbound⟩ := Metric.eventually_nhds_iff_ball.mp ((param_im_pos_eventually τ).and hne)
  refine ⟨R, hR, ?_⟩
  intro z hz hzR f hf
  let e := originalAnalyticRamification N τ
  have he : e ≠ 0 := (originalAnalyticRamification_pos N τ).ne'
  let w := PowerDescent.root e he z
  let σ := ofComplex (param τ w)
  let G : ℂ → ℂ := fun t => originalPlaceEval N ℂ (originalAnalyticPlace N (ofComplex t)) f
  let F : ℂ → ℂ := G ∘ param τ
  have hb : 0 < (param τ w).im ∧ w ≠ 1 :=
    hbound w (by simpa only [Metric.mem_ball, dist_zero_right] using hzR)
  have hσ : (σ : ℂ) = param τ w := by
    simp only [σ, ofComplex_apply_of_im_pos hb.1, UpperHalfPlane.coe_mk]
  have hInv : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R → u ^ e = v ^ e → F u = F v := by
    intro u v hu hv hpow
    have hpu := hbound u (by simpa only [Metric.mem_ball, dist_zero_right] using hu)
    have hpv := hbound v (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
    have hplace := place_eq_of_coord_power_eq N τ (ofComplex (param τ u)) (ofComplex (param τ v))
      (by simpa only [ofComplex_apply_of_im_pos hpu.1, ofComplex_apply_of_im_pos hpv.1,
        coord_param τ hpu.2, coord_param τ hpv.2] using hpow)
    exact congrArg (fun P => originalPlaceEval N ℂ P f) hplace
  obtain ⟨r, ha, hr, hdr, hfg⟩ := PowerDescent.exists_local_branch e he F R hInv z hz hzR
  have hp : AnalyticAt ℂ (param τ) (r z) := by
    rw [hr]
    exact analyticAt_param_of_ne_one τ hb.2
  have hp0 : deriv (param τ) (r z) ≠ 0 := by
    rw [hr]
    exact deriv_param_ne_zero_of_ne_one τ hb.2
  have hmG : MeromorphicAt G (param τ (r z)) := by
    rw [hr, ← hσ]
    exact (meromorphicNFAt_originalPlaceEval N f σ).meromorphicAt
  have hm : MeromorphicAt (F ∘ r) z := (hmG.comp_analyticAt hp).comp_analyticAt ha
  refine ⟨hm.congr (hfg.symm.filter_mono nhdsWithin_le_nhds), ?_, ?_⟩
  · change meromorphicOrderAt (fun t => F (PowerDescent.root e he t)) z = _
    rw [meromorphicOrderAt_congr (hfg.filter_mono nhdsWithin_le_nhds)]
    change meromorphicOrderAt (F ∘ r) z = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero ha hdr]
    change meromorphicOrderAt (G ∘ param τ) (r z) = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero hp hp0, hr, ← hσ]
    simpa only [ofComplex_apply] using originalPlaceEval_meromorphicOrderAt N f hf σ
  · intro hmem
    have hg : AnalyticAt ℂ G (param τ (r z)) := by
      rw [hr, ← hσ]
      exact (originalPlaceEval_analyticAt_iff N f σ).mpr hmem
    exact ((hg.comp hp).comp ha).congr hfg.symm

end
end Dubon2026.SourceFunctionField
