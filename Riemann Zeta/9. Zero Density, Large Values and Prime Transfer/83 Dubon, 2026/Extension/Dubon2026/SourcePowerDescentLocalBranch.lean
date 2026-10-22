import Dubon2026.SourcePowerFiberAnalyticDescent

/-! DUB-17/18 -> original torsion cardinality -> compatible complex
place charts. Away from zero, a function constant on the local power
fibers agrees locally with composition along an actual analytic inverse
branch of that power. The branch has nonzero derivative; this will
transport original meromorphic orders throughout the finite-place chart.
-/
namespace Dubon2026.SourceFunctionField.PowerDescent
noncomputable section
open Filter
open scoped Topology

theorem exists_local_branch (n : ℕ) (hn : n ≠ 0) (F : ℂ → ℂ)
    (R : ℝ) (hInv : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R → u ^ n = v ^ n → F u = F v)
    (z : ℂ) (hz : z ≠ 0) (hR : ‖root n hn z‖ < R) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z ∧ r z = root n hn z ∧ deriv r z ≠ 0 ∧
      (fun t => F (root n hn t)) =ᶠ[𝓝 z] (fun t => F (r t)) := by
  let w := root n hn z
  let P : ℂ → ℂ := fun u => u ^ n
  have hw : w ≠ 0 := by
    intro he
    have h := root_pow n hn z
    change w ^ n = z at h
    rw [he, zero_pow hn] at h
    exact hz h.symm
  have hP : AnalyticAt ℂ P w := analyticAt_id.pow n
  have hPw : P w = z := root_pow n hn z
  have hd : deriv P w ≠ 0 := by
    rw [(hasDerivAt_pow n w).deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hw)
  let r := hP.hasStrictDerivAt.localInverse P (deriv P w) w hd
  have ha : AnalyticAt ℂ r z := by simpa only [hPw] using hP.analyticAt_localInverse hd
  have hr : r z = w := by
    simpa only [hPw] using
      (HasStrictDerivAt.eventually_left_inverse hP.hasStrictDerivAt hd).self_of_nhds
  have hdr : HasStrictDerivAt r (deriv P w)⁻¹ z := by
    simpa only [hPw] using hP.hasStrictDerivAt.to_localInverse hd
  refine ⟨r, ha, hr, ?_, ?_⟩
  · rw [hdr.hasDerivAt.deriv]
    exact inv_ne_zero hd
  · have he : ∀ᶠ t in 𝓝 z, P (r t) = t := by
      simpa only [hPw] using HasStrictDerivAt.eventually_right_inverse hP.hasStrictDerivAt hd
    have hb : ∀ᶠ t in 𝓝 z, ‖r t‖ < R := by
      apply ha.continuousAt.norm.eventually (Iio_mem_nhds ?_)
      change ‖r z‖ < R
      rwa [hr]
    filter_upwards [he, hb] with t ht hbt
    have ht' : r t ^ n = t := ht
    have hnorm : ‖root n hn t‖ = ‖r t‖ := by
      calc ‖root n hn t‖ = ‖root n hn (r t ^ n)‖ := congrArg (fun s => ‖root n hn s‖) ht'.symm
           _ = ‖r t‖ := norm_root_power n hn (r t)
    exact hInv _ _ (hnorm ▸ hbt) hbt ((root_pow n hn t).trans ht'.symm)

end
end Dubon2026.SourceFunctionField.PowerDescent
