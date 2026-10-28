import Dubon2026.SourceComplexWedgeLocalLog

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> smooth local comparison
function. Its exact local integer orders give the wedge/residue identity
by compact-support integration by parts, the proved simple-pole kernel,
and native smooth partition of unity. Holomorphicity of the smooth
comparison function is not assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Wedge
noncomputable section
open MeasureTheory Filter Complex Metric Set DbarFundamental
open scoped Topology Real Manifold ContDiff

variable {a : ℂ} {r : ℝ} {n : ℤ} {Ψ Φ E E' k : ℂ → ℂ}
  (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
  (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0)
  (hΦ : ∀ z ∈ ball a r, Φ z = (z - a) ^ n * Ψ z)
  (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z)
  (hk : ContDiff ℝ 2 k) (hks : HasCompactSupport k) (hkr : tsupport k ⊆ ball a r)

include hΨ hΨ1 hΨa hΦ hE hk hks hkr in

theorem disc_identity :
    Integrable (fun z => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) ∧
    Integrable (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) +
      2 * ((n : ℂ) * E a * k a) =
    2 / π * ∫ z, E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  have hv2 : ContDiff ℝ 2 (vEk E k) := contDiff_vEk hE hk hkr
  have hv1 : ContDiff ℝ 1 (vEk E k) := hv2.of_le (by norm_num)
  have hvs : HasCompactSupport (vEk E k) := hasCompactSupport_vEk hks
  have hvt : tsupport (vEk E k) ⊆ ball a r := tsupport_vEk.trans hkr
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hLg := contDiffOn_Lg hΨ hΨ1
  have hLg' : ContinuousOn (fderiv ℝ (Lg Ψ a)) (ball a r) :=
    hLg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hLx : ContinuousOn (fun z => fderiv ℝ (Lg Ψ a) z 1) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hLy : ContinuousOn (fun z => fderiv ℝ (Lg Ψ a) z I) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hDL : ContinuousOn (D (Lg Ψ a)) (ball a r) := by
    unfold D; exact (hLx.add (continuousOn_const.mul hLy)).div_const _
  have hE'c := continuousOn_E' hE

  set P1 : ℂ → ℂ := fun z => (z - a)⁻¹ * D (vEk E k) z with hP1
  set P2 : ℂ → ℂ := fun z => fderiv ℝ (Lg Ψ a) z 1 * fderiv ℝ (vEk E k) z I -
    fderiv ℝ (Lg Ψ a) z I * fderiv ℝ (vEk E k) z 1 with hP2
  set P3 : ℂ → ℂ := fun z => E' z * D (Lg Ψ a) z * k z with hP3
  have iP1 : Integrable P1 := integrable_inv_sub_mul a (D_continuous hv1) (D_hasCompactSupport hvs)
  obtain ⟨hvxc, hvxs, hvxt⟩ := fderiv_apply_props hv1 hvs 1
  obtain ⟨hvyc, hvys, hvyt⟩ := fderiv_apply_props hv1 hvs I
  have iP2 : Integrable P2 :=
    (integrable_mul_of_tsupport_subset isOpen_ball hLx hvyc hvys (hvyt.trans hvt)).sub
      (integrable_mul_of_tsupport_subset isOpen_ball hLy hvxc hvxs (hvxt.trans hvt))
  have iP3 : Integrable P3 :=
    integrable_mul_of_tsupport_subset isOpen_ball (hE'c.mul hDL) hk.continuous hks hkr

  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ a := by
    have : ({a}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) := compl_mem_ae_iff.2 (measure_singleton a)
    filter_upwards [this] with z hz using hz
  have hpt1 : ∀ z, z ≠ a → E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1) =
      -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := Φ_ne hΨ1 hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP1, hP2, hP3, fderiv_vEk hE hk hz, D]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z * I + E z * n * fderiv ℝ k z I +
        (z - a) * fderiv ℝ (Lg Ψ a) z I * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      have hzv : z ∉ tsupport (vEk E k) := fun h' => hz (hvt h')
      simp only [hP1, hP2, hP3, fderiv_of_notMem_tsupport ℝ hzk, fderiv_of_notMem_tsupport ℝ hzv,
        image_eq_zero_of_notMem_tsupport hzk, D_eq_zero_of_notMem_tsupport hzv]
      simp
  have hpt2 : ∀ z, z ≠ a →
      E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) = P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := Φ_ne hΨ1 hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP3, D]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      simp only [hP3, image_eq_zero_of_notMem_tsupport hzk]
      simp
  have hae1 : (fun z => E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) =ᵐ[volume]
      fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    filter_upwards [hae] with z hz using hpt1 z hz
  have hae2 : (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) =ᵐ[volume]
      P3 := by
    filter_upwards [hae] with z hz using hpt2 z hz
  have iA1 : Integrable fun z => -2 * I * n * P1 z := iP1.const_mul _
  have iA : Integrable fun z => -2 * I * n * P1 z + P2 z := iA1.add iP2
  have iB : Integrable fun z => 2 * I * P3 z := iP3.const_mul _
  have iRHS : Integrable fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := iA.sub iB
  refine ⟨iRHS.congr hae1.symm, iP3.congr hae2.symm, ?_⟩
  rw [integral_congr_ae hae1, integral_congr_ae hae2, integral_sub iA iB, integral_add iA1 iP2,
    integral_const_mul, integral_const_mul]

  have vP1 : ∫ z, P1 z = -π * (E a * k a) := by
    have := DbarFundamental.integral_inv_sub_mul_dbar a (vEk E k) hv1 hvs
    simpa [hP1, D, vEk] using this
  have vP2 : ∫ z, P2 z = 0 := integral_wedge_eq_zero isOpen_ball hLg hv2 hvs hvt
  rw [vP1, vP2]
  have hI : I * I = -1 := Complex.I_mul_I
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (2 * (n : ℂ) * (E a * k a) * π - 2 * ∫ z, P3 z) * hI

end
end Dubon2026.SourceComplexReciprocity.Wedge
