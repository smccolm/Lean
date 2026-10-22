import Dubon2026.SourceAnalyticUnitRoots
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> compact original curve.
Local analytic multiplicity supplies sufficiently many nearby preimages.
Together with the already proved total original j-fiber degree, it will
exclude additional places outside the chosen finite chart neighborhoods.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.
-/
namespace Dubon2026.SourceFunctionField.AnalyticFiber
noncomputable section
open Filter Set Metric Polynomial
open scoped Topology

theorem exists_finset_preimages_of_meromorphicOrderAt_eq {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0)
    {e : ℕ} (he : 0 < e) (hGe : meromorphicOrderAt G 0 = (e : ℤ)) {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : ℂ, a ≠ 0 → ‖a‖ < η →
      ∃ U : Finset ℂ, e ≤ U.card ∧ ∀ u ∈ U, ‖u‖ < r ∧ G u = a := by
  classical

  obtain ⟨h, hh, hh0, hGh⟩ := (meromorphicOrderAt_eq_int_iff hG.meromorphicAt).mp hGe
  simp only [sub_zero, zpow_natCast, smul_eq_mul] at hGh

  obtain ⟨k, hk, hk0, hkh⟩ := exists_analyticAt_pow_eq hh hh0 he

  set ψ : ℂ → ℂ := fun u => u * k u with hψ_def
  have hψan : AnalyticAt ℂ ψ 0 := analyticAt_id.mul hk
  have hψ0 : ψ 0 = 0 := by simp [hψ_def]
  have hderiv : HasDerivAt ψ (k 0) 0 := by
    have := (hasDerivAt_id (0 : ℂ)).mul hk.differentiableAt.hasDerivAt
    simp at this
    exact this
  have hstrict : HasStrictDerivAt ψ (k 0) 0 := by
    have h1 := hψan.hasStrictDerivAt
    rwa [hderiv.deriv] at h1
  have hGψ : ∀ᶠ u in 𝓝[≠] (0 : ℂ), G u = ψ u ^ e := by
    filter_upwards [hGh, hkh.filter_mono nhdsWithin_le_nhds] with u hu hku
    rw [hu, hψ_def, mul_pow, hku]

  have hinj : ∀ᶠ u in 𝓝 (0 : ℂ),
      hstrict.localInverse ψ (k 0) 0 hk0 (ψ u) = u := hstrict.eventually_left_inverse hk0

  obtain ⟨r₁, hr₁, hr₁sub⟩ :=
    Metric.mem_nhds_iff.mp (hinj.and (eventually_nhdsWithin_iff.mp hGψ))
  set r' := min r r₁ with hr'_def
  have hr' : 0 < r' := lt_min hr hr₁
  have hball : ∀ u : ℂ, ‖u‖ < r' →
      hstrict.localInverse ψ (k 0) 0 hk0 (ψ u) = u ∧ (u ≠ 0 → G u = ψ u ^ e) := by
    intro u hu
    have hu' : u ∈ ball (0 : ℂ) r₁ := by
      rw [mem_ball, dist_zero_right]; exact hu.trans_le (min_le_right _ _)
    exact hr₁sub hu'

  have himage : ψ '' ball (0 : ℂ) r' ∈ 𝓝 (0 : ℂ) := by
    have h1 : map ψ (𝓝 0) = 𝓝 (ψ 0) := hstrict.map_nhds_eq hk0
    rw [hψ0] at h1
    rw [← h1]
    exact image_mem_map (ball_mem_nhds 0 hr')
  obtain ⟨s, hs, hssub⟩ := Metric.mem_nhds_iff.mp himage

  refine ⟨s ^ e, pow_pos hs e, fun a ha0 has => ?_⟩

  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / e)) e :=
    Complex.isPrimitiveRoot_exp e he.ne'
  set B : Finset ℂ := (nthRoots e a).toFinset with hB_def
  have hBcard : B.card = e := by
    rw [hB_def, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ha0), hζ.card_nthRoots,
      if_pos (IsAlgClosed.exists_pow_nat_eq a he)]
  have hBmem : ∀ b ∈ B, b ^ e = a := by
    intro b hb
    rw [hB_def, Multiset.mem_toFinset, mem_nthRoots he] at hb
    exact hb
  have hBsmall : ∀ b ∈ B, b ∈ ball (0 : ℂ) s := by
    intro b hb
    rw [mem_ball, dist_zero_right]
    have h1 : ‖b‖ ^ e < s ^ e := by rw [← norm_pow, hBmem b hb]; exact has
    exact lt_of_pow_lt_pow_left₀ e hs.le h1

  have hpre : ∀ b ∈ B, ∃ u : ℂ, ‖u‖ < r' ∧ ψ u = b := by
    intro b hb
    obtain ⟨u, hu, hub⟩ := hssub (hBsmall b hb)
    rw [mem_ball, dist_zero_right] at hu
    exact ⟨u, hu, hub⟩
  choose! σ hσ hψσ using hpre
  refine ⟨B.image σ, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hBcard]
    intro b hb b' hb' hbb'
    have := congrArg ψ hbb'
    rwa [hψσ b hb, hψσ b' hb'] at this
  · intro u hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨(hσ b hb).trans_le (min_le_left _ _), ?_⟩
    have hσ0 : σ b ≠ 0 := by
      intro h0
      have : b = 0 := by rw [← hψσ b hb, h0, hψ0]
      rw [this] at hb
      have := hBmem 0 hb
      rw [zero_pow he.ne'] at this
      exact ha0 this.symm
    rw [(hball (σ b) (hσ b hb)).2 hσ0, hψσ b hb, hBmem b hb]

end
end Dubon2026.SourceFunctionField.AnalyticFiber
