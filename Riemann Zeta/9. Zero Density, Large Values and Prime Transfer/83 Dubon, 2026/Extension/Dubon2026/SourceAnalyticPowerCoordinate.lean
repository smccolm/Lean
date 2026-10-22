import Dubon2026.SourceAnalyticUnitRoots
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! DUB-17/18 -> actual Jacobian torsion -> Abel-Jacobi -> raw reciprocity ->
geometric cell dissection. Branch-point cells require a coordinate in which
the actual local reading is a pure power. Reuse the proved analytic unit-root
lemma and Mathlib's inverse-function theorem; no chart-existence premise.
Source contract: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow.
-/
namespace Dubon2026.SourceFunctionField.AnalyticFiber
noncomputable section
open Filter Set Metric
open scoped Topology

theorem exists_power_coordinate_germ {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0)
    {e : ℕ} (he : 0 < e) (hGe : meromorphicOrderAt G 0 = (e : ℤ)) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧ deriv ψ 0 ≠ 0 ∧
      ∀ᶠ u in 𝓝 0, G u = ψ u ^ e := by
  obtain ⟨h, hh, hh0, hGh⟩ := (meromorphicOrderAt_eq_int_iff hG.meromorphicAt).mp hGe
  simp only [sub_zero, zpow_natCast, smul_eq_mul] at hGh
  obtain ⟨k, hk, hk0, hkh⟩ := exists_analyticAt_pow_eq hh hh0 he
  let ψ : ℂ → ℂ := fun u => u * k u
  have hψ : AnalyticAt ℂ ψ 0 := analyticAt_id.mul hk
  have hd : HasDerivAt ψ (k 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul hk.differentiableAt.hasDerivAt
  refine ⟨ψ, hψ, by simp [ψ], hd.deriv ▸ hk0, ?_⟩
  apply (hG.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hψ.pow e).continuousAt).mp
  filter_upwards [hGh, hkh.filter_mono nhdsWithin_le_nhds] with u hu hku
  change G u = (u * k u) ^ e
  rw [mul_pow, hku, hu]

theorem exists_power_coordinate {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0)
    {e : ℕ} (he : 0 < e) (hGe : meromorphicOrderAt G 0 = (e : ℤ)) :
    ∃ H : OpenPartialHomeomorph ℂ ℂ, 0 ∈ H.source ∧ H 0 = 0 ∧
      AnalyticOnNhd ℂ H H.source ∧ (∀ z ∈ H.source, deriv H z ≠ 0) ∧
      ∀ z ∈ H.source, G z = (H z) ^ e := by
  obtain ⟨ψ, hψ, hψ0, hd, hGψ⟩ := exists_power_coordinate_germ hG he hGe
  have hstrict := hψ.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let H := hstrict.toOpenPartialHomeomorph ψ
  have hH0 : 0 ∈ H.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), deriv ψ z ≠ 0 :=
    hψ.deriv.continuousAt.eventually_ne hd
  obtain ⟨U, hU, hUopen, hU0⟩ :=
    _root_.eventually_nhds_iff.mp (hψ.eventually_analyticAt.and (hne.and hGψ))
  refine ⟨H.restrOpen U hUopen, ⟨hH0, hU0⟩, hψ0, ?_, ?_, ?_⟩
  · intro z hz
    exact (hU z hz.2).1
  · intro z hz
    exact (hU z hz.2).2.1
  · intro z hz
    exact (hU z hz.2).2.2

end
end Dubon2026.SourceFunctionField.AnalyticFiber
