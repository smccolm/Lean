import Dubon2026.SourceAnalyticUnitRoots
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> auxiliary Kummer point division -> analytic cover route.
At a place where the radicand order is n times an integer, its meromorphic
reading has a local n-th root. This reuses the proved analytic unit-root
theorem; it supplies the local analytic entry for the actual torsion cover,
not its global manifold or Picard divisibility. -/
namespace Dubon2026.SourceFunctionField.AnalyticFiber
noncomputable section
open Filter
open scoped Topology

theorem exists_analytic_unit_kummer_factor {G : ℂ → ℂ} (hG : MeromorphicAt G 0)
    (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hord : meromorphicOrderAt G 0 = ((n : ℤ) * k : ℤ)) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a 0 ∧ a 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = (z ^ k * a z) ^ n := by
  obtain ⟨b, hb, hb0, hGb⟩ := (meromorphicOrderAt_eq_int_iff hG).mp hord
  obtain ⟨a, ha, ha0, hab⟩ := exists_analyticAt_pow_eq hb hb0 hn
  refine ⟨a, ha, ha0, ?_⟩
  filter_upwards [hGb, hab.filter_mono nhdsWithin_le_nhds] with z hz hza
  rw [hz, sub_zero, smul_eq_mul, mul_pow, hza, ← zpow_natCast, ← zpow_mul, mul_comm k]

theorem exists_meromorphic_kummer_root {G : ℂ → ℂ} (hG : MeromorphicAt G 0)
    (n : ℕ) (hn : 0 < n) (k : ℤ)
    (hord : meromorphicOrderAt G 0 = ((n : ℤ) * k : ℤ)) :
    ∃ H : ℂ → ℂ, MeromorphicAt H 0 ∧ meromorphicOrderAt H 0 = k ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z ^ n = G z := by
  obtain ⟨a, ha, ha0, hGa⟩ := exists_analytic_unit_kummer_factor hG n hn k hord
  have hH : MeromorphicAt (fun z : ℂ => z ^ k * a z) 0 :=
    (analyticAt_id.meromorphicAt.zpow k).mul ha.meromorphicAt
  refine ⟨fun z => z ^ k * a z, hH, ?_, hGa.mono (fun _ hz => hz.symm)⟩
  apply (meromorphicOrderAt_eq_int_iff hH).mpr
  exact ⟨a, ha, ha0, Filter.Eventually.of_forall (fun z => by simp only [sub_zero, smul_eq_mul])⟩

end
end Dubon2026.SourceFunctionField.AnalyticFiber
