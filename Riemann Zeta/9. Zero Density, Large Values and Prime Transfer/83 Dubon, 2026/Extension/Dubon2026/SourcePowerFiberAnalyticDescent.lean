import Dubon2026.SourceAnalyticPowerDescent

/-! DUB-17/18 -> original torsion cardinality -> actual elliptic place
charts. A function constant on the local fibers of the ramified power
coordinate descends by choosing actual complex roots. Equal powers give
equal norms, so every chosen root remains in the same small disk. The
proved power-descent theorem then gives analyticity. This is the local
descent step to be consumed by the original stabilizer action.
-/
namespace Dubon2026.SourceFunctionField.PowerDescent
noncomputable section
open Filter
open scoped Topology

/-- A chosen actual complex root for the ramified coordinate. -/
def root (n : ℕ) (hn : n ≠ 0) (z : ℂ) : ℂ := by
  letI : NeZero n := ⟨hn⟩
  exact ((Complex.isOpenQuotientMap_pow n).surjective z).choose

theorem root_pow (n : ℕ) (hn : n ≠ 0) (z : ℂ) : root n hn z ^ n = z := by
  letI : NeZero n := ⟨hn⟩
  exact ((Complex.isOpenQuotientMap_pow n).surjective z).choose_spec

theorem root_zero (n : ℕ) (hn : n ≠ 0) : root n hn 0 = 0 :=
  (pow_eq_zero_iff hn).mp (root_pow n hn 0)

theorem norm_root_power (n : ℕ) (hn : n ≠ 0) (z : ℂ) : ‖root n hn (z ^ n)‖ = ‖z‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn).mp
  rw [← norm_pow, root_pow, norm_pow]

theorem analyticAt_root_composite (n : ℕ) (hn : n ≠ 0) (F : ℂ → ℂ)
    (hF : AnalyticAt ℂ F 0) (R : ℝ) (hR : 0 < R)
    (hInv : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R → u ^ n = v ^ n → F u = F v) :
    AnalyticAt ℂ (fun z => F (root n hn z)) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), F (root n hn (z ^ n)) = F z := by
  have he : (fun z : ℂ => F (root n hn (z ^ n))) =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
    have hz' : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact hInv _ z (by rwa [norm_root_power]) hz' (root_pow n hn _)
  exact ⟨analyticAt_of_comp_power n hn _ (hF.congr he.symm), he⟩

end
end Dubon2026.SourceFunctionField.PowerDescent
