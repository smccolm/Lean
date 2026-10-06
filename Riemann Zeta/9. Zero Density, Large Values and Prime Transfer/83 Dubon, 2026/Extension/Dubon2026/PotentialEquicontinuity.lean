import Dubon2026.PotentialPointwise
import Dubon2026.JessenSlopeBounds
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Uniform spatial control and compact convergence of normalized Jessen functions -/

namespace Dubon2026

open Filter Set
open scoped Topology NNReal

/-- The actual normalized potentials are uniformly 1-Lipschitz for every N ≥ 2. -/
theorem lipschitzWith_normalizedJessen {a : ℕ → ℂ} {N : ℕ}
    (hN : 2 ≤ N) (ha : a 1 = 1) : LipschitzWith 1 (normalizedJessen a N) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdist (x y : ℝ) (hxy : x ≤ y) :
      dist (normalizedJessen a N x) (normalizedJessen a N y) ≤ dist x y := by
    have hm := antitone_jessenFunction (by omega : 1 ≤ N) ha hxy
    have hb := jessen_sub_le_log_mul (by omega : 1 ≤ N) ha hxy
    simp only [Real.dist_eq, normalizedJessen, ← sub_div, abs_div,
      abs_of_pos hlog, abs_of_nonneg (sub_nonneg.mpr hm),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rcases le_total x y with hxy | hyx
  · exact hdist x y hxy
  · simpa only [dist_comm] using hdist y x hyx

/-- A common Lipschitz constant upgrades pointwise convergence to compact convergence. -/
theorem tendstoLocallyUniformly_of_lipschitz {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : ∀ N, LipschitzWith K (F N))
    (hpoint : ∀ x, Tendsto (fun N => F N x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have heq : Equicontinuous (fun N => fun x : S => F N x) :=
    (LipschitzWith.uniformEquicontinuous (fun N => fun x : S => F N x) K
      (fun N => by simpa only [mul_one] using
        (hLip N).comp (LipschitzWith.subtype_val S))).equicontinuous
  have hh := (heq.tendsto_uniformFun_iff_pi atTop (fun x : S => f x)).mpr
    (tendsto_pi_nhds.mpr (fun x => hpoint x))
  exact tendstoUniformlyOn_iff_restrict.mpr (UniformFun.tendsto_iff_tendstoUniformly.mp hh)

/-- The potential conclusion of Theorem 2.2, including the corner at α. -/
theorem tendstoLocallyUniformly_normalizedJessen {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) :
    TendstoLocallyUniformly (normalizedJessen a) (fun σ => max (α - σ) 0) atTop := by
  let F : ℕ → ℝ → ℝ := fun N => normalizedJessen a (max N 2)
  have heq : F =ᶠ[atTop] normalizedJessen a := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    simp only [F, max_eq_left hN]
  have hlim : TendstoLocallyUniformly F (fun σ => max (α - σ) 0) atTop := by
    apply tendstoLocallyUniformly_of_lipschitz
      (fun N => lipschitzWith_normalizedJessen (le_max_right N 2) ha)
    intro σ
    exact (tendsto_normalizedJessen ha hQ hcard hc hH1 hH2 σ).congr'
      (heq.symm.mono fun N hh => congrFun hh σ)
  exact hlim.congr_inseparable (heq.mono fun N hh σ => .of_eq (congrFun hh σ))

end Dubon2026
