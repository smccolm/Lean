import Dubon2026.IsolatedPrimeLower
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Literal energy hypotheses and pointwise convergence of normalized Jessen potentials -/

namespace Dubon2026

open Filter Set
open scoped Topology

noncomputable section

/-- The actual isolated-prime quadratic energy in H2. -/
def isolatedPrimeEnergy (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ Q N, ‖a p‖ ^ 2 * (p : ℝ) ^ (-2 * σ)

/-- The actual fixed-truncation Jessen potential with the source normalization. -/
def normalizedJessen (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : ℝ :=
  jessenFunction a N σ / Real.log N

/-- H1 is pointwise in every real abscissa, including the transition. -/
def GlobalEnergyAsymptotic (a : ℕ → ℂ) (α : ℝ) : Prop :=
  ∀ σ : ℝ, Tendsto (fun N : ℕ => Real.log (coefficientEnergy a N σ) / (2 * Real.log N))
    atTop (𝓝 (max (α - σ) 0))

/-- The energy part of H2 is locally uniform on the open half-line. -/
def IsolatedEnergyAsymptotic (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ) : Prop :=
  TendstoLocallyUniformlyOn
    (fun N : ℕ => fun σ : ℝ => Real.log (isolatedPrimeEnergy a Q N σ) / (2 * Real.log N))
    (fun σ => α - σ) atTop (Iio α)

theorem tendsto_normalizedJessen {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α)
    (hH1 : GlobalEnergyAsymptotic a α) (hH2 : IsolatedEnergyAsymptotic a Q α) (σ : ℝ) :
    Tendsto (fun N => normalizedJessen a N σ) atTop (𝓝 (max (α - σ) 0)) := by
  have hu : ∀ᶠ N : ℕ in atTop, normalizedJessen a N σ ≤
      Real.log (coefficientEnergy a N σ) / (2 * Real.log N) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hh := div_le_div_of_nonneg_right (jessenFunction_bounds (by omega : 1 ≤ N) ha σ).2 hlog.le
    simpa only [normalizedJessen, div_div] using hh
  by_cases hσ : σ < α
  · obtain ⟨C, _, hl⟩ := eventually_isolated_jessen_lower ha hQ hcard hc (l := σ) le_rfl hσ
    have henergy := hH2.tendsto_at hσ
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlow : Tendsto (fun N : ℕ =>
        Real.log (isolatedPrimeEnergy a Q N σ) / (2 * Real.log N) - C / Real.log N)
        atTop (𝓝 (max (α - σ) 0)) := by
      simpa only [sub_zero, max_eq_left (sub_nonneg.mpr hσ.le)] using
        henergy.sub (hlog.const_div_atTop C)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (hH1 σ) ?_ hu
    filter_upwards [hl, eventually_ge_atTop (2 : ℕ)] with N hlN hN
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hh := div_le_div_of_nonneg_right (hlN σ ⟨le_rfl, le_rfl⟩) hlogN.le
    change Real.log (isolatedPrimeEnergy a Q N σ) / (2 * Real.log N) - C / Real.log N ≤ _
    convert hh using 1
    simp only [isolatedPrimeEnergy, sub_div]
    ring
  · have hz : max (α - σ) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt hσ))
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (max (α - σ) 0)) := by
      rw [hz]
      exact tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hzero (hH1 σ) ?_ hu
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact div_nonneg (jessenFunction_bounds (by omega : 1 ≤ N) ha σ).1 hlog.le

end

end Dubon2026
