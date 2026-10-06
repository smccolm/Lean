import Dubon2026.DirichletPolynomial
import Dubon2026.JessenMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Nat

/-! # Support consequences of the source's actual isolated-prime comparability hypothesis -/

namespace Dubon2026

open Filter Set
open scoped Topology

/-- The exact prime location required by the abstract criterion. -/
def IsolatedPrimeBlocks (Q : ℕ → Finset ℕ) : Prop :=
  ∀ N p, p ∈ Q N → Nat.Prime p ∧ (N : ℝ) / 2 < p ∧ p ≤ N

/-- The comparability part of H2, uniformly on each closed compact interval below alpha.
This states the literal coefficient ratios; it does not assume support or density consequences. -/
def PrimeCoefficientComparability (a : ℕ → ℂ) (Q : ℕ → Finset ℕ) (α : ℝ) : Prop :=
  ∀ l u : ℝ, l ≤ u → u < α → ∃ K : ℝ, 1 ≤ K ∧
    ∀ᶠ N : ℕ in atTop, ∀ σ ∈ Icc l u, ∀ p ∈ Q N, ∀ q ∈ Q N,
      K⁻¹ ≤ (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ∧
      (‖a p‖ * (p : ℝ) ^ (-σ)) / (‖a q‖ * (q : ℝ) ^ (-σ)) ≤ K

theorem eventually_primeBlock_coefficients_ne_zero {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (hc : PrimeCoefficientComparability a Q α) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ Q N, a p ≠ 0 := by
  obtain ⟨K, hK, hk⟩ := hc (α - 1) (α - 1) le_rfl (by linarith)
  filter_upwards [hk] with N hn
  intro p hp hz
  have hh := (hn (α - 1) ⟨le_rfl, le_rfl⟩ p hp p hp).1
  have hi : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  simp only [hz, norm_zero, zero_mul, zero_div] at hh
  exact (not_le_of_gt hi) hh

theorem eventually_isolated_lastIndex_bounds {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / 2 < lastIndex a N ∧ lastIndex a N ≤ N ∧ 1 < lastIndex a N := by
  filter_upwards [eventually_primeBlock_coefficients_ne_zero hc,
    hcard.eventually_ge_atTop 1] with N hn hcardN
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Q N).card by omega)
  obtain ⟨hprime, hhalf, hpN⟩ := hQ N p hp
  have hpM := le_lastIndex (mem_coefficientSupport.mpr ⟨hprime.one_lt.le, hpN, hn p hp⟩)
  have hpMr : (p : ℝ) ≤ lastIndex a N := by exact_mod_cast hpM
  exact ⟨hhalf.trans_le hpMr, lastIndex_le a N, hprime.one_lt.trans_le hpM⟩

theorem tendsto_isolated_lastIndex_atTop {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    Tendsto (fun N => (lastIndex a N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' _ ?_
    (tendsto_natCast_atTop_atTop.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
  filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc] with N hn
  exact hn.1.le

theorem tendsto_isolated_log_lastIndex_ratio {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    Tendsto (fun N => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    hlog.const_div_atTop (Real.log 2)
  have hl : Tendsto (fun N : ℕ => 1 - Real.log 2 / Real.log N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc,
      eventually_ge_atTop (2 : ℕ)] with N hn hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNp : (0 : ℝ) < N := by linarith
    have hlogN := Real.log_pos hNr
    have hlM := Real.log_le_log (div_pos hNp (by norm_num)) hn.1.le
    rw [Real.log_div hNp.ne' (by norm_num)] at hlM
    have hd := div_le_div_of_nonneg_right hlM hlogN.le
    simpa only [sub_div, div_self hlogN.ne'] using hd
  · filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc,
      eventually_ge_atTop (2 : ℕ)] with N hn hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hMp : (0 : ℝ) < lastIndex a N := by exact_mod_cast (show 0 < lastIndex a N by omega)
    have hlM := Real.log_le_log hMp
      (show (lastIndex a N : ℝ) ≤ (N : ℝ) by exact_mod_cast hn.2.1)
    have hd := div_le_div_of_nonneg_right hlM (Real.log_pos hNr).le
    simpa only [div_self (Real.log_pos hNr).ne'] using hd

theorem eventually_isolated_jessen_probability {a : ℕ → ℂ} {Q : ℕ → Finset ℕ} {α : ℝ}
    (ha : a 1 = 1) (hQ : IsolatedPrimeBlocks Q)
    (hcard : Tendsto (fun N => (Q N).card) atTop atTop)
    (hc : PrimeCoefficientComparability a Q α) :
    ∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N,
      MeasureTheory.IsProbabilityMeasure (normalizedJessenMeasure hN (ha.trans_ne one_ne_zero)) := by
  filter_upwards [eventually_isolated_lastIndex_bounds hQ hcard hc] with N hn
  have hN : 1 ≤ N := (le_of_lt hn.2.2).trans hn.2.1
  exact ⟨hN, normalizedJessenMeasure_isProbability hN ha hn.2.2⟩

end Dubon2026
