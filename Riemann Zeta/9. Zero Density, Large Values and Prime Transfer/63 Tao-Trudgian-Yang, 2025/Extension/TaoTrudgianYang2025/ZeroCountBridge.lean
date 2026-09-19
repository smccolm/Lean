import GuthMaynard.ZeroCount

/-!
# Zero-count convention bridge

The canonical local Guth--Maynard source already uses the paper's global
rectangle: real part in `[σ,1]`, imaginary part in `[-T,T]`, and analytic
multiplicity. This module exposes that agreement under source-facing names.
-/

open Complex

namespace TaoTrudgianYang2025

open RiemannZeta.GuthMaynard

/-- The distinct zeta zeros underlying the paper's multiplicity-weighted
count. -/
noncomputable def paperZeros (σ T : ℝ) : Finset ℂ :=
  zerosInRect σ 1 (-T) T

/-- Membership in the local rectangle is exactly the paper's
`Re ρ ≥ σ`, `|Im ρ| ≤ T` convention (together with the harmless upper edge
`Re ρ ≤ 1`). -/
theorem mem_paperZeros_iff {σ T : ℝ} (ρ : ℂ) :
    ρ ∈ paperZeros σ T ↔
      σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0 := by
  rw [paperZeros, zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle, Set.mem_setOf_eq, abs_le]
  constructor
  · rintro ⟨⟨hσ, hOne, hLower, hUpper⟩, hzero⟩
    exact ⟨hσ, hOne, ⟨by linarith, hUpper⟩, hzero⟩
  · rintro ⟨hσ, hOne, ⟨hLower, hUpper⟩, hzero⟩
    exact ⟨⟨hσ, hOne, by linarith, hUpper⟩, hzero⟩

/-- The paper's zero count, with every distinct zero weighted by its analytic
order of vanishing. -/
noncomputable def paperZeroCount (σ T : ℝ) : ℕ :=
  ∑ ρ ∈ paperZeros σ T, analyticVanishingOrder riemannZeta ρ

/-- Exact bridge to the local rectangle count. -/
theorem paperZeroCount_eq_zeroCountRect (σ T : ℝ) :
    paperZeroCount σ T = zeroCountRect σ 1 (-T) T := by
  rfl

/-- Exact bridge to the canonical local `N(σ,T)`. -/
theorem paperZeroCount_eq_localN (σ T : ℝ) :
    paperZeroCount σ T = RiemannZeta.GuthMaynard.N σ T := by
  rfl

end TaoTrudgianYang2025
