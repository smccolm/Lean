import TaoTrudgianYang2025.JutilaLargeValues
import TaoTrudgianYang2025.CorrectedEnergyPowering

/-!
# Jutila constraints on actual cardinality-energy regions

The uniform large-value theorem constrains real region witnesses.
Powered constraints consume the cardinality-preserving branch of the
corrected two-witness theorem; no fifth-coordinate scaling is asserted.
-/

open Filter

noncomputable section

namespace TaoTrudgianYang2025

/-- Every uniform large-value bound dominates the cardinality coordinate
of every actual feasible energy-region tuple. -/
theorem InLargeValueEnergyRegion.rho_le_of_largeValueBound
    {σ τ ρ e s b : ℝ} (hregion : InLargeValueEnergyRegion σ τ ρ e s)
    (hbound : IsLargeValueBound σ τ b) : ρ ≤ b := by
  by_contra hnot
  have hgap : 0 < ρ-b := by linarith
  let ε : ℝ := (ρ-b)/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, δ, hδ, hp⟩ := hbound ε hε
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hexp : b+ε < ρ-ε := by dsimp [ε]; linarith
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (D := 2*C) hexp)
  let K : ℝ := max C Na
  have hK : 0 < K := hCp.trans_le (le_max_left _ _)
  obtain ⟨P, hP⟩ := hregion.2.2.2.2.2 ε hε δ hδ K hK
  have hN : C ≤ P.N := (le_max_left _ _).trans hP.1
  have ha : Na ≤ P.N := (le_max_right _ _).trans hP.1
  have hc := hp P hN hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1
  have hl := hP.2.2.2.2.2.1
  have hh := hNa P.N ha
  have hpos : 0 < C*P.N^(b+ε) := mul_pos hCp
    (Real.rpow_pos_of_pos (zero_lt_one.trans P.one_lt_N) _)
  nlinarith

theorem InLargeValueEnergyRegion.jutila_cardinality
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (k : ℕ) (hk : 0 < k) : ρ ≤ jutilaLargeValueExponent k σ τ :=
  h.rho_le_of_largeValueBound (jutila_largeValueBound k hk h.1 h.2.1 h.2.2.1)

theorem InCardinalityEnergyRegion.jutila_cardinality
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 0 < k) : ρ ≤ jutilaLargeValueExponent k σ τ := by
  obtain ⟨s, hs⟩ := h
  exact hs.jutila_cardinality k hk

/-- This is the actual corrected cardinality witness, not the distinct
energy-preserving witness or the disproved printed third witness. -/
theorem InCardinalityEnergyRegion.jutila_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k) :
    ρ/q ≤ jutilaLargeValueExponent k σ (τ/q) := by
  obtain ⟨energy, hregion, _⟩ := (correctedCardinalityEnergyPowering _ _ _ _ q hq h).1
  exact hregion.jutila_cardinality k hk

/-- Literal exponent formula needed by the third Add-est clause. -/
theorem jutila_thirteen_formula (σ τ : ℝ) :
    jutilaLargeValueExponent 13 σ τ =
      max (2-2*σ) (max (τ+50/13-(76/13)*σ) (τ+78-104*σ)) := by
  unfold jutilaLargeValueExponent
  norm_num
  congr 2 <;> ring

theorem InCardinalityEnergyRegion.jutila_thirteen_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (q : ℕ) (hq : 1 ≤ q) :
    ρ/q ≤ max (2-2*σ) (max (τ/q+50/13-(76/13)*σ) (τ/q+78-104*σ)) := by
  simpa only [jutila_thirteen_formula] using
    (h.jutila_cardinality_powered q 13 hq (by norm_num))

end TaoTrudgianYang2025
