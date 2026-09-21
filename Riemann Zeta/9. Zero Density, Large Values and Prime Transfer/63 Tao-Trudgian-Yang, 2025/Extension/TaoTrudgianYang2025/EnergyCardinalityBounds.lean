import TaoTrudgianYang2025.ClassicalLargeValueRegions
import TaoTrudgianYang2025.GuthMaynardBridge

/-!
# Cardinality constraints on the actual projected energy region

Uniform large-value bounds are consumed through actual realizing patterns.
The powered constraints use only the corrected cardinality witness.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem InLargeValueEnergyRegion.rho_le_of_largeValueBound
    {σ τ ρ e s B : ℝ} (hregion : InLargeValueEnergyRegion σ τ ρ e s)
    (hbound : IsLargeValueBound σ τ B) : ρ ≤ B := by
  by_contra hcontra
  have hgap : 0 < ρ - B := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρ - B) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨K, hK, δ, hδ, hcard⟩ := hbound ε hε
  let C : ℝ := max K (K ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (hK.trans (le_max_left _ _))
  obtain ⟨P, hNLower, hTLower, hTUpper, hVLower, hVUpper, hCardLower, _⟩ :=
    hregion.2.2.2.2.2 ε hε δ hδ C hC
  have hKN : K ≤ P.N := (le_max_left _ _).trans hNLower
  have hCardUpper := hcard P hKN hTLower hTUpper hVLower hVUpper
  have hKPowerBase : K ^ (1 / ε : ℝ) ≤ P.N := (le_max_right _ _).trans hNLower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKAbsorb : K ≤ P.N ^ ε := by
    calc
      K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ = K ^ ((1 / ε) * ε) := by congr 1; field_simp
      _ = (K ^ (1 / ε : ℝ)) ^ ε := Real.rpow_mul hKpos.le _ _
      _ ≤ P.N ^ ε := Real.rpow_le_rpow (by positivity) hKPowerBase hε.le
  have hPowerOrder : P.N ^ (ρ - ε) ≤ P.N ^ (B + 2 * ε) := by
    calc
      P.N ^ (ρ - ε) ≤ (P.ordinates.card : ℝ) := hCardLower
      _ ≤ K * P.N ^ (B + ε) := hCardUpper
      _ ≤ P.N ^ ε * P.N ^ (B + ε) :=
        mul_le_mul_of_nonneg_right hKAbsorb
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (B + 2 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : B + 2 * ε < ρ - ε := by dsimp [ε]; linarith
  exact (not_lt_of_ge hPowerOrder)
    (Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict)


theorem InCardinalityEnergyRegion.rho_le_of_largeValueBound
    {σ τ ρ e B : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hbound : IsLargeValueBound σ τ B) : ρ ≤ B := by
  obtain ⟨s,hs⟩ := h
  exact hs.rho_le_of_largeValueBound hbound

theorem InCardinalityEnergyRegion.mean_square_cardinality
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ max (2-2*σ) (1-2*σ+τ) := by
  apply h.classical_cardinality.trans
  apply max_le_max le_rfl
  have := min_le_left (1-2*σ) (4-6*σ)
  linarith

theorem InCardinalityEnergyRegion.mean_square_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ/k ≤ max (2-2*σ) (1-2*σ+τ/k) := by
  obtain ⟨energy,hregion,_⟩ := (correctedCardinalityEnergyPowering _ _ _ _ k hk h).1
  exact hregion.mean_square_cardinality

theorem InCardinalityEnergyRegion.guthMaynard_cardinality
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e) :
    ρ ≤ guthMaynardLargeValueExponent σ τ := by
  obtain ⟨s,hs⟩ := h
  exact hs.rho_le_of_largeValueBound
    (guthMaynard_largeValueBound hs.1 hs.2.1 hs.2.2.1)

theorem InCardinalityEnergyRegion.guthMaynard_cardinality_powered
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (k : ℕ) (hk : 1 ≤ k) :
    ρ/k ≤ guthMaynardLargeValueExponent σ (τ/k) := by
  obtain ⟨energy,hregion,_⟩ := (correctedCardinalityEnergyPowering _ _ _ _ k hk h).1
  exact hregion.guthMaynard_cardinality

end TaoTrudgianYang2025

