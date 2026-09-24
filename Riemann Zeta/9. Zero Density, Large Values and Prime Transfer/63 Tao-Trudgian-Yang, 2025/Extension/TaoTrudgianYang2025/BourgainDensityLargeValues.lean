import TaoTrudgianYang2025.BourgainDensityCertificates
import TaoTrudgianYang2025.BourgainLowHeightRows
import TaoTrudgianYang2025.JutilaEnergyRegions
import TaoTrudgianYang2025.LargeValueRegionWitness

/-!
# Actual large-value input for the improved Bourgain density theorem

Jutila k=4 and the proved Bourgain physical source range suffice. There is
no assumed region inequality or unrestricted Bourgain theorem parameter.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem jutila_four_formula (σ τ : ℝ) :
    jutilaLargeValueExponent 4 σ τ =
      max (2-2*σ) (max (τ+(7-11*σ)/2) (τ+24-32*σ)) := by
  unfold jutilaLargeValueExponent
  norm_num
  congr 2 <;> ring

theorem InCardinalityEnergyRegion.bourgain_density_cardinality
    {σ τ ρ energy : ℝ} (h : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτlo : 2*bourgainDensityCutoff σ/3 ≤ τ)
    (hτhi : τ ≤ bourgainDensityCutoff σ) :
    ρ ≤ bourgainDensitySlope σ*τ := by
  have hJ := h.jutila_cardinality 4 (by omega)
  rw [jutila_four_formula] at hJ
  have hfirst := bourgainDensity_first_term hσ hσ₁ hτlo
  by_contra hn
  have hlarge : bourgainDensitySlope σ*τ < ρ := lt_of_not_ge hn
  have hc := bourgainDensity_jutila_side_conditions hσ hσ₁ hτhi hfirst hJ hlarge
  have ha := bourgainDensity_affine_of_jutila_large hσ hσ₁ hfirst hJ hlarge
  by_cases hs : σ ≤ 38/49
  · obtain ⟨hχ,hmargin,_hα,hbound⟩ :=
      bourgainDensity_lower_certificate hσ hs hτhi hc.1 ha
    have hB := h.bourgain_five_terms (α:=τ/3-2*(7*σ-5)/3-max (11-16*σ+τ) 0/6)
      (by linarith : 3/4 < σ) hχ hmargin hc.2.2.1 hc.2.2.2
    exact hn (hB.trans hbound)
  · obtain ⟨hχ,hmargin,_hα,hbound⟩ :=
      bourgainDensity_upper_certificate (le_of_not_ge hs) hσ₁ hτhi hc.1 hc.2.1 hfirst ha
    have hB := h.bourgain_five_terms (α:=τ/3-2*(7*σ-5)/3-max (5*τ/4-1-σ) 0/6)
      (by linarith : 3/4 < σ) hχ hmargin hc.2.2.1 hc.2.2.2
    exact hn (hB.trans hbound)

/-- Genuine uniform cardinality bound, obtained by consuming every actual
region witness in the exact failure-of-uniformity equivalence. -/
theorem bourgainDensity_largeValueBound {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτlo : 2*bourgainDensityCutoff σ/3 ≤ τ)
    (hτhi : τ ≤ bourgainDensityCutoff σ) :
    IsLargeValueBound σ τ (bourgainDensitySlope σ*τ) := by
  apply (isLargeValueBound_iff_region_cardinality
    (by linarith : 1/2 ≤ σ) (by linarith : σ ≤ 1)
    (by linarith [bourgainDensityCutoff_pos hσ] : 0 ≤ τ)).mpr
  intro ρ e s h
  exact (show InCardinalityEnergyRegion σ τ ρ e from ⟨s,h⟩).bourgain_density_cardinality
    hσ hσ₁ hτlo hτhi

theorem largeValueExponent_le_bourgainDensity_range {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτlo : 2*bourgainDensityCutoff σ/3 ≤ τ)
    (hτhi : τ ≤ bourgainDensityCutoff σ) :
    largeValueExponent σ τ ≤ ((bourgainDensitySlope σ*τ : ℝ) : EReal) :=
  largeValueExponent_le_of_bound (bourgainDensity_largeValueBound hσ hσ₁ hτlo hτhi)

end TaoTrudgianYang2025

