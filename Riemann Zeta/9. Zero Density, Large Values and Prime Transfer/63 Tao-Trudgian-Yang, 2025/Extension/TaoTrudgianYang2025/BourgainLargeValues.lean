import TaoTrudgianYang2025.BourgainFullRegion
import TaoTrudgianYang2025.LargeValueExponentAttainment
import TaoTrudgianYang2025.BourgainLargeValueAlgebra

/-!
# The full source Bourgain large-values theorem

The cardinality is the actual large-value exponent, realized by genuine
patterns. Both printed conclusions are derived on the whole source range;
the five-term estimate keeps precisely the printed cardinality cap.
-/

noncomputable section
namespace TaoTrudgianYang2025

def bourgainFiveTermExponent (σ τ α₁ α₂ : ℝ) : ℝ :=
  max (max (max (α₂+2-2*σ) (α₁+α₂/2+2-2*σ)) (-α₂+2*τ+4-8*σ))
    (max (-2*α₁+τ+12-16*σ) (4*α₁+2+max 1 (2*τ-2)-4*σ))

theorem bourgain_largeValue_dichotomy {σ τ α₁ α₂ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    let ρ := (largeValueExponent σ τ).toReal
    ρ ≤ bourgainSmallExponent σ τ α₁ α₂ ∨
      ∃ s : ℝ, 0 ≤ s ∧
        max (-2*α₁+2*σ+s+ρ) (-α₁-α₂/2+2*σ+s/2+3*ρ/2) ≤
          heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ s/2 := by
  obtain ⟨e,s,hm⟩ := exists_energyRegion_at_largeValueExponent hσ hσ1 hτ
  exact (show InCardinalityEnergyRegion σ τ (largeValueExponent σ τ).toReal e
    from ⟨s,hm⟩).bourgain_log_dichotomy_full hα₁ hα₂

theorem largeValueExponent_le_bourgain {σ τ α₁ α₂ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hcap : largeValueExponent σ τ ≤ ((min 1 (4-2*τ) : ℝ) : EReal)) :
    largeValueExponent σ τ ≤ ((bourgainFiveTermExponent σ τ α₁ α₂ : ℝ) : EReal) := by
  have hc := largeValueExponent_coe_toReal hσ hσ1 hτ
  have hr : (largeValueExponent σ τ).toReal ≤ min 1 (4-2*τ) := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hc] using hcap
  have hb := bourgain_simplify_log_dichotomy (hr.trans (min_le_left _ _))
    (hr.trans (min_le_right _ _)) (bourgain_largeValue_dichotomy hσ hσ1 hτ hα₁ hα₂)
  rw [← hc]
  exact EReal.coe_le_coe_iff.mpr hb

theorem bourgain_largeValueBound {σ τ α₁ α₂ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (hcap : largeValueExponent σ τ ≤ ((min 1 (4-2*τ) : ℝ) : EReal)) :
    IsLargeValueBound σ τ (bourgainFiveTermExponent σ τ α₁ α₂) :=
  isLargeValueBound_of_exponent_le
    (largeValueExponent_le_bourgain hσ hσ1 hτ hα₁ hα₂ hcap)

/-- Both printed parts together, at the literal open source domain. -/
theorem bourgain_large_values {σ τ α₁ α₂ : ℝ}
    (hσ : 1/2 < σ) (hσ1 : σ < 1) (hτ : 0 < τ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    let ρ := (largeValueExponent σ τ).toReal
    (ρ ≤ max (max (α₂+2-2*σ) (-α₂+2*τ+4-8*σ)) (-2*α₁+τ+12-16*σ) ∨
      ∃ s : ℝ, 0 ≤ s ∧
        max (-2*α₁+2*σ+s+ρ) (-α₁-α₂/2+2*σ+s/2+3*ρ/2) ≤
          heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ s/2) ∧
    (ρ ≤ min 1 (4-2*τ) →
      ρ ≤ max (max (max (α₂+2-2*σ) (α₁+α₂/2+2-2*σ)) (-α₂+2*τ+4-8*σ))
        (max (-2*α₁+τ+12-16*σ) (4*α₁+2+max 1 (2*τ-2)-4*σ))) := by
  have hd := bourgain_largeValue_dichotomy hσ.le hσ1.le hτ.le hα₁ hα₂
  refine ⟨hd,?_⟩
  intro hc
  exact bourgain_simplify_log_dichotomy (hc.trans (min_le_left _ _))
    (hc.trans (min_le_right _ _)) hd

end TaoTrudgianYang2025

