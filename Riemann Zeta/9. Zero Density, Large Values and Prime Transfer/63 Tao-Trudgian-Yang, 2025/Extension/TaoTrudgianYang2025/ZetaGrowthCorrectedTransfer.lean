import TaoTrudgianYang2025.ZetaRealMomentAboveOne
import TaoTrudgianYang2025.ZetaGrowthHeightOne
import TaoTrudgianYang2025.ZetaLowHeightVanishing

/-! Corrected general growth transfer, with the essential residual condition explicit. -/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem IsZetaGrowthBound.aboveOne_exponent_eq_bot
    {c m σ τ : ℝ} (hGrowth : IsZetaGrowthBound c m)
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1)
    (hτ : 1 < τ) (hgap : c+τ*m < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  let g : ℝ := σ-c-τ*m
  have hg : 0 < g := by dsimp [g]; linarith
  let p : ℝ := 1+(τ+1)/g
  have hp : 1 ≤ p := by
    have hh : 0 ≤ (τ+1)/g := div_nonneg (by linarith) hg.le
    dsimp [p]
    linarith
  have hpg : p*g = g+τ+1 := by dsimp [p]; field_simp; ring
  have hneg : τ*(1+p*m)-p*(σ-c) < 0 := by
    have heq : τ*(1+p*m)-p*(σ-c) = τ-p*g := by dsimp [g]; ring
    rw [heq,hpg]
    linarith
  have hbound := zetaLargeValueExponent_le_of_realMoment_closedStrip_aboveOne
    hc hc1 hp (hGrowth.dyadic_realMoment hp) hσ hσ1 hτ
  apply zetaLargeValueExponent_eq_bot_of_neg
  exact hbound.trans_lt (by exact_mod_cast hneg)

/-- The actual extended-real infimum supplies a genuine growth candidate
strictly below the required threshold. No finiteness or attainment of mu
is assumed. -/
theorem zetaAboveOne_exponent_eq_bot_of_growthExponent
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 1 < τ)
    (hμ : zetaGrowthExponent c < (((σ-c)/τ : ℝ) : EReal)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨x,⟨m,hm,rfl⟩,hlt⟩ := sInf_lt_iff.mp hμ
  have hmr : m < (σ-c)/τ := EReal.coe_lt_coe_iff.mp hlt
  apply hm.aboveOne_exponent_eq_bot hc hc1 hσ hσ1 hτ
  have hh := (lt_div_iff₀ (by linarith : 0 < τ)).mp hmr
  nlinarith

/-- Source-style extended-real growth inequality, on the proved
above-one range. The extended-real infimum may be infinite. -/
theorem zetaAboveOne_exponent_eq_bot_of_mu
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 1 < τ)
    (hgap : (c : EReal)+(τ : EReal)*zetaGrowthExponent c < (σ : EReal)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply zetaAboveOne_exponent_eq_bot_of_growthExponent hc hc1 hσ hσ1 hτ
  by_contra hnot
  have hτp : 0 < τ := by linarith
  have hmul : (τ : EReal)*(((σ-c)/τ : ℝ) : EReal) ≤
      (τ : EReal)*zetaGrowthExponent c :=
    mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (by exact_mod_cast hτp.le)
  have hlower : (σ : EReal) ≤ (c : EReal)+(τ : EReal)*zetaGrowthExponent c := by
    calc
      _ = (c : EReal)+(τ : EReal)*(((σ-c)/τ : ℝ) : EReal) := by
        rw [← EReal.coe_mul,← EReal.coe_add]
        congr 1
        field_simp
        ring
      _ ≤ _ := add_le_add le_rfl hmul
  exact (not_lt_of_ge hlower) hgap


/-- The corrected growth transfer retains the essential low-height
residual condition. The false printed unrestricted contract is not
used or redefined. -/
theorem IsZetaGrowthBound.corrected_exponent_eq_bot
    {c m σ τ : ℝ} (hGrowth : IsZetaGrowthBound c m)
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1)
    (hres : 1-τ < σ) (hgap : c+τ*m < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  rcases lt_trichotomy τ 1 with hlt | heq | hgt
  · exact zetaLargeValueExponent_eq_bot_of_lowHeight hlt hres
  · subst τ
    apply hGrowth.heightOne_exponent_eq_bot hc hc1
    simpa only [one_mul] using hgap
  · exact hGrowth.aboveOne_exponent_eq_bot hc hc1 hσ hσ1 hgt hgap

theorem zetaCorrected_exponent_eq_bot_of_mu
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hres : 1-τ < σ)
    (hgap : (c : EReal)+(τ : EReal)*zetaGrowthExponent c < (σ : EReal)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  rcases lt_trichotomy τ 1 with hlt | heq | hgt
  · exact zetaLargeValueExponent_eq_bot_of_lowHeight hlt hres
  · subst τ
    apply zetaHeightOne_exponent_eq_bot_of_mu hc hc1
    simpa only [EReal.coe_one,one_mul] using hgap
  · exact zetaAboveOne_exponent_eq_bot_of_mu hc hc1 hσ hσ1 hgt hgap

theorem zetaCorrected_empty_threshold_of_mu
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hres : 1-τ < σ)
    (hgap : (c : EReal)+(τ : EReal)*zetaGrowthExponent c < (σ : EReal)) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
      P.N^(σ-δ) ≤ P.V → P.V ≤ P.N^(σ+δ) → P.ordinates = ∅ :=
  (zetaLargeValueExponent_eq_bot_iff_empty_threshold σ τ).mp
    (zetaCorrected_exponent_eq_bot_of_mu hc hc1 hσ hσ1 hres hgap)

theorem zetaCorrected_pointwise_powerSaving_of_mu
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hres : 1-τ < σ)
    (hgap : (c : EReal)+(τ : EReal)*zetaGrowthExponent c < (σ : EReal)) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2*N) →
      (N : ℝ)^(τ-δ) ≤ t → t ≤ (N : ℝ)^(τ+δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ)^(σ-δ) :=
  exists_zetaPointwise_powerSaving_of_exponent_eq_bot
    (zetaCorrected_exponent_eq_bot_of_mu hc hc1 hσ hσ1 hres hgap)

end TaoTrudgianYang2025
