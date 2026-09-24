import TaoTrudgianYang2025.ZetaGrowthRealMoments
import TaoTrudgianYang2025.ZetaPointwiseNonexistence

/-!
# General high-height zeta nonexistence from actual growth bounds

Arbitrarily high real moments turn a strict pointwise growth gap into a
negative cardinality exponent. The source range tau>=2 is retained.
Nothing here asserts the false unrestricted low-height statement.
-/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem IsZetaGrowthBound.highHeight_exponent_eq_bot
    {c m σ τ : ℝ} (hGrowth : IsZetaGrowthBound c m)
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1)
    (hτ : 2 ≤ τ) (hgap : c+τ*m < σ) :
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
  have hbound := zetaLargeValueExponent_le_of_realMoment_closed_strip
    hc hc1 hp (hGrowth.dyadic_realMoment hp) hσ hσ1 hτ
  apply zetaLargeValueExponent_eq_bot_of_neg
  exact hbound.trans_lt (by exact_mod_cast hneg)

/-- The actual extended-real infimum supplies a genuine growth candidate
strictly below the required threshold. No finiteness or attainment of mu
is assumed. -/
theorem zetaHighHeight_exponent_eq_bot_of_growthExponent
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 2 ≤ τ)
    (hμ : zetaGrowthExponent c < (((σ-c)/τ : ℝ) : EReal)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨x,⟨m,hm,rfl⟩,hlt⟩ := sInf_lt_iff.mp hμ
  have hmr : m < (σ-c)/τ := EReal.coe_lt_coe_iff.mp hlt
  apply hm.highHeight_exponent_eq_bot hc hc1 hσ hσ1 hτ
  have hh := (lt_div_iff₀ (by linarith : 0 < τ)).mp hmr
  nlinarith

/-- Source-style extended-real growth inequality, on the proved
high-height range. The extended-real infimum may be infinite. -/
theorem zetaHighHeight_exponent_eq_bot_of_mu
    {c σ τ : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 2 ≤ τ)
    (hgap : (c : EReal)+(τ : EReal)*zetaGrowthExponent c < (σ : EReal)) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply zetaHighHeight_exponent_eq_bot_of_growthExponent hc hc1 hσ hσ1 hτ
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

theorem IsZetaGrowthBound.oneLine_nonneg {m : ℝ}
    (hGrowth : IsZetaGrowthBound 1 m) : 0 ≤ m := by
  have hh := one_le_zetaOneLine_moment_exponent (p := 1) le_rfl
    (hGrowth.dyadic_realMoment le_rfl)
  linarith

theorem IsZetaGrowthBound.highHeight_empty_threshold
    {c m σ τ : ℝ} (hGrowth : IsZetaGrowthBound c m)
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1)
    (hτ : 2 ≤ τ) (hgap : c+τ*m < σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) →
      P.N^(σ-δ) ≤ P.V → P.V ≤ P.N^(σ+δ) → P.ordinates = ∅ :=
  (zetaLargeValueExponent_eq_bot_iff_empty_threshold σ τ).mp
    (hGrowth.highHeight_exponent_eq_bot hc hc1 hσ hσ1 hτ hgap)

theorem IsZetaGrowthBound.highHeight_pointwise_powerSaving
    {c m σ τ : ℝ} (hGrowth : IsZetaGrowthBound c m)
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1)
    (hτ : 2 ≤ τ) (hgap : c+τ*m < σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2*N) →
      (N : ℝ)^(τ-δ) ≤ t → t ≤ (N : ℝ)^(τ+δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ)^(σ-δ) :=
  exists_zetaPointwise_powerSaving_of_exponent_eq_bot
    (hGrowth.highHeight_exponent_eq_bot hc hc1 hσ hσ1 hτ hgap)

end TaoTrudgianYang2025
