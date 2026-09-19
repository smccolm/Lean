import TaoTrudgianYang2025.LargeValuePattern
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Large-value exponents

The predicates below are the source's fixed-parameter epsilon--delta
formulation.  Constants and approximation radii occur before the pattern,
so their required uniformity is visible in the type.
-/

namespace TaoTrudgianYang2025

/-- A real candidate upper bound for `LV(σ,τ)`. -/
def IsLargeValueBound (σ τ ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ P : LargeValuePattern,
          C ≤ P.N →
          P.N ^ (τ - δ) ≤ P.T →
          P.T ≤ P.N ^ (τ + δ) →
          P.N ^ (σ - δ) ≤ P.V →
          P.V ≤ P.N ^ (σ + δ) →
          (P.ordinates.card : ℝ) ≤ C * P.N ^ (ρ + ε)

/-- A real candidate upper bound for `LV_ζ(σ,τ)`. -/
def IsZetaLargeValueBound (σ τ ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ P : ZetaLargeValuePattern,
          C ≤ P.N →
          P.N ^ (τ - δ) ≤ P.T →
          P.T ≤ P.N ^ (τ + δ) →
          P.N ^ (σ - δ) ≤ P.V →
          P.V ≤ P.N ^ (σ + δ) →
          (P.ordinates.card : ℝ) ≤ C * P.N ^ (ρ + ε)

def largeValueBounds (σ τ : ℝ) : Set ℝ :=
  {ρ | IsLargeValueBound σ τ ρ}

def zetaLargeValueBounds (σ τ : ℝ) : Set ℝ :=
  {ρ | IsZetaLargeValueBound σ τ ρ}

/-- The least large-value exponent, with `-∞` available when no patterns
occur eventually. -/
noncomputable def largeValueExponent (σ τ : ℝ) : EReal :=
  sInf (((fun ρ : ℝ ↦ (ρ : EReal)) '' largeValueBounds σ τ) : Set EReal)

/-- The least zeta large-value exponent. -/
noncomputable def zetaLargeValueExponent (σ τ : ℝ) : EReal :=
  sInf (((fun ρ : ℝ ↦ (ρ : EReal)) '' zetaLargeValueBounds σ τ) : Set EReal)

theorem largeValueExponent_le_of_bound {σ τ ρ : ℝ}
    (hρ : IsLargeValueBound σ τ ρ) :
    largeValueExponent σ τ ≤ (ρ : EReal) := by
  apply sInf_le
  exact ⟨ρ, hρ, rfl⟩

theorem zetaLargeValueExponent_le_of_bound {σ τ ρ : ℝ}
    (hρ : IsZetaLargeValueBound σ τ ρ) :
    zetaLargeValueExponent σ τ ≤ (ρ : EReal) := by
  apply sInf_le
  exact ⟨ρ, hρ, rfl⟩

/-- Forgetting the zeta restrictions turns any general large-value bound into
the corresponding zeta bound. -/
theorem IsLargeValueBound.toZeta {σ τ ρ : ℝ}
    (hρ : IsLargeValueBound σ τ ρ) :
    IsZetaLargeValueBound σ τ ρ := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ := hρ ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTLower hTUpper hVLower hVUpper
  exact hbound P.toLargeValuePattern hN hTLower hTUpper hVLower hVUpper

theorem zetaLargeValueExponent_le_largeValueExponent (σ τ : ℝ) :
    zetaLargeValueExponent σ τ ≤ largeValueExponent σ τ := by
  apply sInf_le_sInf
  rintro x ⟨ρ, hρ, rfl⟩
  exact ⟨ρ, hρ.toZeta, rfl⟩

/-- The one-separation bound `|W| ≤ T+1` gives the obvious estimate
`LV(σ,τ) ≤ τ`. -/
theorem obvious_largeValueBound (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ τ := by
  intro ε hε
  refine ⟨2, by norm_num, ε / 2, by linarith, ?_⟩
  intro P hN _ hTUpper _ _
  have hNone : 1 ≤ P.N := by linarith
  have hexponent : 0 ≤ τ + ε / 2 := by linarith
  have honePow : 1 ≤ P.N ^ (τ + ε / 2) :=
    Real.one_le_rpow hNone hexponent
  calc
    (P.ordinates.card : ℝ) ≤ P.T + 1 := P.ordinate_card_cast_le
    _ ≤ P.N ^ (τ + ε / 2) + 1 := by linarith
    _ ≤ 2 * P.N ^ (τ + ε / 2) := by linarith
    _ ≤ 2 * P.N ^ (τ + ε) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)) (by norm_num)

theorem largeValueExponent_le_tau (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ (τ : EReal) :=
  largeValueExponent_le_of_bound (obvious_largeValueBound σ hτ)

theorem zetaLargeValueExponent_le_tau (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (τ : EReal) :=
  zetaLargeValueExponent_le_of_bound (obvious_largeValueBound σ hτ).toZeta

end TaoTrudgianYang2025
