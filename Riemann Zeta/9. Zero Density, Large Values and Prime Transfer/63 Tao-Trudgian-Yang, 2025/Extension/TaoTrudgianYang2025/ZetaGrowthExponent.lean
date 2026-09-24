import GuthMaynard.ZeroCount
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The source fixed-line zeta growth exponent

The bound concerns the actual Riemann zeta function at both signs of the
ordinate. The extended-real infimum retains all candidates without
assuming finiteness or a conjectural lower bound.
-/

open Filter
noncomputable section
namespace TaoTrudgianYang2025

def IsZetaGrowthBound (σ μ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧
    ∀ t : ℝ, C ≤ |t| →
      ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C*|t|^(μ+ε)

def zetaGrowthBounds (σ : ℝ) : Set ℝ :=
  {μ | IsZetaGrowthBound σ μ}

def zetaGrowthExponent (σ : ℝ) : EReal :=
  sInf (((fun μ : ℝ => (μ : EReal)) '' zetaGrowthBounds σ) : Set EReal)

theorem zetaGrowthExponent_le_of_bound {σ μ : ℝ} (h : IsZetaGrowthBound σ μ) :
    zetaGrowthExponent σ ≤ (μ : EReal) :=
  sInf_le ⟨μ,h,rfl⟩

theorem IsZetaGrowthBound.mono {σ μ ν : ℝ}
    (h : IsZetaGrowthBound σ μ) (hle : μ ≤ ν) : IsZetaGrowthBound σ ν := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h ε hε
  refine ⟨C,hC,fun t ht => (hbound t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hC.trans ht) (by linarith))
    (zero_le_one.trans hC)

theorem isZetaGrowthBound_of_exponent_le {σ μ : ℝ}
    (h : zetaGrowthExponent σ ≤ (μ : EReal)) : IsZetaGrowthBound σ μ := by
  intro ε hε
  have hlt : zetaGrowthExponent σ < ((μ+ε/2 : ℝ) : EReal) :=
    h.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨x,⟨ν,hν,rfl⟩,hx⟩ := sInf_lt_iff.mp hlt
  have hνμ : ν < μ+ε/2 := EReal.coe_lt_coe_iff.mp hx
  obtain ⟨C,hC,hbound⟩ := hν (ε/2) (by linarith)
  refine ⟨C,hC,fun t ht => (hbound t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hC.trans ht) (by linarith))
    (zero_le_one.trans hC)

theorem zetaGrowthExponent_le_iff {σ μ : ℝ} :
    zetaGrowthExponent σ ≤ (μ : EReal) ↔ IsZetaGrowthBound σ μ :=
  ⟨isZetaGrowthBound_of_exponent_le,zetaGrowthExponent_le_of_bound⟩

theorem norm_zeta_growth_negative_ordinate (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ)+((-t : ℝ) : ℂ)*Complex.I)‖ =
      ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖ := by
  by_cases ht : t = 0
  · subst t
    simp
  have hne : (σ : ℂ)+(t : ℂ)*Complex.I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact ht hi
  have hc : star ((σ : ℂ)+(t : ℂ)*Complex.I) =
      (σ : ℂ)+((-t : ℝ) : ℂ)*Complex.I := by simp
  have h := congrArg norm
    (RiemannZeta.GuthMaynard.riemannZeta_conj ((σ : ℂ)+(t : ℂ)*Complex.I) hne)
  simpa only [hc,norm_star] using h

theorem norm_zeta_growth_abs_ordinate (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ)+((|t| : ℝ) : ℂ)*Complex.I)‖ =
      ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos (le_of_not_ge ht)]
    exact norm_zeta_growth_negative_ordinate σ t

/-- A genuine positive-height estimate with a separate eventual threshold
gives the paper's single-constant bound at both signs of the ordinate. -/
theorem isZetaGrowthBound_of_eventually_positive {σ μ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ t : ℝ in atTop,
        ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ B*t^(μ+ε)) :
    IsZetaGrowthBound σ μ := by
  intro ε hε
  obtain ⟨B,_hB,hbound⟩ := h ε hε
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hbound
  let C := max 1 (max B T₀)
  have hC : 1 ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B T₀).trans (le_max_right _ _)
  have hTC : T₀ ≤ C := (le_max_right B T₀).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro t ht
  rw [← norm_zeta_growth_abs_ordinate σ t]
  exact (hT₀ |t| (hTC.trans ht)).trans
    (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg (abs_nonneg t) _))

end TaoTrudgianYang2025

