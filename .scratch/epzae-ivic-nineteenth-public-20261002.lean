import TaoTrudgianYang2025
noncomputable section
open Expdb GafniTao RiemannZeta.GuthMaynard
open scoped Interval

namespace IvicNineteenthDensityRegression
open TaoTrudgianYang2025 MeasureTheory

example {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      RiemannZeta.GuthMaynard.IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card : ℝ) ≤ H^ε*(H/V^6+H^3/V^19) :=
  ivicNineteenth_pointValue_card_le hε

example {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 40000 ≤ B ∧ ∀ H U : ℝ, B ≤ H → H^(1/8+ε) ≤ U →
      (∫ t in pointValueSuperlevel H U, zetaMomentCriticalNorm t^6) ≤
        H^ε*(H+H^3/U^13) :=
  ivicNineteenth_restricted_sixth_moment hε

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C B : ℝ, 0 < C ∧ 40000 ≤ B ∧ ∀ T U : ℝ, B ≤ T →
      (4*T)^(1/8+ε) ≤ U →
      (∫ t in -T..T, ivicSixthExcess U t^6) ≤ C*T^ε*(T+T^3/U^13) :=
  ivicNineteenth_excess_symmetric_moment hε

example {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hgap : τ/8 < σ-1/2) :
    IsZetaLargeValueBound σ τ (max (τ+3-6*σ) (3*τ+19/2-19*σ)) :=
  ivicNineteenth_zetaLargeValueBound hσ hτ hgap

example {σ τ : ℝ} (hτ : 0 < τ) (hgap : τ/8 < 2*σ-3/2) :
    IsLargeValueBound σ τ (max (2-2*σ) (max (τ+9-12*σ) (3*τ+57/2-38*σ))) :=
  ivicNineteenth_general_largeValueBound hτ hgap

example {σ : ℝ} (hσ : 155/174 ≤ σ) (hσ₁ : σ ≤ 17/18) :
    TaoTrudgianYang2025.zeroDensityExponent σ ≤ ((24/(30*σ-11):ℝ):EReal) :=
  zeroDensityExponent_le_ivic_nineteenth hσ hσ₁

example :
    TaoTrudgianYang2025.zeroDensityExponent (155/174) ≤
      ((24/(30*(155/174)-11):ℝ):EReal) :=
  zeroDensityExponent_le_ivic_nineteenth (by norm_num) (by norm_num)

example :
    TaoTrudgianYang2025.zeroDensityExponent (9/10) ≤
      ((24/(30*(9/10)-11):ℝ):EReal) :=
  zeroDensityExponent_le_ivic_nineteenth (by norm_num) (by norm_num)

example :
    TaoTrudgianYang2025.zeroDensityExponent (17/18) ≤
      ((24/(30*(17/18)-11):ℝ):EReal) :=
  zeroDensityExponent_le_ivic_nineteenth (by norm_num) (by norm_num)

end IvicNineteenthDensityRegression

#print axioms TaoTrudgianYang2025.ivicNineteenth_pointValue_card_le
#print axioms TaoTrudgianYang2025.ivicNineteenth_restricted_sixth_moment
#print axioms TaoTrudgianYang2025.ivicNineteenth_excess_symmetric_moment
#print axioms TaoTrudgianYang2025.ivicNineteenth_zetaLargeValueBound
#print axioms TaoTrudgianYang2025.ivicNineteenth_general_largeValueBound
#print axioms TaoTrudgianYang2025.zeroDensityExponent_le_ivic_nineteenth
