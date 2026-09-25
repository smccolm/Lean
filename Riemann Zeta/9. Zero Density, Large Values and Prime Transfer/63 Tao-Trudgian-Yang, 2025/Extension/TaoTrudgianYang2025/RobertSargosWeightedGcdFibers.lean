import TaoTrudgianYang2025.RobertSargosGcdScale

/-! Uniform bounds on actual gcd fibers, in a form ready for harmonic summation. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_weighted_gcd_fiber_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (j k : ℕ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      1 ≤ j → 1 ≤ k → (k:ℝ) ≤ 2*Q →
      (∀ p ∈ S, RobertSargosReducedSystem R H Q δ p) →
      (∀ p ∈ S, j = robertSargosCoefficientGcd p) →
      (∀ p ∈ S, k = robertSargosFrequencyGcd p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q)/((j:ℝ)*(k:ℝ)) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_gcd_fiber_count ε hε
  refine ⟨C*(4*(2:ℝ)^ε),by positivity,?_⟩
  intro S R H Q δ j k hR hH hQ hδ hRH hj hk hkQ hmem hjfix hkfix
  have ha := robertSargos_gcd_scale_bound (j := (j:ℝ)) (k := (k:ℝ)) hR hH hQ hδ hε.le
    (by exact_mod_cast hj) (by exact_mod_cast hk) hkQ
  calc
    _ ≤ C*((R/j)*(H/j)*(max 1 (Q/k)))^(1+ε)*(1+δ*max 1 (Q/k)) :=
      hcount S R H Q δ j k hR hH hQ hδ hRH hmem hjfix hkfix
    _ = C*(((R/j)*(H/j)*(max 1 (Q/k)))^(1+ε)*(1+δ*max 1 (Q/k))) := by ring
    _ ≤ C*(4*(2:ℝ)^ε*(R*H*Q)^(1+ε)*(1+δ*Q)/((j:ℝ)*(k:ℝ))) :=
      mul_le_mul_of_nonneg_left ha hC.le
    _ = _ := by ring

end TaoTrudgianYang2025
