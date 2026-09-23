import TaoTrudgianYang2025.SargosPlanarGram

/-! Integration of the literal finite weighted Gram expansion. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem integrable_sargosWeightedPlanarIntegrand_inner_complex {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (a c d α : ℝ) :
    Integrable (fun γ : ℝ => (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ)) := by
  simp_rw [sargosWeightedPlanarIntegrand_eq_gram]
  apply integrable_finsetSum
  intro p hp
  exact (integrable_sargosPlanarKernelTerm_inner hb a c d (u p.1-u p.2) (v p.1-v p.2) α).const_mul (z p.1*conj (z p.2))

theorem integrable_sargosWeightedPlanarIntegrand_inner {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (a c d α : ℝ) :
    Integrable (sargosWeightedPlanarIntegrand S z u v a b c d α) := by
  have h := (integrable_sargosWeightedPlanarIntegrand_inner_complex S z u v hb a c d α).re
  simpa only [Complex.ofReal_re] using h

theorem integral_sargosWeightedPlanarIntegrand_inner_complex {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (a c d α : ℝ) :
    (∫ γ : ℝ, (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ)) =
      ∑ p ∈ S ×ˢ S, (z p.1*conj (z p.2))*
        ∫ γ : ℝ, sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ := by
  simp_rw [sargosWeightedPlanarIntegrand_eq_gram]
  rw [integral_finsetSum (S ×ˢ S) (fun p _ =>
    (integrable_sargosPlanarKernelTerm_inner hb a c d (u p.1-u p.2) (v p.1-v p.2) α).const_mul (z p.1*conj (z p.2)))]
  simp_rw [integral_const_mul]

theorem integrable_sargosWeightedPlanarIntegrand_outer_complex {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    Integrable (fun α : ℝ =>
      ∫ γ : ℝ, (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ)) := by
  simp_rw [integral_sargosWeightedPlanarIntegrand_inner_complex S z u v hb]
  apply integrable_finsetSum
  intro p hp
  exact (integrable_sargosPlanarKernelTerm_outer ha hb c d (u p.1-u p.2) (v p.1-v p.2)).const_mul (z p.1*conj (z p.2))

theorem integrable_sargosWeightedPlanarIntegrand_outer {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    Integrable (fun α : ℝ =>
      ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v a b c d α γ) := by
  have h := (integrable_sargosWeightedPlanarIntegrand_outer_complex S z u v ha hb c d).re
  simpa only [integral_complex_ofReal,RCLike.ofReal_re] using h

theorem integral_sargosWeightedPlanarIntegrand_eq_gram {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u v : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    ((∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℝ) : ℂ) =
      ∑ p ∈ S ×ˢ S, (z p.1*conj (z p.2))*
        ∫ α : ℝ, ∫ γ : ℝ,
          sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ := by
  calc
    _ = ∫ α : ℝ, ∫ γ : ℝ, (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ) := by
      simp only [integral_complex_ofReal]
    _ = ∫ α : ℝ, ∑ p ∈ S ×ˢ S, (z p.1*conj (z p.2))*
        ∫ γ : ℝ, sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ := by
      simp_rw [integral_sargosWeightedPlanarIntegrand_inner_complex S z u v hb]
    _ = ∑ p ∈ S ×ˢ S, ∫ α : ℝ, (z p.1*conj (z p.2))*
        ∫ γ : ℝ, sargosPlanarKernelTerm a b c d (u p.1-u p.2) (v p.1-v p.2) α γ := by
      exact integral_finsetSum (S ×ˢ S) (fun p _ =>
        (integrable_sargosPlanarKernelTerm_outer ha hb c d (u p.1-u p.2) (v p.1-v p.2)).const_mul (z p.1*conj (z p.2)))
    _ = _ := by simp_rw [integral_const_mul]

end TaoTrudgianYang2025
