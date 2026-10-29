import Dubon2026.SourceIntegralTraceDecomposition
import Dubon2026.SourceIntegralTraceDegenerateCusp
import Dubon2026.SourceIntegralTraceCoefficientExtraction
import Dubon2026.SourceIntegralTraceParameters

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. For the actual even-weight
modular form, derive S-slash coefficient integrality from a separately
specified peaked auxiliary form. The trace, signed representatives,
Fourier decomposition, decay vanishing, weight adjustment and coefficient
extraction are all constructed in the proof. Existence of the peaked
auxiliary form remains an explicit upstream obligation. Even-weight
integral ratios suffice for the original field generators by the proved
SourceGammaOneEvenIntegralRatios reduction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

theorem even_weight_slash_coeff_mem_of_peaked_auxiliary
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ)
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hk : Even k) (hw : Even w)
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n, (qExpansion (h : ℝ) (⇑G : ℍ → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n, (qExpansion (h : ℝ) (⇑Θ : ℍ → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n < m₀, (qExpansion 1
      ((⇑Θ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (qExpansion 1
      ((⇑Θ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n, (qExpansion 1
      ((⇑Θ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[atImInfty]
        fun τ : ℍ => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (n : ℕ) :
    (qExpansion 1 ((⇑G : ℍ → ℂ) ∣[k]
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by
  classical
  by_cases hdeg : ∃ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∈ Γ ∨
      -(ModularGroup.S * ModularGroup.T ^ j) ∈ Γ
  · exact slash_coeff_mem_of_coincident_cusps Γ h hh hS R hk G hG hdeg n
  push Not at hdeg
  have hm₀' : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | h0
    · exfalso
      subst h0
      have hwneg : w < 0 := by simpa using hm₀
      have hΘ0 : Θ = 0 := ModularForm.isZero_of_neg_weight hwneg Θ
      obtain ⟨v, _, hv⟩ := hΘS₁
      have hz : ((⇑Θ : ℍ → ℂ) ∣[w]
          ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) = 0 := by
        rw [hΘ0, ModularForm.coe_zero, SlashAction.zero_slash]
      rw [hz, qExpansion_zero, map_zero, mul_zero] at hv
      exact zero_ne_one hv
    · exact h0
  obtain ⟨h₀, hh₀, hh₀h, hT₀, hmin⟩ := exists_width Γ h hh hT
  obtain ⟨r, a, b, d, _, hwt, hd, hrδ⟩ :=
    exists_trace_parameters (hk.add hw) m₀ hm₀ hm₀' δ hδ n
  have hev : Even (k + (r : ℤ) * w) := hk.add (hw.mul_left _)
  obtain ⟨F, A, C, hqF, hA, hC⟩ := exists_integral_trace_decomposition
    Γ h hh hT hS R G hG Θ hΘ r h₀ m₀ δ hev hh₀ hh₀h hT₀ hmin hdeg hdecay
  exact coeff_mem_of_levelOne_trace_decomposition R (k + (r : ℤ) * w)
    a b d r m₀ δ (by omega) hd F A _ _ C hqF hA hΘS hΘS₀ hΘS₁ hC n hrδ

end
end Dubon2026.SourceFunctionField.IntegralTrace
