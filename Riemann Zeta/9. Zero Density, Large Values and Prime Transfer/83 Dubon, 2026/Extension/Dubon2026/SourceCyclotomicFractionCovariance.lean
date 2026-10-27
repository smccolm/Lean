import Dubon2026.SourceCyclotomicLevelRingCovariance
import Dubon2026.SourceCyclotomicConjugateCancellation
import Dubon2026.SourceCyclotomicGammaOneLift

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> covariance and level preservation of actual analytic conjugates.
Transport original numerators and denominators, identify their actual
conjugate quotient by analytic uniqueness, and consume the integral modular
lifts. The original Gamma1 invariance is retained with no extra premise. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem CyclotomicConjugates.modular {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N}
    {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N)
    (s : ℕ) (hs : s.Coprime N) (hσ : σ (zetaK N) = zetaK N ^ s) (A A' : SL(2, ℤ))
    (hconj : ∀ v : Fin 2 → ZMod N,
      vecMulSL N (cyclotomicTorsionVector s v) A =
        cyclotomicTorsionVector s (vecMulSL N v A')) :
    CyclotomicConjugates σ (F ∘ (A' • ·)) (G ∘ (A • ·)) := by
  obtain ⟨_, P, hP, Q, hQ, hQ0, hFQ⟩ := hF
  obtain ⟨P', hP', hPP', hPA⟩ :=
    exists_cyclotomic_levelRing_modular_conjugate σ s hs hσ A A' hconj hP
  obtain ⟨Q', hQ', hQQ', hQA⟩ :=
    exists_cyclotomic_levelRing_modular_conjugate σ s hs hσ A A' hconj hQ
  have hprod : CyclotomicConjugates σ P (G * Q') := by
    simpa only [hFQ] using hFG.mul hQQ'
  have hGQ : G * Q' = P' := hprod.unique hPP'
    (holomorphicCyclotomicFrickeFractions_mul hG (cyclotomicLevelRing_holomorphicFraction hQ'))
    (cyclotomicLevelRing_holomorphicFraction hP')
  have hQA' : Q ∘ (A' • ·) ∈ cyclotomicLevelRing N := by
    simpa only [sl_smul_def, inv_inv, Function.comp_def] using smul_mem_cyclotomicLevelRing A'⁻¹ hQ
  have hQA'0 : Q ∘ (A' • ·) ≠ 0 := by
    intro hz
    apply hQ0
    funext τ
    have he := congrFun hz (A'⁻¹ • τ)
    simpa only [Function.comp_apply, smul_inv_smul, Pi.zero_apply] using he
  apply hPA.of_mul_eq hQA (cyclotomicLevelRing_holomorphicFraction hQA') hQA'0
  · funext τ
    exact congrFun hFQ (A' • τ)
  · funext τ
    exact congrFun hGQ (A • τ)

theorem CyclotomicConjugates.exists_modular {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N}
    {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) (A : SL(2, ℤ)) :
    ∃ A' : SL(2, ℤ), CyclotomicConjugates σ (F ∘ (A' • ·)) (G ∘ (A • ·)) := by
  obtain ⟨s, hs, hσ⟩ := exists_cyclotomic_aut_exponent N σ
  obtain ⟨A', hA'⟩ := exists_modular_cyclotomic_conjugate N s hs A
  exact ⟨A', hFG.modular hF hG s hs hσ A A' hA'⟩

theorem CyclotomicConjugates.gammaOne_invariant {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N}
    {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, F (γ • τ) = F τ) :
    ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (γ • τ) = G τ := by
  intro γ hγ τ
  obtain ⟨s, hs, hσ⟩ := exists_cyclotomic_aut_exponent N σ
  obtain ⟨γ', hγ', hconj⟩ := exists_gammaOne_cyclotomic_conjugate N s hs hγ
  have hrel := hFG.modular hF hG s hs hσ γ γ' hconj
  have heF : F ∘ (γ' • ·) = F := funext (hFinv γ' hγ')
  rw [heF] at hrel
  have hGγ : G ∘ (γ • ·) ∈ holomorphicCyclotomicFrickeFractions N := by
    simpa only [sl_smul_def, inv_inv, Function.comp_def] using
      smul_mem_holomorphicCyclotomicFrickeFractions γ⁻¹ hG
  exact congrFun (hrel.unique hFG hGγ hG) τ

end
end Dubon2026.SourceFricke
