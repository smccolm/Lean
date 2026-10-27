import Dubon2026.SourceFrickeIntegralHolomorphicRepresentative
import Dubon2026.SourceCuspLaurentSpan

/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
character realization -> differential/cusp comparison -> rational Fourier
spanning. The actual holomorphic principal-level function lies in the complex
span of actual holomorphic fractions over the original cyclotomic Fricke
algebra. This consumes integral constant descent and derives holomorphic
representatives, rather than assuming a rational spanning family. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm

/-- Actual holomorphic functions that are fractions of the cyclotomic j/Fricke algebra. -/
def holomorphicCyclotomicFrickeFractions (N : ℕ) : Set (ℍ → ℂ) :=
  {F | MDiff F ∧ ∃ a ∈ cyclotomicLevelRing N, ∃ b ∈ cyclotomicLevelRing N,
    b ≠ 0 ∧ F * b = a}

theorem holomorphicCyclotomicFrickeFractions_periodic {N : ℕ} [NeZero N]
    {F : ℍ → ℂ} (hF : F ∈ holomorphicCyclotomicFrickeFractions N) :
    Function.Periodic (F ∘ ofComplex) N := by
  obtain ⟨hF, a, ha, b, hb, hb0, he⟩ := hF
  exact periodic_cyclotomic_fraction ha hb hb0 hF he

theorem periodic_of_principal_invariant {N : ℕ} {F : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ) :
    Function.Periodic (F ∘ ofComplex) N := by
  apply periodic_comp_ofComplex_of_T
  apply hinv
  simpa only [Int.natAbs_natCast] using
    CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) N (dvd_refl _)

theorem mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (hF : MDiff F)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) :
    F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  obtain ⟨X, hXrep, hXspan⟩ :=
    exists_fricke_laurent_integral_span_of_principal_invariant F hF hinv hpb
  refine hXrep.mem_span_of_laurent_span (by exact_mod_cast NeZero.pos N) hF
    (periodic_of_principal_invariant hinv)
    (fun f hf => ⟨hf.1, holomorphicCyclotomicFrickeFractions_periodic hf⟩) ?_ hXspan
  intro Y hY
  obtain ⟨f, a, b, ha, hb, hb0, hfh, he, hrep, _⟩ :=
    exists_holomorphic_cyclotomic_fraction_of_integral_laurent hY
  exact ⟨f, ⟨hfh, a, ha, b, hb, hb0, he⟩, hrep⟩

end
end Dubon2026.SourceFricke