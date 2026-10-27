import Dubon2026.SourceFrickeHolomorphicIntegralSpan
import Dubon2026.SourceMeromorphicCuspPoleClearing

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational Fourier spanning.
The cyclotomic Laurent representation already proved for actual Fricke
fractions gives every Fourier coefficient after a discriminant power clears
the cusp pole. This eliminates the external recursive division argument and
the additional monic-growth premise at this stage. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

theorem exists_pole_cleared_cyclotomic_qExpansion {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ m : ℕ,
      Function.Periodic ((F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∘ ofComplex) N ∧
      IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∧
      ∀ n : ℕ, (qExpansion N (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ)).coeff n ∈ kN N := by
  have hper := holomorphicCyclotomicFrickeFractions_periodic hF
  obtain ⟨hFhol, a, ha, b, hb, hb0, he⟩ := hF
  obtain ⟨X, hX⟩ := exists_cyclotomic_fraction_represents ha hb hb0 he
  obtain ⟨m, hm⟩ := exists_bounded_mul_discriminant_of_meromorphic hper hX.meromorphicAt
  have hpm := periodic_mul_discriminant hper m
  have hrep : CuspTaylor.Represents
      (coeffMap (algebraMap (kN N) ℂ) (X * discriminantLaurentK N ^ m))
      (cuspFunction N (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ)) := by
    rw [map_mul, map_pow, coeffMap_discriminantLaurentK]
    exact hX.cusp_mul ((represents_discriminant_width N).cusp_pow m)
  have hqrep := CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N)
    hpm (hFhol.mul (CuspForm.discriminant.holo'.pow m)) hm
  have hseries := hrep.eq_series hqrep
  refine ⟨m, hpm, hm, fun n => ?_⟩
  have hc := congrArg (fun Y : LaurentSeries ℂ => Y.coeff (n : ℤ)) hseries
  dsimp only at hc
  rw [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at hc
  rw [← hc]
  exact (X * discriminantLaurentK N ^ m).coeff (n : ℤ) |>.property

/-- Actual holomorphic functions with cyclotomic Fourier coefficients after clearing a cusp pole. -/
def cyclotomicPoleBoundedFunctions (N : ℕ) : Set (ℍ → ℂ) :=
  {F | MDiff F ∧ ∃ m : ℕ,
    Function.Periodic ((F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∧
    ∀ n : ℕ, (qExpansion N (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ)).coeff n ∈ kN N}

theorem mem_span_pole_cleared_cyclotomic_of_principal_invariant
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (hF : MDiff F)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) :
    F ∈ Submodule.span ℂ (cyclotomicPoleBoundedFunctions N) := by
  apply (Submodule.span_mono (show holomorphicCyclotomicFrickeFractions N ⊆
    cyclotomicPoleBoundedFunctions N from fun g hg =>
      ⟨hg.1, exists_pole_cleared_cyclotomic_qExpansion hg⟩))
  exact mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant F hF hinv hpb

end
end Dubon2026.SourceFricke