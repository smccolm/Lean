import Dubon2026.SourceHolomorphicCoprimeDivision
import Dubon2026.SourceInverseJLimits

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> cusp-image characterization. Reuse the native modular forms, existing
E4 limit and discriminant identity. The actual E4/E6 factor is holomorphic,
has no identically-zero power, and tends to one at infinity. Only the
missing E6 limit is proved using its native constant Fourier coefficient. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped Topology Manifold ModularForm

/-- The actual Eisenstein factor used to lower the modular weight. -/
def eisensteinFactor (a b : ℕ) : ℍ → ℂ := fun τ => E₄ τ ^ a * E₆ τ ^ b

theorem mdifferentiable_eisensteinFactor (a b : ℕ) : MDiff (eisensteinFactor a b) :=
  (JMultiplicity.mdiff_E₄.pow a).mul (JMultiplicity.mdiff_E₆.pow b)

theorem E4_ne_zero_or_E6_ne_zero (τ : ℍ) : E₄ τ ≠ 0 ∨ E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have he := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [h.1, h.2] at he
  exact discriminant_ne_zero τ (by rw [he]; norm_num)

theorem tendsto_E6_atImInfty : Tendsto (E₆ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : cuspFunction 1 (E₆ : ℍ → ℂ) 0 = 1 := by
    simpa only [qExpansion_coeff, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedDeriv_zero, one_mul] using
      (EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩)
  have ht := (ModularFormClass.analyticAt_cuspFunction_zero E₆ one_pos
    one_mem_strictPeriods_SL).continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  simpa only [Function.comp_def,
    SlashInvariantFormClass.eq_cuspFunction E₆ _ one_mem_strictPeriods_SL one_ne_zero, h0] using ht

theorem exists_E4_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 :=
  (JMultiplicity.tendsto_E₄_atImInfty.eventually_ne one_ne_zero).exists

theorem exists_E6_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 :=
  (tendsto_E6_atImInfty.eventually_ne one_ne_zero).exists

theorem tendsto_eisensteinFactor (a b : ℕ) :
    Tendsto (eisensteinFactor a b) atImInfty (𝓝 1) := by
  simpa only [one_pow, mul_one] using
    (JMultiplicity.tendsto_E₄_atImInfty.pow a).mul (tendsto_E6_atImInfty.pow b)

theorem exists_eisensteinFactor_ne_zero (a b : ℕ) : ∃ τ : ℍ, eisensteinFactor a b τ ≠ 0 :=
  ((tendsto_eisensteinFactor a b).eventually_ne one_ne_zero).exists

theorem isBoundedAtImInfty_eisensteinFactor (a b : ℕ) : IsBoundedAtImInfty (eisensteinFactor a b) :=
  (tendsto_eisensteinFactor a b).isBigO_one ℝ

end
end Dubon2026.SourceFunctionField.CuspWeightCriterion