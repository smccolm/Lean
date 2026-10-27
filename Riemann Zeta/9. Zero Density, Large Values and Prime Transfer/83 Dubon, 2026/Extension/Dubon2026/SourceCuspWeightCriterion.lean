import Dubon2026.SourceCuspWeightHolomorphicDivision
import Dubon2026.SourceCuspWeightTransformation

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> exact cusp-image characterization. The actual cusp-form image is
characterized by the E4/E6 power divisibilities, vanishing at every cusp,
and original subgroup invariance with the exact weight balance. Local
monic division, coprime gluing and native analytic cancellation construct
the actual cusp form. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff. -/
namespace Dubon2026.SourceFunctionField.CuspWeightCriterion
noncomputable section
open UpperHalfPlane ModularForm Filter
open scoped Topology Manifold MatrixGroups ModularForm
local notation "Δ" => ModularForm.discriminant

theorem forward {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m : ℕ}
    (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ}
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) :
    ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
      (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
      (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) := by
  have hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := f.holo'
  refine ⟨⟨fun τ => f τ ^ 3 * E₆ τ ^ (3 * b), (hfhol.pow 3).mul (JMultiplicity.mdiff_E₆.pow _), fun τ => ?_⟩,
    ⟨fun τ => f τ ^ 2 * E₄ τ ^ (2 * a), (hfhol.pow 2).mul (JMultiplicity.mdiff_E₄.pow _), fun τ => ?_⟩,
    fun A => ?_, fun γ hγ τ => ?_⟩
  · rw [← hf τ]; ring
  · rw [← hf τ]; ring
  ·
    have hfA : IsZeroAtImInfty ((⇑f : ℍ → ℂ) ∣[k] A) := CuspFormClass.zero_at_infty_slash f A
    have hEq : ((F ∘ (A • ·)) * Δ ^ m : ℍ → ℂ) = fun τ => ((⇑f : ℍ → ℂ) ∣[k] A) τ * eisensteinFactor a b τ := by
      funext τ
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply]
      exact (slash_mul_eisensteinFactor hk hf A τ).symm
    rw [hEq]
    exact hfA.mul_boundedAtFilter (isBoundedAtImInfty_eisensteinFactor a b)
  ·
    have h := slash_mul_eisensteinFactor hk hf γ τ
    have hinv : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
      have := SlashInvariantForm.slash_action_eqn f (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    rw [hinv] at h
    rw [eisensteinFactor, hf τ] at h
    have hΔ : Δ τ ^ m ≠ 0 := pow_ne_zero _ (discriminant_ne_zero τ)
    exact (mul_left_injective₀ hΔ h).symm

theorem backward {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m : ℕ}
    (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ} (hF : MDiff F)
    (h₁ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ)
    (h₂ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ)
    (h₃ : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m))
    (h₄ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k,
      ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m := by

  obtain ⟨H₁, hH₁, hH₁E⟩ := exists_div_E4 hF h₁
  obtain ⟨H₂, hH₂, hH₂E⟩ := exists_div_E6 hF h₂
  have hcop : ∀ τ : ℍ, E₄ τ ^ a ≠ 0 ∨ E₆ τ ^ b ≠ 0 := fun τ =>
    (E4_ne_zero_or_E6_ne_zero τ).imp (pow_ne_zero a) (pow_ne_zero b)
  obtain ⟨f, hfhol, hfE⟩ := exists_mul_eq_of_coprime (JMultiplicity.mdiff_E₄.pow a) (JMultiplicity.mdiff_E₆.pow b)
    hH₁ hH₂ hcop hH₁E hH₂E
  have hfE' : ∀ τ : ℍ, f τ * eisensteinFactor a b τ = F τ * Δ τ ^ m := hfE

  have hinv : ∀ γ ∈ Γ, f ∣[k] γ = f := by
    intro γ hγ
    have hzero : ∀ τ : ℍ, ((f ∣[k] γ) τ - f τ) * eisensteinFactor a b τ = 0 := by
      intro τ
      rw [sub_mul, slash_mul_eisensteinFactor hk hfE' γ τ, hfE' τ, h₄ γ hγ τ, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_eisensteinFactor_ne_zero a b
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (f ∣[k] γ) τ - f τ) := by
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hfhol.slash k _
      exact h1.sub hfhol
    have hz := ((UpperHalfPlane.mul_eq_zero_iff hdiff
      (mdifferentiable_eisensteinFactor a b)).mp (funext hzero)).resolve_right
        (fun he => hτ₀ (congrFun he τ₀))
    exact sub_eq_zero.mp hz

  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] A) := by
    intro A
    have hE1 : Tendsto (eisensteinFactor a b) atImInfty (𝓝 1) := tendsto_eisensteinFactor a b
    have hne : ∀ᶠ τ in atImInfty, eisensteinFactor a b τ ≠ 0 := hE1.eventually_ne one_ne_zero
    have hq : Tendsto (fun τ => ((F ∘ (A • ·)) * Δ ^ m) τ / eisensteinFactor a b τ) atImInfty (𝓝 0) := by
      have h__af := (h₃ A).div hE1 one_ne_zero
      simp at h__af
      exact h__af
    refine (hq.congr' ?_)
    filter_upwards [hne] with τ hτ
    rw [div_eq_iff hτ]
    simpa [Pi.mul_apply, Function.comp_apply, Pi.pow_apply] using (slash_mul_eisensteinFactor hk hfE' A τ).symm

  let fC : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := f
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hfhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  exact ⟨fC, fun τ => hfE τ⟩

theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : ℍ,
        f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) ↔
      ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :=
  ⟨fun ⟨f, hf⟩ => forward hk f hf, fun ⟨h₁, h₂, h₃, h₄⟩ => backward hk hF h₁ h₂ h₃ h₄⟩

end
end Dubon2026.SourceFunctionField.CuspWeightCriterion
