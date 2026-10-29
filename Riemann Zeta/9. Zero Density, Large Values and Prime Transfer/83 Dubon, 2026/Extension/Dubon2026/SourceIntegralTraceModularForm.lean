import Dubon2026.SourceGammaOnePlusMinus
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Construct the actual
level-one modular form from the prescribed signed coset transversal.
Native plusMinus and its membership theorem replace the upstream
duplicate signed subgroup. Native trace uses arbitrary quotient
representatives; the prescribed representatives here expose the
distinguished cusp term required by coefficient extraction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_exists_levelOne_coe_eq_sum_slash. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane GammaOne
variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

theorem slash_neg_even (hk : Even k) (F : ℍ → ℂ) (y : SL(2, ℤ)) : F ∣[k] (-y) = F ∣[k] y := by
  ext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul]
  congr 1
  have : ((-y : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(y : GL (Fin 2) ℝ) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.toGL]
  rw [this, denom_neg, Even.neg_zpow (Even.neg hk)]

variable (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)

private theorem slash_pm_mul (hk : Even k) {γ : SL(2, ℤ)} (hγ : γ ∈ plusMinus Γ) (y : SL(2, ℤ)) :
    (⇑f : ℍ → ℂ) ∣[k] (γ * y) = (⇑f : ℍ → ℂ) ∣[k] y := by
  rcases (mem_plusMinus_iff Γ γ).mp hγ with hγ | hγ
  · rw [SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) γ) (Subgroup.mem_map_of_mem _ hγ))
  · rw [show γ * y = -((-γ) * y) by rw [neg_mul, neg_neg], slash_neg_even hk, SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) (-γ)) (Subgroup.mem_map_of_mem _ hγ))

private theorem mdifferentiable_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact fun _ => mdifferentiableAt_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem isBoundedAtImInfty_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (g i)) : IsBoundedAtImInfty (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Filter.const_boundedAtFilter _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_levelOne_trace
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (s : Finset SL(2, ℤ))
    (hcover : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) :
    ∃ F : ModularForm 𝒮ℒ k,
      (⇑F : UpperHalfPlane → ℂ) = ∑ x ∈ s, ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  classical

  have rep : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ plusMinus Γ := by
    intro g
    obtain ⟨x, hx, hg⟩ := hcover g
    exact ⟨x, hx, (mem_plusMinus_iff Γ _).mpr hg⟩
  choose ρ hρs hρ using rep

  have ρ_eq : ∀ (g : SL(2, ℤ)) (x : SL(2, ℤ)), x ∈ s → g * x⁻¹ ∈ plusMinus Γ → ρ g = x := fun g x hx hgx =>
    hsep _ (hρs g) _ hx ((mem_plusMinus_iff Γ _).mp (by
      have := (plusMinus Γ).mul_mem ((plusMinus Γ).inv_mem (hρ g)) hgx
      rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this))

  set T : ℍ → ℂ := ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) with hT
  have hTx : T = ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] x) := by
    rw [hT]; exact Finset.sum_congr rfl fun x _ => (ModularForm.SL_slash _ x).symm

  have hinv : ∀ a : SL(2, ℤ), T ∣[k] a = T := by
    intro a
    rw [hTx, SlashAction.sum_slash]
    simp_rw [← SlashAction.slash_mul]
    refine Finset.sum_nbij' (fun x => ρ (x * a)) (fun x => ρ (x * a⁻¹)) (fun x _ => hρs _) (fun x _ => hρs _)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · apply ρ_eq _ _ hx
      have := (plusMinus Γ).inv_mem (hρ (x * a))
      rw [mul_inv_rev, inv_inv, mul_inv_rev, ← mul_assoc] at this
      exact this
    · apply ρ_eq _ _ hx
      have := (plusMinus Γ).inv_mem (hρ (x * a⁻¹))
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, ← mul_assoc] at this
      exact this
    ·
      have h := slash_pm_mul f hk (hρ (x * a)) (ρ (x * a))
      rw [inv_mul_cancel_right] at h
      exact h
  have hslash : ∀ A ∈ 𝒮ℒ, T ∣[k] A = T := by
    intro A hA
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hA
    exact hinv a
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T := by
    rw [hT]
    exact mdifferentiable_sum s _ fun x _ => (ModularFormClass.holo f).slash k _
  have hbdd : ∀ {c : OnePoint ℝ}, IsCusp c 𝒮ℒ → c.IsBoundedAt T k := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    rw [hTx, SlashAction.sum_slash]
    refine isBoundedAtImInfty_sum s _ fun x _ => ?_
    rw [← SlashAction.slash_mul]
    exact ModularFormClass.bdd_at_infty_slash f (x * γ)
  exact ⟨ModularForm.mk (SlashInvariantForm.mk T hslash) hholo (fun hc => hbdd hc), rfl⟩

end
end Dubon2026.SourceFunctionField.IntegralTrace
