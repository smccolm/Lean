import Dubon2026.SourceFrickeStableFractionV2
import Dubon2026.SourceFrickeStableMonicV2

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite
Gamma1 character realization -> Picard/H1 comparison -> cusp differential
realization -> rational Fourier structure. The modular orbit of the original
holomorphic function supplies the stable family, rather than assuming a
Fricke representation. The actual family theorem and native action polynomial
then give its Fricke fraction and monic relation over the original analytic j.
-/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups ModularForm Manifold

theorem mdifferentiable_slFn {F : ℍ → ℂ} (hF : MDiff F) (γ : SL(2, ℤ)) :
    MDiff (γ • F) := by
  have h : MDiff (F ∣[(0 : ℤ)] γ⁻¹) := hF.slash 0 _
  have he : F ∣[(0 : ℤ)] γ⁻¹ = γ • F := by
    funext τ
    simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one, sl_smul_apply]
  exact he ▸ h

/-- Adjoin the actual modular orbit to the actual Fricke generators. -/
def modularOrbitGens (N : ℕ) [NeZero N] (F : ℍ → ℂ) (hF : MDiff F)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) : LevelGens N where
  S := levelGen N ∪ Set.range (fun γ : SL(2, ℤ) => γ • F)
  levelGen_subset := Set.subset_union_left
  poleBounded := by
    rintro f (hf | ⟨γ, rfl⟩)
    · exact levelGen_poleBounded N f hf
    · refine ⟨mdifferentiable_slFn hF γ, ?_⟩
      simpa only [sl_smul_def, Function.comp_def] using hpb γ⁻¹
  smul_mem := by
    rintro δ f (hf | ⟨γ, rfl⟩)
    · exact Or.inl (smul_mem_levelGen δ hf)
    · exact Or.inr ⟨δ * γ, mul_smul δ γ F⟩
  invariant := by
    rintro f (hf | ⟨α, rfl⟩) γ hγ τ
    · exact (LevelGens.std N).invariant f hf γ hγ τ
    · simp only [sl_smul_apply]
      have hc : α⁻¹ * γ * α ∈ CongruenceSubgroup.Gamma N := by
        simpa using Subgroup.Normal.conj_mem (CongruenceSubgroup.Gamma_normal N) γ hγ α⁻¹
      calc
        F (α⁻¹ • (γ • τ)) = F ((α⁻¹ * γ * α) • (α⁻¹ • τ)) := by simp only [mul_smul, smul_inv_smul]
        _ = F (α⁻¹ • τ) := hinv _ hc _

theorem exists_fraction_and_monic_j_of_principal_invariant {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (hF : MDiff F)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) :
    (∃ a b : ↥(levelRing N), b ≠ 0 ∧ F * b = a) ∧
      ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
        F τ ^ d + ∑ i : Fin d, (p i).eval (JMultiplicity.jf τ) * F τ ^ (i : ℕ) = 0 := by
  let D := modularOrbitGens N F hF hinv hpb
  have hmem : F ∈ D.S := Or.inr ⟨1, one_smul _ F⟩
  exact ⟨D.exists_frac hmem,
    D.ring_monic_j_relation ⟨F, Algebra.subset_adjoin hmem⟩⟩

end
end Dubon2026.SourceFricke
